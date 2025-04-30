export MCMCConfig, solve_task, html_path, get_strat, is_solved, get_task_constrain_fn, long_json, short_json, quick_evaluate_solution, no_evaluate_solution
export warmstart_config
@kwdef struct MCMCConfig
    steps::Int = 5000
    time_limit::Float64 = 0. # overrides steps if nonzero
    pcfg::Grammar
    size_dist::Any = Geometric(0.5)
    start::Union{String,Nothing} = nothing
    check_solved::Function = e -> e
    eval_builder::Function = task -> TaskConstrain(task, BDDEvalStateConfig(; time_limit = 0.015, max_depth = 500); temperature = 0.4)
    evaluate_solution::Function = quick_evaluate_solution
    log_every::Int = 100
end



function no_evaluate_solution(expr, task)
    return nothing, nothing
end

function quick_evaluate_solution(expr, task)
    @warn "Using quick evaluation"
    tc = TaskConstrain(task, BDDEvalStateConfig(; time_limit = 1.0, max_depth = 1000); temperature = 1.0)
    train_res = tc(expr; cache=false, test=false)
    test_res = task.num_train < length(task.ios) ? tc(expr; cache=false, test=true) : nothing
    return train_res, test_res
end

function train_only_evaluate_solution(expr, task)
    # @warn "Using train only evaluation"
    tc = TaskConstrain(task, BDDEvalStateConfig(; time_limit = 1.0, max_depth = 1000); temperature = 1.0, train_only=true)
    train_res = tc(expr; cache=false, test=false)
    test_res = tc(expr; cache=false, test=true)
    return train_res, test_res
end


html_path(::MCMCConfig) = "html/mcmc.html"
get_strat(::MCMCConfig) = :mcmc
JSON.lower(x::MCMCConfig) = Dict(
    :strat => :mcmc,
    :steps => x.steps,
    :time_limit => x.time_limit,
    :pcfg => string(x.pcfg),
    :start => x.start,
    :size_dist => x.size_dist,
    :log_every => x.log_every,
)

warmstart_config(x::MCMCConfig) = MCMCConfig(
    100,
    0.,
    x.pcfg,
    x.size_dist,
    x.start,
    x.check_solved,
    x.eval_builder,
    x.evaluate_solution,
    x.log_every,
)


struct MCMCStep
    step::Int
    expr::String
    loglikelihood::Float64
    logprior::Float64
    logposterior::Float64
    loglikelihood_ratio::Float64
    logproposal_ratio::Float64
    logprior_ratio::Float64
    acceptance::Float64
end

struct MCMCStateLog
    step::Int
    num_accepted::Int
    proposals::Vector{String}
    expr::String
    logprior::Float64
    train_res::Union{TaskConstrainResult,Nothing}
    test_res::Union{TaskConstrainResult,Nothing}
    quick_train_res::Union{TaskConstrainResult,Nothing}
    quick_test_res::Union{TaskConstrainResult,Nothing}
    time::Float64
    time_in_eval::Float64
end



mutable struct MCMCResult
    config::MCMCConfig
    current::PExpr
    task_res::TaskConstrainResult
    likelihood::Float64
    prior::Float64
    posterior::Float64
    samples::Dict{String, Int}
    task_constrain_fn::TaskConstrain
    solved::Bool
    time::Float64
    evaltime::Float64
    history::Vector{MCMCStep}
    num_steps::Int
    unique_constrains::Int
    tdd::TimeDataDict
    state_log::Vector{MCMCStateLog}
end
is_solved(x::MCMCResult) = x.solved
get_task_constrain_fn(x::MCMCResult) = x.task_constrain_fn
get_task_constrain_fn(x::Vector{MCMCResult}) = get_task_constrain_fn(x[end])

function JSON.lower(x::MCMCResult)
    Dict(
        :config => x.config,
        :current => string(x.current),
        :task_res => x.task_res,
        :likelihood => x.likelihood,
        :prior => x.prior,
        :posterior => x.posterior,
        :samples => x.samples,
        :solved => x.solved,
        :time => x.time,
        :evaltime => x.evaltime,
        :unique_constrains => x.unique_constrains,
        :history => x.history,
        :state_log => x.state_log,
    )
end

short_json(x::Vector) = short_json.(x)

function short_json(x::MCMCResult)
    Dict(
        :config => x.config,
        :task_res => x.task_res,
        :current => string(x.current),
        :likelihood => x.likelihood,
        :prior => x.prior,
        :posterior => x.posterior,
        :solved => x.solved,
        :time => x.time,
        :evaltime => x.evaltime,
        :num_steps => x.num_steps,
        :unique_constrains => x.unique_constrains,
        :state_log => x.state_log,
    )
end


function solve_task(
    config::MCMCConfig,
    task::PTask
)
    pcfg = config.pcfg
    tdd = TimeDataDict()

    solved = false

    tstart = time()
    time_in_eval = 0.
    start = isnothing(config.start) ? pcfg.start_expr_of_type[return_type(task.type)] : parse_expr(config.start)

    current = parsed_expr(pcfg, copy(start), return_type(task.type), arg_types(task.type))
    
    logprior_curr = logprob(pcfg_dist, pcfg, current)
    task_constrain_fn = config.eval_builder(task)
    old_time_limit = get_time_limit(task_constrain_fn.config)
    set_time_limit!(task_constrain_fn.config, 1.0)
    task_constrain_fn(current.expr.child; cache=false) # warmstart
    task_constrain_fn(current.expr.child; cache=false) # warmstart
    task_constrain_fn(current.expr.child; cache=false) # warmstart
    set_time_limit!(task_constrain_fn.config, old_time_limit)
    task_res_curr = task_constrain_fn(current.expr.child)
    loglikelihood_curr = task_res_curr.logweight

    samples = Dict{String, Int}()
    history = Vector{MCMCStep}()
    state_log = Vector{MCMCStateLog}()
    proposals = Vector{String}()
    num_accepted = 0

    i = 0
    while (config.time_limit > 0 && time() - tstart < config.time_limit) || (i < config.steps)
        i += 1

        if (i-1) % config.log_every == 0
            time_in_eval += @elapsed((train_res, test_res) = config.evaluate_solution(current.expr.child, task))
            quick_train_res = task_res_curr
            time_in_eval += @elapsed(quick_test_res = task.num_train < length(task.ios) ? task_constrain_fn(current.expr.child; cache=false, test=true) : nothing)
            push!(state_log, MCMCStateLog(i, num_accepted, proposals, string(current.expr.child), logprior_curr, train_res, test_res, quick_train_res, quick_test_res, time() - tstart, time_in_eval))
        end


        proposal, logproposal_ratio, path = modify_expression(
            reparse(current, pcfg),
            pcfg
        )

        task_res_after = task_constrain_fn(proposal.expr.child)
        loglikelihood_after = task_res_after.logweight
        logprior_after = logprob(pcfg_dist, pcfg, proposal)

        loglikelihood_ratio = loglikelihood_after - loglikelihood_curr
        logprior_ratio = logprior_after - logprior_curr
        acceptance_ratio = min(1, exp(loglikelihood_ratio + logproposal_ratio + logprior_ratio))

        u = rand()
        if u < acceptance_ratio


            num_accepted += 1
            # Only print if there's a real change in the expression and likelihood
            if string(current.expr.child) != string(proposal.expr.child) # && !isapprox(loglikelihood_after, loglikelihood_curr)
                push!(
                    history,
                    MCMCStep(
                        i,
                        highlight_subexpression((proposal.expr.child), path, "<<<", ">>>"),
                        loglikelihood_after,
                        logprior_after,
                        logprior_after + loglikelihood_after,
                        loglikelihood_ratio,
                        logproposal_ratio,
                        logprior_ratio,
                        acceptance_ratio,
                    )
                )
            end

            current = proposal
            loglikelihood_curr = loglikelihood_after
            logprior_curr = logprior_after
            task_res_curr = task_res_after

            if isapprox(loglikelihood_curr, 0.0)
                solved = true
                break
            end

        end

        # Update the samples dictionary
        !haskey(samples, string(current.expr.child)) && (samples[string(current.expr.child)] = 0)
        samples[string(current.expr.child)] += 1
    end

    if isempty(state_log) || state_log[end].step != i
        time_in_eval += @elapsed((train_res, test_res) = config.evaluate_solution(current.expr.child, task))
        quick_train_res = task_res_curr
        time_in_eval += @elapsed(quick_test_res = task.num_train < length(task.ios) ? task_constrain_fn(current.expr.child; cache=false, test=true) : nothing)
        push!(state_log, MCMCStateLog(i, num_accepted, proposals, string(current.expr.child), logprior_curr, train_res, test_res, quick_train_res, quick_test_res, time() - tstart, time_in_eval))
    end


    res = [MCMCResult(config, current.expr.child, task_res_curr, exp(loglikelihood_curr), exp(logprior_curr), exp(loglikelihood_curr + logprior_curr), samples, task_constrain_fn, solved, time() - tstart, total_time(task_constrain_fn),  history, i, length(task_constrain_fn.cache), tdd, state_log)]
    empty!(task_constrain_fn.cache) # to be safe
    return res
end