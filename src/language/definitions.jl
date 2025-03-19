export def_constructors, def_joshrule, def_classic

function def_constructors()
    prims_minimal()
    @define "given" """
    (λ p q -> (case p of True => q))
    """

    @define "geometric" "(Y (λ rec p -> (if (flip p) (O) (S (rec p)))))"
    @define "geom" "geometric"
    @define "geom_fuel" "(Y (λ rec p fuel -> (case fuel of O => (O) | S => (λfuel -> (if (flip p) (O) (S (rec p fuel)))))))"
#     @define "geom_bounded_list" "(Y (λ rec n -> (if (flip 0.5) (Nil) (Cons (geom_bounded n) (rec n)))))"
    @define "geom_get_fuel" "(λp -> (case (get_config :fuel) of O => (geometric p) | S => (λn -> (geom_fuel p n))))"


    @define "geom_list" "(Y (λ rec plen p -> (if (flip plen) (Nil) (Cons (geom p) (rec plen p)))))"


    @define "take" "int -> list -> list" "(Y (λ rec n xs -> (case n of O => (Nil) | S => (λn2 -> (case xs of Nil => (Nil) | Cons => (λhd tl -> (Cons hd (rec n2 tl))))))))"


    @define inc "int -> int" "(λx->(S x))"
    @define dec "int -> int" "(λx->(case x of O => (O) | S => (λx2 -> x2)))"
    @define pflip "(λx->(if (flip x) (True) (False)))"
#     @define randnat "((Y (λ rec unit -> (if (flip 0.5) (O) (S (rec unit))))) (Unit))"
#     @define randnat "(geom 0.5)"
    @define randnat "(geom_get_fuel 0.2)"
    @define randnatlist "((Y (λ rec unit -> (if (flip 0.5) (Nil) (Cons randnat (rec unit))))) (Unit))"

    # (uniform n) samples a nat uniformly from 0 to n inclusive; randdigit is 0 to 9 inclusive, randnatlist digit is a list with a geometrically distributed length containing random digits
    # @define uniform "(Y (λ rec n -> (if (flip (fdiv 1 (S n))) n (rec (dec n)))))"
    # define(:randdigit, "(uniform $(peano_str(9)))")

    # define(:randdigit, "(if (flip 0.1) $(peano_str(0)) (if (flip 0.11111111) $(peano_str(1)) (if (flip 0.125) $(peano_str(2)) (if (flip 0.142857) $(peano_str(3)) (if (flip 0.1666667) $(peano_str(4)) (if (flip 0.2) $(peano_str(5)) (if (flip 0.25) $(peano_str(6)) (if (flip 0.333333333) $(peano_str(7)) (if (flip 0.5) $(peano_str(8)) $(peano_str(9)))))))))))")

    # @define make_random_digit "randnat"


    @define make_random_digit "(random_digit)"
    @define randlistdigit "((Y (λ rec unit -> (if (flip 0.5) (Nil) (Cons (random_digit) (rec unit))))) (Unit))"
    @define make_random_list "randlistdigit"
    @define make_nil "int" "(Nil)"

    # @define make_random_digit "randdigit" 

    # @define fold "(λ_ _ _->(Y (λ_->(λ_->(if (isempty #1) #4 (#5 (#2 (cdr #1)) (car #1))))) #1))))";

    # super annoying if you try to define over a builtin like `car` it freaks out and uses the carop version in an annoying way
    @define car "list -> int" "(λxs->(case xs of Cons => (λ hd tl -> hd)))"
    @define cdr "list -> list" "(λxs->(case xs of Cons => (λ hd tl -> tl)))"
    @define cdr_safe "list -> list" "(λxs->(case xs of Nil => (Nil) | Cons => (λ hd tl -> tl)))"
    @define isempty "list -> bool" "(λx->(case x of Nil => true | Cons => (λ _ _ -> false)))"

    # fast:
    @define fold_general "(Y (λrec f init xs -> (if (isempty xs) init (f (rec f init (cdr xs)) (car xs)))))"
    # @define fold "(list -> int -> list) -> int -> list -> list" "fold_general"
    # fold f init xs

    # dc list domain style fold: (fold xs init f) and it is (f x acc)
    # @define fold "list -> list -> (int -> list -> list) -> list" "(Y (λrec xs init f -> (if (isempty xs) init (f (car xs) (rec (cdr xs) init f )))))"
    @define fold "list -> list -> (int -> list -> list) -> list" "(Y (λrec xs init f -> (case xs of Nil => init | Cons => (λhd tl -> (f hd (rec tl init f))))))"

    # @define fold "list -> int -> (list -> int -> list) -> list" "fold_general"

    # slow:
    # @define fold "(λf init -> (Y (λrec xs -> (case xs of Nil => init | Cons => (λhd tl -> (f (rec tl) hd))))))";

    # fast:
    # @define filter "(int -> bool) -> list -> list" "(λf xs-> (fold (λacc x -> (if (f x) (Cons x acc) acc)) (Nil) xs))";
    # fast:
    # @define filter "(int -> bool) -> list -> list" "(Y (λ rec f xs -> (if (isempty xs) (Nil) (if (f (car xs)) (Cons (car xs) (rec f (cdr xs))) (rec f (cdr xs))))))"

    # @define pif "(λcond e1 e2 -> (case cond of True => e1 | False => e2))"
    @define "+" "int -> int -> int" "(Y (λrec x y -> (case y of O => x | S => (λy2 -> (S (rec x y2))))))"
#     @define "-" "int -> int -> int" "(Y (λrec x y -> (case y of O => x | S => (λy2 -> (rec (dec x) y2)))))"

    # saturating subtraction
    @define "-" "int -> int -> int" "(Y (λrec x y -> (case y of O => x | S => (λy2 -> (case x of O => (O) | S => (λx2 -> (rec x2 y2)))))))"


    @define map "(int -> int) -> list -> list" "(Y (λ rec f xs -> (case xs of Nil => (Nil) | Cons => (λhd tl -> (Cons (f hd) (rec f tl))))))"
    @define mapi "(int -> int -> int) -> list -> list" "(λ f xs0 -> ((λ mapi_help -> (mapi_help xs0 0)) (Y (λ rec xs i -> (case xs of Nil => (Nil) | Cons => (λhd tl -> (Cons (f hd i) (rec tl (inc i)))))))))"
    # slower slightly:
    # @define map "(int -> int) -> list -> list" "(Y (λ rec f xs -> (if (isempty xs) (Nil) (Cons (f (car xs)) (rec f (cdr xs))))))"
    @define "==" "int -> int -> bool" "(Y (λ rec x y -> (case x of O => (case y of O => true | S => (λ _ -> false)) | S => (λ x2 -> (case y of O => false | S => (λ y2 -> (rec x2 y2)))))))"
    @define filter "(int -> bool) -> list -> list" "(Y (λ rec f xs -> (if (isempty xs) (Nil) (if (f (car xs)) (Cons (car xs) (rec f (cdr xs))) (rec f (cdr xs))))))"
    # slow:
    @define filter_slow "(int -> bool) -> list -> list" "(Y (λ rec f xs -> (case xs of Nil => (Nil) | Cons => (λhd tl -> (if (f hd) (Cons hd (rec f tl)) (rec f tl))))))"
    @define filteri "(int -> int -> bool) -> list -> list" "(λ f xs0 -> ((λ filteri_help -> (filteri_help xs0 0)) (Y (λ rec xs i -> (case xs of Nil => (Nil) | Cons => (λhd tl -> (if (f hd i) (Cons hd (rec tl (inc i))) (rec tl (inc i)))))))))"
    # @define filter "(int -> bool) -> list -> list" "(Y (λ rec f xs -> (case xs of Nil => (Nil) | Cons => (λhd tl -> (if (f hd) (Cons hd (rec f tl)) (rec f tl))))))"
    # @define filter "(int -> bool) -> list -> list" "(Y (λ rec f xs -> (case xs of Nil => (Nil) | Cons => (λhd tl -> ((λz -> (if (f hd) (Cons hd z) z)) (rec f tl)) ))))"
#     @define iseven "int -> bool" "(Y (λ rec x -> (case x of O => true | S => (λ x2 -> (case x2 of O => false | S => (λ x3 -> (rec x3)))))))"
    @define not "bool -> bool" "(λx -> (if x false true))"
    @define iseven "int -> bool" "(Y (λ rec x -> (case x of O => true | S => (λ x2 -> (not (rec x2))))))"
    # slower:
    # @define iseven "int -> bool" "(Y (λ rec x -> (if (== x (O)) true (if (== x (S (O))) false (rec (dec (dec x)))))))"
    @define ">" "int -> int -> bool" "(Y (λ rec x y -> (case x of O => false | S => (λ x2 -> (case y of O => true | S => (λ y2 -> (rec x2 y2)))))))"
    @define ">=" "int -> int -> bool" "(Y (λ rec x y -> (case x of O => (case y of O => true | S => (λ _ -> false)) | S => (λ x2 -> (case y of O => true | S => (λ y2 -> (rec x2 y2)))))))"

    @define cons "int -> list -> list" "(λhd tl -> (Cons hd tl))"
    @define length "list -> int" "(fold_general (λacc x -> (inc acc)) 0)"
    @define range "int -> list" "(λ N -> (Y (λ rec n -> (if (== n N) (Nil) (Cons n (rec (inc n))))) 0))"
    @define index "int -> list -> int" "(Y (λ rec n xs -> (if (== n (O)) (car xs) (rec (dec n) (cdr xs)))))"
    @define mod "int -> int -> int" "(Y (λ rec x y -> (if (>= x y) (rec (- x y) y) x)))"
    @define "*" "int -> int -> int" "(Y (λ rec x y -> (if (== x (O)) (O) (if (== x (S (O))) y (+ y (rec (dec x) y))))))"


    @define append "list -> list -> list" "(Y (λrec xs ys -> (case xs of Nil => ys | Cons => (λ hd tl -> (Cons hd (rec tl ys))))))"
    @define paren_grammar "((Y (λ rec suffix -> (if (flip 0.5) suffix ((λx->(Cons x (rec (Cons x suffix)))) make_random_digit)))) (Nil))"
    @define paren_grammar_2 "((Y (λrec unit -> (if (flip 0.5) (Nil) ((λx->(append (Cons x (rec unit)) (Cons x (Nil)))) make_random_digit)))) (Unit))"

    @define append_one "list -> int -> list" "(Y (λrec xs y -> (case xs of Nil => (Cons y (Nil)) | Cons => (λ hd tl -> (Cons hd (rec tl y))))))"


    # (Y (λrec xs y -> (Cons (case xs of Nil => y | Cons => (λhd _ -> hd)) (case xs of Nil => (Nil) | Cons => (λ_ tl -> rec tl y) )) ))

    # yandp: yang and piantadosi grammar
    # @define pair "list -> int -> list" "(Y (λrec xs y -> (case xs of Nil => (Cons y (Nil)) | Cons => (λ hd tl -> (Cons hd (rec tl y))))))"
    # @define pair "list -> int -> list" "(Y (λrec xs y -> (Cons (case xs of Nil => y | Cons => (λhd _ -> hd)) (case xs of Nil => (Nil) | Cons => (λ_ tl -> (rec tl y)) )) ))"
    # @define first "snoclist -> int" "car"
    # @define rest "snoclist -> snoclist" "cdr"
    @define and "bool -> bool -> bool" "(λx y -> (if x y false))"
    @define or "bool -> bool -> bool" "(λx y -> (if x true y))"
    @define not "bool -> bool" "(λx -> (if x false true))"
    # @define "ϵ" "(Nil)"

    @define "ϵ" "(SNil)"
    @define snoc_append "(Y (λrec xs ys -> (case ys of SNil => xs | Snoc => (λprefix last -> (Snoc (rec xs prefix) last)))))"
    @define pair "snoclist -> int -> snoclist" "(λxs y -> (Snoc xs y))"

    @define make_random_snoclist "((Y (λ rec unit -> (if (flip 0.5) (SNil) (Snoc (rec unit) (random_digit))))) (Unit))"

    # perturb -- a "likelihood at the end" for rational rules
    @define perturb "list -> list" "(Y (λ rec xs -> (case xs of Nil => (if (flip 0.99) (Nil) (Cons make_random_digit (rec (Nil)))) | Cons => (λ hd tl -> (if (flip 0.99) (Cons hd (rec tl)) (if (flip 0.5) (rec tl) (Cons make_random_digit (rec (if (flip 0.5) xs tl)))))))))"

    # snocy time


#     @assert constrain("(>= 3 3)", [], true) |> weight |> exp ≈ 1.0 
#     @assert constrain("(>= 10 3)", [], true) |> weight |> exp ≈ 1.0
#     @assert constrain("(>= 2 3)", [], false) |> weight |> exp ≈ 1.0
#     @assert constrain("(mod 7 3)", [], to_value(1)) |> weight |> exp ≈ 1.0
#     @assert constrain("(mod 7 7)", [], to_value(0)) |> weight |> exp ≈ 1.0
#     @assert constrain("(mod 2 7)", [], to_value(2)) |> weight |> exp ≈ 1.0
#     @assert constrain("(range #1)", [to_value(5)], to_value([0, 1, 2, 3, 4])) |>
#             weight |>
#             exp ≈ 1.0
#     @assert constrain(
#                 "(index #2 #1)",
#                 [to_value([0, 1, 2, 3, 4]), to_value(2)],
#                 to_value(2),
#             ) |>
#             weight |>
#             exp ≈ 1.0
#     @assert constrain("(* 3 4)", [], to_value(12)) |> weight |> exp ≈ 1.0
#     @assert constrain("(== (* 0 4) 0)", [], true) |> weight |> exp ≈ 1.0
#     @assert constrain("(== (* 4 4) 16)", [], true) |> weight |> exp ≈ 1.0
#     # @assert constrain("(uniform #1)", [to_value(0)], to_value(0)) |> weight |> exp ≈ 1
#     # @assert constrain("(uniform #1)", [to_value(1)], to_value(0)) |> weight |> exp ≈ 1 / 2
#     # @assert constrain("(uniform #1)", [to_value(5)], to_value(2)) |> weight |> exp ≈ 1 / 6
#     # @assert constrain("randdigit", [], to_value(3)) |> weight |> exp ≈ 0.1
#     # @assert constrain("(fdiv 1 #1)", [to_value(5)], 0.2) |> weight |> exp ≈ 1.0
#     @assert constrain("(S (O))", [], to_value(1)) |> weight |> exp ≈ 1.0
#     @assert constrain("(S #1)", [to_value(2)], to_value(3)) |> weight |> exp ≈ 1.0
#     @assert constrain("(Cons #1 (Nil))", [to_value(2)], to_value([2])) |> weight |> exp ≈
#             1.0
#     @assert constrain("(O)", [], to_value(1)) |> weight |> exp ≈ 0.0
#     @assert constrain("(case (O) of O => (O))", [], to_value(0)) |> weight |> exp ≈ 1.0
#     @assert constrain("(case (S (O)) of S => (λ_->(O)))", [], to_value(0)) |>
#             weight |>
#             exp ≈ 1.0
#     @assert constrain("(case (S (O)) of S => (λx->x))", [], to_value(0)) |> weight |> exp ≈
#             1.0
#     @assert constrain("(> #1 #2)", [to_value(6), to_value(3)], true) |> weight |> exp ≈ 1.0
#     @assert constrain("(iseven #1)", [to_value(6)], true) |> weight |> exp ≈ 1.0
#     @assert constrain("(iseven #1)", [to_value(5)], false) |> weight |> exp ≈ 1.0
#     @assert constrain(
#                 "(filter (λx -> (== x (S (O)))) #1)",
#                 [to_value([1, 2, 3, 2, 1])],
#                 to_value([1, 1]),
#             ) |>
#             weight |>
#             exp ≈ 1.0
#     @assert constrain("(== (S (O)) (S (O)))", [], true) |> weight |> exp ≈ 1.0
#     @assert constrain("(== (S #1) #2)", [to_value(3), to_value(4)], true) |> weight |> exp ≈
#             1.0
#     @assert constrain(
#                 "(map (λx -> (S (O))) #1)",
#                 [to_value([1, 2, 3])],
#                 to_value([1, 1, 1]),
#             ) |>
#             weight |>
#             exp ≈ 1.0
#     @assert constrain("(car #1)", [to_value([1, 2, 3])], to_value(1)) |> weight |> exp ≈ 1
#     @assert constrain("(cdr #1)", [to_value([1, 2, 3])], to_value([2, 3])) |>
#             weight |>
#             exp ≈ 1
#     @assert constrain("(+ #1 #2)", [to_value(5), to_value(4)], to_value(9)) |>
#             weight |>
#             exp ≈ 1
#     @assert constrain("(- #1 #2)", [to_value(9), to_value(3)], to_value(6)) |>
#             weight |>
#             exp ≈ 1
#     @assert constrain("(dec #1)", [to_value(9)], to_value(8)) |> weight |> exp ≈ 1
#     @assert constrain("randnat", [], to_value(0)) |> weight |> exp ≈ 1 / 2
#     @assert constrain("randnat", [], to_value(1)) |> weight |> exp ≈ 1 / 4
#     @assert constrain("randnat", [], to_value(2)) |> weight |> exp ≈ 1 / 8
#     @assert constrain("randnatlist", [], to_value([])) |> weight |> exp ≈ 1 / 2
#     @assert constrain("randnatlist", [], to_value([0])) |> weight |> exp ≈ 1 / 4 * 1 / 2
#     @assert constrain("randnatlist", [], to_value([1, 1])) |> weight |> exp ≈
#             1 / 8 * 1 / 4 * 1 / 4
#     # @assert constrain("randdigit", [], to_value(8)) |> weight |> exp ≈ 1 / 10

#     @assert constrain("make_random_digit", [], to_value(3)) |> weight |> exp ≈ 1 / 10
#     @assert constrain("make_random_digit", [], to_value(10)) |> weight |> exp ≈ 0.0
#     @assert constrain("(if (flip 0.5) 3 4)", [], to_value(3)) |> weight |> exp ≈ 1 / 2
#     @assert constrain("(if (flip 0.5) 3 4)", [], to_value(4)) |> weight |> exp ≈ 1 / 2
#     @assert constrain("(+ make_random_digit make_random_digit)", [], to_value(2)) |>
#             weight |>
#             exp ≈ 1 / 10 * 1 / 10 * 3
#     @assert constrain("(- make_random_digit make_random_digit)", [], to_value(9)) |>
#             weight |>
#             exp ≈ 1 / 10 * 1 / 10
#     @assert constrain("(== make_random_digit 2)", [], true) |> weight |> exp ≈ 1 / 10
#     @assert constrain("(> make_random_digit 4)", [], true) |> weight |> exp ≈ 1 / 2
#     @assert constrain("((λx -> (> x x)) make_random_digit)", [], true) |> weight |> exp ≈
#             0.0
#     @assert constrain("((λx -> (> (inc x) x)) make_random_digit)", [], true) |>
#             weight |>
#             exp ≈ 1.0
#     @assert constrain(
#                 "((λx -> (Cons x (Cons x (Nil)))) (random_digit))",
#                 [],
#                 to_value([2, 2]),
#             ) |>
#             weight |>
#             exp ≈ 1 / 10
#     @assert constrain("make_random_list", [], to_value([1, 2, 3])) |> weight |> exp ≈
#             (1 / 2)^4 * (1 / 10)^3

#     @assert constrain("(map (λx -> (+ x 1)) (Cons 3 (Nil)))", [], to_value([4])) |>
#             weight |>
#             exp ≈ 1
#     @assert constrain(
#                 "(filter (λx -> (> x 4)) #1)",
#                 [to_value([2, 5, 2, 2, 5, 8])],
#                 to_value([5, 5, 8]),
#             ) |>
#             weight |>
#             exp ≈ 1

end
