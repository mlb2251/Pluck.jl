"use strict";

make_controls()
add_svg()
reload()
make_callstack_panel()

function reload() {
    clear_svg()
    resize_svg()
    // load bdd json
    load_by_path(json => {
        show_bdd(build_bdd(json))
    })
}


function make_controls() {
    add_controls()
    let controls = get_controls()
}

function build_bdd(json) {
    // make nodes
    let nodes = json.nodes.map((node, idx) => {
        let [label, lo_is_neg, lo_idx, hi_is_neg, hi_idx] = node
        let callsite = json.callsite_of_label ? json.callsite_of_label[label] : undefined
        if (idx == 0) {
            return {
                is_false: true,
                is_const: true,
                parents: [],
            }
        } else if (idx == 1) {
            return {
                is_true: true,
                is_const: true,
                parents: [],
            }
        }
        return {
            label,
            callstack: json.callstack_of_label[label],
            callsite,
            lo: {
                is_neg: lo_is_neg,
                idx: lo_idx,
            },
            hi: {
                is_neg: hi_is_neg,
                idx: hi_idx,
            },
            parents: [],
        }
    })

    // add child pointers
    for (let node of nodes) {
        if (!node.is_const) {
            node.lo.node = nodes[node.lo.idx]
            node.hi.node = nodes[node.hi.idx]
        }
    }

    let root = {
        is_neg: json.root[0],
        idx: json.root[1],
        node: nodes[json.root[1]],
    }

    window.root = root
    return {
        root,
        nodes,
        sources: json.sources || {}
    }
}

function make_callstack_panel() {
    if (d3.select("#callstack-panel").size() === 0) {
        d3.select("body")
            .append("div")
            .attr("id", "callstack-panel")
            .style("position", "fixed")
            .style("top", "20px")
            .style("right", "20px")
            .style("width", "320px")
            .style("max-height", "80vh")
            .style("overflow", "auto")
            .style("padding", "12px")
            .style("border", "1px solid #ccc")
            .style("border-radius", "6px")
            .style("background", "#fafafa")
            .style("font-family", "sans-serif")
            .style("font-size", "13px")
            .html("<b>Callstack</b><br><span style='color:#666'>click a node to inspect</span>")
    }
}

function set_positions(bdd) {
    // loop through the nodes and set .max_depth as the depth of the node
    // by the longest path to it
    bdd.root.node.max_depth = 0
    let worklist = [bdd.root.node]
    while (worklist.length > 0) {
        let node = worklist.pop()
        if (node.is_const) {
            continue
        }
        node.lo.node.max_depth = Math.max(node.lo.node.max_depth || 0, node.max_depth + 1)
        node.hi.node.max_depth = Math.max(node.hi.node.max_depth || 0, node.max_depth + 1)
        node.lo.node.parents.push([node, false])
        node.hi.node.parents.push([node, true])
        worklist.push(node.lo.node, node.hi.node)
    }

    let label_sorted_nodes = bdd.nodes.slice().sort((a, b) => a.label - b.label)

    let curr = -1
    let curr_label = -1
    let num_duplicates = 0
    for (let node of label_sorted_nodes) {
        if (node.label != curr_label) {
            curr_label = node.label
            curr += 1
            num_duplicates = 0
        } else {
            num_duplicates += 1
        }
        node.idx = curr
        node.duplicates = num_duplicates
    }

    let nodes_by_max_depth = {}
    for (let node of label_sorted_nodes) {
        if (!nodes_by_max_depth[node.max_depth]) {
            nodes_by_max_depth[node.max_depth] = []
        }
        nodes_by_max_depth[node.max_depth].push(node)
    }

    // set y positions based on max_depth and x positions
    // based on the number of nodes at the same depth
    for (let [depth, nodes] of Object.entries(nodes_by_max_depth)) {
        for (let i = 0; i < nodes.length; i++) {
            // nodes[i].y = depth * 100
            if (nodes[i].is_const)
                nodes[i].y = (label_sorted_nodes[label_sorted_nodes.length - 1].idx + 1) * 100
            else
                nodes[i].y = nodes[i].idx * 100
            // nodes[i].x = Math.random() * 1000 - 500
            // nodes[i].x = 0
            nodes[i].x = nodes[i].duplicates * 100 + nodes[i].idx * -50
        }
    }

    // bump children to avoid overlap
    // for (let node of label_sorted_nodes) {
    //     if (node.is_const) {
    //         continue
    //     }
    //     // shift in dir its alreayd shifted a bit in instead?


    //     let goal_lo = node.x + 500
    //     let goal_hi = node.x - 500
    //     let bump_frac = 0.5
    //     node.lo.node.x = goal_lo * bump_frac + node.lo.node.x * (1 - bump_frac)
    //     node.hi.node.x = goal_hi * bump_frac + node.hi.node.x * (1 - bump_frac)
    //     }
}

function show_bdd(bdd) {
    let { root, nodes } = bdd

    set_positions(bdd)
    window.sources = bdd.sources || {}
    console.log(root)
    let g_bdd = get_foreground("g_bdd").append("g")
        .attr("transform", "translate(300, 100)")


    const link = d3.linkVertical()
        .x(d => d.x)
        .y(d => d.y)

    function update_node(node) {
        node.g_node.attr("transform", `translate(${node.x}, ${node.y})`)
        if (node.lo_line)
            node.lo_line.attr("d", link({ source: { x: 0, y: 10 }, target: { x: node.lo.node.x - node.x, y: node.lo.node.y - node.y - 18.5 } }))
        if (node.hi_line)
            node.hi_line.attr("d", link({ source: { x: 0, y: 10 }, target: { x: node.hi.node.x - node.x, y: node.hi.node.y - node.y - 18.5 } }))
        for (let [parent, is_hi] of node.parents) {
            let line = is_hi ? parent.hi_line : parent.lo_line
            if (line) {
                line.attr("d", link({ source: { x: 0, y: 10 }, target: { x: node.x - parent.x, y: node.y - parent.y - 18.5 } }))
            }
        }
    }


    for (let node of nodes) {
        node.g_node = g_bdd.append("g")
            .attr("transform", `translate(${node.x}, ${node.y})`)
        node.g_circle = node.g_node.append("circle")
            .classed("node", true)
            .attr("r", 10)

        let text = node.is_true ? "T" : node.is_false ? "F" : node.label // + ": " + show_callstack(node.callstack)
        node.g_node.append("text")
            .text(text)
            .attr("transform", "translate(20, 0)")
            .attr("dominant-baseline", "middle")

        // lo hi lines
        if (!node.is_const) {
            if (!node.lo.node.is_const) {
                node.lo_line = node.g_node
                    .append("path")
                    .classed("edge", true)
                    .classed("lo", true)
                    .classed("complement", node.lo.is_neg)
            } else {
                node.lo_ball = node.g_node
                    .append("circle")
                    .classed("ball_true", node.lo.node.is_true)
                    .classed("ball_false", node.lo.node.is_false)
                    .attr("transform", "translate(0, 10)")
                    .attr("r", 5)
            }

            if (!node.hi.node.is_const) {
                node.hi_line = node.g_node
                    .append("path")
                    .classed("edge", true)
                    .classed("hi", true)
                    .classed("complement", node.hi.is_neg)
            } else {
                node.hi_ball = node.g_node
                    .append("circle")
                    .classed("ball_true", node.hi.node.is_true)
                    .classed("ball_false", node.hi.node.is_false)
                    .attr("transform", "translate(0, -10)")
                    .attr("r", 5)
            }

            update_node(node)

        }

        // make node draggable
        node.g_node.call(d3.drag()
            .subject(function () {
                return {
                    x: node.x,
                    y: node.y
                }
            })
            .container(get_foreground().node())
            .on("drag", function (e) {
                node.x += e.dx
                node.y += e.dy
                update_node(node)
            }))



        function show_callstack_text(node) {
            if (node.callstack && !node.callstack_text) {
                let lines = [show_callstack(node.callstack)]
                if (node.callsite && node.callsite.stacktrace && node.callsite.stacktrace.length > 0) {
                    let top = node.callsite.stacktrace[node.callsite.stacktrace.length - 1]
                    if (top.loc) {
                        lines.push(`${top.loc.file}:${top.loc.line}`)
                    }
                }
                node.callstack_text = node.g_node.append("text")
                    .selectAll("tspan")
                    .data(lines)
                    .enter()
                    .append("tspan")
                    .text(d => d)
                    .attr("x", 40)
                    .attr("dy", (d, i) => i === 0 ? "0" : "1.2em")
                    .style("font-size", "12px")
                    .attr("dominant-baseline", "middle")
            }
        }
        function hide_callstack_text(node) {
            if (node.callstack_text)
                node.callstack_text.remove()
            node.callstack_text = undefined
        }

        // hover to see call stack
        node.g_circle.on("mouseover", function () {
            show_callstack_text(node)
        })
        node.g_circle.on("mouseout", function () {
            if (!node.clicked)
                hide_callstack_text(node)
        })
        node.g_circle.on("click", function () {
            node.clicked = !node.clicked
            if (node.clicked)
                show_callstack_text(node)
            else
                hide_callstack_text(node)
            update_callstack_panel(node)
        })

    }



    // add incoming line to root
    root.line = g_bdd
        .append("path")
        .classed("edge", true)
        .classed("hi", true)
        .classed("complement", root.is_neg)
        .attr("d", link({ source: { x: root.node.x, y: root.node.y - 60 }, target: { x: root.node.x, y: root.node.y - 18.5 } }))

}

function show_callstack(callstack) {
    return "[" + callstack.join(" ➤ ") + "]"
}

function update_callstack_panel(node) {
    let panel = d3.select("#callstack-panel")
    if (!panel.size()) return

    let html = `<b>Node ${node.label}</b><br>`
    if (node.callstack) {
        html += `<div><span style="color:#444">callstack</span><br>${show_callstack(node.callstack)}</div>`
    }
    if (node.callsite && node.callsite.call_frames) {
        html += `<div style="margin-top:8px;"><span style="color:#444">call frames (${node.callsite.call_frames.length})</span><br>`
        if (node.callsite.call_frames.length === 0) {
            html += `<span style="color:#888">none</span>`
        } else {
            html += `<ol style="padding-left:18px; margin:4px 0;">`
            node.callsite.call_frames.forEach((f, i) => {
                let loc = f.loc ? `${f.loc.file}:${f.loc.line}` : "no location"
                let nextSpan = i + 1 < node.callsite.call_frames.length ? node.callsite.call_frames[i + 1].called_from_span : null
                let originSpan = node.callsite.origin_span || null
                if (!nextSpan && originSpan) {
                    nextSpan = originSpan
                }
                let rendered = render_span_with_highlight(f.span, nextSpan)
                html += `<li><span style="color:#222">${f.name}</span><br><span style="color:#666; font-size:12px">${loc}</span><br><span style="color:#777; font-size:12px">${rendered}</span></li>`
            })
            html += `</ol>`
        }
        html += `</div>`
    }
    panel.html(html)
}

function highlight_called_from(frame, calledFromExpr, calledFromLoc, calledFromSpan=null) {
    // deprecated; rendering handled by render_span_with_highlight
    return frame.expr || ""
}

function render_span_with_highlight(frameSpan, highlightSpan) {
    if (!frameSpan || !frameSpan.file || !window.sources || !window.sources[frameSpan.file]) return ""
    const src = window.sources[frameSpan.file]
    const lines = src.split("\n")

    // Convert 1-based (line, col) to absolute 0-based offset in the file text.
    const offset = (line, col) => {
        let off = 0
        for (let i = 0; i < line - 1; i++) off += lines[i].length + 1
        return off + (col - 1)
    }

    const frameStart = offset(frameSpan.start_line, frameSpan.start_col)
    const frameEnd = offset(frameSpan.end_line, frameSpan.end_col) + 1 // inclusive end_col
    if (frameStart < 0 || frameEnd > src.length || frameEnd <= frameStart) return ""

    const full = src.slice(frameStart, frameEnd)

    if (!highlightSpan || !highlightSpan.file || highlightSpan.file !== frameSpan.file) return full

    const hlStart = offset(highlightSpan.start_line, highlightSpan.start_col)
    const hlEnd = offset(highlightSpan.end_line, highlightSpan.end_col) + 1
    if (hlStart < frameStart || hlEnd > frameEnd || hlEnd <= hlStart) return full

    const relStart = hlStart - frameStart
    const relEnd = hlEnd - frameStart
    return full.slice(0, relStart) + "<b>" + full.slice(relStart, relEnd) + "</b>" + full.slice(relEnd)
}
