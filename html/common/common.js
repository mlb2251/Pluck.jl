"use strict";



function def(obj, key, def) {
    if (obj[key] === undefined)
        obj[key] = def;
    return obj[key];
}

function assert_def(obj, key) {
    if (obj[key] === undefined)
        throw new Error(`undefined key ${key}`);
}

function makeGraph(spec) {
    assert_def(spec, "g");
    def(spec, "x", 0);
    def(spec, "y", 0);
    def(spec, "width", 600);
    def(spec, "height", 300);
    def(spec, "xmin", -5);
    def(spec, "xmax", 5);
    def(spec, "ymin", 0);
    def(spec, "ymax", 1);
    def(spec, "x_label", "");
    def(spec, "y_label", "");
    def(spec, "title", "");
    def(spec, "legend", undefined);
    def(spec, "yticks", undefined);
    def(spec, "xticks", undefined);

    const xScale = d3.scaleLinear()
        .domain([spec.xmin, spec.xmax])
        .range([0, spec.width]);
    const yScale = d3.scaleLinear()
        .domain([spec.ymin, spec.ymax])
        .range([spec.height, 0]);
    const graph = spec.g.append("g")
        .attr("transform", `translate(${spec.x}, ${spec.y})`);
    let axis_bottom = d3.axisBottom(xScale)
    if (spec.xticks) {
        axis_bottom.tickValues(spec.xticks)
    }
    let x_axis = graph.append("g")
        .attr("transform", `translate(0, ${spec.height})`)
        .call(axis_bottom);
    let axis_left = d3.axisLeft(yScale)
    if (spec.yticks) {
        axis_left.tickValues(spec.yticks)
    } 
    let y_axis = graph.append("g")
        .attr("transform", `translate(0, 0)`)
        .call(axis_left);

    // format ticks
    x_axis.selectAll("text").style("font", "18px sans-serif")
    y_axis.selectAll("text").style("font", "18px sans-serif")

    // x axis label
    let x_label = graph.append("text")
        .attr("x", spec.width / 2)
        .attr("y", spec.height + 60)
        .style("font", "22px sans-serif")
        .style("text-anchor", "middle")
        .text(spec.x_label)

    // y axis label
    let y_label = graph.append("g")
        .attr("transform", `translate(-60, ${spec.height/2}) rotate(-90)`)
        .append("text")
        .style("font", "22px sans-serif")
        .style("text-anchor", "middle")
        .text(spec.y_label)
    
    // add a title
    let title = graph.append("text")
        .attr("x", spec.width / 2)
        .attr("y", -30)
        .style("font", "24px sans-serif")
        .style("text-anchor", "middle")
        .text(spec.title)

    let legend = d3.select()
    // add a legend
    if (spec.legend) {
        legend = graph.append("g")
            .attr("transform", `translate(20, 10)`)
        for (let i = 0; i < spec.legend.length; i++) {
            const rowHeight = 30;
            const marker = spec.legend[i].marker;
            const color = spec.legend[i].color;
            
            if (marker) {
                if (marker === "star") {
                    if (typeof drawStar === 'function') {
                        drawStar(legend, 7.5, i * rowHeight + 7.5, 5, 13.5, 6.75, color);
                    } else {
                        legend.append("rect")
                            .attr("x", 0)
                            .attr("y", i * rowHeight)
                            .attr("width", 15)
                            .attr("height", 15)
                            .attr("fill", color);
                    }
                } else if (marker === "diamond") {
                    legend.append("rect")
                        .attr("x", -1.5)
                        .attr("y", i * rowHeight - 1.5)
                        .attr("width", 18)
                        .attr("height", 18)
                        .attr("fill", color)
                        .attr("stroke", "white")
                        .attr("stroke-width", 1.5)
                        .attr("transform", `rotate(45, 7.5, ${i * rowHeight + 7.5})`);
                } else if (marker === "triangle") {
                    legend.append("polygon")
                        .attr("points", `7.5,${i * rowHeight - 5.25} -5.25,${i * rowHeight + 16.5} 20.25,${i * rowHeight + 16.5}`)
                        .attr("fill", color)
                        .attr("stroke", "white")
                        .attr("stroke-width", 1.5);
                } else if (marker === "circle") {
                    legend.append("circle")
                        .attr("cx", 7.5)
                        .attr("cy", i * rowHeight + 7.5)
                        .attr("r", 9)
                        .attr("fill", color)
                        .attr("stroke", "white")
                        .attr("stroke-width", 1.5);
                } else {
                    legend.append("rect")
                        .attr("x", 0)
                        .attr("y", i * rowHeight)
                        .attr("width", 15)
                        .attr("height", 15)
                        .attr("fill", color);
                }
            } else {
                legend.append("rect")
                    .attr("x", 0)
                    .attr("y", i * rowHeight)
                    .attr("width", 15)
                    .attr("height", 15)
                    .attr("fill", color);
            }
            
            legend.append("text")
                .attr("x", 20)
                .attr("y", i * rowHeight + 10)
                .text(spec.legend[i].name)
                .style("font", "20px sans-serif")
                .style("dominant-baseline", "middle");
        }
    }
    
    return {
        xScale: xScale,
        yScale: yScale,
        x_axis: x_axis,
        y_axis: y_axis,
        x_label: x_label,
        y_label: y_label,
        title: title,
        legend: legend,
        g: graph,
        spec: spec
    };
}

function plot_curve(graph, spec) {
    def(spec, "styles", {})
    def(spec.styles, "stroke-width", 4)
    def(spec.styles, "stroke-dasharray", "")
    def(spec, "attrs", {})
    def(spec, "color", "blue")
    assertdef(spec.xs)
    assertdef(spec.ys)
    assert(spec.xs.length == spec.ys.length, "xs and ys must have the same length")
    let path = graph.g.append("path")
        .datum(spec.xs.map((x, i) => [x, spec.ys[i]]))
        .attr("d", d3.line().x(d => graph.xScale(d[0])).y(d => graph.yScale(d[1])))
        .attr("stroke", spec.color)
        .attr("fill", "none")

    for (let [key, value] of Object.entries(spec.styles)) {
        path.style(key, value)
    }
    for (let [key, value] of Object.entries(spec.attrs)) {
        path.attr(key, value)
    }
    return path
}

function show_prob(prob, digits = 0) {
    if (prob == 0)
        return "0"
    if (prob == 1)
        return "1"
    if (prob >= 1e-3 && prob <= 1e3)
        return prob.toPrecision(Math.max(digits, 1))
    return prob.toExponential(digits)
}

function logaddexp(x, y) {
    if (x == -Infinity)
        return y
    if (y == -Infinity)
        return x
    return Math.max(x, y) + Math.log1p(Math.exp(-Math.abs(x - y)))
}

// json maps NaN and -Inf and Inf to `null` so we undo that
function null_to_neginf(x) {
    return x == null ? -Infinity : x
}

function logsumexp(logweights){
    return logweights.reduce((a, b) => logaddexp(a, b), -Infinity);
}
function logmeanexp(logweights){
    return logsumexp(logweights) - Math.log(logweights.length);
}

function total_logweight(particles) {
    return particles.reduce((a, b) => logaddexp(a, b.logweight), -Infinity);
}
function log_mean_weight(particles) {
    return total_logweight(particles) - Math.log(particles.length);
}
function normalized_logweights(particles) {
    let total_logwt = total_logweight(particles);
    return particles.map(p => p.logweight - total_logwt);
}
function normalized_weights(particles) {
    return normalized_logweights(particles).map(w => Math.exp(w));
}

function get_foreground() {
    return d3.select("#frame-foreground");
}

// Note: in certain cases with a display:none selection this won't include the final transform applied to the display:none
// element, so you should wrap the element in a <g> and apply the transform to the <g> instead.
// Also the reason this is all based on getScreenCTM is that getClientBoundingRect also doesn't work with invisible or size
// zero elements and has weird behavior when the visible bounding box is in a subregion of the actual translated element.
function get_foreground_point(selection) {
    return DOMPointReadOnly.fromPoint(
        DOMPointReadOnly.fromPoint({x: 0, y:0}).matrixTransform(selection.node().getScreenCTM())
    ).matrixTransform(get_foreground().node().getScreenCTM().inverse())
}

const enabled_anchors = {}

function make_anchor(g, x, y, uid, func) {
    // the marker is both a visual indicator (if drawn), and a reference point within "g" that will
    // be used to position the hover box correctly even if g is transformed (while still allowing us to
    // draw into the overall frame foreground and thus draw over things that are in front of g)
    // the extra `g` here is needed for get_foreground_point to work correctly, see note on that function
    let marker = g.append("g").attr("transform",`translate(${x},${y})`).append("circle").attr("r", 1).attr("display", "none")
    // let pt = get_foreground_point(marker)
    // get_foreground().append("circle").attr("transform",`translate(${pt.x},${pt.y})`).attr("r", 1).attr("fill", "red")
    let anchor = {
        func: func,
        marker: marker,
        x: x,
        y: y,
        xoff: 120,
        yoff: -30,
        xmargin: 5,
        ymargin: 10,
        header_fill: "rgb(213, 210, 239)",
        enabled: false,
        uid: uid
    }
    if (uid != undefined && enabled_anchors[uid]) {
        anchor.xoff = enabled_anchors[uid].xoff
        anchor.yoff = enabled_anchors[uid].yoff
        make_hover(anchor)
    }
    return anchor
}

function anchor_transform(anchor) {
    let marker_pt = get_foreground_point(anchor.marker)
    return `translate(${marker_pt.x + anchor.xoff},${marker_pt.y + anchor.yoff})`
}

function toggle_hover(anchor) {
    if (anchor.enabled)
        remove_hover(anchor)
    else
        make_hover(anchor)
}

function make_hover(anchor) {
    if (anchor.enabled)
        return
    enabled_anchors[anchor.uid] = anchor
    anchor.enabled = true
    anchor.g_wide = get_foreground().append("g")
        .classed("hover", true)
        .attr("transform", anchor_transform(anchor))
    anchor.line = anchor.g_wide.append("line")
        .attr("x1", -5)
        .attr("y1", -20)
        .attr("x2", -anchor.xoff)
        .attr("y2", -anchor.yoff)
        .attr("stroke", "black")
        .attr("stroke-dasharray", "2,2")
    // this is where anything drawn within the box should go
    anchor.g_box = anchor.g_wide.append("g")

    // call the function to draw the contents of the box
    anchor.func(anchor)

    // make the box around it
    make_hover_box(anchor)
}

function remove_hover(anchor) {
    if (!anchor.enabled)
        return
    enabled_anchors[anchor.uid] = undefined
    anchor.enabled = false
    anchor.g_wide.remove()
}

function make_hover_box(anchor) {
    const bbox = anchor.g_box.node().getBBox()

    anchor.background = anchor.g_wide.append("rect")
        .classed("hover_background", true)
        .attr("x", bbox.x - anchor.xmargin)
        .attr("y", bbox.y - anchor.ymargin)
        .attr("width", bbox.width + anchor.xmargin * 2)
        .attr("height", bbox.height + anchor.ymargin * 2)
        .lower()

    // thin header bar of a darker color
    anchor.header = anchor.g_wide.append("rect")
        .classed("hover_header", true)
        .attr("x", bbox.x - anchor.xmargin)
        .attr("y", bbox.y - anchor.ymargin)
        .attr("width", bbox.width + anchor.xmargin * 2)
        .attr("height", anchor.ymargin)
        .attr("fill", anchor.header_fill)

    // add click and drag controls to box
    anchor.header.call(d3.drag()
        .subject(function () {
            return {
                x: anchor.x + anchor.xoff,
                y: anchor.y + anchor.yoff
            }
        })
        .container(get_foreground().node())
        .on("drag", function (e) {
            anchor.xoff += e.dx
            anchor.yoff += e.dy
            anchor.g_wide.attr("transform", anchor_transform(anchor))
            anchor.line.attr("x2", -anchor.xoff)
            anchor.line.attr("y2", -anchor.yoff)
        }))

    anchor.header.on("click", function () {
        remove_hover(anchor)
    })

}

function log2(x) {
    return Math.log(x) / Math.log(2);
}
function exp2(x) {
    return Math.pow(2, x);
}
function showN(x, digits = 2) {
    if (x == 0)
        return "0"
    if (Math.abs(x) >= 1000 || Math.abs(x) <= .001)
        return x.toExponential(digits)
    return x.toPrecision(digits+1)
}

// Helper function to draw a star
function drawStar(parent, cx, cy, spikes, outerRadius, innerRadius, fill) {
    let points = "";
    
    // Use a more precise method to draw a star
    for (let i = 0; i < spikes; i++) {
        // Outer point
        let outerAngle = (Math.PI * 2 * i) / spikes - Math.PI / 2;
        let outerX = cx + Math.cos(outerAngle) * outerRadius;
        let outerY = cy + Math.sin(outerAngle) * outerRadius;
        
        if (i === 0) {
            points += "M" + outerX + "," + outerY + " ";
        } else {
            points += "L" + outerX + "," + outerY + " ";
        }
        
        // Inner point
        let innerAngle = (Math.PI * 2 * i + Math.PI) / spikes - Math.PI / 2;
        let innerX = cx + Math.cos(innerAngle) * innerRadius;
        let innerY = cy + Math.sin(innerAngle) * innerRadius;
        points += "L" + innerX + "," + innerY + " ";
    }
    
    points += "Z";
    
    parent.append("path")
        .attr("d", points)
        .attr("fill", fill)
        .attr("stroke", "white")
        .attr("stroke-width", 1.5);
}

const url_params = new URLSearchParams(window.location.search)

function load_by_path(f) {
    if (!url_params.has("path")) {
        error("?path= url parameter not specified")
    }
    load_json(url_params.get("path"), f)
}

function load_by_paths(f) {
    if (!url_params.has("path")) {
        throw new Error("?path= url parameter not specified")
    }
    load_jsons(url_params.getAll("path"), f)
}

function load_json(path, f) {
    return d3.json('../../' + path, { cache: "no-store" })
        .then(f)
        .catch(e => {
            let res = {
                promise_failed: true,
                path: path,
                f: f,
                error: e
            }
            console.error(res)
            console.error(e)
            return res
        })
}

function load_json_with_retry(url, retries = 10, delay = 5000) {
    return new Promise((resolve, reject) => {
        const attempt = (n) => {
            d3.json('../' + url, { cache: "no-store" })
                .then(resolve)
                .catch((error) => {
                    if (n === 0) {
                        reject(error);
                    } else {
                        console.log(`Retrying ${url}... (${retries - n + 1})`);
                        setTimeout(() => attempt(n - 1), Math.random() * delay);
                    }
                });
        };
        attempt(retries);
    });
}



// load multiple json files in sequence
// and call `f` with the list of loaded json objects
function load_jsons(paths, f) {
    return Promise.all(paths.map(path => load_json(path, j=>j))).then(f)
}

function add_header() {
    return d3.select("body").append("div").attr("id", "header")
}

function add_controls() {
    return d3.select("body").append("div").attr("id", "controls")
}


let zoom_control;
function add_svg() {
    d3.select("body").append("div").attr("id", "svg")
    let svg = d3.select("#svg").append("svg")
    let defs = d3.select("#svg svg").append("defs")
    defs.append("marker")
        .attr("id", "arrowhead")
        .attr("markerWidth", 5)
        .attr("markerHeight", 3.5)
        .attr("refX", 0)
        .attr("refY", 1.75)
        .attr("orient", "auto")
        .append("polygon")
        .attr("points", "0 0, 5 1.75, 0 3.5")
    let background = svg.append("rect")
        .attr("id", "frame-background")
    let foreground = svg.append("g")
        .attr("id", "frame-foreground")

    // add zoom control to background
    zoom_control = d3.zoom().on('zoom', e => foreground.attr('transform', e.transform));
    background.call(zoom_control);
}

function get_zoom_control() {
    return zoom_control
}

function get_foreground() {
    return d3.select("#frame-foreground")
}
function get_background() {
    return d3.select("#frame-background")
}
function get_svg() {
    return d3.select("#svg svg")
}
function get_controls() {
    return d3.select("#controls")
}
function get_header() {
    return d3.select("#header")
}

function clear_svg() {
    get_foreground().selectAll("*").remove()
}

function resize_svg() {
    const svg_margin = 50
    const SVG_WIDTH = ((window.innerWidth > 0) ? window.innerWidth : screen.width) - svg_margin * 2;
    const SVG_HEIGHT = ((window.innerHeight > 0) ? window.innerHeight : screen.height) - 200;
    get_svg().attr("width", SVG_WIDTH)
        .attr("height", SVG_HEIGHT)
        .attr("transform", `translate(${svg_margin},0)`)
    get_background()
        .attr("width", SVG_WIDTH)
        .attr("height", SVG_HEIGHT)
}

function error(message) {
    d3.select("#error").append("div").text(message)
    throw new Error(message)
}

function assert(condition, message="assertion failed") {
    if (!condition) {
        error(message)
    }
}
function assertdef(x) {
    assert(x !== undefined, "unexpected undefined value")
    return x
}

function assertdefs(...xs) {
    return xs.map(assertdef)
}

function count(k) {
    return Array.from({ length: k }, (_, i) => i)
}

function show(x) {
    console.log(x)
    return x
}
