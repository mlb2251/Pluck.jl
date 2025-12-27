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

    const xScale = d3.scaleLinear()
        .domain([spec.xmin, spec.xmax])
        .range([0, spec.width]);
    const yScale = d3.scaleLinear()
        .domain([spec.ymin, spec.ymax])
        .range([spec.height, 0]);
    const graph = spec.g.append("g")
        .attr("transform", `translate(${spec.x}, ${spec.y})`);
    graph.append("g")
        .attr("transform", `translate(0, ${spec.height})`)
        .call(d3.axisBottom(xScale));
    graph.append("g")
        .attr("transform", `translate(0, 0)`)
        .call(d3.axisLeft(yScale));
    return {
        xScale: xScale,
        yScale: yScale,
        g: graph,
        spec: spec
    };
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

function logsumexp(logweights) {
    return logweights.reduce((a, b) => logaddexp(a, b), -Infinity);
}
function logmeanexp(logweights) {
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
        DOMPointReadOnly.fromPoint({ x: 0, y: 0 }).matrixTransform(selection.node().getScreenCTM())
    ).matrixTransform(get_foreground().node().getScreenCTM().inverse())
}

const enabled_anchors = {}

function make_anchor(g, x, y, uid, func) {
    // the marker is both a visual indicator (if drawn), and a reference point within "g" that will
    // be used to position the hover box correctly even if g is transformed (while still allowing us to
    // draw into the overall frame foreground and thus draw over things that are in front of g)
    // the extra `g` here is needed for get_foreground_point to work correctly, see note on that function
    let marker = g.append("g").attr("transform", `translate(${x},${y})`).append("circle").attr("r", 1).attr("display", "none")
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
    if (x > 10)
        return x.toFixed(0) // eg 1234234
    if (x > 1)
        return x.toFixed(1) // eg 4.3
    return x.toPrecision(digits) // eg 1.2e-3
}

const url_params = new URLSearchParams(window.location.search)

function load_by_path(f) {
    if (!url_params.has("path")) {
        throw new Error("?path= url parameternot specified")
    }
    d3.json('../' + url_params.get("path"), { cache: "no-store" })
        .then(f)
}

function add_controls() {
    d3.select("body").append("div").attr("id", "controls")
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