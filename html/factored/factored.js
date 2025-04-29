"use strict";

// Add CSS link
d3.select("head").append("link")
    .attr("rel", "stylesheet")
    .attr("href", "factored.css");

// Setup basic DOM structure with d3-jetpack's chaining
const body = d3.select("body");
const error_div = body.append("div#error");
const header = body.append("div.header");
body.append("br");
body.append("div#controls");
const content = body.append("div#content");

// Create tooltip
const tooltip = body.append("div.tooltip");

// Global state
let currentHighlightedSpan = null;
// Global array to store all values
let all_values = [];

// Initialize
content.on("mouseleave", clearAllHighlights);
reload();

/**
 * Initiates data loading to display results
 */
function reload() {
    // Reset global array when reloading
    all_values = [];
    load_by_path(show_results);
}

/**
 * Renders the results in the content area
 * @param {Array} json - The JSON data to display
 */
function show_results(json) {
    // Clear previous content
    content.html("");
    
    // Process each entry with d3 chaining
    json.forEach(entry => {
        assert(entry.results.length === 1);
        let val = entry.results[0].val;
        let prob = Number(entry.results[0].prob);

        // Transform value
        preprocessValue(val);
        
        // Create query container and append elements
        content.append("div.query")
            .call(q => {
                q.append("span.query-text").text(entry.query_str);
                q.append("br");
                q.append("span.prob").text(show_prob(prob));
                q.append("span").html(": " + formatTransformedValue(val));
            });
    });
    
    // Apply initial colors
    setTimeout(applyInitialColors, 10);
}

/**
 * Applies background colors to all span containers based on their probabilities
 */
function applyInitialColors() {
    // Use d3 selection instead of querySelectorAll
    d3.selectAll('.span-container').each(function() {
        const valueIndex = d3.select(this).attr('data-index');
        applyColorBasedOnState(this, valueIndex);
    });
}

/**
 * Applies background color to a span based on its state and probability values
 * @param {Element} span - The span element to apply color to
 * @param {number} valueIndex - The index into the all_values array
 */
function applyColorBasedOnState(span, valueIndex) {
    assertdefs(span, valueIndex)

    // Use d3 to select the element
    const el = d3.select(span);
    const isCollapsed = el.classed('collapsed');
    
    // Get value from the array
    const val = assertdef(all_values[valueIndex]);
    
    // Create color scale
    const colorScale = d3.scaleLinear()
        .domain([0, 1])
        .range(["#fcb3b3", "#bbfcb3"]) // Light red to light green
        .interpolate(d3.interpolateHsl);
    
    // Apply color based on state
    if (isCollapsed) {
        el.st({backgroundColor: colorScale(val.prob_total)});
    } else {
        el.st({backgroundColor: colorScale(val.prob_constructor)});
    }
}

/**
 * Recursively transforms value objects and calculates total probabilities
 * @param {Object} val - The value object to transform
 * @returns {Object} - The transformed value object
 */
function preprocessValue(val) {
    if (val.constructor === "Prob") {
        const prob_constructor = Number(val.args[0].value);
        const constructor = val.args[1].value;
        const args = uncons(val.args[2]);

        val.constructor = constructor;
        val.args = args;
        val.prob_constructor = prob_constructor;
    } else {
        val.prob_constructor = 1.0;
    }
    
    // Transform child args
    val.args.map(preprocessValue);
    
    // Calculate total probability
    val.prob_total = val.prob_constructor * val.args.reduce((acc, arg) => acc * arg.prob_total, 1);
    
    return val;
}

/**
 * Converts a nested Cons/Nil structure to a JavaScript array
 * @param {Object} val - The value to convert
 * @returns {Array} - The resulting array
 */
function uncons(val) {
    if (val.constructor === "Nil") {
        return [];
    } else if (val.constructor === "Cons") {
        const head = val.args[0];
        const tail = uncons(val.args[1]);
        return [head, ...tail];
    }
    error("uncons: " + JSON.stringify(val));
}

/**
 * Formats a transformed value as HTML for display
 * @param {Object} val - The value to format
 * @returns {string} - HTML representation of the value
 */
function formatTransformedValue(val) {
    if (!val) return "null";
    
    switch(val.type) {
        case "Value": {
            // Add the value to the global array
            const valueIndex = all_values.length;
            all_values.push(val);
            
            const tooltipId = "tooltip-" + valueIndex;
            
            // Create container with d3
            const container = d3.create("span")
                .attr("class", "span-container")
                .attr("data-index", valueIndex)
                .attr("onclick", `toggleCollapse(event, ${valueIndex})`)
                .attr("onmouseover", `spanMouseOver(event, ${valueIndex}, '${tooltipId}')`)
                .attr("onmouseout", `handleMouseOut('${tooltipId}')`);
            
            // Add constructor name
            container.text(`(${val.constructor}`);
            
            // Add collapsible content
            const innerContent = container.append("span.inner-content");
            val.args.forEach(arg => {
                innerContent.append("span").html(" " + formatTransformedValue(arg));
            });
            
            // Add ellipsis and close paren
            container.append("span.ellipsis").text("...");
            container.append("text").text(")");
            
            return container.node().outerHTML;
        }
        case "FloatValue":
            return val.value.toFixed(2);
        case "HostValue":
            return val.value;
        default:
            return JSON.stringify(val);
    }
}

/**
 * Formats a probability value for display
 * @param {number} prob - The probability value
 * @returns {string} - Formatted probability string
 */
function show_prob(prob) {
    return prob.toExponential(2);
}

/**
 * Formats a log probability value for display
 * @param {number} prob - The log probability value
 * @returns {string} - Formatted log probability string
 */
function show_logprob(prob) {
    return prob.toFixed(1);
}

/**
 * Creates tooltip content based on value data
 * @param {number} valueIndex - The index into all_values
 * @returns {string} - HTML content for the tooltip
 */
function createTooltipContent(valueIndex) {
    // Use d3.create to build tooltip content
    const content = d3.create("div");
    const val = all_values[valueIndex];
    
    if (!val) return "";
    
    if (val.prob_constructor !== undefined) {
        content.append("div").text(`Constructor: ${show_prob(val.prob_constructor)}`);
    }
    
    if (val.prob_total !== undefined) {
        content.append("div").text(`Total: ${show_prob(val.prob_total)}`);
    }
    
    if (val.constructor) {
        content.append("div").text(`Type: ${val.constructor}`);
    }
    
    return content.html();
}

/**
 * Handles mouse over events on spans, highlighting them and showing tooltip
 * @param {Event} event - The mouse event
 * @param {number} valueIndex - The index into all_values
 * @param {string} tooltipId - The ID for the tooltip to show
 */
function spanMouseOver(event, valueIndex, tooltipId) {
    event.stopPropagation();
    
    const span = d3.select(`[data-index="${valueIndex}"]`);
    if (span.empty()) return;
    
    // Clear previous highlight
    if (currentHighlightedSpan !== null) {
        d3.select(`[data-index="${currentHighlightedSpan}"]`).classed('highlight-outline', false);
    }
    
    // Add highlight to current span
    span.classed('highlight-outline', true);
    currentHighlightedSpan = valueIndex;
    
    // Ensure color is applied correctly
    applyColorBasedOnState(span.node(), valueIndex);
    
    // Show tooltip
    if (tooltipId) {
        const tooltipContent = createTooltipContent(valueIndex);
        
        if (tooltipContent) {
            showTooltip(event, tooltipContent, tooltipId);
        }
    }
}

/**
 * Handles mouse out events, hiding tooltip and clearing highlights
 * @param {string} tooltipId - The ID of the tooltip to hide
 */
function handleMouseOut(tooltipId) {
    if (tooltipId) {
        hideTooltip(tooltipId);
    }
    
    if (currentHighlightedSpan !== null) {
        d3.select(`[data-index="${currentHighlightedSpan}"]`).classed('highlight-outline', false);
        currentHighlightedSpan = null;
    }
}

/**
 * Clears all highlighted spans
 */
function clearAllHighlights() {
    if (currentHighlightedSpan !== null) {
        d3.select(`[data-index="${currentHighlightedSpan}"]`).classed('highlight-outline', false);
        currentHighlightedSpan = null;
    }
}

/**
 * Toggles the collapsed state of a span
 * @param {Event} event - The click event
 * @param {number} valueIndex - The index into all_values
 */
function toggleCollapse(event, valueIndex) {
    event.stopPropagation();
    
    const span = d3.select(`[data-index="${valueIndex}"]`);
    if (span.empty()) return;
    
    // Toggle class using d3
    span.classed('collapsed', !span.classed('collapsed'));
    applyColorBasedOnState(span.node(), valueIndex);
    
    // Update tooltip
    const tooltipId = "tooltip-" + valueIndex;
    const tooltipContent = createTooltipContent(valueIndex);
    
    if (tooltipContent) {
        showTooltip(event, tooltipContent, tooltipId);
    }
}

/**
 * Shows a tooltip at the specified position with the given content
 * @param {Event} event - The triggering event (for positioning)
 * @param {string} text - The HTML content for the tooltip
 * @param {string} id - The ID to associate with the active tooltip
 */
function showTooltip(event, text, id) {
    // Use d3 for tooltip positioning
    tooltip
        .html(text)
        .attr("data-active-tooltip", id)
        .st({
            visibility: "visible",
            left: (event.pageX + 10) + "px",
            top: (event.pageY + 10) + "px"
        });
    
    event.stopPropagation();
}

/**
 * Hides the tooltip if it matches the given ID
 * @param {string} id - The ID of the tooltip to hide
 */
function hideTooltip(id) {
    const activeId = tooltip.attr("data-active-tooltip");
    if (!id || id === activeId) {
        tooltip.st({visibility: "hidden"});
    }
}

