using JSON

"""
    convert_final_json_to_mc(json_file::String)::String

Convert a final.X.json file to the input.mc format.

# Arguments
- `json_file::String`: Path to the final.X.json file

# Returns
- A formatted string in the input.mc format

# Example
```julia
result = convert_final_json_to_mc("final.1.json")
println(result)
```
"""
function convert_final_json_to_mc(json_file::String)::String
    # Read and parse JSON
    json_data = JSON.parsefile(json_file)
    
    # Convert the tree structure to Julia notation
    tree_str = tree_to_string(json_data["symbiontTree"], 4)
    
    # Convert interactions array
    interactions_str = format_array_2d_inline(json_data["interactions"], 4)
    
    # Convert hostDistances array
    host_distances_str = format_array_2d_inline(json_data["hostDistances"], 4)
    
    # Build the final output
    result = """let input = { symbiontTree = $tree_str
    """
    result *= """
, interactions =
    $interactions_str
"""
    result *= """
, hostDistances =
    $host_distances_str
"""
    if haskey(json_data, "subrootLength")
        data = json_data["subrootLength"]
        result *= """
, subrootLength = $(data)
"""
        data = json_data["subrootLabel"]
        result *= """
, subrootLabel = $(data)
"""
    end


    result *= """} in
let tmp = anonPLACEHOLDER input {} in
dprint tmp
"""
    
    return result
end

"""
    tree_to_string(node::Dict, indent::Int=4)::String

Recursively convert a tree node to Julia notation.
"""
function tree_to_string(node, indent::Int=4)::String
    indent_str = repeat(" ", indent)
    next_indent = indent + 2
    next_indent_str = repeat(" ", next_indent)
    
    # Get the constructor type and data
    constructor = get(node, "__constructor__", nothing)
    data = get(node, "__data__", node)
    
    if constructor == "Leaf"
        # Format as: Leaf { label = X, age = Y }
        label = data["label"]
        age = data["age"]
        return "Leaf\n$(indent_str)  { label = $label\n$(indent_str)  , age = $age\n$(indent_str)  }"
    elseif constructor == "Node" || haskey(data, "left")
        # Format as Node with left and right children
        label = data["label"]
        age = data["age"]
        left = data["left"]
        right = data["right"]
        
        left_str = tree_to_string(left, next_indent)
        right_str = tree_to_string(right, next_indent)
        
        return """Node
$(indent_str)  { age = $age
$(indent_str)  , label = $label
$(indent_str)  , left = $left_str
$(indent_str)  , right = $right_str
$(indent_str)  }"""
    else
        error("Unknown node type: $constructor")
    end
end

"""
    format_array_2d_inline(arr::Vector, indent::Int=6)::String

Format a 2D array with opening bracket inline (for interactions and hostDistances).
"""
function format_array_2d_inline(arr::Vector, indent::Int=6)::String
    indent_str = repeat(" ", indent)
    
    lines = ["[ "]
    
    for (i, row) in enumerate(arr)
        # Format each row
        formatted_row = map(x -> x isa Float64 ? string(x) : string(x), row)
        row_str = "[" * join(formatted_row, ", ") * "]"
        
        if i == 1
            # First row: append to the opening bracket line
            lines[end] = lines[end] * row_str
        else
            # Subsequent rows: add with comma at the beginning
            push!(lines, ", " * row_str)
        end
    end
    
    # Close the bracket on its own line
    push!(lines, "]")
    
    return join(lines, "\n$indent_str")
end

# If run as a script, convert the file and save output
if abspath(PROGRAM_FILE) == @__FILE__
    if length(ARGS) > 0
        input_file = ARGS[1]
        output_file = length(ARGS) > 1 ? ARGS[2] : replace(input_file, ".json" => ".mc")
        
        result = convert_final_json_to_mc(input_file)
        write(output_file, result)
        println("Converted $input_file to $output_file")
    else
        println("Usage: julia convert.jl <input.json> [output.mc]")
    end
end
