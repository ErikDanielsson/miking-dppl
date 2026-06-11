using JSON, DataFrames

function parse_interactions(json_file::String)
    """
    Parse JSON file and extract the interactions matrix from the first sample.
    Returns a matrix where each row represents an interaction object's interactions.
    """
    data = JSON.parsefile(json_file)
    first_sample = data["samples"][1]
    
    # Get dimensions
    n_items = length(first_sample)
    interactions_length = length(first_sample[1]["__data__"]["interactions"])
    
    # Build matrix from interactions
    matrix = zeros(Int, n_items, interactions_length)
    for (i, item) in enumerate(first_sample)
        matrix[i, :] = item["__data__"]["interactions"]
    end
    
    return matrix
end

function make_input_files(
    phyjson_fn::String,
    interactions_csv::String,
    simdata_fn::String,
    interaction_fn::String,
    subrootLabel=-1
)
    interactions = parse_interactions(interaction_fn)
    make_final_phyjson(phyjson_fn, simdata_fn, interactions, subrootLabel)
    write_interactions_csv(interactions_csv, interactions)
end

function make_final_phyjson(fn::String, simdata_fn::String, interactions::Matrix, subrootLabel=-1)
    simdata = JSON.parsefile(simdata_fn)
    infdata = Dict() 
    infdata["interactions"] = interactions'
    infdata["symbiontTree"] = simdata["symbiontTree"]
    infdata["hostDistances"] = simdata["hostDistances"]
    if haskey(simdata, "subrootLength")
        infdata["subrootLength"] = simdata["subrootLength"]
        infdata["subrootLabel"] = subrootLabel
    end
    open(fn, "w") do f
        JSON.json(f, infdata; pretty=true, inline_limit=size(interactions, 1) + 1)
    end
end


function write_interactions_csv(csv_file::String, interactions::Matrix)
    """
    Write interaction matrix to CSV with:
    - First column: row indices as species_1, ..., species_n
    - Header: column indices as species_1, ..., species_m
    """
    n_rows, n_cols = size(interactions)
    println(interactions)
    
    # Create column names: species_1, ..., species_m
    col_names = ["species_$i" for i in 1:n_cols]
    
    # Create row names: species_1, ..., species_n
    row_names = ["species_$i" for i in 1:n_rows]
    
    # Create DataFrame with the interaction matrix
    df = DataFrame(interactions, col_names)
    
    # Insert row names as the first column
    insertcols!(df, 1, :species => row_names)
    
    # Write to CSV
    CSV.write(csv_file, df)
end