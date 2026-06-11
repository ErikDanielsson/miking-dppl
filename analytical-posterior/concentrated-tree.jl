include("process-interactions.jl")
include("phyjson-to-mc.jl")
using JSON, CSV, DataFrames

function generate_tree(depth, label_counter; age_multiplier=1.)
    if depth == 1
        # Create two leaves
        label_counter[1] += 1
        left = Dict("label" => label_counter[1])
        label_counter[1] += 1
        right = Dict("label" => label_counter[1])
        return Dict(
            "label" => 0,
            "age" => 0.0,
            "left" => left,
            "right" => right
        )
    else
        left = generate_tree(depth - 1, label_counter)
        right = generate_tree(depth - 1, label_counter)
        return Dict(
            "label" => 0,
            "age" => Float64(depth) * age_multiplier,
            "left" => left,
            "right" => right
        )
    end
end

tree = generate_tree(5, [0])

# Non-trivial slow evolution dataset: phylogenetic structure with multiple states
interactions = vcat(
    fill([2, 0], 8),  # First clade
    fill([2, 1], 8),  # Second clade
    fill([2, 2], 8),  # Third clade
    fill([1, 2], 8)   # Fourth clade
)

# Convert the concentrated tree dict (no __constructor__/__data__) to phyjson format.
# Leaf labels are 1..n_leaves; internal labels start at internal_counter.
function to_phyjson(node::Dict, internal_counter::Ref{Int})
    if !haskey(node, "left")
        return Dict(
            "__constructor__" => "Leaf",
            "__data__" => Dict("label" => node["label"], "age" => 0.0)
        )
    else
        internal_counter[] += 1
        return Dict(
            "__constructor__" => "Node",
            "__data__" => Dict(
                "label" => internal_counter[],
                "age" => node["age"],
                "left" => to_phyjson(node["left"], internal_counter),
                "right" => to_phyjson(node["right"], internal_counter)
            )
        )
    end
end

# Convert tree dict to Newick with branch lengths derived from node ages.
# Call with parent_age = root age so the root gets no branch-length suffix.
function dict_to_newick(node::Dict, parent_age::Float64)::String
    if !haskey(node, "left")
        branch_len = parent_age  # leaf age is 0.0
        return "species_$(node["label"]):$(branch_len)"
    else
        left_str = dict_to_newick(node["left"], node["age"])
        right_str = dict_to_newick(node["right"], node["age"])
        branch_len = parent_age - node["age"]
        inner = "($(left_str),$(right_str))"
        return branch_len > 0.0 ? "$(inner):$(branch_len)" : inner
    end
end

function serialize_tree_julia(node::Dict, indent::Int=0)::String
    pad = "    " ^ indent
    pad1 = "    " ^ (indent + 1)
    if !haskey(node, "left")
        return "Dict(\"label\" => $(node["label"]))"
    else
        left_str = serialize_tree_julia(node["left"], indent + 1)
        right_str = serialize_tree_julia(node["right"], indent + 1)
        return "Dict(\n$(pad1)\"label\" => $(node["label"]), \"age\" => $(node["age"]),\n$(pad1)\"left\" => $(left_str),\n$(pad1)\"right\" => $(right_str)\n$(pad))"
    end
end

function write_turing_script(output_dir::String, tree::Dict, interactions::Vector, subrootLength::Float64)
    analytical_dir = joinpath(output_dir, "analytical")
    mkpath(analytical_dir)
    tree_str = serialize_tree_julia(tree)
    interactions_str = "[" * join(["[$(v[1]), $(v[2])]" for v in interactions], ", ") * "]"

    script = """
using Turing, DynamicPPL, Mooncake, DifferentiationInterface
using LinearAlgebra, LogExpFunctions, StatsPlots, CSV, DataFrames

function rate_matrix_two_hosts(μ, λ)
    λ01, λ10, λ12, λ21 = λ
    m = [
        0.0 λ01 0.0 0.0 0.0;
        λ10 0.0 λ12 0.0 0.0;
        0.0 λ21 0.0 λ21 0.0;
        0.0 0.0 λ12 0.0 λ10;
        0.0 0.0 0.0 λ01 0.0
    ]
    m -= diagm(vec(sum(m; dims=2)))
    return μ * m
end

function encode(arr)
    if arr[1] == 0 && arr[2] == 2; return 1
    elseif arr[1] == 1 && arr[2] == 2; return 2
    elseif arr[1] == 2 && arr[2] == 2; return 3
    elseif arr[1] == 2 && arr[2] == 1; return 4
    elseif arr[1] == 2 && arr[2] == 0; return 5
    else; return 6
    end
end

function pruning_algorithm(tree, parent_age, Q, interactions)
    if !haskey(tree, "left")
        encoding = encode(interactions[tree["label"]])
        kernel = exp(Q * parent_age)
        return kernel[:, encoding], 0.0
    else
        currentAge = tree["age"]
        leftMsg, leftlll = pruning_algorithm(tree["left"], currentAge, Q, interactions)
        rightMsg, rightlll = pruning_algorithm(tree["right"], currentAge, Q, interactions)
        combined = leftMsg .* rightMsg
        lll = log(sum(combined))
        kernel = exp(Q * (parent_age - currentAge))
        return (kernel * (combined / exp(lll))), lll + leftlll + rightlll
    end
end

function log_lik_two_host_tree(tree, Q, subrootLength, interactions)
    if any(isnan, Q) || any(x -> abs(x) > 1e6, Q)
        return -Inf
    end
    subrootAge = tree["age"] + subrootLength
    msg, lll = pruning_algorithm(tree, subrootAge, Q, interactions)
    return log(mean(msg)) + lll
end

tree = $(tree_str)

interactions = $(interactions_str)

subrootLength = $(subrootLength)

@model function concentrated_tree_HRM(subrootLength, interactions, tree)
    μ ~ Exponential(10.0)
    β ~ Exponential(1.0)
    λ ~ Dirichlet([1.0, 1.0, 1.0, 1.0])
    Q = rate_matrix_two_hosts(μ, λ)
    @addlogprob! log_lik_two_host_tree(tree, Q, subrootLength, interactions)
end

model = concentrated_tree_HRM(subrootLength, interactions, tree)

n_samples = 50000
chain = sample(model, NUTS(; adtype=AutoMooncake()), n_samples)

println(chain)

CSV.write("$analytical_dir/chain.csv", DataFrame(chain))

for var in names(chain, :parameters)
    savefig(plot(chain[[var]]; size=(800, 600)), "$analytical_dir/trace_\$(var).png")
    savefig(density(chain[[var]]; size=(800, 600)), "$analytical_dir/density_\$(var).png")
    savefig(histogram(chain[[var]]; size=(800, 600)), "$analytical_dir/histogram_\$(var).png", normalize=:pdf, bins=min(500, div(n_samples, 10))
end
"""
    write(joinpath(analytical_dir, "turing-inference.jl"), script)
end

function export_concentrated_tree(output_dir::String="concentrated-tree")
    rb_dir = joinpath(output_dir, "revbayes")
    tppl_dir = joinpath(output_dir, "treeppl")
    tmp_dir = joinpath(output_dir, "tmp")
    mkpath(rb_dir)
    mkpath(tppl_dir)
    mkpath(tmp_dir)

    # Build phyjson symbiont tree; leaf labels 1..32, internals 33 onwards
    n_leaves = 32
    internal_counter = Ref(n_leaves)
    symbiont_phyjson = to_phyjson(tree, internal_counter)

    subrootLength = 5.0
    subrootLabel = -1

    # Trivial host tree: species_1 <- root -> species_2, equal branch lengths 1.0
    # Pairwise distance between the two hosts = 2.0
    host_distances = [[0.0, 2.0], [2.0, 0.0]]

    # Convert interactions Vector{Vector{Int}} → Matrix (n_symbionts × n_hosts = 32 × 2)
    interactions_matrix = Matrix(hcat(interactions...)')

    # Write final phyjson directly (no intermediate simulation-dataset file needed)
    final_phyjson_fn = joinpath(tppl_dir, "final.json")
    open(final_phyjson_fn, "w") do f
        JSON.json(f, Dict(
            "interactions" => interactions_matrix',
            "symbiontTree" => symbiont_phyjson,
            "hostDistances" => host_distances,
            "subrootLength" => subrootLength,
            "subrootLabel" => subrootLabel,
        ); pretty=true, inline_limit=size(interactions_matrix, 1) + 1)
    end

    # Write TreePPL .mc input
    result = convert_final_json_to_mc(final_phyjson_fn)
    write(joinpath(tppl_dir, "input.mc"), result)

    # Write the Turing script

    write_turing_script(output_dir, tree, interactions, subrootLength)

    # Write Newick files for RevBayes
    symbiont_newick = dict_to_newick(tree, tree["age"]) * ":$(subrootLength);"
    write(joinpath(rb_dir, "final-symbiont-tree.newick"), symbiont_newick)
    write(joinpath(rb_dir, "final-host-tree.newick"), "(species_1:1.0,species_2:1.0);")

    # Write interactions CSV and convert to Nexus
    interactions_csv = joinpath(tmp_dir, "interactions.csv")
    write_interactions_csv(interactions_csv, interactions_matrix)
    interactions_nex = joinpath(rb_dir, "interactions.nex")
    run(`Rscript R-scripts/csv-to-nex.R $interactions_csv $interactions_nex`)
end

export_concentrated_tree()
