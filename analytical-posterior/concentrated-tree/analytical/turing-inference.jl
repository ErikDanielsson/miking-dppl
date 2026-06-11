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

tree = Dict(
    "label" => 0, "age" => 5.0,
    "left" => Dict(
        "label" => 0, "age" => 4.0,
        "left" => Dict(
            "label" => 0, "age" => 3.0,
            "left" => Dict(
                "label" => 0, "age" => 2.0,
                "left" => Dict(
                    "label" => 0, "age" => 0.0,
                    "left" => Dict("label" => 1),
                    "right" => Dict("label" => 2)
                ),
                "right" => Dict(
                    "label" => 0, "age" => 0.0,
                    "left" => Dict("label" => 3),
                    "right" => Dict("label" => 4)
                )
            ),
            "right" => Dict(
                "label" => 0, "age" => 2.0,
                "left" => Dict(
                    "label" => 0, "age" => 0.0,
                    "left" => Dict("label" => 5),
                    "right" => Dict("label" => 6)
                ),
                "right" => Dict(
                    "label" => 0, "age" => 0.0,
                    "left" => Dict("label" => 7),
                    "right" => Dict("label" => 8)
                )
            )
        ),
        "right" => Dict(
            "label" => 0, "age" => 3.0,
            "left" => Dict(
                "label" => 0, "age" => 2.0,
                "left" => Dict(
                    "label" => 0, "age" => 0.0,
                    "left" => Dict("label" => 9),
                    "right" => Dict("label" => 10)
                ),
                "right" => Dict(
                    "label" => 0, "age" => 0.0,
                    "left" => Dict("label" => 11),
                    "right" => Dict("label" => 12)
                )
            ),
            "right" => Dict(
                "label" => 0, "age" => 2.0,
                "left" => Dict(
                    "label" => 0, "age" => 0.0,
                    "left" => Dict("label" => 13),
                    "right" => Dict("label" => 14)
                ),
                "right" => Dict(
                    "label" => 0, "age" => 0.0,
                    "left" => Dict("label" => 15),
                    "right" => Dict("label" => 16)
                )
            )
        )
    ),
    "right" => Dict(
        "label" => 0, "age" => 4.0,
        "left" => Dict(
            "label" => 0, "age" => 3.0,
            "left" => Dict(
                "label" => 0, "age" => 2.0,
                "left" => Dict(
                    "label" => 0, "age" => 0.0,
                    "left" => Dict("label" => 17),
                    "right" => Dict("label" => 18)
                ),
                "right" => Dict(
                    "label" => 0, "age" => 0.0,
                    "left" => Dict("label" => 19),
                    "right" => Dict("label" => 20)
                )
            ),
            "right" => Dict(
                "label" => 0, "age" => 2.0,
                "left" => Dict(
                    "label" => 0, "age" => 0.0,
                    "left" => Dict("label" => 21),
                    "right" => Dict("label" => 22)
                ),
                "right" => Dict(
                    "label" => 0, "age" => 0.0,
                    "left" => Dict("label" => 23),
                    "right" => Dict("label" => 24)
                )
            )
        ),
        "right" => Dict(
            "label" => 0, "age" => 3.0,
            "left" => Dict(
                "label" => 0, "age" => 2.0,
                "left" => Dict(
                    "label" => 0, "age" => 0.0,
                    "left" => Dict("label" => 25),
                    "right" => Dict("label" => 26)
                ),
                "right" => Dict(
                    "label" => 0, "age" => 0.0,
                    "left" => Dict("label" => 27),
                    "right" => Dict("label" => 28)
                )
            ),
            "right" => Dict(
                "label" => 0, "age" => 2.0,
                "left" => Dict(
                    "label" => 0, "age" => 0.0,
                    "left" => Dict("label" => 29),
                    "right" => Dict("label" => 30)
                ),
                "right" => Dict(
                    "label" => 0, "age" => 0.0,
                    "left" => Dict("label" => 31),
                    "right" => Dict("label" => 32)
                )
            )
        )
    )
)

interactions = [[2, 0], [2, 0], [2, 0], [2, 0], [2, 0], [2, 0], [2, 0], [2, 0], [2, 1], [2, 1], [2, 1], [2, 1], [2, 1], [2, 1], [2, 1], [2, 1], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2], [2, 2], [1, 2], [1, 2], [1, 2], [1, 2], [1, 2], [1, 2], [1, 2], [1, 2]]

subrootLength = 5.0

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

CSV.write("concentrated-tree/analytical/chain.csv", DataFrame(chain))

for var in names(chain, :parameters)
    savefig(plot(chain[[var]]; size=(800, 600)), "concentrated-tree/analytical/trace_$(var).png")
    savefig(density(chain[[var]]; size=(800, 600)), "concentrated-tree/analytical/density_$(var).png")
    savefig(histogram(chain[[var]]; size=(800, 600)), "concentrated-tree/analytical/histogram_$(var).png", normalize=:pdf, bins=min(500, div(n_samples, 10))
end
