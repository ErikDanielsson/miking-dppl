using Phylo, Random

Random.seed!(12)
n_hosts = 5
n_symbionts = 5
depth = 10
symbiont_tree = rand(Ultrametric(n_symbionts, 10.))
host_tree = rand(Ultrametric(n_hosts, 10.))
