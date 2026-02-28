#!/usr/bin/env fish

echo running transformation
build/temp noDebug > build/model.mc
and echo transformation complete, fixing stuff
and sed \
  -e '/^ *external /{s/^.*$//;N;/^\n *in$/d;D}' \
  -e "s/\(Bernoulli\|Exponential\|Gaussian\|Gamma\|Poisson\|Uniform\|Dirichlet\|Categorical\)/mk\1/g" \
  build/model.mc > $argv[1]
