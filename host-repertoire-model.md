## Host repertoire model with custom graph inference

### Inference machinery
The code is shared across
- `hrm-template.mc`: Inference entrypoint -- this is compiled along with the model scripts
- `coreppl/src/coreppl-to-mexpr/pval-graph/host-rep-mcmc.mc`: The MCMC inference machinery
- `coreppl/src/coreppl-to-mexpr/pval-graph/helpers.mc`: Some misc. functions
- `coreppl/src/coreppl-to-mexpr/pval-graph/continues.mc`: Continues for single chain MCMC and Pigeons -- very close to what we have in TreePPL

### Model scripts
The compiled model scripts are in `subroot-HRM/`. There are several scripts there, compiled from the TreePPL host repertoire model at commit [`b256a8d`](https://github.com/ErikDanielsson/treeppl/tree/b256a8d7b4200447a8f0275777a575dd514c7ad5):
- `subroot-HRM.b256a8d.mc`: The coreppl script
- `subroot-HRM.b256a8d.transformed.mc`: The script after the graph transformation is applied
- `subroot-HRM.b256a8d.renamed.mc`: The script after basic stores have been **renamed** to match the names in `coreppl/src/coreppl-to-mexpr/pval-graph/host-rep-mcmc.mc`. Everything up to this point can be done programmatically
- `subroot-HRM.b256a8d.edit.mc`: The script after **manual** edits of the stores, so that the correct data is given to the MCMC inference machinery -- this is the part that connects the model script to the inference and that cannot be automated currently
- `subroot-HRM.b256a8d.full-HRM.diff`: Diff between `subroot-HRM.b256a8d.renamed.mc` and `subroot-HRM.b256a8d.edit.mc`, i.e. all manual changes
- `subroot-HRM.b256a8d.full-HRM.mc`: The final script that can be compiled with `miking`
- `subroot-HRM.b256a8d.full-HRM.out`: The binary 

Generation of all scripts, except `subroot-HRM.b256a8d.edit.mc` is done by the Makefile `graph.mk`. 
For example, generating the final binary can be done my running `make -f graph.mk subroot-HRM/subroot-HRM.b256a8d.full-HRM.out`.

### Running and modifying scripts

The final binary can be run as `PPL_SEED=1 PPL_OUTPUT=samples.json ./subroot-HRM.b256a8d.full-HRM.out`.
If you use that specific sample file name, then there is a python plotting script: `subroot-HRM/plot.py`
that will plot the samples in an online fashion. This requires some dependencies listed in the (automatically generated)
`requirements.txt` -- it might be easier to just look at the dependencies in the actual script -- I have not tested if the environment is reproducible.

**MCMC configuration**
- The number of MCMC iterations and the sampling period is set in `hrm-template.mc`.
- To select to use Pigeons or single chain MCMC there is a comment on line 202 in `hrm-template.mc`
- The MCMC moves and schedule are configured in `coreppl/src/coreppl-to-mexpr/pval-graph/host-rep-mcmc.mc`. 
There are some comments there on what everything does that are hopefully intelligible.  

**Changing input data** 
The simplest approach is to change the edit script with the new input, and rerun the compilation pipeline from there. 

Alternatively, you might succeed in recompiling and transforming the model with the new in data, and then applying the diff.
This worked fairly well for me, but tends to be fragile, especially since there has been changes to the transformation since I last used it.

