# PA194 site-25 zero branch to site 27

`PA194Path25To27.zeroBranchPath25To27` composes the physical run with the
actual source-program paths at both ends. From state 24, left half 1 and
`modelWord (path 25) (zeros(k+2, 1+2·sourceFileCode args))`, it reaches
state 24, left half 1 and
`modelWord (path 27) (zeros(k+1, 1+2·sourceFileCode args))`. The only
register assumption is `args 8 = 0`; all other logical registers, the spare,
and the complete numeric suffix can be arbitrary model elements. The clock
is the exact named sum in the theorem.

`PA194Path27Frame.frame_bits_general` relates the model-word encoding to the
actual standard zipper frame for any standard path and complete physical file
list. `PA194Path27Frame.frameSelectedBlank` combines that result with the
source register permutation for standard numeric arguments, explicitly
requiring the separate numeric suffix to be zero. This standard zipper-frame
bridge has a narrower scope than the arbitrary-suffix all-model run.

`check-path25-to27.sh` recompiles the incremental source suffix with the five
overlays documented in `TWO-HEADER-PASSES.md`. It checks selected direct object
hashes and the printed axiom reports; the supplied overlays still require an
independently audited coherent transitive import closure. Set
`PA194_TWO_PASSES_SOURCE_DIR` for sources outside the repository.

The theorem gives a model-uniform semantic physical execution for one source
instruction, not an object-theory iPRA derivation or an all-instruction
simulation. In particular it does not prove a consistency implication.
