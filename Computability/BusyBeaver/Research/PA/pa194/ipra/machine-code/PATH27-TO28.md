# PA194 site 27 positive branch to site 28

`PA194Path27To28.positiveBranchPath27To28` is a model-uniform physical-run theorem for the pinned literal PA194 stepper. It starts at state 24 with left half 1 and a right half consisting of the actual source-program path 27, a zero run, a delimiter, and the complete encoded source file. Its sole branch hypothesis is that logical register 0 equals `m + 1`.

At the exact model-valued clock in the theorem it returns to state 24 with left half 1, actual source path 28, and source file `sourceFileCode (Function.update e 0 m)`. Every other logical register and the entire numeric suffix remain arbitrary and are preserved. Both zero runs have length `(k + 1) + 1`; since path 28 is one bit longer, the output has one additional total header padding cell. The theorem composes the actual physical positive transition, the six-register return, and a kernel-checked input/output identification. It does not require a blank suffix.

`check-path27-to28.sh` builds the 23-source increment from the nine site-27 decision modules through this path-to-path theorem and checks printed axiom reports for `sorryAx`. It accepts `PA194_TWO_PASSES_SOURCE_DIR` to select these sources, and explicitly requires the parent, project, foundation, parent-startup and dense-startup overlays. Direct imported object hashes are checked, but those checks do not establish a coherent transitive closure: the input overlays must independently be audited and coherent.

This is an all-model semantic physical execution for one branch. It is not by itself a native iPRA proof, an arbitrary-instruction simulation, or either consistency implication.
