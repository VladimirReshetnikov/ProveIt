# PA194 site-25 positive branch to site 26

`PA194Path25To26.positiveBranchPath25To26` proves a model-uniform literal
physical run between headers using the repository's actual source-program
paths 25 and 26. It assumes `args 8 = m+1`, the positive case of the site-25
instruction `dec 8`. The output source file is exactly
`sourceFileCode (Function.update args 8 m)`; every other logical register,
the spare, and the complete numeric suffix are preserved. Both the clock and
the final tape halves are explicit. The theorem allows arbitrary model-valued
registers, header length, predecessor, and suffix.

The output header has one more zero of padding than the input: the input is
`modelWord (path 25) (zeros(k+2, 1+2·sourceFileCode args))`, and the output is
`modelWord (path 26) (zeros(k+3, 1+2·sourceFileCode updated))`. This matches
the additional padding left by a successful decrement. The physical state is
24 and the left tape half is 1 at both ends. `PA194Path26Header.path26`
checks the actual standard path `[1,0,0,0,0,1]` with the kernel.

The proof composes the common source-header traversal, selected positive row,
preceding-register rewind, state-12/13 scans and final controller return.
`PA194PositiveOutputFile.sourceFileAfterDecrement` identifies the preserved
file and the one updated slot, including an arbitrary numeric suffix.

`check-path25-to26.sh` rebuilds this incremental source suffix with the same
five overlays described in `TWO-HEADER-PASSES.md`, checking selected direct
object hashes and the printed axiom reports. The overlays must have an
independently audited coherent transitive import closure: matching direct
hashes does not establish that closure. `PA194_TWO_PASSES_SOURCE_DIR` may
point to an external source directory.

This is an all-model semantic run for one source instruction, not yet an
object-theory iPRA derivation or an all-instruction source-machine simulation.
