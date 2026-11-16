# PA194 site-25 selected-zero branch

`PA194Site27Step.zeroBranchSite27` is a model-uniform physical-machine run
from a state-24 header of the form `1 + 256·zeros(k, 2·f + 1)` to a state-24
header of the form `17 + 128·zeros(k+1, 2·f + 1)`, both with left half 1.
Here `f` is the physical source-file code of `args`, and `zeros` is the
primitive-recursive binary zero-prefix operation; the theorem spells out the
powers of two by repeated addition. Its exact elapsed clock is the named sum
in the theorem. The seven low-order destination header bits are
`[1, 0, 0, 0, 1, 0, 0]`, the path-27 prefix, followed by `k+1` zero bits.

The sole register assumption is `args 8 = 0`. All other logical register
values, the physical spare, and the entire numeric tape suffix are arbitrary
model elements. The same `f` occurs in input and output, so the file is
preserved exactly; the proof does not assume blank tail cells. The clock and
inputs may be nonstandard elements of a candidate PRA model. This is an
all-model semantic theorem; the present module does not itself construct an
object-theory iPRA derivation of a universally quantified sentence.

`PA194ZeroOutputFile.sourceFileAfterZero` establishes the needed source-file
identity, and `PA194ZeroOutputArithmetic.outputArithmetic` identifies the
physical endpoint with the explicit prefix. A separate check connecting the
numeric header to the repository's `path 27` frame is being pursued.

`check-site27-step.sh` recompiles the entire incremental suffix, including the
zero-to-24 controller and the three output modules, using the five overlays
documented in `TWO-HEADER-PASSES.md`. It prints and checks the relevant axioms.
The supplied overlays must have an independently audited coherent transitive
import closure; pinning direct imported objects does not audit that closure.
`PA194_TWO_PASSES_SOURCE_DIR` can point at an external directory of sources.

This one selected source instruction is not a complete source-machine
simulation and does not prove either direction of the consistency equivalence.
