# Model-uniform PA194 source header to state 17

`PA194SeedHeaderTo17.sourceHeaderTo17` proves a physical run in every candidate
PRA model, for arbitrary model-valued header length `k`, left half `l`, and all
11 source-file arguments. In particular, its parameters and execution clock
can be nonstandard. The encoded file is `sourceFileCode e`, using the checked
logical-to-physical register permutation; no file suffix is discarded.

Write `f` for that file, `s = zeros(k, 2*f+1)`, and `a = 16*(2*l+1)`; this
arithmetic is explanatory shorthand for the nested additions in the Lean
statement. The input is state 24 with left half `l` and right half `256*s+1`.
The output is state 17 with left half `half(a)` and right half
`parity(a)+4*w`, where `w` is the explicit model-valued one-run in the theorem.
The exact clock is the displayed primitive-recursive expression, equivalent
to `2*k+18` in the candidate arithmetic.

The proof obtains the even separator directly from `sourceFileCode`, follows
the 12 checked controller steps to state 84, and composes the existing
model-length zero-scan and state-15/16 return to 17. This is a conditional
physical trace on the stated header layout. It is a prefix of the seeded
first-instruction route; it does not yet prove that an arbitrary source
instruction is implemented, nor either PA consistency reduction.

`check-seed-header-to17.sh` rebuilds the source-frame and 12-step prefix
modules, checks selected source and directly imported object hashes, compiles
this theorem, and rejects `sorryAx`. It retains transitive prerequisite objects
from the documented overlays rather than rebuilding or pinning their complete
dependency closure; it is a suffix check, not a full independent audit.
