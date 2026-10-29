# Candidate PRA subtraction cancellation laws

`PRASubSuccCancel` derives the universal closure of
`succ(x)-succ(y)=x-y` in candidate PRA. `PRASubAddition` uses that law and
the reviewed addition laws to derive `(x+y)-x=y`. Both are proved for
arbitrary equality models by parametric open induction, and completeness
yields closed derivations in the candidate theory. They are prerequisites
for the Q order clause; neither completes that clause or establishes
standard PRA equivalence.

The independent replay `/tmp/pra-sub-laws-root-ijxurewk` passed all four
files without warnings and matched the author object hashes; its four axiom
reports use only `propext`, `Classical.choice`, and `Quot.sound`. The
merged subtraction source and rebuilt object are pinned in the driver.
Foundation, Mathlib, PRATheory, and other inherited prerequisite objects
remain a cache boundary. The [evidence packet](pra-subtraction-laws-root-replay/)
preserves final and stale exploratory attempts and the subtraction refresh.
