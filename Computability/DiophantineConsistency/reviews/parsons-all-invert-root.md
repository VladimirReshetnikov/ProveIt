# Height-preserving universal inversion

`ParsonsAllInvert.invert` proves the standard universal inversion for an
actual cut-free Foundation LK derivation: any chosen occurrences of `∀x A`
in a finite sequent can be replaced by `A[t]`, for an arbitrary term `t`,
while retaining cut-freeness and without increasing the derivation height.
Occurrences can be selected independently, including in the presence of
contraction. The proof is by strong induction on height; for the principal
universal rule it rewrites the eigenvariable premise by `t, &0, &1, …`,
with separate proofs that rewriting preserves height and cut-freeness.

`invert_below_exs` gives the immediate client needed for an induction
counterexample rule: opening a universal side in the existential-rule premise
produces a cut-free derivation strictly below the original existential
conclusion's height. The result is a Lean existence proof of a derivation;
its reported axiom dependencies include classical choice.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`; both objects and complete logs match. The
six axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`.
The [16-file replay manifest](parsons-all-invert-replay/FILES.json) has
SHA-256 `205407e4197c8b3dd14b56c973492de2c1afa2482e57a15f5994aacde8c11bb2`.
The direct `ParsonsLeaves` source hash
`52c72156de467be271f42cf40089520b887e33c25f3bc8eba7284077b52fb51b`
matches its frozen snapshot, and its object hash is
`052d6e5c611fdc8aff91a473f9fc8951190fabcd93cf03c8258772a2b951d8f6`.
Earlier provider chains, Foundation/Mathlib, and completeness objects remain
an inherited boundary, not a fresh transitive source audit.

This establishes a height bound for opening a side formula; it does not
construct the global marked recursion, turn an arbitrary non-prenex Π₂ side
into a strict normal form, prove conservation, or identify the target rule
calculus with PRA. In particular, the existential-rule client by itself does
not supply the Σ₁ guard required by the induction counterexample case.

## Independent root replay

A third build at `/tmp/parsons-all-invert-build-d1_xog4p` passed; source,
object and complete-log hashes match both author runs. The leaves provider
matches the independently rebuilt object. The [independent artifacts](parsons-all-invert-replay/root-build/)
are preserved; Foundation/Mathlib remains an inherited boundary.
