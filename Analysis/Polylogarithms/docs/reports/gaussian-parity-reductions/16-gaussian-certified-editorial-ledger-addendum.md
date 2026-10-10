# Proposed editorial-ledger addendum: Gaussian proof upgrades

A research continuation, *From Conjectural Gaussian Reductions to Certified
Polylogarithm Evaluation* (9 October 2026), supplies analytic proofs of
`gauss:eq:wt5-sporadic` and `gauss:eq:g51`, `g42`, `g33`, `g24`, `g15`.
The weight-five relation is `960 A5 - 224 B5`, where `A5` and `B5` are the
imaginary parts of the `(1,4)` and `(2,3)` same-argument shuffle products.
It extends to an explicit all-odd-weight family. The five weight-six rows are
endpoint-safe specializations of Panzer's published depth-two parity formula.
Their original coefficients are unchanged.

The report also gives a geometric Chebyshev–moment evaluator with exact
classical moment expressions and outward-rounded certificates, including
mixed roots with product one. Kernel-rate optimality is not a full algorithmic
lower bound, and the conductor-dependent approximation degree is not a full
bit-complexity estimate.

`gauss:eq:S4-closed` remains conjectural. All period independence, minimal-depth,
and unproved triple-candidate statements retain their previous status.
The delivered code is tested but not proof-assistant verified. The report is
unrefereed and makes no claim of first publication for its specializations.
