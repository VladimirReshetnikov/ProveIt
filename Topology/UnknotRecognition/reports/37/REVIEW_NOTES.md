# Proof and implementation audit notes

This is the author's self-audit, not an external peer review or a formal proof.

## Corrections prevented during development

- Arbitrary vertex cuts are not antichains. Unrestricted prefix/suffix splitting
  double-counts paths visiting multiple cut vertices; over F2 it can erase a real
  entry. The implementation uses first-hit prefixes, including terminal-cut rules.
- Weighted cut capacity is vector-space dimension, not cut cardinality. A single
  vertex can transmit rank greater than one.
- A cut upper bound is not an exact rank. Cancellation, nilpotence, and closure
  can lower the rank. A lower homology bound of one is not an acceptance test.
- Separate rank caps must respect adjacent constraints from d^2=0. The greedy
  budget maximizes an **unweighted** sum on a path; it is not asserted to solve a
  weighted objective or a general separator optimization.
- The sharpness realization is a complex of vector spaces, not necessarily a
  Khovanov complex and not necessarily the original graph.
- The closed reference Morse perturbation can contain scalar coefficients. It is
  not the production all-scalars/positive-weight split; acyclicity is verified
  independently in this model.
- Synthetic graph counts are `V=2R+2M+4`, `E=2R+3M+2`. Endpoint composition counts
  `R(3M+R+3)` apply to **odd M**; even M cancels at the shared bottleneck.
- Rank-only factorization is valid at fixed closure, not as a substitute for maps
  during subsequent tangle extension.
- The conditional asymptotic theorem explicitly charges graph construction,
  closure evaluation, scalar contraction data, actual allocated state, and binary
  integer arithmetic. It is not a general unknot recognition bound.

## Executed checks

`results/tests.txt`: 36 test methods passed. `results/knot_audit.json`: 80 diagrams,
160 matching configurations, 1,070 maps, zero disagreements. Six supplied braid
certificates were replayed with the dense verifier. Mutation checks reject altered
inputs/ranks/matchings/cuts. The terminal preflight is tested with factor evaluation
mocked to fail, proving that the rejection branch does not evaluate maps.

The PDF was compiled with resolved references, no overfull boxes, and visually
inspected across all 27 pages using rasterized contact sheets, with full-page
inspection of dense equations and tables. This is visual/layout verification, not
proof-assistant verification of mathematical content.

## Evidence not supplied

No full repository checkout, production scanner adapter, upstream test-suite run,
Lean formalization, actual hard-knot corpus, comparison with production sparse
cancellation, or proof that the synthetic family is realized by knots. The corpus
is not an estimate of worst-case recognition complexity. The current mathematical
claims should still receive independent review before production adoption.
