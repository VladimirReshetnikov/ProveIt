# Independent source review: positive 80 to positive 81

The pinned `research/ordinary13-positive80-to81-model-draft/` proposes an
all-model transfer; its source, all imported graph clients, proof tactics and
provider/axiom closure are **unelaborated**. The author's receipt reproduces.
This independent checker parses both generated Lean literals against their
JSONs, compares their 73 common graph rows and exact 7/8-row finalizers, and
runs 625 bounded square-to-product controls. Reproduce with
`python3 -I -S -B check.py | cmp - receipt.json` in this directory. The
finite tests do not prove a model equivalence.

At a positive 80 valuation v, `lower` subtracts one at the ten shifted
coordinates, retaining direct f, r and y. The source's `lift_lower v hv`
uses positivity to recover v. The forward 89→88→87→86→85 maps then raise
J, gamma, w and eta; the exact 85 prototype is evaluated at this same
`image85 v`. The separate prototype `residuals_zero` source supplies its
four unit-derived residuals, and `field_equalities` proposes to identify
those four values with the 81 parent at v. Thus the proposed 80-zero→81-zero
direction depends on the exact unit-factor proof and those field identities;
it does not use the reverse r replacement or an eta-forcing assumption.
The port tuple p is an arbitrary integer tuple in this local theorem, not a
compact-beta specialization. Every predecessor/cast and simplifier step still
needs Lean checking.

In the other direction, the 81 output is exactly
`A0²+A1²+(Fa−1)²+g72²`. In the ordered model difference ring, a zero sum of
squares forces each summand zero. The corresponding 80 factors are then all
1, so its output is zero. The source states this direction at arbitrary
model-natural valuations; it does not need the separate input-positivity
premise. The `nlinarith` and domain-square arguments remain unelaborated.

`sameNoZero` uses **positiveShift 80 first and positiveShift 81 second**:
a zero of shifted 81 yields a zero of shifted 80 in the first implication,
and a zero of shifted 80 yields a zero of shifted 81 at the necessarily
positive shifted valuation in the other implication. `bridge80` passes the
exact shifted 81 `PolynomialBridge` as the parent premise. Its `native85`
uses the same compact tuple and retains that exact premise; the earlier
85→80 source chain and all of its obligations remain inherited. Neither an
81 parent bridge nor the target consistency formulation has been verified.

During preparation, the source author added the required explicit
`Eta85ToPositive80` import and corrected a reversed rewrite in the
81-zero→80-zero simplification. This review pins the revised transfer SHA
`d4e3d7811a59e194771b357465bafac5b1cdcbd3168dab1c0a12e4eddb6050d8`.
Neither repair nor the remaining `rfl`, `simp`, `ring`, `nlinarith`, and
`#print axioms` commands has been validated by Lean. No further mathematical
or source-interface mismatch was found in the inspected cuts; graph zero
maps, compact byte/PDF bindings, a parent endpoint, and iPRA equivalence
remain separate.
