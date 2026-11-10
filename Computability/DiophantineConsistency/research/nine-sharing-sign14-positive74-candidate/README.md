# Fourteen positive inputs: 74-gate external circuit candidate

`build.py` makes a separate positive-coordinate form of the pinned 86-gate natural-coordinate seed. For each of its 14 natural inputs `v[i]`, it substitutes `v[i] = u[i] - 1` with `u[i] ≥ 1`. Thus positive inputs and natural inputs correspond bijectively. The fixed ports remain arbitrary integers.

The builder cancels `(u−1)+1`, changes `b−(F−1)` to `(b+1)−F`, and changes `(A−(F−1))−1` to `A−F`. These are integer-ring identities. Exact ordered-subtree sharing of the resulting five residuals and their sum of squares gives 74 live binary arithmetic gates: 18 additions, 18 subtractions and 38 multiplications. Five squares and four sum operations are included. These counts depend on the stated sharing and input conventions; the 86-gate input circuit uses natural rather than positive coordinates, so the counts are not a same-interface comparison or a minimality claim.

The builder verifies the pinned source, rewrite occurrence counts, six assignment controls and full circuit liveness. The rewrite rules also hold as polynomial identities over arbitrary integers, so the affine translation preserves total degree; the source's checked symbolic degree 124 would transfer once this specific AST and coordinate bridge are formally bound. The builder itself is external evidence, not a Lean theorem or a formal interpretation of JSON, PDF or fixed-port bytes. Independent structural and count review is pending.

Independent structural and gate-count audit passed: `../../reviews/nine-sharing-sign14-positive74-candidate-independent/`. Lean positive-coordinate transport and external file binding remain open.
