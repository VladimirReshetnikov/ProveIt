# Conditional five-norm quartic candidate: 33 witnesses

This is an **external, conditional candidate**, not a proved reduction, Lean
model bridge, or iPRA endpoint. It modifies the reviewed 38-witness seed by
representing each of five potentially signed materialized gates by one natural
coordinate, rather than a pair. Its exact 24 residuals use 14 shifted source
inputs plus 19 cut coordinates, for **33 natural witnesses plus the unused
distinguished Jones input**. Each residual has syntactic witness-degree at
most two, so the sum of squares has degree at most four. The first residual
still specializes at all-zero witnesses to `−(beta+1)^2`.

If a gate's signed-pair value is `P−N`, a positive cut now asserts
`w − (P−N) = 0`, and the negative cut asserts `w − (N−P) = 0`. This gives
unconditional ring reconstruction from a satisfying seed. The missing forward
step must establish the following signs for **every model solution of the same
five original norm equations**, then represent the corresponding nonnegative
differences by model-natural witnesses:

| Cut | Required sign | Reason to formalize |
| --- | --- | --- |
| `gap` | `gap ≥ 0` | The transport norm and port bounds give `F+alpha<q`; hence `(q−1)(q−F)+alpha>0`. |
| `tau` | `tau ≥ 0` | The same scalar window gives `R+2<E`; since `N≥1` and `k>0`, `E*N+k−R>0`. |
| `cTminusR` | `c*T−R ≥ 0` | The maintained first-index result gives `2*R<c`; use `T≥1` and `c>0`. |
| `V` | `f²*(c*T−R)−c ≥ 0` | From the strict strong norm, positive `I=i*c²`, and positive `Delta`, show `f≥2`; combine this with `2*R<c` and `T≥1`. |
| `V2minusY2` | `V²−y² ≤ 0` | The auxiliary norm gives `S²*(V²−y²)=1−y²≤0`; use `S>0` and `y≥1`. |

These are mathematical proof plans, **not checked Lean lemmas in this
packet**. The existing `ArithmeticPellFirstIndex.scalar_window` supplies the
window under its positive-input, transport and `MC<beta`, `MF<2*beta`
hypotheses. `ArithmeticPellFirstIndex.maintained_first_indices` supplies the
first-index bound directly with the original index under its full transport,
first, main, strict and auxiliary equations and positive-input hypotheses.
One must explicitly transfer the
ring equations and fixed-port bounds to those natural-model hypotheses; in
particular avoid silently treating truncated natural subtraction as ring
subtraction. Alternatively, `ArithmeticCarrier94Indices.ordinary_first_indices`
uses the **scaled** index `Delta * i_source`: then its `i*c²` is
`S = Delta*i_source*c²`, its strict equation is exactly the `scaled_Ns=Delta`
constraint, and its auxiliary equation is `Na=1`. This substitution and the
source-to-natural equations remain proof obligations, not an assertion that
the ordinary theorem applies directly to `i_source`. The actual once-shifted
high port and all four model-natural port casts must also be proved. No global
sign assumption on arbitrary source inputs is valid or needed.

`check.py` externally replays all 60 used graph rows in the free commutative
ring, checks both signs of each cut residual, the five norm residuals,
normalization, syntactic degree, exact fixed-port bytes and the separate
source/graph comparison. Eight numerical replays permit **integer** cut
coordinates; they include eight negative cut assignments, demonstrating why
those tests do not establish natural-witness existence. The earlier
`norm38` packet explains the ordered-ring norm theorem and the `Delta` scaling
identity. The present five sign obligations, a same-model forward witness
construction, reverse gate replay in Lean, degree and normalization proofs,
and the Jones and consistency transfers all remain open.

Run `python3 -I -S -B check.py`; no Lean process is used. The checked builder
pins the original graph and refuses to overwrite `seed.json`.
