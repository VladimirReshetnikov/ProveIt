# Independent source review: conditional positive-81 calibration

This review pins the final source in
`research/ordinary13-positive81-calibration-model-draft/`. The author's
receipt reproduces. The independent checker tests its exact witness/cut
interfaces, 9,504 scalar rank instances, and 27 positive-coordinate image
controls. Run `python3 -I -S -B check.py | cmp - receipt.json` from this
directory. These tests do not elaborate the source or prove its conditional
cuts in arbitrary models.

`compact_early_index` supplies tau, n and w together, including that n's
first Pell ordinate, `k=2n+4XY²w`, and `(2n) mod q⁴=R+1`. The source
extracts those components in the correct order. `ExactIndexCut` remains a
separate explicit hypothesis: it upgrades **that same** n and w from the
stated ordinate, decomposition and congruence to `2n=R+1`. The standalone
`Positive81ExactIndexCutDraft.exact_pair` does not prove the graph cut. It
records the positive-eta `P72Exact.indices_ordinary` interface, including
its same n/w, main norm and index m, strong norm, exact absdiff auxiliary
equation, `R≥26`, and `R+1<mu`; it returns both `m=R` and the exact pair.
The current calibration source does not derive those graph bindings from a
zero. In particular, an early congruence alone is not the asserted equality.

`OrientedMainCut` is another explicit hypothesis, requiring one and the same
natural main to satisfy the x coordinate, y coordinate and exact oriented
no-`E*q` balance at R. The proof retains the early index quotient w and passes
it to `EtaZeroGrowthDraft.power`; the separate graph input `v6` is its w0
argument. Its first-ordinate equality is passed in the correct reversed
orientation. No equality of an unrelated main root is silently inferred, and
no residue-90 extra-`E*q` graph theorem is used. The mapped prototype permits
eta zero in `prototype_power` only because the two cuts are hypotheses; the
positive-eta fact-level route is not thereby proved for eta zero.

For the scalar bound, q≥2 and F<q yield natural `q−1≥1` and `q−F≥1`;
the graph's shifted alpha is at least 1, so rank coefficient A≥2. With
`Q=q²−1≥1`, one has `q²=Q+1≤2Q≤A*Q≤R`. The final step from `q²≤R`
and the conditional `X=Exp.exp R` uses the existing model `lt_exp R`
interface to conclude `q²≤X`. The source obtains q≥2 and F<q through its
compact beta/J and positive-gap draft dependencies; it does not get this bound
from the rank window alone. These model calls and their casts remain
unelaborated.

For a positive 81 valuation, the one-way `prototype_zero_of81` route maps
through 80→89→85 without assuming the unresolved 83→81 root map. The image
restores original J and w after predecessor/increment, so
`original81_coordinates` proposes `q=1+J*beta`, `X=(1+J*beta)*w` at the
same `ports K`. `calibration81_original` applies both cuts at that identical
mapped valuation and still leaves them explicit. No concrete K, port bytes,
parent bridge, theorem `CrossRootCut`, or physical PDF is supplied by the
calibration wrapper.

No mathematical witness-order, carrier, or rank-bound mismatch was found in
the inspected source. The standalone `rfl`/`simp`/model order and exponential
lemmas, graph-zero maps, exact-index/auxiliary proof, oriented-main binding,
all providers, axiom reports and iPRA endpoint still require a coherent Lean
build. This review pins the author's final q/X-extension source SHA
`fe9386694b4ea07e10ea94b6cd8c3810cb70d394e0bfedd985d358183a753086`;
no source was changed in this review.
