# Conditional model-level rank half-window

[`FreeMainRankHalf.rank_half`](FreeMainRankHalf.lean) passed guarded
[Lean check attempt02](observations/attempt02/result.json). In any `IΣ₁`
model's difference ring, a nonnegative `q`, the inequalities
`q≤X`, `q³≤Y`, `R+1<q⁴`, `3≤c`, nonnegative `g`, and the displayed main
Pell equation imply `2R<c`. It applies the separately checked
`IndependentYBounds.pell_c_bound`, without an early first-index congruence.

Lean exited 0 with axiom report `[propext, Classical.choice, Quot.sound]`, no
warnings or `sorryAx`, stable direct guards and no monitor stop. The object
SHA-256 is `419eed176429e0e1f2d31f05db1963bb3d893a6d63b0f249aa89e83b6d867079`.
The source comment “unchecked draft” predates the check and is preserved to
match the receipt. Direct captured-provider guards inherit transitive,
dynamic and between-sample ancestry. The first attempt's strict/nonstrict
inequality error, source and log are retained at `observations/attempt01/`.

This is a **conditional generic bridge**, not yet an extraction of those
hypotheses from actual 72-graph zeros or the compact44 ports. In particular
it does not prove the signed half-index theorem's separate large-c bound,
`m=R`, the reverse existence implication, or an iPRA endpoint.
