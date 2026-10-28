# Read-only lower-bound simplification after adaptive projection

2026-10-26, `/root/complemented47_review`. This is a source-based mathematical challenge of ROOT's proposed simplification, not a new Lean theorem or edit to the frozen power packet.

The frozen `NativeAdaptivePowerProjection.adaptive_projection` (source SHA256 `92a4d01435c031ea51706162503e5e51239c39eb5eebdfcaac587c933ef09c84`) proves `q ∣ 3*X` from its displayed literal carrier hypotheses. Its proof already derives `16 ≤ q` from `15 ≤ ports 0`, positive integer `J`, and `q = ports 0 * J + 1`. Positive `X` is an explicit original variable-domain hypothesis, not a recovered power or source premise.

Consequently `0 < 3*X`, and the existing core theorem

```lean
Int.le_of_dvd (bpos : 0 < b) (H : a ∣ b) : a ≤ b
```

applied with `a=q`, `b=3*X` gives `q ≤ 3*X`. Combined with `16 ≤ q`, integer arithmetic gives `6 ≤ X`, hence `2 ≤ X.toNat`. This directly excludes `X=1` before applying the large-base Pell growth bound. No cancellation of `3`, coprimality, restored source, first/main index equality supplied as a premise, or conclusion `X=2^R` is involved. In particular, the argument remains valid when `3 ∣ q`.

The divisibility is established in projection before the growth argument: `scaled_projection_algebra` supplies the witness, and the main projection wrapper derives its hypotheses from the actual classified carriers. Thus replacing the later `X=1` growth/mod-8 branch with this bound would be noncircular. It would not replace the subsequent large-base growth or small-projection uniqueness arguments.

The current frozen Recovery source (`cd97a608e86cefcba299f53f76150112c63898327f82460c7daf78b229d6f0ae`) and both focused-check sources remain unchanged. Its existing proof is not invalidated. The relevant `Int.le_of_dvd` declaration was read at Lean4.32 `Init/Data/Int/DivMod/Lemmas.lean:81`; no new compilation was performed for this observation. Any implementation should be a separately reviewed follow-up, after the current packet's independent acceptance.
