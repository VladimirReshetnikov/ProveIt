import IPRADerivations.AnalyticNumberTheory.PNTStageStep

/-!
# The arithmetic of the crossing case (`pnt_ipra_constructive_2026-11-14`, `con:deficit`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `contraction.tex`, proof of Lemma `con:deficit`,
third case: between a high sample and a later low sample, `|r| < a/2` and the stretch is long, so
"`∫_{t_u}^{t_v} d(t) dt ≥ (a/2)(15a/(32·5)) = 3a²/64`". Discretely: a low sample at the divisor `d_u` (value
`m_u = ⌊x/d_u⌋`), a high sample at `d_v > d_u` (`m_v`), the interior `d_u < d ≤ b = d_v − 1` with deficit sum `G_c`
and mass `M_c`. From

* `A M_c ≤ 2 G_c` (`BlockDeficit.case_mid_sum`), `(b − d_u) F q ≤ M_c + F b`, `m_v ≤ q` (`BlockCases.mass_interior`),
* `A m_u ≤ 8 D (m_u − m_v)` (`BlockTests.cross_gap`), and the divisions `x = d_u m_u + r_U = d_v m_v + r_V`,

`crossC_alg` derives `3 A² F x ≤ 48 D G + 100 A D F (D₂ + Q₁)` for every `G ≥ G_c`, `d_u, d_v, b ≤ D₂`, `m_v ≤ Q₁`,
`A ≤ 4D`. The proof multiplies by `m_u ≥ 1` (an exact certificate found by elimination, with nonnegative remainder
`AF(Am_u + 8Dm_v r_U + 8D r_V + 8D m_v + 8D)`) and cancels it.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.CrossAlg

open_ipra exports

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The crossing-case arithmetic. -/
theorem crossC_alg {G Gc Mc mu mv du dv b c t q x F A Ds rU rV D2 Q1 : PTm n}
    (hs1 : Γ ⊢[PRAAx] le (A * Mc) (two * Gc)) (hs2 : Γ ⊢[PRAAx] le (c * (F * q)) (Mc + F * b))
    (hs3 : Γ ⊢[PRAAx] le mv q) (hs4 : Γ ⊢[PRAAx] le (A * mu) (num 8 * (Ds * t)))
    (hs5 : Γ ⊢[PRAAx] le Gc G) (hs8 : Γ ⊢[PRAAx] le A (two * (two * Ds))) (hs9 : Γ ⊢[PRAAx] le mv Q1)
    (hb2 : Γ ⊢[PRAAx] le b D2) (hdv2 : Γ ⊢[PRAAx] le dv D2) (hdu2 : Γ ⊢[PRAAx] le du D2)
    (hmu : Γ ⊢[PRAAx] le one mu) (hrU : Γ ⊢[PRAAx] lt rU du) (hrV : Γ ⊢[PRAAx] lt rV dv)
    (eU : Γ ⊢[PRAAx] x ≐ du * mu + rU) (eV : Γ ⊢[PRAAx] x ≐ dv * mv + rV) (edv : Γ ⊢[PRAAx] dv ≐ b + one)
    (et : Γ ⊢[PRAAx] mu ≐ mv + t) (ec : Γ ⊢[PRAAx] b ≐ du + c) :
    Γ ⊢[PRAAx] le (num 3 * (A * (A * (F * x))))
      (num 48 * (Ds * G) + num 100 * (A * (Ds * (F * (D2 + Q1))))) := by
  have eU' := natEq eU; have eV' := natEq eV; have edv' := natEq edv; have et' := natEq et; have ec' := natEq ec
  have z : Γ ⊢[PRAAx] le (A * (A * (F * x)))
      (num 16 * (Ds * Gc) + num 8 * (Ds * (A * (F * b))) + A * (A * (F * dv)) + num 8 * (A * (F * (Ds * mv))) +
        num 16 * (A * (F * (Ds * du)))) := by
    refine cancel_pos hmu ?_
    ipra_le 8 * 𝔞 Ds * 𝔞 mu * sl hs1 + 8 * 𝔞 Ds * 𝔞 mu * 𝔞 A * sl hs2 +
        8 * 𝔞 Ds * 𝔞 mu * 𝔞 A * 𝔞 F * 𝔞 c * sl hs3 + 𝔞 A * 𝔞 F * 𝔞 mv * 𝔞 dv * sl hs4 +
        𝔞 A * 𝔞 A * 𝔞 F * 𝔞 mu * sl hrV + 8 * 𝔞 Ds * 𝔞 A * 𝔞 F * 𝔞 mv * sl hrV + 8 * 𝔞 Ds * 𝔞 A * 𝔞 F * sl hrU +
        8 * 𝔞 Ds * 𝔞 A * 𝔞 F * 𝔞 du * sl hmu +
        𝔞 A * 𝔞 F * (𝔞 A * 𝔞 mu + 8 * 𝔞 Ds * 𝔞 mv * 𝔞 rU + 8 * 𝔞 Ds * 𝔞 rV + 8 * 𝔞 Ds * 𝔞 mv + 8 * 𝔞 Ds) with
      8 * 𝔞 A * 𝔞 Ds * 𝔞 F * (𝔞 mv - 1) * eU' - 𝔞 A * 𝔞 F * (𝔞 A * 𝔞 mu + 8 * 𝔞 Ds * 𝔞 mv - 8 * 𝔞 Ds) * eV' -
        8 * 𝔞 A * 𝔞 Ds * 𝔞 F * 𝔞 mu * 𝔞 mv * ec' - 8 * 𝔞 A * 𝔞 Ds * 𝔞 F * 𝔞 mu * 𝔞 mv * edv' +
        8 * 𝔞 A * 𝔞 Ds * 𝔞 F * 𝔞 dv * 𝔞 mv * et'
  ipra_le 3 * sl z + 48 * 𝔞 Ds * sl hs5 + 24 * 𝔞 Ds * 𝔞 A * 𝔞 F * sl hb2 + 3 * 𝔞 A * 𝔞 F * 𝔞 dv * sl hs8 +
    12 * 𝔞 A * 𝔞 Ds * 𝔞 F * sl hdv2 + 24 * 𝔞 A * 𝔞 F * 𝔞 Ds * sl hs9 + 48 * 𝔞 A * 𝔞 F * 𝔞 Ds * sl hdu2 +
    16 * 𝔞 A * 𝔞 Ds * 𝔞 F * 𝔞 D2 + 76 * 𝔞 A * 𝔞 Ds * 𝔞 F * 𝔞 Q1

end LeanProofs.IPRA.AnalyticNumberTheory.CrossAlg
