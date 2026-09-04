import FabiusFunction.TransseriesBlockClasses
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# A monomial determines its exponents and its coefficient

The uniqueness step that the transseries volume uses to read exponents
off an expansion, and in particular the engine of
`plt:cor:mot-both-generators-needed`: on the power-logarithmic scale, an
asymptotic equivalence

`X^a (log X)^b ~ c · X^{a'} (log X)^{b'}`   with `c > 0`

forces `a = a'`, `b = b'` and `c = 1`.  Nothing can be traded between the
two exponents, and no positive constant can absorb a mismatch — which is
why an expansion on this scale determines its exponent pairs, and why a
scale confined to pure powers or to pure logarithms cannot carry an
expansion whose terms use both directions.

The proof is the dominance trichotomy: a lexicographically smaller
exponent pair sends the ratio to `0`, a larger one sends it to `+∞`, and
only the diagonal case survives, where the limit is `c⁻¹` and the
hypothesis pins it to `1`.

* `tendsto_plMonomial_div_const_mul_one_iff` — the statement as a limit
  of the quotient, which is the form the applications need.
* `isEquivalent_plMonomial_const_mul_iff` — the same as an `IsEquivalent`
  equivalence.
-/

set_option autoImplicit false

open Filter Topology Asymptotics

namespace Fabius

private theorem div_const_mul (x y c : ℝ) : x / (c * y) = c⁻¹ * (x / y) := by
  rw [mul_comm c y, ← div_div, div_eq_mul_inv, mul_comm]

/-- **A monomial determines its exponents and its coefficient.**  If
`X^a (log X)^b` is asymptotic to `c · X^{a'} (log X)^{b'}` with `c > 0`,
then the exponent pairs agree and `c = 1`.  This is the uniqueness that
makes an expansion on a power–logarithmic scale well posed. -/
theorem tendsto_plMonomial_div_const_mul_one_iff {a b a' b' c : ℝ} (hc : 0 < c) :
    Tendsto (fun X => plMonomial a b X / (c * plMonomial a' b' X)) atTop (𝓝 1) ↔
      (a = a' ∧ b = b' ∧ c = 1) := by
  have hc0 : c ≠ 0 := hc.ne'
  have hrw : (fun X => plMonomial a b X / (c * plMonomial a' b' X)) =
      fun X => c⁻¹ * (plMonomial a b X / plMonomial a' b' X) := by
    funext X
    exact div_const_mul _ _ _
  constructor
  · intro h
    rw [hrw] at h
    rcases lt_trichotomy a a' with hlt | rfl | hgt
    · exfalso
      have h0 : Tendsto (fun X => c⁻¹ * (plMonomial a b X / plMonomial a' b' X))
          atTop (𝓝 (c⁻¹ * 0)) :=
        (tendsto_plMonomial_div_atTop_zero (Or.inl hlt)).const_mul _
      rw [mul_zero] at h0
      exact zero_ne_one (tendsto_nhds_unique h0 h)
    · rcases lt_trichotomy b b' with hlt | rfl | hgt
      · exfalso
        have h0 : Tendsto (fun X => c⁻¹ * (plMonomial a b X / plMonomial a b' X))
            atTop (𝓝 (c⁻¹ * 0)) :=
          (tendsto_plMonomial_div_atTop_zero (Or.inr ⟨rfl, hlt⟩)).const_mul _
        rw [mul_zero] at h0
        exact zero_ne_one (tendsto_nhds_unique h0 h)
      · refine ⟨rfl, rfl, ?_⟩
        have h1 : Tendsto (fun X => c⁻¹ * (plMonomial a b X / plMonomial a b X))
            atTop (𝓝 (c⁻¹ * 1)) :=
          (tendsto_plMonomial_div_atTop_one a b).const_mul _
        rw [mul_one] at h1
        have : c⁻¹ = 1 := tendsto_nhds_unique h1 h
        field_simp at this
        linarith [this]
      · exfalso
        have htop : Tendsto (fun X => plMonomial a b X / plMonomial a b' X)
            atTop atTop :=
          tendsto_plMonomial_div_atTop (Or.inr ⟨rfl, hgt⟩)
        have hinf : Tendsto (fun X => c⁻¹ * (plMonomial a b X / plMonomial a b' X))
            atTop atTop :=
          htop.const_mul_atTop (by positivity)
        exact not_tendsto_nhds_of_tendsto_atTop hinf 1 h
    · exfalso
      have htop : Tendsto (fun X => plMonomial a b X / plMonomial a' b' X)
          atTop atTop :=
        tendsto_plMonomial_div_atTop (Or.inl hgt)
      have hinf : Tendsto (fun X => c⁻¹ * (plMonomial a b X / plMonomial a' b' X))
          atTop atTop :=
        htop.const_mul_atTop (by positivity)
      exact not_tendsto_nhds_of_tendsto_atTop hinf 1 h
  · rintro ⟨rfl, rfl, rfl⟩
    simpa using tendsto_plMonomial_div_atTop_one a b

/-- The same uniqueness in `IsEquivalent` form. -/
theorem isEquivalent_plMonomial_const_mul_iff {a b a' b' c : ℝ} (hc : 0 < c) :
    ((fun X => plMonomial a b X) ~[atTop] fun X => c * plMonomial a' b' X) ↔
      (a = a' ∧ b = b' ∧ c = 1) := by
  have hne : ∀ᶠ X in atTop, c * plMonomial a' b' X ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    exact (mul_pos hc (plMonomial_pos hX)).ne'
  rw [Asymptotics.isEquivalent_iff_tendsto_one hne]
  have hfun : ((fun X => plMonomial a b X) / fun X => c * plMonomial a' b' X) =
      fun X => plMonomial a b X / (c * plMonomial a' b' X) := rfl
  rw [hfun]
  exact tendsto_plMonomial_div_const_mul_one_iff hc

end Fabius
