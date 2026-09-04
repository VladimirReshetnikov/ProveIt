import FabiusFunction.TransseriesBlockClasses
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# A monomial determines its exponents and its coefficient

The uniqueness step that the transseries volume uses to read exponents
off an expansion, and the engine of `plt:cor:mot-both-generators-needed`:
on the power-logarithmic scale, an asymptotic equality of two scaled
monomials

`c · X^a (log X)^b ~ c' · X^{a'} (log X)^{b'}`   with `c, c' ≠ 0`

forces `a = a'`, `b = b'` and `c = c'`.  Nothing can be traded between
the two exponents, and no constant can absorb a mismatch — which is why
an expansion on this scale determines its exponent pairs, and why a scale
confined to pure powers or to pure logarithms cannot carry an expansion
whose terms use both directions.

The proof is the dominance trichotomy.  A lexicographically smaller
exponent pair sends the quotient to `0`; a larger one sends it to `+∞`,
and then multiplying by the inverse constant would give a divergent
function a finite limit; only the diagonal survives, where the limit is
`c/c'` and the hypothesis pins it to `1`.  No case split on the sign of
the constants is needed.

* `tendsto_const_mul_plMonomial_div_one_iff` — the statement as a limit of
  the quotient, which is the form the applications need.
* `isEquivalent_const_mul_plMonomial_iff` — the same as an `IsEquivalent`
  equivalence.
* `tendsto_plMonomial_div_const_mul_one_iff`,
  `isEquivalent_plMonomial_const_mul_iff` — the special case of a bare
  monomial on the left, where the conclusion reads `c = 1`.
-/

set_option autoImplicit false

open Filter Topology Asymptotics

namespace Fabius

/-- **Uniqueness with coefficients on both sides.**  Two scaled monomials
are asymptotically equal only if their exponent pairs and their
coefficients agree. -/
theorem tendsto_const_mul_plMonomial_div_one_iff {a b a' b' c c' : ℝ}
    (hc : c ≠ 0) (hc' : c' ≠ 0) :
    Tendsto (fun X => (c * plMonomial a b X) / (c' * plMonomial a' b' X))
        atTop (𝓝 1) ↔ (a = a' ∧ b = b' ∧ c = c') := by
  have hrw : (fun X => (c * plMonomial a b X) / (c' * plMonomial a' b' X)) =
      fun X => (c / c') * (plMonomial a b X / plMonomial a' b' X) := by
    funext X
    exact mul_div_mul_comm _ _ _ _
  have hk : c / c' ≠ 0 := div_ne_zero hc hc'
  constructor
  · intro h
    rw [hrw] at h
    have hzero : ∀ {p q p' q' : ℝ}, (p < p' ∨ (p = p' ∧ q < q')) →
        Tendsto (fun X => (c / c') * (plMonomial p q X / plMonomial p' q' X))
          atTop (𝓝 0) := by
      intro p q p' q' hlex
      have := (tendsto_plMonomial_div_atTop_zero hlex).const_mul (c / c')
      rwa [mul_zero] at this
    have htop : ∀ {p q p' q' : ℝ}, (p' < p ∨ (p' = p ∧ q' < q)) →
        ¬ Tendsto (fun X => (c / c') * (plMonomial p q X / plMonomial p' q' X))
          atTop (𝓝 1) := by
      intro p q p' q' hlex hcon
      have hdiv := tendsto_plMonomial_div_atTop hlex
      have hback : Tendsto (fun X => plMonomial p q X / plMonomial p' q' X)
          atTop (𝓝 ((c / c')⁻¹ * 1)) := by
        refine (hcon.const_mul (c / c')⁻¹).congr fun X => ?_
        rw [← mul_assoc, inv_mul_cancel₀ hk, one_mul]
      exact not_tendsto_nhds_of_tendsto_atTop hdiv _ hback
    rcases lt_trichotomy a a' with hlt | rfl | hgt
    · exact absurd (tendsto_nhds_unique (hzero (Or.inl hlt)) h) zero_ne_one
    · rcases lt_trichotomy b b' with hlt | rfl | hgt
      · exact absurd (tendsto_nhds_unique (hzero (Or.inr ⟨rfl, hlt⟩)) h)
          zero_ne_one
      · refine ⟨rfl, rfl, ?_⟩
        have h1 : Tendsto
            (fun X => (c / c') * (plMonomial a b X / plMonomial a b X)) atTop
            (𝓝 (c / c' * 1)) := (tendsto_plMonomial_div_atTop_one a b).const_mul _
        rw [mul_one] at h1
        have hkey : c / c' = 1 := tendsto_nhds_unique h1 h
        field_simp at hkey
        linarith
      · exact absurd h (htop (Or.inr ⟨rfl, hgt⟩))
    · exact absurd h (htop (Or.inl hgt))
  · rintro ⟨rfl, rfl, rfl⟩
    rw [hrw, div_self hc]
    simpa using tendsto_plMonomial_div_atTop_one a b

/-- The `IsEquivalent` form of two-sided uniqueness. -/
theorem isEquivalent_const_mul_plMonomial_iff {a b a' b' c c' : ℝ}
    (hc : c ≠ 0) (hc' : c' ≠ 0) :
    ((fun X => c * plMonomial a b X) ~[atTop] fun X => c' * plMonomial a' b' X) ↔
      (a = a' ∧ b = b' ∧ c = c') := by
  have hne : ∀ᶠ X in atTop, c' * plMonomial a' b' X ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    exact mul_ne_zero hc' (plMonomial_pos hX).ne'
  rw [Asymptotics.isEquivalent_iff_tendsto_one hne]
  have hfun : ((fun X => c * plMonomial a b X) /
      fun X => c' * plMonomial a' b' X) =
      fun X => (c * plMonomial a b X) / (c' * plMonomial a' b' X) := rfl
  rw [hfun]
  exact tendsto_const_mul_plMonomial_div_one_iff hc hc'

/-- **A bare monomial on the left.**  If `X^a (log X)^b` is asymptotic to
`c · X^{a'} (log X)^{b'}` with `c > 0`, then the exponent pairs agree and
`c = 1`. -/
theorem tendsto_plMonomial_div_const_mul_one_iff {a b a' b' c : ℝ} (hc : 0 < c) :
    Tendsto (fun X => plMonomial a b X / (c * plMonomial a' b' X)) atTop (𝓝 1) ↔
      (a = a' ∧ b = b' ∧ c = 1) := by
  have h := tendsto_const_mul_plMonomial_div_one_iff (a := a) (b := b)
    (a' := a') (b' := b') (c := 1) (c' := c) one_ne_zero hc.ne'
  simp only [one_mul] at h
  rw [h]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, h3.symm⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, h3.symm⟩

/-- The same, in `IsEquivalent` form. -/
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
