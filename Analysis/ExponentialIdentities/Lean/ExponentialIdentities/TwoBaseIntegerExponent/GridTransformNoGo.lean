import Mathlib.Tactic

namespace LeanProofs.TwoBaseIntegerExponent

/-!
# Structural-prime grid-transformation obstruction

The dyadic and triadic input/output valuation-direction matrices are
`[[1, 0], [a, c]]` and `[[0, 1], [d, b]]`.  This module proves that no one
nonsingular change of exponent directions can make both matrices monomial
unless the original data already lie in the simultaneous favorable branch of the
structural-residual analysis.
-/

/-- A `2 × 2` matrix, written by entries, has exactly one nonzero entry in
each row and each column. -/
def monomialSupport2x2 (x y z w : ℤ) : Prop :=
  (x ≠ 0 ∧ y = 0 ∧ z = 0 ∧ w ≠ 0) ∨
  (x = 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ w = 0)

/-- Let `C = [[x,y],[z,w]]` be a nonsingular common change of exponent
directions.  Both transformed structural-prime valuation matrices are
monomial exactly when `C` itself is monomial, the two diagonal output
valuations vanish, and the two cross valuations are nonzero. -/
theorem simultaneous_cross_support_iff
    (a b c d x y z w : ℤ) (hdet : x * w - y * z ≠ 0) :
    (monomialSupport2x2 x y (a * x + c * z) (a * y + c * w) ∧
      monomialSupport2x2 z w (d * x + b * z) (d * y + b * w)) ↔
    (a = 0 ∧ b = 0 ∧ c ≠ 0 ∧ d ≠ 0 ∧ monomialSupport2x2 x y z w) := by
  constructor
  · rintro ⟨h₂, h₃⟩
    rcases h₂ with h₂ | h₂ <;> rcases h₃ with h₃ | h₃
    · rcases h₂ with ⟨hx, hy, hout₂x, hout₂y⟩
      rcases h₃ with ⟨hz, hw, -, -⟩
      exfalso
      apply hdet
      simp [hy, hw]
    · rcases h₂ with ⟨hx, hy, hout₂x, hout₂y⟩
      rcases h₃ with ⟨hz, hw, hout₃x, hout₃y⟩
      have ha : a = 0 := by
        simpa [hz] using (mul_eq_zero.mp (by simpa [hz] using hout₂x)).resolve_right hx
      have hc : c ≠ 0 := by
        intro hc
        apply hout₂y
        simp [hy, hc]
      have hb : b = 0 := by
        have : b * w = 0 := by simpa [hy, hz] using hout₃y
        exact (mul_eq_zero.mp this).resolve_right hw
      have hd : d ≠ 0 := by
        intro hd
        apply hout₃x
        simp [hd, hz]
      exact ⟨ha, hb, hc, hd, Or.inl ⟨hx, hy, hz, hw⟩⟩
    · rcases h₂ with ⟨hx, hy, hout₂x, hout₂y⟩
      rcases h₃ with ⟨hz, hw, hout₃x, hout₃y⟩
      have hc : c ≠ 0 := by
        intro hc
        apply hout₂x
        simp [hx, hc]
      have ha : a = 0 := by
        have : a * y = 0 := by simpa [hx, hw] using hout₂y
        exact (mul_eq_zero.mp this).resolve_right hy
      have hb : b = 0 := by
        have : b * z = 0 := by simpa [hx, hw] using hout₃x
        exact (mul_eq_zero.mp this).resolve_right hz
      have hd : d ≠ 0 := by
        intro hd
        apply hout₃y
        simp [hd, hw]
      exact ⟨ha, hb, hc, hd, Or.inr ⟨hx, hy, hz, hw⟩⟩
    · rcases h₂ with ⟨hx, hy, -, -⟩
      rcases h₃ with ⟨hz, hw, -, -⟩
      exfalso
      apply hdet
      simp [hx, hz]
  · rintro ⟨rfl, rfl, hc, hd, hC⟩
    rcases hC with hC | hC
    · rcases hC with ⟨hx, rfl, rfl, hw⟩
      constructor
      · exact Or.inl ⟨hx, rfl, by simp, by simpa using mul_ne_zero hc hw⟩
      · exact Or.inr ⟨rfl, hw, by simpa using mul_ne_zero hd hx, by simp⟩
    · rcases hC with ⟨rfl, hy, hz, rfl⟩
      constructor
      · exact Or.inr ⟨rfl, hy, by simpa using mul_ne_zero hc hz, by simp⟩
      · exact Or.inl ⟨hz, rfl, by simp, by simpa using mul_ne_zero hd hy⟩

end LeanProofs.TwoBaseIntegerExponent
