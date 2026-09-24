import Surreal.HahnSeries.IdealMultipliers

/-!
# Fraction-pair formulas for multipliers and coefficients

The formulas preceding `odg:def:cor:internal`. Witnesses range over the
original coefficient-restricted ring; the fraction field is represented
by pairs with nonzero denominator.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries

noncomputable section

variable {Γ K O : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field K] [CommRing O]

/-- The printed universal-existential formula Mult on fraction representatives. -/
def MultiplierFormula (i : O →+* K) (a b : coefficientRestrictedSubring (Γ := Γ) i) : Prop :=
  b ≠ 0 ∧ ∀ x : coefficientRestrictedSubring (Γ := Γ) i, x.val ∈ purelyInfiniteIdeal →
    ∃ y : coefficientRestrictedSubring (Γ := Γ) i, y.val ∈ purelyInfiniteIdeal ∧ a * x = b * y

/-- The printed coefficient formula, with its separate zero branch. -/
def CoefficientFormula (i : O →+* K) (a b : coefficientRestrictedSubring (Γ := Γ) i) : Prop :=
  b ≠ 0 ∧ (a = 0 ∨ (a ≠ 0 ∧ MultiplierFormula i a b ∧ MultiplierFormula i b a))

private theorem inclusion_ne_zero (i : O →+* K) {a : coefficientRestrictedSubring (Γ := Γ) i}
    (ha : a ≠ 0) : a.val.val ≠ 0 := by
  intro h
  exact ha (Subtype.ext (Subtype.ext h))

/-- The pair formula says exactly that the represented fraction preserves the ideal. -/
theorem multiplierFormula_iff (i : O →+* K) (a b : coefficientRestrictedSubring (Γ := Γ) i) :
    MultiplierFormula i a b ↔ b ≠ 0 ∧ IsPurelyInfiniteMultiplier (a.val.val / b.val.val) := by
  constructor
  · rintro ⟨hb, hm⟩
    refine ⟨hb, fun x hx => ?_⟩
    let x' := purelyInfiniteRestricted i x hx
    obtain ⟨y, hy, he⟩ := hm x' ((purelyInfiniteSeries_iff x'.val).mp hx)
    have he' := congrArg (coefficientRestrictedHahnInclusion i) he
    change a.val.val * x = b.val.val * y.val.val at he'
    have hdiv : (a.val.val / b.val.val) * x = y.val.val := by
      rw [div_mul_eq_mul_div, div_eq_iff (inclusion_ne_zero i hb)]
      simpa only [mul_comm] using he'
    rw [hdiv]
    exact (purelyInfiniteSeries_iff y.val).mpr hy
  · rintro ⟨hb, hm⟩
    refine ⟨hb, fun x hx => ?_⟩
    have hy := hm x.val.val ((purelyInfiniteSeries_iff x.val).mpr hx)
    let y := purelyInfiniteRestricted i ((a.val.val / b.val.val) * x.val.val) hy
    refine ⟨y, (purelyInfiniteSeries_iff y.val).mp hy, ?_⟩
    apply coefficientRestrictedHahnInclusion_injective i
    change a.val.val * x.val.val = b.val.val * ((a.val.val / b.val.val) * x.val.val)
    field_simp [inclusion_ne_zero i hb]

/-- Mult is exactly membership of the represented fraction in the support ring. -/
theorem multiplierFormula_iff_support (i : O →+* K)
    (a b : coefficientRestrictedSubring (Γ := Γ) i) :
    MultiplierFormula i a b ↔ b ≠ 0 ∧ a.val.val / b.val.val ∈ nonpositiveSupportSubring Γ K := by
  rw [multiplierFormula_iff, purelyInfiniteMultiplier_iff]

/-- Coeff defines the embedded coefficient field, including zero. -/
theorem coefficientFormula_iff (i : O →+* K) (a b : coefficientRestrictedSubring (Γ := Γ) i) :
    CoefficientFormula i a b ↔ b ≠ 0 ∧ ∃ c : K, a.val.val / b.val.val = C c := by
  rw [coefficient_iff_multiplier_and_inverse]
  constructor
  · rintro ⟨hb, rfl | ⟨ha, hab, hba⟩⟩
    · exact ⟨hb, Or.inl (by simp)⟩
    · refine ⟨hb, Or.inr ⟨div_ne_zero (inclusion_ne_zero i ha) (inclusion_ne_zero i hb),
        (multiplierFormula_iff i a b).mp hab |>.2, ?_⟩⟩
      simpa only [inv_div] using ((multiplierFormula_iff i b a).mp hba).2
  · rintro ⟨hb, hz | ⟨hf, hm, hi⟩⟩
    · refine ⟨hb, Or.inl ?_⟩
      have ha := (div_eq_zero_iff).mp hz
      exact Subtype.ext (Subtype.ext (ha.resolve_right (inclusion_ne_zero i hb)))
    · have ha : a ≠ 0 := by intro h; apply hf; simp [h]
      exact ⟨hb, Or.inr ⟨ha, (multiplierFormula_iff i a b).mpr ⟨hb, hm⟩,
        (multiplierFormula_iff i b a).mpr ⟨ha, by simpa only [inv_div] using hi⟩⟩⟩

/-- Cross multiplication is the equivalence relation used by both interpreted formulas. -/
theorem fraction_eq_of_cross_eq (i : O →+* K)
    {a b c d : coefficientRestrictedSubring (Γ := Γ) i} (hb : b ≠ 0) (hd : d ≠ 0)
    (h : a * d = c * b) : a.val.val / b.val.val = c.val.val / d.val.val := by
  apply (div_eq_div_iff (inclusion_ne_zero i hb) (inclusion_ne_zero i hd)).mpr
  exact congrArg (coefficientRestrictedHahnInclusion i) h

/-- Mult does not depend on the chosen nonzero-denominator representative. -/
theorem multiplierFormula_congr (i : O →+* K)
    {a b c d : coefficientRestrictedSubring (Γ := Γ) i} (hb : b ≠ 0) (hd : d ≠ 0)
    (h : a * d = c * b) : MultiplierFormula i a b ↔ MultiplierFormula i c d := by
  rw [multiplierFormula_iff, multiplierFormula_iff, fraction_eq_of_cross_eq i hb hd h]
  exact and_congr (iff_of_true hb hd) Iff.rfl

/-- Coeff likewise descends to the interpreted fraction field. -/
theorem coefficientFormula_congr (i : O →+* K)
    {a b c d : coefficientRestrictedSubring (Γ := Γ) i} (hb : b ≠ 0) (hd : d ≠ 0)
    (h : a * d = c * b) : CoefficientFormula i a b ↔ CoefficientFormula i c d := by
  rw [coefficientFormula_iff, coefficientFormula_iff, fraction_eq_of_cross_eq i hb hd h]
  exact and_congr (iff_of_true hb hd) Iff.rfl

/-- Subtracting a coefficient leaves a purely infinite series exactly at the extracted coefficient. -/
theorem coefficientGraph_iff (f : nonpositiveSupportSubring Γ K) (c : K) :
    PurelyInfiniteSeries (f.val - C c) ↔ c = nonpositiveConstantCoeff f := by
  change PurelyInfiniteSeries (f - nonpositiveConstants c).val ↔ _
  rw [purelyInfiniteSeries_iff]
  change nonpositiveConstantCoeff (f - nonpositiveConstants c) = 0 ↔ _
  rw [map_sub, nonpositiveConstantCoeff_constants, sub_eq_zero, eq_comm]

/-- The parameter-free ring formula obtained by expanding each ideal test. -/
def QuadraticMultiplierFormula {R : Type*} [CommRing R] (a b : R) : Prop :=
  b ≠ 0 ∧ ∀ x : R, (∃ z : R, x ^ 2 = 2 * z ^ 2) →
    ∃ y : R, (∃ z : R, y ^ 2 = 2 * z ^ 2) ∧ a * x = b * y

/-- The coefficient formula uses only ring operations, quantifiers, and ordinary numerals. -/
def QuadraticCoefficientFormula {R : Type*} [CommRing R] (a b : R) : Prop :=
  b ≠ 0 ∧ (a = 0 ∨ (a ≠ 0 ∧ QuadraticMultiplierFormula a b ∧ QuadraticMultiplierFormula b a))

/-- Expanding a proved quadratic ideal definition gives both literal reconstruction formulas. -/
theorem quadratic_reconstruction (i : O →+* K)
    (hkernel : ∀ x : coefficientRestrictedSubring (Γ := Γ) i,
      x.val ∈ purelyInfiniteIdeal ↔ ∃ z : coefficientRestrictedSubring i, x ^ 2 = 2 * z ^ 2)
    (a b : coefficientRestrictedSubring (Γ := Γ) i) :
    (QuadraticMultiplierFormula a b ↔
      b ≠ 0 ∧ a.val.val / b.val.val ∈ nonpositiveSupportSubring Γ K) ∧
    (QuadraticCoefficientFormula a b ↔ b ≠ 0 ∧ ∃ c : K, a.val.val / b.val.val = C c) := by
  have hm : ∀ a b : coefficientRestrictedSubring (Γ := Γ) i,
      MultiplierFormula i a b ↔ QuadraticMultiplierFormula a b := by
    intro a b
    simp only [MultiplierFormula, QuadraticMultiplierFormula, hkernel]
  constructor
  · rw [← hm, multiplierFormula_iff_support]
  · have hc : CoefficientFormula i a b ↔ QuadraticCoefficientFormula a b := by
      simp only [CoefficientFormula, QuadraticCoefficientFormula, hm]
    rw [← hc, coefficientFormula_iff]

/-- The literal formulas reconstruct support and coefficient rings for integer Hahn pullbacks. -/
theorem integerRestricted_quadratic_reconstruction [CharZero K] (r : K) (hr : r ^ 2 = 2)
    (a b : coefficientRestrictedSubring (Γ := Γ) (Int.castRingHom K)) :
    (QuadraticMultiplierFormula a b ↔
      b ≠ 0 ∧ a.val.val / b.val.val ∈ nonpositiveSupportSubring Γ K) ∧
    (QuadraticCoefficientFormula a b ↔ b ≠ 0 ∧ ∃ c : K, a.val.val / b.val.val = C c) :=
  quadratic_reconstruction (Int.castRingHom K) (integerRestricted_purelyInfinite_iff_quadratic r hr) a b

/-- The same ring formulas reconstruct the Gaussian Hahn support and coefficient rings. -/
theorem gaussianRestricted_quadratic_reconstruction [CharZero K]
    (i : GaussianInt →+* K) (hi : Function.Injective i) (r : K) (hr : r ^ 2 = 2)
    (a b : coefficientRestrictedSubring (Γ := Γ) i) :
    (QuadraticMultiplierFormula a b ↔
      b ≠ 0 ∧ a.val.val / b.val.val ∈ nonpositiveSupportSubring Γ K) ∧
    (QuadraticCoefficientFormula a b ↔ b ≠ 0 ∧ ∃ c : K, a.val.val / b.val.val = C c) :=
  quadratic_reconstruction i (gaussianRestricted_purelyInfinite_iff_quadratic i hi r hr) a b

end
end Surreal.HahnSeries
