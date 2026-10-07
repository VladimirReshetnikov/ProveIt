import OAI.Combinatorics.Progressions.Nilpotent.CurrentBracketInductionStep

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial

variable {σ : Type*}

noncomputable def weightedBasisBracketCoefficient (w : σ → ℕ) (d : ℕ) :
    WeightedBasisIndex w d → WeightedBasisIndex w d → WeightedBasisIndex w d → ℤ := by
  classical
  exact fun a b c => match a, b, c with
    | Sum.inl i, Sum.inr a, Sum.inr c =>
        if a.val - Finsupp.single i 1 = c.val then (a.val i : ℤ) else 0
    | Sum.inr a, Sum.inl i, Sum.inr c =>
        -(if a.val - Finsupp.single i 1 = c.val then (a.val i : ℤ) else 0)
    | _, _, _ => 0

variable [Fintype σ]

theorem weightedBasis_structureConstants (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (a b c : WeightedBasisIndex w d) :
    lieStructureConstants (weightedBasis w d hw) a b c =
      (weightedBasisBracketCoefficient w d a b c : ℚ) := by
  classical
  unfold lieStructureConstants
  cases c with
  | inl c =>
      rw [weightedBasis_repr_inl]
      cases a <;> cases b <;> rfl
  | inr c =>
      rw [weightedBasis_repr_inr]
      change (scalarDirectionalDerivative (weightedBasis w d hw a).val.base
        (weightedBasis w d hw b).val.polynomial -
        scalarDirectionalDerivative (weightedBasis w d hw b).val.base
          (weightedBasis w d hw a).val.polynomial).coeff c.val = _
      cases a with
      | inl i =>
          cases b with
          | inl j => simp [weightedBasisBracketCoefficient]
          | inr a =>
              simp [weightedBasisBracketCoefficient, scalarDirectionalDerivative_apply,
                Pi.single_apply, pderiv_monomial, coeff_monomial]
      | inr a =>
          cases b with
          | inl i =>
              simp [weightedBasisBracketCoefficient, scalarDirectionalDerivative_apply,
                Pi.single_apply, pderiv_monomial, coeff_monomial]
          | inr b => simp [weightedBasisBracketCoefficient]

omit [Fintype σ] in
theorem weightedBasisBracketCoefficient_natAbs_le (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (a b c : WeightedBasisIndex w d) :
    (weightedBasisBracketCoefficient w d a b c).natAbs ≤ d := by
  classical
  have hb : ∀ (i : σ) (a : {a : σ →₀ ℕ | Finsupp.weight w a < d}), a.val i ≤ d := by
    intro i a
    exact (Finsupp.le_weight w (hw i).ne' a.val).trans (Nat.le_of_lt a.property)
  cases a <;> cases b <;> cases c <;>
    simp only [weightedBasisBracketCoefficient, Int.natAbs_neg] <;>
    (try split_ifs) <;>
    simp only [Int.natAbs_zero, Int.natAbs_natCast, Nat.zero_le] <;> exact hb _ _

theorem weightedBasis_structure_height_succ (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (a b c : WeightedBasisIndex w d) :
    RationalHeightLE (lieStructureConstants (weightedBasis w d hw) a b c) (d + 1) := by
  rw [weightedBasis_structureConstants]
  constructor
  · simpa using (weightedBasisBracketCoefficient_natAbs_le w d hw a b c).trans (Nat.le_succ d)
  · simp

theorem weightedBasis_structure_height (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (a b c : WeightedBasisIndex w d) :
    RationalHeightLE (lieStructureConstants (weightedBasis w d hw) a b c) (2 * d + 1) :=
  (weightedBasis_structure_height_succ w d hw a b c).mono (by omega)

end Erdos3.PolynomialTranslationLie

end

end OAI
