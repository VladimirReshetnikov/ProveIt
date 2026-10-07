/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.RowRestrictedDeckSiteMask
import OAI.Combinatorics.Progressions.Linear.AllocatedFixedKernelReplacement

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

theorem canonicalCoefficientDeckPeriodCap_le_exp {m : ℕ} (O Q : Fin m → Type*)
    [∀ j, Fintype (O j)] [∀ j, Fintype (Q j)] {period : ℕ} {L : ℝ}
    (hperiod : (period : ℝ) ≤ Real.exp L) :
    coefficientDeckPeriodCap O Q period ≤
      Real.exp (∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (O j) * L)) := by
  unfold coefficientDeckPeriodCap
  calc
    _ ≤ ∏ j, ∏ _i : Q j, Real.exp ((Fintype.card (O j) : ℝ) * L) := by
      apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
      intro j _
      apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
      intro i _
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hperiod _
    _ = _ := by
      simp only [← Real.exp_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem periodFunctionLabelCard_le_exp {m : ℕ} (Q : Fin m → Type*)
    [∀ j, Fintype (Q j)] {period : ℕ} [NeZero period] {L : ℝ}
    (hperiod : (period : ℝ) ≤ Real.exp L) :
    (Fintype.card (∀ j, Q j → ZMod period) : ℝ) ≤
      Real.exp (∑ j, (Fintype.card (Q j) : ℝ) * L) := by
  simp only [Fintype.card_pi, ZMod.card, Finset.prod_const, Finset.card_univ,
    Nat.cast_prod, Nat.cast_pow]
  calc
    _ ≤ ∏ j, Real.exp ((Fintype.card (Q j) : ℝ) * L) := by
      apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
      intro j _
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hperiod _
    _ = _ := (Real.exp_sum _ _).symm

theorem canonicalPeriod_primitive_bounds {m M period : ℕ} [NeZero period]
    (A : Type*) [Fintype A] (n : Fin m → ℕ) (O Q : Fin m → Type*)
    [∀ j, Fintype (O j)] [∀ j, Fintype (Q j)] {Pk : ℝ}
    (hM : (M : ℝ) ≤ Real.exp Pk) (hperiod : period ≤ M ^ (m + 1)) :
    let L := ((m + 1 : ℕ) : ℝ) * Pk
    let maskLog := (Fintype.card A : ℝ) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (O j) * L)
    let labelLog := (∑ j, (n j : ℝ) * L) + ∑ j, (Fintype.card (Q j) : ℝ) * L
    (period : ℝ) ≤ Real.exp L ∧
    (layerKernelIndexBound m M : ℝ) ^ Fintype.card A * coefficientDeckPeriodCap O Q period ≤
      Real.exp maskLog ∧
    (Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, Q j → ZMod period)) : ℝ) ≤
      Real.exp labelLog := by
  intro L maskLog labelLog
  have hp : (period : ℝ) ≤ Real.exp L := by
    calc
      _ ≤ ((M ^ (m + 1) : ℕ) : ℝ) := Nat.cast_le.mpr hperiod
      _ = (M : ℝ) ^ (m + 1) := Nat.cast_pow _ _
      _ ≤ (Real.exp Pk) ^ (m + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hM _
      _ = _ := (Real.exp_nat_mul _ _).symm
  have hk : (layerKernelIndexBound m M : ℝ) ^ Fintype.card A ≤
      Real.exp ((Fintype.card A : ℝ) * ((m * 2 ^ (m + 1) : ℕ) * Pk)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (layerKernelIndexBound_le_exp m hM) _
  have hd := canonicalCoefficientDeckPeriodCap_le_exp O Q hp
  have hleft := periodFunctionLabelCard_le_exp (fun j => Fin (n j)) hp
  have hright := periodFunctionLabelCard_le_exp Q hp
  refine ⟨hp, ?_, ?_⟩
  · calc
      _ ≤ Real.exp ((Fintype.card A : ℝ) * ((m * 2 ^ (m + 1) : ℕ) * Pk)) *
          Real.exp (∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (O j) * L)) :=
        mul_le_mul hk hd (coefficientDeckPeriodCap_nonneg O Q period) (Real.exp_nonneg _)
      _ = _ := (Real.exp_add _ _).symm
  · have hh := mul_le_mul hleft hright (Nat.cast_nonneg
        (Fintype.card (∀ j, Q j → ZMod period))) (Real.exp_nonneg _)
    rw [Fintype.card_prod, Nat.cast_mul]
    simpa only [Nat.card_fin, ← Real.exp_add, labelLog,
      ← Nat.card_eq_fintype_card] using hh

end Erdos3.VectorPolynomial

end

end OAI
