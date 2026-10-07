/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Geometry.CoefficientAmbientCoordinates

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem coefficientSlot_card_le {K : Type*} [Fintype K] (m : ℕ) :
    Fintype.card (CoefficientSlot K m) ≤ m * (m + 1) * (Fintype.card K + 1) ^ m := by
  simp only [CoefficientSlot, Fintype.card_sigma]
  calc
    _ ≤ ∑ _j : Fin m, (m + 1) * (Fintype.card K + 1) ^ m := by
      apply Finset.sum_le_sum
      intro j _
      apply (boundedCoefficientExponent_card_le (j.val + 1)).trans
      apply Nat.mul_le_mul (by omega)
      exact Nat.pow_le_pow_right (by omega) (Nat.succ_le_of_lt j.isLt)
    _ = _ := by simp; ring

theorem exists_coefficient_tensor_mass_budget (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {K : Type*} [Fintype K] {P B : ℝ},
      0 ≤ P → (Fintype.card K : ℝ) ≤ P → 0 ≤ B → B ≤ Real.exp P →
      B ^ Fintype.card (CoefficientSlot K m) ≤ Real.exp ((P + A) ^ A) := by
  open Polynomial in
    obtain ⟨A, hA, hb⟩ := exists_natPolynomial_eval_budget (C (m * (m + 1)) * (X + 1) ^ m * X)
  refine ⟨A, hA, ?_⟩
  intro K _ P B hP hK hB hBP
  have hc : (Fintype.card (CoefficientSlot K m) : ℝ) ≤
      (m : ℝ) * ((m : ℝ) + 1) * (P + 1) ^ m := by
    have h : (Fintype.card (CoefficientSlot K m) : ℝ) ≤
        (m : ℝ) * ((m : ℝ) + 1) * ((Fintype.card K : ℝ) + 1) ^ m := by
      exact_mod_cast coefficientSlot_card_le (K := K) m
    apply h.trans
    gcongr
  have he : (m : ℝ) * ((m : ℝ) + 1) * (P + 1) ^ m * P ≤ (P + A) ^ A := by
    simpa [Polynomial.eval₂_pow] using hb P hP
  calc
    _ ≤ (Real.exp P) ^ Fintype.card (CoefficientSlot K m) := pow_le_pow_left₀ hB hBP _
    _ = Real.exp ((Fintype.card (CoefficientSlot K m) : ℝ) * P) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp ((P + A) ^ A) := Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_right hc hP).trans he)

theorem finiteTensorCoefficientMass_le {D : Type*} [Fintype D] [DecidableEq D]
    {F : D → Type*} [∀ d, Fintype (F d)] (c : ∀ d, F d → ℂ) {B : ℝ}
    (hc : ∀ d, (∑ a, ‖c d a‖) ≤ B) :
    (∑ a : ∀ d, F d, ‖∏ d, c d (a d)‖) ≤ B ^ Fintype.card D := by
  rw [finiteTensorCoefficientMass]
  exact (Finset.prod_le_prod₀ (fun d _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    (fun d _ => hc d)).trans_eq (by simp)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem coefficientAmbientIndex_card_le {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {d : ℕ}
    (hd : ∀ j, Fintype.card (J j) ≤ d) :
    Fintype.card (CoefficientAmbientIndex K J) ≤
      m * (m + 1) * (Fintype.card K + 1)^m * d := by
  calc
    _ = ∑ s : CoefficientSlot K m, Fintype.card (J s.1) := Fintype.card_sigma
    _ ≤ ∑ _s : CoefficientSlot K m, d := Finset.sum_le_sum (fun s _ => hd s.1)
    _ = Fintype.card (CoefficientSlot K m) * d := by simp
    _ ≤ _ := Nat.mul_le_mul_right d (coefficientSlot_card_le (K := K) m)

theorem coefficientAmbientIndex_card_le_real {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {P : ℝ} (hP : 0 ≤ P)
    (hK : (Fintype.card K : ℝ) ≤ P) (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P) :
    (Fintype.card (CoefficientAmbientIndex K J) : ℝ) ≤
      (m : ℝ) * (m + 1) * (P + 1)^m * P := by
  have hs : (Fintype.card (CoefficientSlot K m) : ℝ) ≤ (m : ℝ) * (m + 1) * (P + 1)^m := by
    have h := Nat.cast_le (α := ℝ).mpr (coefficientSlot_card_le (K := K) m)
    push_cast at h
    exact h.trans (by gcongr)
  calc
    _ = ∑ s : CoefficientSlot K m, (Fintype.card (J s.1) : ℝ) := by
      rw [Fintype.card_sigma, Nat.cast_sum]
    _ ≤ ∑ _s : CoefficientSlot K m, P := Finset.sum_le_sum (fun s _ => hJ s.1)
    _ = (Fintype.card (CoefficientSlot K m) : ℝ) * P := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hs hP

noncomputable def coefficientAmbientInputPolynomial (m : ℕ) : Polynomial ℕ :=
  Polynomial.C (m * (m + 1)) * (Polynomial.X + 1)^m * (Polynomial.X + 1) + Polynomial.X + 1

theorem coefficient_ambient_input_exp_bounds {m : ℕ} {K : Type*} [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {P A L Q : ℝ}
    (hP : 0 ≤ P) (hK : (Fintype.card K : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hA : 0 ≤ A) (hAP : A ≤ Real.exp P) (hL : 0 ≤ L) (hLP : L ≤ Real.exp P)
    (hbudget : (m : ℝ) * (m + 1) * (P + 1)^m * (P + 1) + P + 1 ≤ Q) :
    P ≤ Q ∧ (Fintype.card (CoefficientAmbientIndex K J) : ℝ) ≤ Q ∧
      A^Fintype.card (CoefficientSlot K m) ≤ Real.exp Q ∧
      (Fintype.card (CoefficientSlot K m) : ℝ) * L * A^Fintype.card (CoefficientSlot K m) ≤
        Real.exp Q := by
  let T := (m : ℝ) * (m + 1) * (P + 1)^m
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hpoly' : T * (P + 1) + P + 1 ≤ Q := hbudget
  have hN : (Fintype.card (CoefficientSlot K m) : ℝ) ≤ T := by
    have h := Nat.cast_le (α := ℝ).mpr (coefficientSlot_card_le (K := K) m)
    push_cast at h
    exact h.trans (by dsimp [T]; gcongr)
  have hNP : (Fintype.card (CoefficientSlot K m) : ℝ) * P ≤ T * P :=
    mul_le_mul_of_nonneg_right hN hP
  have hcap : A^Fintype.card (CoefficientSlot K m) ≤
      Real.exp ((Fintype.card (CoefficientSlot K m) : ℝ) * P) := by
    simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ hA hAP (Fintype.card (CoefficientSlot K m))
  have hNexp : (Fintype.card (CoefficientSlot K m) : ℝ) ≤ Real.exp T :=
    hN.trans (by linarith [Real.add_one_le_exp T])
  refine ⟨(by nlinarith), ?_, ?_, ?_⟩
  · exact (coefficientAmbientIndex_card_le_real hP hK hJ).trans (by dsimp [T] at hpoly'; nlinarith)
  · exact hcap.trans (Real.exp_le_exp.mpr (by nlinarith))
  · calc
      _ ≤ Real.exp T * Real.exp P * Real.exp ((Fintype.card (CoefficientSlot K m) : ℝ) * P) := by gcongr
      _ = Real.exp (T + P + (Fintype.card (CoefficientSlot K m) : ℝ) * P) := by
        rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

theorem exists_coefficient_ambient_input_budget (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {K : Type*} [Fintype K] {J : Fin m → Type*} [∀ j, Fintype (J j)]
      {P A L : ℝ}, 0 ≤ P → (Fintype.card K : ℝ) ≤ P →
      (∀ j, (Fintype.card (J j) : ℝ) ≤ P) →
      0 ≤ A → A ≤ Real.exp P → 0 ≤ L → L ≤ Real.exp P →
      P ≤ (P + a)^a ∧
      (Fintype.card (CoefficientAmbientIndex K J) : ℝ) ≤ (P + a)^a ∧
      A^Fintype.card (CoefficientSlot K m) ≤ Real.exp ((P + a)^a) ∧
      (Fintype.card (CoefficientSlot K m) : ℝ) * L * A^Fintype.card (CoefficientSlot K m) ≤
        Real.exp ((P + a)^a) := by
  obtain ⟨a, ha, hpoly⟩ := exists_natPolynomial_eval_budget (coefficientAmbientInputPolynomial m)
  refine ⟨a, ha, ?_⟩
  intro K _ J _ P A L hP hK hJ hA hAP hL hLP
  apply coefficient_ambient_input_exp_bounds hP hK hJ hA hAP hL hLP
  simpa [coefficientAmbientInputPolynomial, Polynomial.eval₂_pow] using hpoly P hP

end Erdos3.VectorPolynomial

end

end OAI
