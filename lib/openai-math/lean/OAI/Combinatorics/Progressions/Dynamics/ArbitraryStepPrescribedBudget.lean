import Mathlib.Analysis.SpecialFunctions.Exp
import OAI.Combinatorics.Progressions.Lattices.StrideSelectedResidueBadProduct

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem arbitraryStep_prescribed_product_dvd (Pr : Finset ℕ)
    (hprime : ∀ p ∈ Pr, p.Prime) (step : ℕ) :
    (∏ p : Pr, p.val ^ padicValNat p.val step) ∣ step := by
  rw [Finset.prod_coe_sort Pr (fun p : ℕ => p ^ padicValNat p step)]
  have hprod : (∏ p ∈ Pr, p ^ padicValNat p step) =
      ∏ p ∈ Pr, p ^ step.factorization p := by
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.factorization_def step (hprime p hp)]
  rw [hprod]
  exact selected_factorization_product_dvd Pr step

theorem arbitraryStep_prescribed_product_le (Pr : Finset ℕ)
    (hprime : ∀ p ∈ Pr, p.Prime) {step : ℕ} (hstep : 0 < step) :
    (∏ p : Pr, p.val ^ padicValNat p.val step) ≤ step :=
  Nat.le_of_dvd hstep (arbitraryStep_prescribed_product_dvd Pr hprime step)

theorem arbitraryStep_prescribed_product_cast_le (Pr : Finset ℕ)
    (hprime : ∀ p ∈ Pr, p.Prime) {step : ℕ} (hstep : 0 < step) :
    ((∏ p : Pr, p.val ^ padicValNat p.val step : ℕ) : ℝ) ≤ step := by
  exact_mod_cast arbitraryStep_prescribed_product_le Pr hprime hstep

theorem arbitraryStep_prescribed_product_exp_le (Pr : Finset ℕ)
    (hprime : ∀ p ∈ Pr, p.Prime) {step : ℕ} (hstep : 0 < step)
    {cost : ℝ} (hcost : (step : ℝ) ≤ 2 * Real.exp cost) :
    ((∏ p : Pr, p.val ^ padicValNat p.val step : ℕ) : ℝ) ≤
      Real.exp (cost + 1) := by
  calc
    _ ≤ (step : ℝ) := arbitraryStep_prescribed_product_cast_le Pr hprime hstep
    _ ≤ 2 * Real.exp cost := hcost
    _ ≤ Real.exp 1 * Real.exp cost :=
      mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (1 : ℝ)] : (2 : ℝ) ≤ Real.exp 1)
        (Real.exp_pos cost).le
    _ = Real.exp (cost + 1) := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
