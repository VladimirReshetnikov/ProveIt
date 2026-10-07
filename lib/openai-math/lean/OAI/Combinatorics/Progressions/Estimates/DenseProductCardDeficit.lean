/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem denseProductDeficit_le_sum {I : Type*} (S : Finset I) (f : I → ℝ)
    (hf : ∀ i ∈ S, f i ∈ Set.Icc (0 : ℝ) 1) :
    1 - ∏ i ∈ S, f i ≤ ∑ i ∈ S, (1 - f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hfi := hf i (Finset.mem_insert_self i S)
    have hfS : ∀ j ∈ S, f j ∈ Set.Icc (0 : ℝ) 1 :=
      fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hprod : ∏ j ∈ S, f j ≤ 1 :=
      Finset.prod_le_one₀ (fun j hj => (hfS j hj).1) (fun j hj => (hfS j hj).2)
    have hih := ih hfS
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    nlinarith [mul_nonneg (sub_nonneg.mpr hfi.2) (sub_nonneg.mpr hprod)]

theorem denseProductCardDeficit_le_sum {I : Type*} [Fintype I]
    (a b : I → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, b i ≤ a i) :
    1 - (∏ i, (b i : ℝ)) / (∏ i, (a i : ℝ)) ≤
      ∑ i, ((a i - b i : ℕ) : ℝ) / (a i : ℝ) := by
  have hpos (i : I) : (0 : ℝ) < a i := by exact_mod_cast ha i
  have hle (i : I) : (b i : ℝ) ≤ a i := by exact_mod_cast hb i
  have hfrac (i : I) : (b i : ℝ) / a i ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (Nat.cast_nonneg _) (hpos i).le, (div_le_one (hpos i)).mpr (hle i)⟩
  have h := denseProductDeficit_le_sum Finset.univ (fun i => (b i : ℝ) / a i)
    (fun i _ => hfrac i)
  rw [Finset.prod_div_distrib] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.cast_sub (hb i), sub_div, div_self (ne_of_gt (hpos i))]

theorem denseProductCardDeficit_le_card_mul {I : Type*} [Fintype I]
    (a b : I → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, b i ≤ a i)
    (η : ℝ) (hdeficit : ∀ i, ((a i - b i : ℕ) : ℝ) / (a i : ℝ) ≤ η) :
    1 - (∏ i, (b i : ℝ)) / (∏ i, (a i : ℝ)) ≤ (Fintype.card I : ℝ) * η := by
  calc
    _ ≤ ∑ i, ((a i - b i : ℕ) : ℝ) / (a i : ℝ) :=
      denseProductCardDeficit_le_sum a b ha hb
    _ ≤ ∑ _i : I, η := Finset.sum_le_sum (fun i _ => hdeficit i)
    _ = _ := by simp

theorem denseProductNatCardDeficit_le_card_mul {I : Type*} [Fintype I]
    (a b : I → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, b i ≤ a i)
    (η : ℝ) (hdeficit : ∀ i, ((a i - b i : ℕ) : ℝ) / (a i : ℝ) ≤ η) :
    1 - ((∏ i, b i : ℕ) : ℝ) / ((∏ i, a i : ℕ) : ℝ) ≤
      (Fintype.card I : ℝ) * η := by
  simpa only [Nat.cast_prod] using denseProductCardDeficit_le_card_mul a b ha hb η hdeficit

end Erdos3

end

end OAI
