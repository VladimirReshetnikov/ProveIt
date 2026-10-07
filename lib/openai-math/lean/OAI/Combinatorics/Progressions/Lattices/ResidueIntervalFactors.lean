/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import Mathlib.Data.ZMod.Basic
import OAI.Combinatorics.Progressions.Estimates.NativeBoundedVariablePatchExpansion

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def residueSiteIndicator {m : ℕ} (r : ZMod m) (u : ℤ) : ℝ :=
  if (u : ZMod m) = r then 1 else 0

theorem residueSiteIndicator_range {m : ℕ} (r : ZMod m) (u : ℤ) :
    0 ≤ residueSiteIndicator r u ∧ residueSiteIndicator r u ≤ 1 := by
  unfold residueSiteIndicator
  split_ifs <;> norm_num

theorem prod_residueSiteIndicator {S : Type*} [Fintype S] (m : ℕ)
    (r : S → ZMod m) (u : S → ℤ) :
    (∏ i, residueSiteIndicator (r i) (u i)) = if (fun i => (u i : ZMod m)) = r then 1 else 0 := by
  classical
  by_cases h : (fun i => (u i : ZMod m)) = r
  · simp only [h, ite_true]
    apply Finset.prod_eq_one
    intro i _
    simp only [residueSiteIndicator, congrFun h i, ite_true]
  · rw [ite_eq_right h]
    have hn : ∃ i, (u i : ZMod m) ≠ r i := not_forall.mp (fun hi => h (funext hi))
    obtain ⟨i, hi⟩ := hn
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [residueSiteIndicator, hi])

noncomputable def residueIntervalSiteWeight (B r H : ℝ) {m : ℕ}
    (a : ZMod m) (k : Fin (intervalSiteCount B r)) (u : ℤ) : ℝ :=
  residueSiteIndicator a u * intervalSiteWeight B r k ((u : ℝ) / H)

theorem residueIntervalSiteWeight_range (B H : ℝ) {r : ℝ} (hr : 0 < r) {m : ℕ}
    (a : ZMod m) (k : Fin (intervalSiteCount B r)) (u : ℤ) :
    0 ≤ residueIntervalSiteWeight B r H a k u ∧ residueIntervalSiteWeight B r H a k u ≤ 1 := by
  obtain ⟨ha0, ha1⟩ := residueSiteIndicator_range a u
  obtain ⟨hw0, hw1⟩ := intervalSiteWeight_range B hr k ((u : ℝ) / H)
  exact ⟨mul_nonneg ha0 hw0, (mul_le_mul ha1 hw1 hw0 zero_le_one).trans_eq (one_mul 1)⟩

theorem prod_residueIntervalSiteWeight {S : Type*} [Fintype S] (B r H : ℝ) (m : ℕ)
    (a : S → ZMod m) (k : S → Fin (intervalSiteCount B r)) (u : S → ℤ) :
    (∏ i, residueIntervalSiteWeight B r H (a i) (k i) (u i)) =
      (if (fun i => (u i : ZMod m)) = a then 1 else 0) *
        intervalTensorWeight B r k (fun i => (u i : ℝ) / H) := by
  classical
  simp only [residueIntervalSiteWeight, Finset.prod_mul_distrib, prod_residueSiteIndicator,
    intervalTensorWeight]

end Erdos3

end

end OAI
