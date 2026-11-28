import Mathlib.Data.List.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Sound branch certificates for finite progression bounds

The checker branches on admitting or omitting the next point. If a point is
admitted, the points completing a forbidden triple with it and an earlier
admitted point are removed. It can stop whenever the total weight of admitted
and remaining points is below the target.
-/

namespace GRHArticle.ProgressionFree

private def listWeight {α : Type*} (weight : α → ℕ) (L : List α) : ℕ :=
  (L.map weight).sum

private theorem listWeight_filter_le {α : Type*} (weight : α → ℕ)
    (accept : α → Bool) (L : List α) :
    listWeight weight (L.filter accept) ≤ listWeight weight L := by
  induction L with
  | nil => exact le_rfl
  | cons a L ih =>
    cases ha : accept a <;> simp [listWeight,ha] at ih ⊢ <;> omega

/-- Points remaining after taking `y` in addition to the already selected list. -/
def branchRemaining {α : Type*} (forbidden : α → α → α → Bool)
    (picked : List α) (y : α) (remaining : List α) : List α :=
  remaining.filter fun z ↦ picked.all fun x ↦ !(forbidden x y z)

/-- A true result certifies a weight bound on every accepted sublist. Any
failure due to insufficient fuel returns false. -/
def finiteGPBranchCheck {α : Type*} (weight : α → ℕ) (forbidden : α → α → α → Bool)
    (target : ℕ) : (fuel spent : ℕ) → (picked remaining : List α) → Bool
  | 0, _, _, _ => false
  | n+1, spent, picked, remaining =>
    if spent + listWeight weight remaining ≤ target then true
    else
      match remaining with
      | [] => false
      | y::tail =>
        finiteGPBranchCheck weight forbidden target n spent picked tail &&
        finiteGPBranchCheck weight forbidden target n (spent + weight y) (y::picked)
          (branchRemaining forbidden picked y tail)

private theorem filter_branchRemaining_of_free {α : Type*} (forbidden : α → α → α → Bool)
    (accept : α → Bool)
    (hFree : ∀ x y z, accept x = true → accept y = true → accept z = true → forbidden x y z = false)
    {picked : List α} (hp : ∀ x ∈ picked, accept x = true) {y : α} (hy : accept y = true)
    (tail : List α) :
    (branchRemaining forbidden picked y tail).filter accept = tail.filter accept := by
  unfold branchRemaining
  rw [List.filter_filter]
  apply List.filter_congr
  intro z _
  cases hz : accept z
  · simp
  · have h : (picked.all fun x ↦ !(forbidden x y z)) = true := by
      apply List.all_eq_true.mpr
      intro x hx
      rw [hFree x y z (hp x hx) hy hz]
      rfl
    simp [h]

/-- Soundness at an intermediate state with the already selected points in
an arbitrary admissible family. -/
theorem finiteGPBranchCheck_sound_at {α : Type*} (weight : α → ℕ)
    (forbidden : α → α → α → Bool) (target : ℕ) (accept : α → Bool)
    (hFree : ∀ x y z, accept x = true → accept y = true → accept z = true → forbidden x y z = false)
    (fuel spent : ℕ) (picked remaining : List α)
    (hp : ∀ x ∈ picked, accept x = true)
    (h : finiteGPBranchCheck weight forbidden target fuel spent picked remaining = true) :
    spent + listWeight weight (remaining.filter accept) ≤ target := by
  induction fuel generalizing spent picked remaining with
  | zero => simp [finiteGPBranchCheck] at h
  | succ fuel ih =>
    cases remaining with
    | nil =>
      rw [finiteGPBranchCheck] at h
      split at h
      · exact (Nat.add_le_add_left (listWeight_filter_le weight accept []) spent).trans ‹_›
      · exact Bool.noConfusion h
    | cons y tail =>
      rw [finiteGPBranchCheck] at h
      split at h
      · exact (Nat.add_le_add_left (listWeight_filter_le weight accept (y::tail)) spent).trans ‹_›
      · obtain ⟨hNo,hYes⟩ := Bool.and_eq_true_iff.mp h
        cases hy : accept y
        · have hN := ih spent picked tail hp hNo
          simpa [List.filter_cons,hy] using hN
        · have hP : ∀ x ∈ y::picked, accept x = true := by
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact hy
            · exact hp x hx
          have hY := ih (spent + weight y) (y::picked) _ hP hYes
          rw [filter_branchRemaining_of_free forbidden accept hFree hp hy] at hY
          simpa only [List.filter_cons,hy,↓reduceIte,listWeight,List.map_cons,List.sum_cons,
            Nat.add_assoc] using hY

/-- The exact integer weight of any accepted set in the original list is
bounded by the target certified at the empty initial state. -/
theorem finiteGPBranchCheck_sound {α : Type*} (weight : α → ℕ)
    (forbidden : α → α → α → Bool) (target : ℕ) (accept : α → Bool)
    (hFree : ∀ x y z, accept x = true → accept y = true → accept z = true → forbidden x y z = false)
    (fuel : ℕ) (L : List α)
    (hc : finiteGPBranchCheck weight forbidden target fuel 0 [] L = true) :
    ((L.filter accept).map weight).sum ≤ target := by
  simpa only [Nat.zero_add,listWeight] using
    finiteGPBranchCheck_sound_at weight forbidden target accept hFree fuel 0 [] L
      (by simp) hc

end GRHArticle.ProgressionFree
