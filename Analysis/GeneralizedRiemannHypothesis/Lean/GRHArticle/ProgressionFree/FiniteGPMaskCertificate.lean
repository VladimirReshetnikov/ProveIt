import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Bitwise

/-!
# A finite progression checker using a candidate mask

The mask contains every allowed member of a candidate family, including
previously selected points. A certified upper bound on the whole candidate
mask can prune the branch. The specified completions may omit forbidden
points, because the checker only relies on the removals it actually makes.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped BigOperators

/-- Every member of a finite set is represented in the available mask. -/
def gpMaskContains (A : Finset ℕ) (mask : ℕ) : Prop :=
  ∀ a ∈ A, mask.testBit a = true

/-- Clear the specified candidate bit. -/
def clearGPBit (mask i : ℕ) : ℕ := mask ^^^ (mask &&& (1 <<< i))

theorem testBit_clearGPBit (mask i j : ℕ) :
    (clearGPBit mask i).testBit j = (mask.testBit j && decide (i ≠ j)) := by
  rw [clearGPBit,Nat.shiftLeft_eq,one_mul,Nat.testBit_xor,Nat.testBit_and,Nat.testBit_two_pow]
  by_cases h : i = j <;> cases hb : mask.testBit j <;> simp [h]

private theorem gpMaskContains_clear {A : Finset ℕ} {mask i : ℕ}
    (h : gpMaskContains A mask) (hi : i ∉ A) : gpMaskContains A (clearGPBit mask i) := by
  intro a ha
  have he : i ≠ a := fun he ↦ hi (he ▸ ha)
  simp [testBit_clearGPBit,h a ha,he]

private def clearGPCompletions (completion : ℕ → ℕ → Option ℕ) (y : ℕ) :
    List ℕ → ℕ → ℕ
  | [], mask => mask
  | x::xs, mask =>
    let M := match completion x y with
      | none => mask
      | some z => clearGPBit mask z
    clearGPCompletions completion y xs M

private theorem gpMaskContains_clearGPCompletions {A : Finset ℕ}
    (completion : ℕ → ℕ → Option ℕ)
    (hCompletion : ∀ x ∈ A, ∀ y ∈ A, ∀ z, completion x y = some z → z ∉ A)
    {y : ℕ} (hy : y ∈ A) {picked : List ℕ} (hp : ∀ x ∈ picked, x ∈ A)
    {mask : ℕ} (h : gpMaskContains A mask) :
    gpMaskContains A (clearGPCompletions completion y picked mask) := by
  induction picked generalizing mask with
  | nil => exact h
  | cons x xs ih =>
    rw [clearGPCompletions]
    apply ih (fun a ha ↦ hp a (List.mem_cons_of_mem _ ha))
    split
    · exact h
    · rename_i z hz
      exact gpMaskContains_clear h (hCompletion x (hp x List.mem_cons_self) y hy z hz)

/-- Include or exclude the next entry. The inclusion branch clears the
specified completions with every previously chosen entry. -/
def finiteGPMaskCheck (capacity : ℕ → ℕ) (completion : ℕ → ℕ → Option ℕ) (target : ℕ) :
    (candidates picked : List ℕ) → (mask : ℕ) → Bool
  | [], _, mask => decide (capacity mask ≤ target)
  | y::ys, picked, mask =>
    if mask.testBit y then
      if capacity mask ≤ target then true else
        finiteGPMaskCheck capacity completion target ys picked (clearGPBit mask y) &&
        finiteGPMaskCheck capacity completion target ys (y::picked)
          (clearGPCompletions completion y picked mask)
    else finiteGPMaskCheck capacity completion target ys picked mask

/-- Soundness of the full-mask pruning rule. For soundness any available
upper bound is allowed, including one assembled from weighted local tables. -/
theorem finiteGPMaskCheck_sound_at (capacity : ℕ → ℕ) (completion : ℕ → ℕ → Option ℕ)
    (target : ℕ) (w : ℕ → ℕ) (A : Finset ℕ)
    (hCap : ∀ mask, gpMaskContains A mask → (∑ a ∈ A, w a) ≤ capacity mask)
    (hCompletion : ∀ x ∈ A, ∀ y ∈ A, ∀ z, completion x y = some z → z ∉ A)
    (candidates picked : List ℕ) (mask : ℕ) (hp : ∀ x ∈ picked, x ∈ A)
    (hMask : gpMaskContains A mask)
    (hc : finiteGPMaskCheck capacity completion target candidates picked mask = true) :
    (∑ a ∈ A, w a) ≤ target := by
  induction candidates generalizing picked mask with
  | nil =>
    exact (hCap mask hMask).trans (of_decide_eq_true hc)
  | cons y ys ih =>
    rw [finiteGPMaskCheck] at hc
    split at hc
    · split at hc
      · exact (hCap mask hMask).trans ‹_›
      · obtain ⟨hNo,hYes⟩ := Bool.and_eq_true_iff.mp hc
        by_cases hy : y ∈ A
        · have hPick : ∀ x ∈ y::picked, x ∈ A := by
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact hy
            · exact hp x hx
          exact ih _ _ hPick (gpMaskContains_clearGPCompletions completion hCompletion hy hp hMask) hYes
        · exact ih _ _ hp (gpMaskContains_clear hMask hy) hNo
    · exact ih _ _ hp hMask hc

/-- Initial-state soundness of the mask checker. -/
theorem finiteGPMaskCheck_sound (capacity : ℕ → ℕ) (completion : ℕ → ℕ → Option ℕ)
    (target : ℕ) (w : ℕ → ℕ) (A : Finset ℕ)
    (hCap : ∀ mask, gpMaskContains A mask → (∑ a ∈ A, w a) ≤ capacity mask)
    (hCompletion : ∀ x ∈ A, ∀ y ∈ A, ∀ z, completion x y = some z → z ∉ A)
    (candidates : List ℕ) (mask : ℕ) (hMask : gpMaskContains A mask)
    (hc : finiteGPMaskCheck capacity completion target candidates [] mask = true) :
    (∑ a ∈ A, w a) ≤ target :=
  finiteGPMaskCheck_sound_at capacity completion target w A hCap hCompletion
    candidates [] mask (by simp) hMask hc

private def clearCachedGPBit (update : ℕ → ℕ → ℕ → ℕ) (s : ℕ × ℕ) (i : ℕ) : ℕ × ℕ :=
  if s.1.testBit i then (clearGPBit s.1 i,update s.1 s.2 i) else s

private theorem clearCachedGPBit_correct (capacity : ℕ → ℕ) (update : ℕ → ℕ → ℕ → ℕ)
    (h : ∀ m i, update m (capacity m) i = capacity (clearGPBit m i)) (m i : ℕ) :
    clearCachedGPBit update (m,capacity m) i = (clearGPBit m i,capacity (clearGPBit m i)) := by
  by_cases hi : m.testBit i = true
  · simp [clearCachedGPBit,hi,h]
  · have hm : clearGPBit m i = m := by
      apply Nat.eq_of_testBit_eq
      intro j
      by_cases he : i = j
      · simp [testBit_clearGPBit,←he,Bool.eq_false_of_not_eq_true hi]
      · simp [testBit_clearGPBit,he]
    simp [clearCachedGPBit,hi,hm]

private def clearCachedGPCompletions (update : ℕ → ℕ → ℕ → ℕ)
    (completion : ℕ → ℕ → Option ℕ) (y : ℕ) : List ℕ → (ℕ × ℕ) → ℕ × ℕ
  | [], s => s
  | x::xs, s =>
    let S := match completion x y with
      | none => s
      | some z => clearCachedGPBit update s z
    clearCachedGPCompletions update completion y xs S

private theorem clearCachedGPCompletions_correct (capacity : ℕ → ℕ) (update : ℕ → ℕ → ℕ → ℕ)
    (h : ∀ m i, update m (capacity m) i = capacity (clearGPBit m i)) (completion : ℕ → ℕ → Option ℕ)
    (y : ℕ) (picked : List ℕ) (mask : ℕ) :
    clearCachedGPCompletions update completion y picked (mask,capacity mask) =
      let m := clearGPCompletions completion y picked mask
      (m,capacity m) := by
  induction picked generalizing mask with
  | nil => rfl
  | cons x xs ih =>
    rw [clearCachedGPCompletions,clearGPCompletions]
    cases hc : completion x y with
    | none => exact ih mask
    | some z =>
      dsimp only
      rw [clearCachedGPBit_correct capacity update h]
      exact ih (clearGPBit mask z)

/-- The same search with an incrementally updated upper bound. The second
component stores the capacity corresponding to the first component's mask. -/
def finiteGPCachedMaskCheck (update : ℕ → ℕ → ℕ → ℕ) (completion : ℕ → ℕ → Option ℕ) (target : ℕ) :
    (candidates picked : List ℕ) → (maskAndCapacity : ℕ × ℕ) → Bool
  | [], _, s => decide (s.2 ≤ target)
  | y::ys, picked, s =>
    if s.1.testBit y then
      if s.2 ≤ target then true else
        finiteGPCachedMaskCheck update completion target ys picked (clearCachedGPBit update s y) &&
        finiteGPCachedMaskCheck update completion target ys (y::picked)
          (clearCachedGPCompletions update completion y picked s)
    else finiteGPCachedMaskCheck update completion target ys picked s

/-- Correct updates give the same branch choices as recomputing from the
mask at every step. -/
theorem finiteGPCachedMaskCheck_eq (capacity : ℕ → ℕ) (update : ℕ → ℕ → ℕ → ℕ)
    (h : ∀ m i, update m (capacity m) i = capacity (clearGPBit m i)) (completion : ℕ → ℕ → Option ℕ)
    (target : ℕ) (candidates picked : List ℕ) (mask : ℕ) :
    finiteGPCachedMaskCheck update completion target candidates picked (mask,capacity mask) =
      finiteGPMaskCheck capacity completion target candidates picked mask := by
  induction candidates generalizing picked mask with
  | nil => rfl
  | cons y ys ih =>
    rw [finiteGPCachedMaskCheck,finiteGPMaskCheck]
    simp only [clearCachedGPBit_correct capacity update h,clearCachedGPCompletions_correct capacity update h,ih]

/-- A frozen checkpoint for independent finite certificate replay. -/
structure GPMaskCheckpoint where
  candidates : List ℕ
  picked : List ℕ
  maskAndCapacity : ℕ × ℕ
  deriving Repr, DecidableEq

/-- Execute the search from one checkpoint. -/
def finiteGPCachedMaskCheckAt (update : ℕ → ℕ → ℕ → ℕ) (completion : ℕ → ℕ → Option ℕ)
    (target : ℕ) (s : GPMaskCheckpoint) : Bool :=
  finiteGPCachedMaskCheck update completion target s.candidates s.picked s.maskAndCapacity

/-- Collect exactly the unfinished checkpoints after bounded initial
expansion. The subtrees can then be replayed independently. -/
def finiteGPCachedMaskFrontier (update : ℕ → ℕ → ℕ → ℕ) (completion : ℕ → ℕ → Option ℕ)
    (target : ℕ) : ℕ → GPMaskCheckpoint → List GPMaskCheckpoint
  | 0, s => [s]
  | d+1, s =>
    match s.candidates with
    | [] => if s.maskAndCapacity.2 ≤ target then [] else [s]
    | y::ys =>
      if s.maskAndCapacity.1.testBit y then
        if s.maskAndCapacity.2 ≤ target then [] else
          finiteGPCachedMaskFrontier update completion target d
            ⟨ys,s.picked,clearCachedGPBit update s.maskAndCapacity y⟩ ++
          finiteGPCachedMaskFrontier update completion target d
            ⟨ys,y::s.picked,clearCachedGPCompletions update completion y s.picked s.maskAndCapacity⟩
      else
        finiteGPCachedMaskFrontier update completion target d ⟨ys,s.picked,s.maskAndCapacity⟩

/-- Replaying all checkpoints is equivalent to running the full search. -/
theorem finiteGPCachedMaskFrontier_all_eq (update : ℕ → ℕ → ℕ → ℕ) (completion : ℕ → ℕ → Option ℕ)
    (target depth : ℕ) (s : GPMaskCheckpoint) :
    (finiteGPCachedMaskFrontier update completion target depth s).all
        (finiteGPCachedMaskCheckAt update completion target) =
      finiteGPCachedMaskCheckAt update completion target s := by
  induction depth generalizing s with
  | zero => simp [finiteGPCachedMaskFrontier]
  | succ depth ih =>
    rcases s with ⟨candidates,picked,M⟩
    cases candidates with
    | nil =>
      by_cases hc : M.2 ≤ target <;>
        simp [finiteGPCachedMaskFrontier,finiteGPCachedMaskCheckAt,finiteGPCachedMaskCheck,hc]
    | cons y ys =>
      by_cases hb : M.1.testBit y = true
      · by_cases hc : M.2 ≤ target
        · simp [finiteGPCachedMaskFrontier,finiteGPCachedMaskCheckAt,finiteGPCachedMaskCheck,hb,hc]
        · simp only [finiteGPCachedMaskFrontier,hb,hc,if_true,if_false,List.all_append,ih]
          simp [finiteGPCachedMaskCheckAt,finiteGPCachedMaskCheck,hb,hc]
      · simpa [finiteGPCachedMaskFrontier,finiteGPCachedMaskCheckAt,finiteGPCachedMaskCheck,hb,
          Bool.false_eq_true] using ih ⟨ys,picked,M⟩

/-- A list of individually successful checkpoint checks certifies the
original search. -/
theorem finiteGPCachedMaskCheckAt_of_frontier (update : ℕ → ℕ → ℕ → ℕ) (completion : ℕ → ℕ → Option ℕ)
    (target depth : ℕ) (s : GPMaskCheckpoint)
    (h : ∀ t ∈ finiteGPCachedMaskFrontier update completion target depth s,
      finiteGPCachedMaskCheckAt update completion target t = true) :
    finiteGPCachedMaskCheckAt update completion target s = true := by
  rw [←finiteGPCachedMaskFrontier_all_eq update completion target depth s]
  exact List.all_eq_true.mpr h

end GRHArticle.ProgressionFree
