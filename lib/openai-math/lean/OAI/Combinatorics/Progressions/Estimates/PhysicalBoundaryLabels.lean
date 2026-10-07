/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Geometry.PhysicalBoxPartition

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem integer_cut_side_stable {a u v : ℤ} {r : ℕ}
    (hmove : |u - v| ≤ (r : ℤ)) (hfar : (r : ℤ) < |u - a|) :
    a ≤ u ↔ a ≤ v := by
  have hm := abs_le.mp hmove
  by_cases h : a ≤ u
  · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hfar
    have hv : a ≤ v := by omega
    exact ⟨fun _ => hv, fun _ => h⟩
  · have hu : u ≤ a := by omega
    rw [abs_of_nonpos (sub_nonpos.mpr hu)] at hfar
    have hv : ¬ a ≤ v := by omega
    exact ⟨fun h' => (h h').elim, fun h' => (hv h').elim⟩

theorem integer_interval_membership_stable {a b u v : ℤ} {r : ℕ}
    (hmove : |u - v| ≤ (r : ℤ))
    (hleft : (r : ℤ) < |u - a|) (hright : (r : ℤ) < |u - b|) :
    (a ≤ u ∧ u < b) ↔ (a ≤ v ∧ v < b) := by
  have hl := integer_cut_side_stable hmove hleft
  have hr := integer_cut_side_stable hmove hright
  constructor <;> intro h <;> constructor <;> omega

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def physicalBoxClassify (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (x : I → ℤ) : Option (∀ i, (P i).Label) :=
  if hx : x ∈ translatedIntegerBox lo N then some (physicalBoxCell lo N P ⟨x, hx⟩) else none

def physicalBoundaryNear (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (r : I → ℕ) (x : I → ℤ) : Prop :=
  ∃ i c, |x i - intervalCellLower (lo i) (P i) c| ≤ (r i : ℤ) ∨
    |x i - intervalCellUpper (lo i) (P i) c| ≤ (r i : ℤ)

theorem physicalBoxClassify_eq_some_iff (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hstep : ∀ i c, (P i).step c = 1)
    (hpos : ∀ i c, 0 < (P i).length c) (x : I → ℤ) (c : ∀ i, (P i).Label) :
    physicalBoxClassify lo N P x = some c ↔ ∀ i,
      intervalCellLower (lo i) (P i) (c i) ≤ x i ∧ x i < intervalCellUpper (lo i) (P i) (c i) := by
  constructor
  · intro h
    by_cases hx : x ∈ translatedIntegerBox lo N
    · simp only [physicalBoxClassify, dite_eq_left hx, Option.some.injEq] at h
      exact (physicalBoxCell_eq_iff lo N P hstep ⟨x, hx⟩ c).mp h
    · simp only [physicalBoxClassify, dite_eq_right hx] at h
      cases h
  · intro h
    have hxcell : x ∈ translatedIntegerBox (fun i => intervalCellLower (lo i) (P i) (c i))
        (fun i => (P i).length (c i)) := by
      apply (mem_translatedIntegerBox _ _ x).mpr
      intro i
      exact h i
    have hx := physicalBoxCell_subset lo N P hstep hpos c hxcell
    have hc := (physicalBoxCell_eq_iff lo N P hstep ⟨x, hx⟩ c).mpr h
    simp only [physicalBoxClassify, dite_eq_left hx, Option.some.injEq]
    exact hc

theorem physicalBoxClassify_stable (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hstep : ∀ i c, (P i).step c = 1)
    (hpos : ∀ i c, 0 < (P i).length c) (r : I → ℕ) (u v : I → ℤ)
    (hmove : ∀ i, |u i - v i| ≤ (r i : ℤ)) (hfar : ¬ physicalBoundaryNear lo N P r u) :
    physicalBoxClassify lo N P u = physicalBoxClassify lo N P v := by
  have hi (i : I) (c : (P i).Label) :
      (intervalCellLower (lo i) (P i) c ≤ u i ∧ u i < intervalCellUpper (lo i) (P i) c) ↔
      (intervalCellLower (lo i) (P i) c ≤ v i ∧ v i < intervalCellUpper (lo i) (P i) c) := by
    apply integer_interval_membership_stable (hmove i)
    · exact lt_of_not_ge (fun h => hfar ⟨i, c, Or.inl h⟩)
    · exact lt_of_not_ge (fun h => hfar ⟨i, c, Or.inr h⟩)
  have hc (c : ∀ i, (P i).Label) :
      physicalBoxClassify lo N P u = some c ↔ physicalBoxClassify lo N P v = some c := by
    rw [physicalBoxClassify_eq_some_iff lo N P hstep hpos u c,
      physicalBoxClassify_eq_some_iff lo N P hstep hpos v c]
    exact forall_congr' (fun i => hi i (c i))
  cases hu : physicalBoxClassify lo N P u with
  | some c => exact ((hc c).mp hu).symm
  | none =>
      cases hv : physicalBoxClassify lo N P v with
      | none => rfl
      | some c =>
          have h := (hc c).mpr hv
          rw [hu] at h
          cases h

end Erdos3

end

end OAI
