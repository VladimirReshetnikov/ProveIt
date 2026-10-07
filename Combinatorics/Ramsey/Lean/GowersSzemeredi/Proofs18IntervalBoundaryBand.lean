import GowersSzemeredi.Proofs18RelativeIntervalModel

/-! A cell of small modular diameter that meets both sides of an interval
boundary lies in an explicit set of at most 4*d+2 points. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Bands around the two endpoints of the interval [0,L). -/
def intervalBoundaryBand (N L d : Nat) : Finset (ZMod N) :=
  ((Finset.range (d + 1) ∪ Finset.Ico (N - d) N) ∪ Finset.Icc (L - d) (L + d)).image
    (fun i : Nat ↦ (i : ZMod N))

/-- Increasing the radius enlarges the boundary band. -/
theorem intervalBoundaryBand_mono (N L : Nat) {d D : Nat} (h : d ≤ D) :
    intervalBoundaryBand N L d ⊆ intervalBoundaryBand N L D := by
  apply Finset.image_mono
  intro x hx
  simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico, Finset.mem_Icc] at hx ⊢
  omega

/-- Counting the bands before reduction modulo N gives a uniform bound,
including overlapping bands and intervals near either end of the group. -/
theorem intervalBoundaryBand_card (N L d : Nat) :
    (intervalBoundaryBand N L d).card ≤ 4 * d + 2 := by
  have h₁ := Finset.card_union_le (Finset.range (d + 1)) (Finset.Ico (N - d) N)
  have h₂ := Finset.card_union_le (Finset.range (d + 1) ∪ Finset.Ico (N - d) N)
    (Finset.Icc (L - d) (L + d))
  have h₃ := Finset.card_image_le (s := (Finset.range (d + 1) ∪ Finset.Ico (N - d) N) ∪ Finset.Icc (L - d) (L + d))
    (f := fun i : Nat ↦ (i : ZMod N))
  simp only [Finset.card_range, Nat.card_Ico, Nat.card_Icc] at h₁ h₂
  unfold intervalBoundaryBand
  exact h₃.trans (by omega)

/-- A point lies in the boundary band if its standard representative is
near zero, near N, or within d of L. -/
theorem mem_intervalBoundaryBand_of_val {N : Nat} [NeZero N] {L d : Nat} (x : ZMod N)
    (hx : x.val ≤ d ∨ N ≤ x.val + d ∨ (L ≤ x.val + d ∧ x.val ≤ L + d)) :
    x ∈ intervalBoundaryBand N L d := by
  apply Finset.mem_image.mpr
  refine ⟨x.val, ?_, ZMod.natCast_zmod_val x⟩
  rcases hx with h | h | ⟨hlo, hhi⟩
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_range.mpr (by omega)))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨by omega, x.val_lt⟩))
  · exact Finset.mem_union_right _ (Finset.mem_Icc.mpr ⟨by omega, hhi⟩)

/-- A member of a modular interval has an index in the displayed range. -/
theorem mem_modInterval_index {N : Nat} (a x : ZMod N) (d : Nat)
    (hx : x ∈ (modInterval N a (d + 1)).carrier) :
    ∃ i : Nat, i ≤ d ∧ x = a + (i : ZMod N) := by
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
  refine ⟨i, by have := i.isLt; simpa only [modInterval] using Nat.le_of_lt_succ this, ?_⟩
  simpa only [modInterval, mul_one] using hi.symm

/-- Every point of a small-diameter cell crossing the cut at L lies in
the boundary bands. This uses both witnesses of crossing, not just its size. -/
theorem crossing_cell_subset_intervalBoundaryBand {N : Nat} [NeZero N]
    (C : Finset (ZMod N)) (L d : Nat) (hdiam : diameterAtMost C d)
    (hin : ∃ x ∈ C, x.val < L) (hout : ∃ y ∈ C, L ≤ y.val) :
    C ⊆ intervalBoundaryBand N L d := by
  obtain ⟨a, ha⟩ := hdiam
  have hindex (z : ZMod N) (hz : z ∈ C) :
      ∃ i : Nat, i ≤ d ∧ z.val = (a.val + i) % N := by
    obtain ⟨i, hi, hzi⟩ := mem_modInterval_index a z d (ha hz)
    refine ⟨i, hi, ?_⟩
    rw [hzi, ← ZMod.natCast_zmod_val a, ← Nat.cast_add, ZMod.val_natCast]
    simp only [ZMod.natCast_zmod_val]
  intro z hz
  apply mem_intervalBoundaryBand_of_val
  obtain ⟨i, hi, hzi⟩ := hindex z hz
  by_cases hd : N ≤ d
  · exact Or.inl (z.val_lt.le.trans hd)
  have haN := a.val_lt
  by_cases hwrap : N ≤ a.val + d
  · by_cases hzWrap : N ≤ a.val + i
    · left
      have hless : a.val + i < N + N := by omega
      rw [Nat.mod_eq_sub_mod hzWrap, Nat.mod_eq_of_lt (by omega)] at hzi
      omega
    · right; left
      rw [Nat.mod_eq_of_lt (by omega)] at hzi
      omega
  · obtain ⟨x, hx, hxL⟩ := hin
    obtain ⟨y, hy, hyL⟩ := hout
    obtain ⟨ix, hix, hxv⟩ := hindex x hx
    obtain ⟨iy, hiy, hyv⟩ := hindex y hy
    rw [Nat.mod_eq_of_lt (by omega)] at hzi hxv hyv
    right; right
    omega

end LeanProofs.GowersSzemeredi
