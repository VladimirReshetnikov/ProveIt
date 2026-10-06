import GowersSzemeredi.Proofs05BoxPartition

/-! # Slices of proper boxes and differences controlled by diameter -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

@[simp] theorem centeredAbs_neg {N : Nat} [NeZero N] (x : ZMod N) :
    centeredAbs (-x) = centeredAbs x := ZMod.natAbs_valMinAbs_neg x

theorem centeredAbs_natCast_le {N i : Nat} [NeZero N] :
    centeredAbs (i : ZMod N) ≤ i := by
  rw [centeredAbs, ZMod.valMinAbs_natAbs_eq_min, ZMod.val_natCast]
  exact (Nat.min_le_left _ _).trans (Nat.mod_le i N)

theorem centeredAbs_intCast_le {N : Nat} [NeZero N] (i : Int) :
    centeredAbs (i : ZMod N) ≤ i.natAbs := by
  cases i with
  | ofNat n => simpa using centeredAbs_natCast_le (N := N) (i := n)
  | negSucc n =>
    have hcast : ((Int.negSucc n : Int) : ZMod N) = -((n + 1 : Nat) : ZMod N) := by
      push_cast; ring
    rw [hcast, centeredAbs_neg]
    simpa using centeredAbs_natCast_le (N := N) (i := n + 1)

/-- An interval diameter bounds the centered distance between any two members. -/
theorem diameterAtMost.centeredAbs_sub_le {N d : Nat} [NeZero N]
    {A : Finset (ZMod N)} (h : diameterAtMost A d) {x y : ZMod N}
    (hx : x ∈ A) (hy : y ∈ A) : centeredAbs (x - y) ≤ d := by
  classical
  obtain ⟨a, ha⟩ := h
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (ha hx)
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (ha hy)
  have heq : x - y = (((i.val : Int) - j.val : Int) : ZMod N) := by
    dsimp [modInterval] at hi hj
    rw [← hi, ← hj]
    push_cast; ring
  rw [heq]
  apply (centeredAbs_intCast_le _).trans
  have hi' : i.val < d + 1 := i.isLt
  have hj' : j.val < d + 1 := j.isLt
  omega

theorem diameterAtMostReal.centeredAbs_sub_le {N : Nat} [NeZero N]
    {A : Finset (ZMod N)} {s : Real} (h : diameterAtMostReal A s)
    {x y : ZMod N} (hx : x ∈ A) (hy : y ∈ A) :
    (centeredAbs (x - y) : Real) ≤ s := by
  obtain ⟨d, hd, hds⟩ := h
  exact (show (centeredAbs (x - y) : Real) ≤ d by
    exact_mod_cast hd.centeredAbs_sub_le hx hy).trans hds

/-- Every point of a progression of length at least two has an adjacent point
in one of the two orientations. No order on the modular progression is used. -/
theorem ModAP.adjacent_mem {N : Nat} (P : ModAP N) (hP : 2 ≤ P.length)
    {y : ZMod N} (hy : y ∈ P.carrier) :
    y + P.step ∈ P.carrier ∨ y - P.step ∈ P.carrier := by
  classical
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
  by_cases hi : i.val + 1 < P.length
  · left
    apply Finset.mem_image.mpr
    refine ⟨⟨i.val + 1, hi⟩, Finset.mem_univ _, ?_⟩
    dsimp
    push_cast; ring
  · right
    have hi0 : 0 < i.val := by have := i.isLt; omega
    apply Finset.mem_image.mpr
    refine ⟨⟨i.val - 1, by have := i.isLt; omega⟩, Finset.mem_univ _, ?_⟩
    dsimp
    rw [Nat.cast_sub (by omega : 1 ≤ i.val)]
    push_cast; ring

/-- Add an axis with the same common difference. -/
def boxCons {N k : Nat} (P : Box N k) (I : ModAP N)
    (hstep : I.step = P.commonDiff) : Box N (k + 1) where
  axis := Fin.cons I P.axis
  commonDiff := P.commonDiff
  axis_step := by intro i; refine Fin.cases hstep (fun j => P.axis_step j) i

/-- Forget the first axis. -/
def boxTail {N k : Nat} (P : Box N (k + 1)) : Box N k where
  axis i := P.axis i.succ
  commonDiff := P.commonDiff
  axis_step i := P.axis_step i.succ

theorem boxCons_isProper {N k : Nat} (P : Box N k) (I : ModAP N)
    (hstep : I.step = P.commonDiff) (hP : P.IsProper) (hI : I.IsProper) :
    (boxCons P I hstep).IsProper := by
  intro i; exact Fin.cases hI (fun j => hP j) i

theorem boxTail_isProper {N k : Nat} (P : Box N (k + 1)) (hP : P.IsProper) :
    (boxTail P).IsProper := fun i => hP i.succ

theorem boxTail_width {N k : Nat} (P : Box N (k + 1)) (hk : 0 < k) :
    P.width ≤ (boxTail P).width :=
  (boxTail P).le_width_of_le_axis hk (fun i => P.width_le_axis_length i.succ)

theorem boxCons_width {N k m : Nat} (P : Box N k) (I : ModAP N)
    (hstep : I.step = P.commonDiff) (hm : m ≤ P.width) (hI : m ≤ I.length) :
    m ≤ (boxCons P I hstep).width := by
  apply Box.le_width_of_le_axis _ (by omega)
  intro i
  exact Fin.cases hI (fun j => hm.trans (P.width_le_axis_length j)) i

@[simp] theorem mem_boxTail_cons {N k : Nat} [NeZero N]
    (P : Box N (k + 1)) (y : ZMod N) (x : Point N k) :
    Fin.cons y x ∈ P.carrier ↔ y ∈ (P.axis 0).carrier ∧ x ∈ (boxTail P).carrier := by
  simp only [Box.carrier, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => ⟨h 0, fun i => h i.succ⟩,
    fun h i => Fin.cases h.1 h.2 i⟩

@[simp] theorem boxTail_boxCons {N k : Nat} (P : Box N k) (I : ModAP N)
    (hstep : I.step = P.commonDiff) : boxTail (boxCons P I hstep) = P := by
  cases P; rfl

/-- Retain precisely the cells meeting a fixed first-coordinate slice. -/
theorem box_slice_partition {N k M : Nat} [NeZero N] (P : Box N k)
    (I : ModAP N) (hstep : I.step = P.commonDiff)
    (Q : Fin M → Box N (k + 1)) (hQ : IsBoxPartition Q (boxCons P I hstep))
    (y : ZMod N) (hy : y ∈ I.carrier) :
    ∃ L : Nat, ∃ j : Fin L → Fin M,
      (∀ a, y ∈ ((Q (j a)).axis 0).carrier) ∧
      IsBoxPartition (fun a => boxTail (Q (j a))) P := by
  classical
  let S := {a : Fin M // y ∈ ((Q a).axis 0).carrier}
  let e := Fintype.equivFin S
  refine ⟨Fintype.card S, fun a => (e.symm a).val, fun a => (e.symm a).property, ?_⟩
  constructor
  · intro x
    constructor
    · intro hx
      have hxy : Fin.cons y x ∈ (boxCons P I hstep).carrier := by
        rw [mem_boxTail_cons, boxTail_boxCons]
        exact ⟨hy, hx⟩
      obtain ⟨a, ha⟩ := (hQ.1 _).mp hxy
      obtain ⟨hay, hax⟩ := (mem_boxTail_cons _ _ _).mp ha
      refine ⟨e ⟨a, hay⟩, ?_⟩
      simpa only [Equiv.symm_apply_apply] using hax
    · rintro ⟨a, ha⟩
      have hxy : Fin.cons y x ∈ (Q (e.symm a).val).carrier :=
        (mem_boxTail_cons _ _ _).mpr ⟨(e.symm a).property, ha⟩
      have := (hQ.1 _).mpr ⟨_, hxy⟩
      simpa only [mem_boxTail_cons, boxTail_boxCons] using (And.right
        ((mem_boxTail_cons _ _ _).mp this))
  · intro a b hab
    apply Finset.disjoint_left.mpr
    intro x hxa hxb
    have hne : (e.symm a).val ≠ (e.symm b).val := by
      intro he
      exact (bne_iff_ne.mp hab) (e.symm.injective (Subtype.ext he))
    exact Finset.disjoint_left.mp (hQ.2 _ _ (bne_iff_ne.mpr hne))
      ((mem_boxTail_cons _ _ _).mpr ⟨(e.symm a).property, hxa⟩)
      ((mem_boxTail_cons _ _ _).mpr ⟨(e.symm b).property, hxb⟩)

end LeanProofs.GowersSzemeredi
