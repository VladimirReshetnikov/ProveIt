import GowersSzemeredi.Proofs05ResiduePartition
import GowersSzemeredi.Proofs05Downstream
import GowersSzemeredi.Proofs16BoxGeometry

/-!
# Prescribed-step partitions of proper boxes

The one-dimensional residue partitions combine independently along the axes.
Every child is proper, has the prescribed common difference, and has every
axis length equal to the target or target minus one.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace LeanProofs.GowersSzemeredi

/-- A uniform lower bound on axis lengths is a lower bound on width. -/
theorem Box.le_width_of_le_axis {N k v : Nat} (P : Box N k) (hk : 0 < k)
    (h : ∀ i, v ≤ (P.axis i).length) : v ≤ P.width := by
  classical
  simp only [Box.width, dif_neg (Nat.ne_of_gt hk)]
  apply Finset.le_min'
  intro y hy
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
  exact h i

/-- A box of one chosen progression from each axis family. -/
def boxProductCell {N k : Nat} (m : Fin k → Nat)
    (Q : (i : Fin k) → Fin (m i) → ModAP N) (d : ZMod N)
    (hstep : ∀ i j, (Q i j).step = d) (j : ∀ i, Fin (m i)) : Box N k where
  axis i := Q i (j i)
  commonDiff := d
  axis_step i := hstep i (j i)

/-- Products of axis partitions form a partition of the original box. -/
theorem boxProductCell_partition {N k : Nat} [NeZero N] (P : Box N k)
    (m : Fin k → Nat) (Q : (i : Fin k) → Fin (m i) → ModAP N) (d : ZMod N)
    (hstep : ∀ i j, (Q i j).step = d)
    (hpart : ∀ i, IsPartition (fun j => (Q i j).carrier) (P.axis i).carrier) :
    IsBoxPartition
      (fun j : Fin (Fintype.card (∀ i, Fin (m i))) =>
        boxProductCell m Q d hstep ((Fintype.equivFin _).symm j)) P := by
  classical
  let e := Fintype.equivFin (∀ i, Fin (m i))
  constructor
  · intro x
    simp only [Box.carrier, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx
      have hex : ∀ i, ∃ j, x i ∈ (Q i j).carrier := fun i => ((hpart i).1 _).mp (hx i)
      choose j hj using hex
      refine ⟨e j, ?_⟩
      simpa only [boxProductCell, e, Equiv.symm_apply_apply] using hj
    · rintro ⟨j, hj⟩ i
      exact ((hpart i).1 _).mpr ⟨(e.symm j) i, hj i⟩
  · intro j l hjl
    apply Finset.disjoint_left.mpr
    intro x hxj hxl
    have hj : ∀ i, x i ∈ (Q i ((e.symm j) i)).carrier := by
      simpa only [Box.carrier, Finset.mem_filter, Finset.mem_univ, true_and, boxProductCell] using hxj
    have hl : ∀ i, x i ∈ (Q i ((e.symm l) i)).carrier := by
      simpa only [Box.carrier, Finset.mem_filter, Finset.mem_univ, true_and, boxProductCell] using hxl
    have heq : e.symm j = e.symm l := by
      funext i
      by_contra hne
      exact Finset.disjoint_left.mp ((hpart i).2 _ _ (bne_iff_ne.mpr hne)) (hj i) (hl i)
    exact (bne_iff_ne.mp hjl) (e.symm.injective heq)

/-- A proper box admits a partition with prescribed step and almost-equal
axis lengths whenever p*v^2 fits in its width. -/
theorem section5_box_residue_partition {N k : Nat} [NeZero N]
    (P : Box N k) (hP : P.IsProper) (hk : 0 < k) (p v : Nat)
    (hp : 0 < p) (hv : 1 ≤ v) (hsize : p * v ^ 2 ≤ P.width) :
    ∃ M : Nat, ∃ Q : Fin M → Box N k,
      IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
      (∀ j, v - 1 ≤ (Q j).width) ∧
      (∀ j i, 0 < ((Q j).axis i).length ∧
        (((Q j).axis i).length = v - 1 ∨ ((Q j).axis i).length = v)) ∧
      ∀ j, (Q j).commonDiff = (p : ZMod N) * P.commonDiff := by
  classical
  have haxis (i : Fin k) : p * v ^ 2 ≤ (P.axis i).length :=
    hsize.trans (P.width_le_axis_length i)
  choose m R hm hRpart hRprop hRstep using
    fun i => section5_residue_target_partition (P.axis i).length p v hp hv (haxis i)
  let T (i : Fin k) (j : Fin (m i)) := section5Transport (P.axis i) (R i j)
  have hTpart (i : Fin k) : IsPartition (fun j => (T i j).carrier) (P.axis i).carrier :=
    section5Transport_partition (P.axis i) (R i) (hP i) (hRpart i)
  have hTproper (i : Fin k) (j : Fin (m i)) : (T i j).IsProper :=
    section5Transport_isProper (P.axis i) (R i j) (hP i) (hRprop i j).1
      (IsPartition.cell_subset (hRpart i) j)
  have hTstep (i : Fin k) (j : Fin (m i)) : (T i j).step = (p : ZMod N) * P.commonDiff := by
    change ((R i j).step : ZMod N) * (P.axis i).step = _
    rw [hRstep, P.axis_step]
  let Q := fun j : Fin (Fintype.card (∀ i, Fin (m i))) =>
    boxProductCell m T ((p : ZMod N) * P.commonDiff) hTstep ((Fintype.equivFin _).symm j)
  refine ⟨_, Q, boxProductCell_partition P m T _ hTstep hTpart, ?_, ?_, ?_, ?_⟩
  · intro j i
    exact hTproper i _
  · intro j
    apply Box.le_width_of_le_axis _ hk
    intro i
    have hlen := (hRprop i (((Fintype.equivFin _).symm j) i)).2.2
    change v - 1 ≤ (R i (((Fintype.equivFin _).symm j) i)).length
    omega
  · intro j i
    exact (hRprop i _).2
  · intro j
    rfl

/-- Natural index vectors of a box. -/
def boxIndexSet {N k : Nat} (P : Box N k) : Finset (Fin k → Nat) :=
  Fintype.piFinset fun i => Finset.range (P.axis i).length

/-- Its common-step affine parametrization. -/
def boxIndexPoint {N k : Nat} (P : Box N k) (t : Fin k → Nat) : Point N k :=
  fun i => (P.axis i).start + P.commonDiff * (t i : ZMod N)

/-- The natural index box parametrizes precisely the modular carrier. -/
theorem Box.carrier_eq_index_image {N k : Nat} [NeZero N] (P : Box N k) :
    P.carrier = (boxIndexSet P).image (boxIndexPoint P) := by
  classical
  ext x
  simp only [Box.carrier, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro hx
    have hex : ∀ i, ∃ t : Nat, t < (P.axis i).length ∧
        (P.axis i).start + P.commonDiff * (t : ZMod N) = x i := by
      intro i
      obtain ⟨t, _, ht⟩ := Finset.mem_image.mp (hx i)
      refine ⟨t, t.isLt, ?_⟩
      simpa only [P.axis_step, mul_comm] using ht
    choose t ht htx using hex
    refine ⟨t, ?_, funext htx⟩
    exact Fintype.mem_piFinset.mpr fun i => Finset.mem_range.mpr (ht i)
  · rintro ⟨t, ht, rfl⟩ i
    have hi := Finset.mem_range.mp (Fintype.mem_piFinset.mp ht i)
    apply Finset.mem_image.mpr
    refine ⟨⟨t i, hi⟩, Finset.mem_univ _, ?_⟩
    simp only [boxIndexPoint, P.axis_step, mul_comm]

end LeanProofs.GowersSzemeredi
