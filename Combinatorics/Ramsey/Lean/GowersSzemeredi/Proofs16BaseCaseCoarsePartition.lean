import GowersSzemeredi.Proofs16BaseCaseRestriction
import GowersSzemeredi.ProgressionChunks

/-!
# Proper one-dimensional coarse box partitions for Lemma 16.3

This module isolates the elementary geometry used in the short-box branch of
the repaired base case.  A proper one-dimensional modular box is enumerated by
its progression index, then split into consecutive proper child boxes whose
lengths differ by at most one.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi.BaseCase

lemma boxOne_width {N : Nat} (P : Box N 1) :
    P.width = (P.axis 0).length := by
  simp [Box.width]

def boxOnePoint {N : Nat} (P : Box N 1) (i : Nat) : Point N 1 :=
  fun _ => (P.axis 0).start + (i : Nat) * (P.axis 0).step

lemma boxOnePoint_injective {N : Nat} [NeZero N] (P : Box N 1)
    (hP : P.IsProper) {i j : Nat}
    (hi : i < P.width) (hj : j < P.width)
    (hij : boxOnePoint P i = boxOnePoint P j) : i = j := by
  have haxis := hP 0
  rw [ModAP.IsProper, ModAP.carrier] at haxis
  have haxis' :
      ((Finset.univ : Finset (Fin (P.axis 0).length)).image
          (fun t : Fin (P.axis 0).length =>
            (P.axis 0).start + (t : Nat) * (P.axis 0).step)).card =
        (Finset.univ : Finset (Fin (P.axis 0).length)).card := by
    simpa using haxis
  have hinj : Function.Injective
      (fun t : Fin (P.axis 0).length =>
        (P.axis 0).start + (t : Nat) * (P.axis 0).step) := by
    have hinjOn := Finset.card_image_iff.mp haxis'
    intro a b hab
    exact hinjOn (Finset.mem_univ a) (Finset.mem_univ b) hab
  have hi' : i < (P.axis 0).length := by simpa [boxOne_width] using hi
  have hj' : j < (P.axis 0).length := by simpa [boxOne_width] using hj
  let i' : Fin (P.axis 0).length := ⟨i, hi'⟩
  let j' : Fin (P.axis 0).length := ⟨j, hj'⟩
  have hcoord :
      (P.axis 0).start + (i' : Nat) * (P.axis 0).step =
        (P.axis 0).start + (j' : Nat) * (P.axis 0).step := by
    simpa [i', j', boxOnePoint] using congrFun hij 0
  exact congrArg Fin.val (hinj hcoord)

lemma boxOne_carrier_eq_image {N : Nat} [NeZero N] (P : Box N 1) :
    P.carrier = (Finset.univ : Finset (Fin P.width)).image
      (fun i : Fin P.width => boxOnePoint P i) := by
  classical
  ext x
  simp only [Box.carrier, Finset.mem_filter, Finset.mem_univ, true_and,
    ModAP.carrier, Finset.mem_image]
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := hx 0
    let j : Fin P.width := ⟨i, by rw [boxOne_width]; exact i.isLt⟩
    refine ⟨j, ?_⟩
    apply funext
    intro t
    fin_cases t
    simpa [j, boxOnePoint] using hi
  · rintro ⟨i, rfl⟩ j
    fin_cases j
    let t : Fin (P.axis 0).length :=
      ⟨i, by simpa [boxOne_width] using i.isLt⟩
    exact ⟨t, by simp [t, boxOnePoint]⟩

lemma boxOne_carrier_card_eq_axis_card {N : Nat} [NeZero N]
    (P : Box N 1) : P.carrier.card = (P.axis 0).carrier.card := by
  classical
  have himage : P.carrier.map (pointOneEquiv N).toEmbedding =
      (P.axis 0).carrier := by
    ext z
    constructor
    · intro hz
      rw [Finset.mem_map] at hz
      obtain ⟨x, hx, hzx⟩ := hz
      have hx0 := (Finset.mem_filter.mp hx).2 0
      simpa [pointOneEquiv, ← hzx] using hx0
    · intro hz
      let x : Point N 1 := fun _ => z
      rw [Finset.mem_map]
      refine ⟨x, ?_, by simp [x, pointOneEquiv]⟩
      rw [Box.carrier, Finset.mem_filter]
      refine ⟨Finset.mem_univ x, ?_⟩
      intro i
      fin_cases i
      simpa [x] using hz
  rw [← himage]
  simp

lemma boxOne_card_eq_width {N : Nat} [NeZero N] (P : Box N 1)
    (hP : P.IsProper) : P.carrier.card = P.width := by
  rw [boxOne_carrier_eq_image]
  rw [Finset.card_image_iff.mpr]
  · simp only [Finset.card_univ, Fintype.card_fin]
  · intro i _ j _ hij
    apply Fin.ext
    exact boxOnePoint_injective P hP i.isLt j.isLt hij

def coarseChildBox {N : Nat} (P : Box N 1) (m : Nat)
    (j : Fin (P.width / m)) : Box N 1 where
  axis := fun _ =>
    { start := (P.axis 0).start +
        (coarseChunkStart m (P.width % m) j : Nat) * (P.axis 0).step
      step := (P.axis 0).step
      length := coarseChunkLength m (P.width % m) j }
  commonDiff := P.commonDiff
  axis_step := by intro i; simpa using P.axis_step 0

@[simp] lemma coarseChildBox_width {N : Nat} (P : Box N 1)
    (m : Nat) (j : Fin (P.width / m)) :
    (coarseChildBox P m j).width = coarseChunkLength m (P.width % m) j := by
  simp [coarseChildBox, Box.width]

lemma coarseChildBox_carrier {N : Nat} [NeZero N]
    (P : Box N 1) (m : Nat) (j : Fin (P.width / m)) :
    (coarseChildBox P m j).carrier =
      (Finset.univ : Finset (Fin (coarseChunkLength m (P.width % m) j))).image
        (fun i : Fin (coarseChunkLength m (P.width % m) j) =>
          boxOnePoint P (coarseChunkStart m (P.width % m) j + i)) := by
  classical
  ext x
  simp only [Box.carrier, coarseChildBox, Finset.mem_filter, Finset.mem_univ,
    true_and, ModAP.carrier, Finset.mem_image]
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := hx 0
    refine ⟨i, ?_⟩
    apply funext
    intro t
    fin_cases t
    simpa [boxOnePoint, add_mul, add_assoc] using hi
  · rintro ⟨i, rfl⟩ t
    fin_cases t
    exact ⟨i, by simp [boxOnePoint, add_mul, add_assoc]⟩

lemma coarseChildBox_proper {N : Nat} [NeZero N]
    (P : Box N 1) (hP : P.IsProper) (m : Nat) (hm : 0 < m)
    (hLm : m * m ≤ P.width) (j : Fin (P.width / m)) :
    (coarseChildBox P m j).IsProper := by
  intro i
  fin_cases i
  rw [ModAP.IsProper]
  classical
  rw [ModAP.carrier, Finset.card_image_iff.mpr]
  · simp only [Finset.card_univ, Fintype.card_fin]
  · intro a _ b _ hab
    apply Fin.ext
    have hab' : boxOnePoint P
        (coarseChunkStart m (P.width % m) j + a) =
        boxOnePoint P (coarseChunkStart m (P.width % m) j + b) := by
      funext u
      fin_cases u
      simpa [coarseChildBox, boxOnePoint, add_mul] using hab
    exact Nat.add_left_cancel (boxOnePoint_injective P hP
      (coarseChunk_index_lt hm hLm j a.isLt)
      (coarseChunk_index_lt hm hLm j b.isLt) hab')

lemma coarseChildBox_partition {N : Nat} [NeZero N]
    (P : Box N 1) (hP : P.IsProper) (m : Nat) (hm : 0 < m)
    (hLm : m * m ≤ P.width) :
    IsBoxPartition (fun j : Fin (P.width / m) => coarseChildBox P m j) P := by
  classical
  constructor
  · intro x
    constructor
    · intro hx
      rw [boxOne_carrier_eq_image] at hx
      obtain ⟨t, _ht, htx⟩ := Finset.mem_image.mp hx
      obtain ⟨j, i, hi, ht⟩ := exists_coarseChunk hm hLm t.isLt
      refine ⟨j, ?_⟩
      change x ∈ (coarseChildBox P m j).carrier
      rw [coarseChildBox_carrier]
      apply Finset.mem_image.mpr
      exact ⟨⟨i, hi⟩, Finset.mem_univ _, by simpa [← ht] using htx⟩
    · rintro ⟨j, hxj⟩
      change x ∈ (coarseChildBox P m j).carrier at hxj
      rw [coarseChildBox_carrier] at hxj
      obtain ⟨i, _hi, hix⟩ := Finset.mem_image.mp hxj
      rw [boxOne_carrier_eq_image]
      let t : Fin P.width :=
        ⟨coarseChunkStart m (P.width % m) j + i,
          coarseChunk_index_lt hm hLm j i.isLt⟩
      apply Finset.mem_image.mpr
      exact ⟨t, Finset.mem_univ t, by simpa [t] using hix⟩
  · intro j j' hjj'
    rw [Finset.disjoint_left]
    intro x hx hx'
    change x ∈ (coarseChildBox P m j).carrier at hx
    change x ∈ (coarseChildBox P m j').carrier at hx'
    rw [coarseChildBox_carrier] at hx hx'
    obtain ⟨i, _hi, hxi⟩ := Finset.mem_image.mp hx
    obtain ⟨i', _hi', hxi'⟩ := Finset.mem_image.mp hx'
    have hindex :
        coarseChunkStart m (P.width % m) j + i =
          coarseChunkStart m (P.width % m) j' + i' := by
      apply boxOnePoint_injective P hP
      · exact coarseChunk_index_lt hm hLm j i.isLt
      · exact coarseChunk_index_lt hm hLm j' i'.isLt
      · exact hxi.trans hxi'.symm
    have := coarseChunk_unique j j' i i' i.isLt i'.isLt rfl hindex
    exact (bne_iff_ne.mp hjj') this

lemma isMultilinear_const_one {N : Nat} (c : ZMod N) :
    IsMultilinear (fun _ : Point N 1 => c) := by
  classical
  let e0 : Fin 1 → Bool := fun _ => false
  refine ⟨fun e => if e = e0 then c else 0, ?_⟩
  intro x
  rw [Finset.sum_eq_single e0]
  · simp [e0]
  · intro e _ hne
    simp [hne]
  · simp

lemma mem_partialGraph_one {N : Nat} [NeZero N]
    (B : Finset (Point N 1)) (phi : Point N 1 → ZMod N)
    (x : Point N 1) (y : ZMod N) :
    (x, y) ∈ partialGraph B phi ↔ x ∈ B ∧ y = phi x := by
  classical
  rw [partialGraph, Finset.mem_image]
  constructor
  · rintro ⟨z, hz, hzx⟩
    have hzx' : z = x := congrArg Prod.fst hzx
    subst z
    exact ⟨hz, (congrArg Prod.snd hzx).symm⟩
  · rintro ⟨hx, rfl⟩
    exact ⟨x, hx, rfl⟩

end LeanProofs.GowersSzemeredi.BaseCase
