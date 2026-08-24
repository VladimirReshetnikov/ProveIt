import GowersSzemeredi.Proofs16BaseCaseRestriction

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

def coarseChunkStart (m b j : Nat) : Nat :=
  j * m + min j b

def coarseChunkLength (m b j : Nat) : Nat :=
  if j < b then m + 1 else m

lemma coarseChunk_end (m b j : Nat) :
    coarseChunkStart m b j + coarseChunkLength m b j =
      coarseChunkStart m b (j + 1) := by
  by_cases hjb : j < b
  · simp [coarseChunkStart, coarseChunkLength, hjb, min_eq_left hjb.le]
    ring
  · have hbj : b ≤ j := Nat.le_of_not_gt hjb
    have hsucc : b ≤ j + 1 := hbj.trans (Nat.le_succ _)
    simp [coarseChunkStart, coarseChunkLength, hjb, min_eq_right hbj,
      min_eq_right hsucc]
    ring

lemma coarse_remainder_le_quotient {L m : Nat} (hm : 0 < m)
    (hLm : m * m ≤ L) : L % m ≤ L / m := by
  have hmm : m ≤ L / m := (Nat.le_div_iff_mul_le hm).2 hLm
  exact (Nat.mod_lt L hm).le.trans hmm

lemma coarseChunk_total {L m : Nat} (hm : 0 < m)
    (hLm : m * m ≤ L) :
    coarseChunkStart m (L % m) (L / m) = L := by
  have hb := coarse_remainder_le_quotient hm hLm
  rw [coarseChunkStart, min_eq_right hb, Nat.mul_comm (L / m) m]
  exact Nat.div_add_mod L m

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

lemma coarseChunk_length_bounds {L m : Nat} (hm : 0 < m)
    (j : Fin (L / m)) :
    m ≤ coarseChunkLength m (L % m) j ∧
      coarseChunkLength m (L % m) j ≤ 2 * m := by
  unfold coarseChunkLength
  split_ifs <;> omega

lemma coarseChunkStart_mono {m b j k : Nat} (hjk : j ≤ k) :
    coarseChunkStart m b j ≤ coarseChunkStart m b k := by
  unfold coarseChunkStart
  exact Nat.add_le_add (Nat.mul_le_mul_right m hjk) (min_le_min hjk le_rfl)

lemma coarseChunk_index_lt {L m : Nat} (hm : 0 < m)
    (hLm : m * m ≤ L) (j : Fin (L / m)) {i : Nat}
    (hi : i < coarseChunkLength m (L % m) j) :
    coarseChunkStart m (L % m) j + i < L := by
  calc
    coarseChunkStart m (L % m) j + i <
        coarseChunkStart m (L % m) j +
          coarseChunkLength m (L % m) j := Nat.add_lt_add_left hi _
    _ = coarseChunkStart m (L % m) (j + 1) := coarseChunk_end _ _ _
    _ ≤ coarseChunkStart m (L % m) (L / m) := by
      apply coarseChunkStart_mono
      omega
    _ = L := coarseChunk_total hm hLm

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

lemma exists_coarseChunk {L m t : Nat} (hm : 0 < m)
    (hLm : m * m ≤ L) (ht : t < L) :
    ∃ j : Fin (L / m), ∃ i : Nat,
      i < coarseChunkLength m (L % m) j ∧
      t = coarseChunkStart m (L % m) j + i := by
  let n := L / m
  let b := L % m
  have hdecomp : L = n * m + b := by
    calc
      L = m * (L / m) + L % m := (Nat.div_add_mod L m).symm
      _ = (L / m) * m + L % m := by rw [Nat.mul_comm m (L / m)]
      _ = n * m + b := by rfl
  have hbn : b ≤ n := coarse_remainder_le_quotient hm hLm
  by_cases hfront : t < b * (m + 1)
  · let j : Fin n := ⟨t / (m + 1), by
      have hjb : t / (m + 1) < b :=
        (Nat.div_lt_iff_lt_mul (by omega : 0 < m + 1)).2 hfront
      exact hjb.trans_le hbn⟩
    let i := t % (m + 1)
    have hjb : (j : Nat) < b :=
      (Nat.div_lt_iff_lt_mul (by omega : 0 < m + 1)).2 hfront
    have hjb' : (j : Nat) < L % m := by simpa [b] using hjb
    refine ⟨j, i, ?_, ?_⟩
    · simpa [coarseChunkLength, hjb', i] using Nat.mod_lt t (by omega : 0 < m + 1)
    · have htdiv : t = t / (m + 1) * (m + 1) + t % (m + 1) := by
        calc
          t = (m + 1) * (t / (m + 1)) + t % (m + 1) :=
            (Nat.div_add_mod t (m + 1)).symm
          _ = t / (m + 1) * (m + 1) + t % (m + 1) := by
            rw [Nat.mul_comm (m + 1) (t / (m + 1))]
      rw [coarseChunkStart, min_eq_left hjb'.le]
      dsimp only [j, i]
      calc
        t = t / (m + 1) * (m + 1) + t % (m + 1) := htdiv
        _ = t / (m + 1) * m + t / (m + 1) + t % (m + 1) := by ring
  · have hback : b * (m + 1) ≤ t := Nat.le_of_not_gt hfront
    let u := t - b * (m + 1)
    have hu : u < (n - b) * m := by
      have hrewrite : L = b * (m + 1) + (n - b) * m := by
        calc
          L = n * m + b := hdecomp
          _ = ((n - b) + b) * m + b := by rw [Nat.sub_add_cancel hbn]
          _ = b * (m + 1) + (n - b) * m := by ring
      dsimp only [u]
      omega
    let j : Fin n := ⟨b + u / m, by
      have huq : u / m < n - b := (Nat.div_lt_iff_lt_mul hm).2 hu
      omega⟩
    let i := u % m
    have hbj : b ≤ (j : Nat) := by simp [j]
    have hbj' : L % m ≤ (j : Nat) := by simpa [b] using hbj
    refine ⟨j, i, ?_, ?_⟩
    · simpa [coarseChunkLength, Nat.not_lt.mpr hbj', i] using Nat.mod_lt u hm
    · have htu : t = b * (m + 1) + u := by dsimp only [u]; omega
      have hmod : u = u / m * m + u % m := by
        calc
          u = m * (u / m) + u % m := (Nat.div_add_mod u m).symm
          _ = u / m * m + u % m := by rw [Nat.mul_comm m (u / m)]
      rw [htu, hmod, coarseChunkStart, min_eq_right hbj']
      dsimp only [j, i]
      ring

lemma coarseChunk_unique {L m t : Nat}
    (j j' : Fin (L / m)) (i i' : Nat)
    (hi : i < coarseChunkLength m (L % m) j)
    (hi' : i' < coarseChunkLength m (L % m) j')
    (ht : t = coarseChunkStart m (L % m) j + i)
    (ht' : t = coarseChunkStart m (L % m) j' + i') : j = j' := by
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hj | hj
  · have hlt : t < coarseChunkStart m (L % m) j' := by
      calc
        t = coarseChunkStart m (L % m) j + i := ht
        _ < coarseChunkStart m (L % m) j +
            coarseChunkLength m (L % m) j := Nat.add_lt_add_left hi _
        _ = coarseChunkStart m (L % m) (j + 1) := coarseChunk_end _ _ _
        _ ≤ coarseChunkStart m (L % m) j' := by
          apply coarseChunkStart_mono
          omega
    rw [ht'] at hlt
    omega
  · have hlt : t < coarseChunkStart m (L % m) j := by
      calc
        t = coarseChunkStart m (L % m) j' + i' := ht'
        _ < coarseChunkStart m (L % m) j' +
            coarseChunkLength m (L % m) j' := Nat.add_lt_add_left hi' _
        _ = coarseChunkStart m (L % m) (j' + 1) := coarseChunk_end _ _ _
        _ ≤ coarseChunkStart m (L % m) j := by
          apply coarseChunkStart_mono
          omega
    rw [ht] at hlt
    omega

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
