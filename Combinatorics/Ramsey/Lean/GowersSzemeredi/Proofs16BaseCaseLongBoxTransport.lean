import GowersSzemeredi.Proofs07SimultaneousLinearity
import GowersSzemeredi.Proofs16BaseCaseCoarsePartition

/-!
# Transporting the long-box branch of Lemma 16.3

This module identifies a proper one-dimensional modular box with its integer
index progression.  Integer progression cells transport back to proper modular
subboxes, and affine maps on the index cells transport to multilinear maps on
those subboxes.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi.BaseCase

def boxOneIndexAP {N : Nat} (P : Box N 1) : IntAP where
  start := 0
  step := 1
  length := P.width

def boxOneIntPoint {N : Nat} (P : Box N 1) (z : Int) : Point N 1 :=
  fun _ => (P.axis 0).start + (z : ZMod N) * (P.axis 0).step

noncomputable def boxOneIndexDomain {N : Nat} [NeZero N]
    (P : Box N 1) (B : Finset (Point N 1)) : Finset Int :=
  (boxOneIndexAP P).carrier.filter fun z => boxOneIntPoint P z ∈ B

def boxOneIndexMap {N : Nat} (P : Box N 1)
    (phi : Point N 1 → ZMod N) : Int → ZMod N :=
  fun z => phi (boxOneIntPoint P z)

lemma boxOneIndexAP_proper {N : Nat} (P : Box N 1) :
    (boxOneIndexAP P).IsProper := by
  constructor
  · simp [boxOneIndexAP]
  · classical
    rw [IntAP.carrier]
    rw [Finset.card_image_iff.mpr]
    · simp only [Finset.card_univ, Fintype.card_fin]
    · intro i _ j _ hij
      apply Fin.ext
      simpa [boxOneIndexAP] using hij

lemma boxOneIndexAP_length {N : Nat} (P : Box N 1) :
    (boxOneIndexAP P).length = P.width := rfl

lemma boxOneIndexDomain_subset {N : Nat} [NeZero N]
    (P : Box N 1) (B : Finset (Point N 1)) :
    boxOneIndexDomain P B ⊆ (boxOneIndexAP P).carrier := by
  intro z hz
  exact (Finset.mem_filter.mp hz).1

lemma boxOneIntPoint_of_nat {N : Nat} (P : Box N 1) (i : Nat) :
    boxOneIntPoint P i = boxOnePoint P i := by
  funext j
  fin_cases j
  simp [boxOneIntPoint, boxOnePoint]

lemma boxOneIntPoint_injective_on_indexAP {N : Nat} [NeZero N]
    (P : Box N 1) (hP : P.IsProper) :
    Set.InjOn (boxOneIntPoint P) (boxOneIndexAP P).carrier := by
  intro x hx y hy hxy
  rw [IntAP.carrier] at hx hy
  obtain ⟨i, _hi, hix⟩ := Finset.mem_image.mp hx
  obtain ⟨j, _hj, hjy⟩ := Finset.mem_image.mp hy
  subst x
  subst y
  simp only [boxOneIndexAP, zero_add, Nat.mul_one] at hxy ⊢
  have hnat := boxOnePoint_injective P hP i.isLt j.isLt (by
    simpa [boxOneIntPoint_of_nat] using hxy)
  simp [hnat]

lemma boxOneIndexDomain_card {N : Nat} [NeZero N]
    (P : Box N 1) (hP : P.IsProper) (B : Finset (Point N 1)) :
    (boxOneIndexDomain P B).card = (B ∩ P.carrier).card := by
  classical
  let f := boxOneIntPoint P
  have hinj : Set.InjOn f (boxOneIndexDomain P B) :=
    (boxOneIntPoint_injective_on_indexAP P hP).mono
      (fun z hz => (Finset.mem_filter.mp hz).1)
  have himage : (boxOneIndexDomain P B).image f = B ∩ P.carrier := by
    ext x
    constructor
    · intro hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have hz' := Finset.mem_filter.mp hz
      refine Finset.mem_inter.mpr ⟨hz'.2, ?_⟩
      rw [boxOne_carrier_eq_image]
      rw [IntAP.carrier] at hz'
      obtain ⟨i, _hi, hiz⟩ := Finset.mem_image.mp hz'.1
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_univ i, ?_⟩
      simpa [f, boxOneIndexAP, boxOneIntPoint_of_nat] using
        congrArg (boxOneIntPoint P) hiz
    · intro hx
      have hx' := Finset.mem_inter.mp hx
      rw [boxOne_carrier_eq_image] at hx'
      obtain ⟨i, _hi, hix⟩ := Finset.mem_image.mp hx'.2
      rw [Finset.mem_image]
      refine ⟨(i : Int), ?_, ?_⟩
      · rw [boxOneIndexDomain, Finset.mem_filter]
        constructor
        · rw [IntAP.carrier]
          apply Finset.mem_image.mpr
          exact ⟨i, Finset.mem_univ i, by simp [boxOneIndexAP]⟩
        · simpa [f, boxOneIntPoint_of_nat, hix] using hx'.1
      · simpa [f, boxOneIntPoint_of_nat] using hix
  rw [← himage, Finset.card_image_iff.mpr]
  intro x hx y hy hxy
  exact hinj hx hy hxy

lemma boxOneIndex_freiman {N : Nat} [NeZero N]
    (P : Box N 1) (B : Finset (Point N 1))
    (phi : Point N 1 → ZMod N)
    (hphi : FreimanHom 8 (pointOneDomain B) (pointOneMap phi)) :
    FreimanHom 8 (boxOneIndexDomain P B) (boxOneIndexMap P phi) := by
  let f : Int → ZMod N := fun z =>
    (P.axis 0).start + (z : ZMod N) * (P.axis 0).step
  have hpoint (z : Int) :
      (pointOneEquiv N).symm (f z) = boxOneIntPoint P z := by
    funext i
    fin_cases i
    rfl
  have hf : IsAddFreimanHom 8 (boxOneIndexDomain P B : Set Int)
      (pointOneDomain B : Set (ZMod N)) f := by
    refine ⟨?_, ?_⟩
    · intro z hz
      change f z ∈ pointOneDomain B
      rw [mem_pointOneDomain]
      have hzB := (Finset.mem_filter.mp hz).2
      rw [hpoint z]
      exact hzB
    · intro s t hs ht hsc htc hsum
      have hsum_f (u : Multiset Int) :
          (u.map f).sum =
            (u.card : ZMod N) * (P.axis 0).start +
              ((u.sum : Int) : ZMod N) * (P.axis 0).step := by
        induction u using Multiset.induction_on with
        | empty => simp
        | cons z u ihu =>
            simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
            rw [ihu]
            push_cast
            dsimp only [f]
            ring
      have hcast : ((s.sum : Int) : ZMod N) = (t.sum : ZMod N) := by rw [hsum]
      rw [hsum_f s, hsum_f t, hsc, htc, hcast]
  have hcomp := hphi.comp hf
  have hfun : pointOneMap phi ∘ f = boxOneIndexMap P phi := by
    funext z
    change phi ((pointOneEquiv N).symm (f z)) = phi (boxOneIntPoint P z)
    exact congrArg phi (hpoint z)
  rw [hfun] at hcomp
  rw [FreimanHom]
  exact hcomp

def indexCellBox {N : Nat} (P : Box N 1) (S : IntAP) : Box N 1 where
  axis := fun _ =>
    { start := (P.axis 0).start + (S.start : ZMod N) * (P.axis 0).step
      step := (S.step : ZMod N) * (P.axis 0).step
      length := S.length }
  commonDiff := (S.step : ZMod N) * P.commonDiff
  axis_step := by intro i; rw [P.axis_step 0]

@[simp] lemma indexCellBox_width {N : Nat} (P : Box N 1) (S : IntAP) :
    (indexCellBox P S).width = S.length := by
  simp [indexCellBox, Box.width]

lemma indexCellBox_carrier {N : Nat} [NeZero N]
    (P : Box N 1) (S : IntAP) :
    (indexCellBox P S).carrier = S.carrier.image (boxOneIntPoint P) := by
  classical
  ext x
  simp only [Box.carrier, indexCellBox, Finset.mem_filter, Finset.mem_univ,
    true_and, ModAP.carrier, IntAP.carrier, Finset.mem_image]
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := hx 0
    let z : Int := S.start + ((i : Nat) * S.step : Nat)
    refine ⟨z, ⟨i, rfl⟩, ?_⟩
    apply funext
    intro j
    fin_cases j
    calc
      boxOneIntPoint P z 0 =
          (P.axis 0).start +
            ((S.start : ZMod N) + (i : Nat) * (S.step : ZMod N)) *
              (P.axis 0).step := by
        simp [z, boxOneIntPoint, Nat.cast_mul]
      _ = ((indexCellBox P S).axis 0).start +
          (i : Nat) * ((indexCellBox P S).axis 0).step := by
        simp [indexCellBox]
        ring
      _ = x 0 := hi
  · rintro ⟨z, ⟨i, rfl⟩, rfl⟩ j
    fin_cases j
    refine ⟨i, ?_⟩
    simp [boxOneIntPoint, Nat.cast_mul]
    ring

lemma indexCellBox_proper {N : Nat} [NeZero N]
    (P : Box N 1) (hP : P.IsProper) (S : IntAP)
    (hS : S.IsProper) (hsub : S.carrier ⊆ (boxOneIndexAP P).carrier) :
    (indexCellBox P S).IsProper := by
  intro i
  fin_cases i
  rw [ModAP.IsProper]
  have hcardBox : (indexCellBox P S).carrier.card = S.carrier.card := by
    rw [indexCellBox_carrier]
    rw [Finset.card_image_iff.mpr]
    intro x hx y hy hxy
    exact boxOneIntPoint_injective_on_indexAP P hP (hsub hx) (hsub hy) hxy
  have hScard : S.carrier.card = S.length := hS.2
  exact (boxOne_carrier_card_eq_axis_card (indexCellBox P S)).symm.trans
    (hcardBox.trans hScard)

lemma indexCells_partition {N M : Nat} [NeZero N]
    (P : Box N 1) (hP : P.IsProper) (S : Fin M → IntAP)
    (hS : IsIntAPPartition S (boxOneIndexAP P)) :
    IsBoxPartition (fun j => indexCellBox P (S j)) P := by
  classical
  constructor
  · intro x
    constructor
    · intro hx
      rw [boxOne_carrier_eq_image] at hx
      obtain ⟨i, _hi, hix⟩ := Finset.mem_image.mp hx
      let z : Int := i
      have hzR : z ∈ (boxOneIndexAP P).carrier := by
        rw [IntAP.carrier]
        apply Finset.mem_image.mpr
        exact ⟨i, Finset.mem_univ i, by simp [z, boxOneIndexAP]⟩
      obtain ⟨j, hzS⟩ := (hS.1 z).mp hzR
      refine ⟨j, ?_⟩
      change x ∈ (indexCellBox P (S j)).carrier
      rw [indexCellBox_carrier]
      apply Finset.mem_image.mpr
      exact ⟨z, hzS, by simpa [z, boxOneIntPoint_of_nat] using hix⟩
    · rintro ⟨j, hxj⟩
      change x ∈ (indexCellBox P (S j)).carrier at hxj
      rw [indexCellBox_carrier] at hxj
      obtain ⟨z, hzS, hzx⟩ := Finset.mem_image.mp hxj
      have hzR := hS.cell_subset j hzS
      rw [IntAP.carrier] at hzR
      obtain ⟨i, _hi, hiz⟩ := Finset.mem_image.mp hzR
      rw [boxOne_carrier_eq_image]
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_univ i, ?_⟩
      have hiz' : (i : Int) = z := by
        simpa [boxOneIndexAP] using hiz
      calc
        boxOnePoint P i = boxOneIntPoint P i := (boxOneIntPoint_of_nat P i).symm
        _ = boxOneIntPoint P z := congrArg (boxOneIntPoint P) hiz'
        _ = x := hzx
  · intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    change x ∈ (indexCellBox P (S i)).carrier at hxi
    change x ∈ (indexCellBox P (S j)).carrier at hxj
    rw [indexCellBox_carrier] at hxi hxj
    obtain ⟨z, hzS, hzx⟩ := Finset.mem_image.mp hxi
    obtain ⟨w, hwS, hwx⟩ := Finset.mem_image.mp hxj
    have hzR := hS.cell_subset i hzS
    have hwR := hS.cell_subset j hwS
    have hzw : z = w := boxOneIntPoint_injective_on_indexAP P hP hzR hwR
      (hzx.trans hwx.symm)
    subst w
    exact Finset.disjoint_left.mp (hS.2 i j hij) hzS hwS

lemma isMultilinear_affine_one {N : Nat} (a b : ZMod N) :
    IsMultilinear (fun x : Point N 1 => a * x 0 + b) := by
  classical
  let e0 : Fin 1 → Bool := fun _ => false
  let e1 : Fin 1 → Bool := fun _ => true
  refine ⟨fun e => if e = e0 then b else if e = e1 then a else 0, ?_⟩
  intro x
  have he (e : Fin 1 → Bool) : e = e0 ∨ e = e1 := by
    by_cases h : e 0 = false
    · left
      funext i
      fin_cases i
      exact h
    · right
      funext i
      fin_cases i
      simpa using h
  have he10 : e1 ≠ e0 := by
    intro h
    have h0 := congrFun h 0
    simp [e0, e1] at h0
  rw [← Finset.sum_erase_add Finset.univ
    (fun e => (if e = e0 then b else if e = e1 then a else 0) *
      ∏ i, (if e i then x i else 1)) (Finset.mem_univ e0)]
  have hrest :
      ∑ e ∈ (Finset.univ.erase e0),
          (if e = e0 then b else if e = e1 then a else 0) *
            ∏ i, (if e i then x i else 1) = a * x 0 := by
    rw [Finset.sum_eq_single e1]
    · simp [e0, e1, he10]
    · intro e heMem hne
      have he' := he e
      rcases he' with he0 | he1
      · exact ((Finset.mem_erase.mp heMem).1 he0).elim
      · exact (hne he1).elim
    · simp [e0, e1, he10]
  rw [hrest]
  simp [e0]

lemma proper_modAP_step_ne_zero_of_two_le {N : Nat}
    (P : ModAP N) (hP : P.IsProper) (hL : 2 ≤ P.length) : P.step ≠ 0 := by
  intro hstep
  have hcarrier : P.carrier = {P.start} := by
    classical
    ext x
    simp only [ModAP.carrier, Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · rintro ⟨i, rfl⟩
      simp [hstep]
    · rintro rfl
      exact ⟨⟨0, by omega⟩, by simp [hstep]⟩
  have := hP
  rw [ModAP.IsProper, hcarrier] at this
  simp at this
  omega

def indexCellAffine {N : Nat} (P : Box N 1) (S : IntAP)
    (a b : ZMod N) : Point N 1 → ZMod N :=
  let start := (P.axis 0).start + (S.start : ZMod N) * (P.axis 0).step
  let d := (S.step : ZMod N) * (P.axis 0).step
  fun x => a * d⁻¹ * (x 0 - start) + b

lemma indexCellAffine_multilinear {N : Nat} (P : Box N 1) (S : IntAP)
    (a b : ZMod N) : IsMultilinear (indexCellAffine P S a b) := by
  let d := (S.step : ZMod N) * (P.axis 0).step
  let start := (P.axis 0).start + (S.start : ZMod N) * (P.axis 0).step
  have h := isMultilinear_affine_one (a * d⁻¹) (b - a * d⁻¹ * start)
  convert h using 1
  funext x
  simp [indexCellAffine, d, start]
  ring

lemma indexCellAffine_value {N : Nat} [Fact N.Prime]
    (P : Box N 1) (S : IntAP)
    (a b : ZMod N) (i : Fin S.length)
    (hd : (S.step : ZMod N) * (P.axis 0).step ≠ 0) :
    indexCellAffine P S a b
        (boxOneIntPoint P (S.start + ((i : Nat) * S.step : Nat))) =
      a * (i : Nat) + b := by
  let d : ZMod N := (S.step : ZMod N) * (P.axis 0).step
  have hd' : d ≠ 0 := by simpa only [d] using hd
  dsimp only [indexCellAffine, boxOneIntPoint]
  have hcoord :
      (P.axis 0).start +
          ((S.start + ((i : Nat) * S.step : Nat) : Int) : ZMod N) *
            (P.axis 0).step -
        ((P.axis 0).start + (S.start : ZMod N) * (P.axis 0).step) =
      (i : ZMod N) * ((S.step : ZMod N) * (P.axis 0).step) := by
    push_cast
    ring
  rw [hcoord]
  change a * d⁻¹ * ((i : ZMod N) * d) + b = a * (i : Nat) + b
  calc
    a * d⁻¹ * ((i : ZMod N) * d) + b =
        a * (i : ZMod N) * (d⁻¹ * d) + b := by ring
    _ = a * (i : Nat) + b := by rw [inv_mul_cancel₀ hd']; ring

end LeanProofs.GowersSzemeredi.BaseCase
