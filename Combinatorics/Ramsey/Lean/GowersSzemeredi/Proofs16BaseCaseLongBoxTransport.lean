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
    rw [IntAP.carrier, Finset.card_image_iff.mpr]
    · simp only [Finset.card_univ, Fintype.card_fin]
    · intro i _ j _ hij
      apply Fin.ext
      simpa [boxOneIndexAP] using hij

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
  have himg : P.carrier = (boxOneIndexAP P).carrier.image (boxOneIntPoint P) := by
    rw [boxOne_carrier_eq_image, IntAP.carrier, Finset.image_image]
    exact Finset.image_congr fun i _ => by simp [boxOneIndexAP, boxOneIntPoint_of_nat]
  rw [Finset.inter_comm, himg, ← Finset.filter_mem_eq_inter, Finset.filter_image,
    Finset.card_image_of_injOn]
  · rfl
  · exact (boxOneIntPoint_injective_on_indexAP P hP).mono
      (Finset.coe_subset.2 (Finset.filter_subset _ _))

lemma boxOneIndex_freiman {N : Nat} [NeZero N]
    (P : Box N 1) (B : Finset (Point N 1))
    (phi : Point N 1 → ZMod N)
    (hphi : FreimanHom 8 (pointOneDomain B) (pointOneMap phi)) :
    FreimanHom 8 (boxOneIndexDomain P B) (boxOneIndexMap P phi) := by
  let f : Int → ZMod N := fun z =>
    (P.axis 0).start + (z : ZMod N) * (P.axis 0).step
  have hpoint (z : Int) :
      (pointOneEquiv N).symm (f z) = boxOneIntPoint P z := by abel
  have hf : IsAddFreimanHom 8 (boxOneIndexDomain P B : Set Int)
      (pointOneDomain B : Set (ZMod N)) f := by
    refine ⟨?_, ?_⟩
    · intro z hz
      change f z ∈ pointOneDomain B
      rw [mem_pointOneDomain]
      have hzB := (Finset.mem_filter.mp hz).2
      rw [hpoint z]
      exact hzB
    · intro s t _ _ hsc htc hsum
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
  have hfun : pointOneMap phi ∘ f = boxOneIndexMap P phi := by abel
  rw [hfun] at hcomp
  rw [FreimanHom]
  exact hcomp

def indexCellBox {N : Nat} (P : Box N 1) (S : IntAP) : Box N 1 where
  axis := fun _ =>
    { start := (P.axis 0).start + (S.start : ZMod N) * (P.axis 0).step
      step := (S.step : ZMod N) * (P.axis 0).step
      length := S.length }
  commonDiff := (S.step : ZMod N) * P.commonDiff
  axis_step := by intro _; rw [P.axis_step 0]

@[simp] lemma indexCellBox_width {N : Nat} (P : Box N 1) (S : IntAP) :
    (indexCellBox P S).width = S.length := by
  simp [indexCellBox, Box.width]

lemma indexCellBox_carrier {N : Nat} [NeZero N]
    (P : Box N 1) (S : IntAP) :
    (indexCellBox P S).carrier = S.carrier.image (boxOneIntPoint P) := by
  ext x
  simp only [Box.carrier, indexCellBox, ModAP.carrier, IntAP.carrier, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_image, Fin.forall_fin_one, exists_exists_eq_and,
    boxOneIntPoint, funext_iff]
  refine exists_congr fun i => ?_
  push_cast
  constructor <;> intro h <;> rw [← h] <;> ring

lemma indexCellBox_proper {N : Nat} [NeZero N]
    (P : Box N 1) (hP : P.IsProper) (S : IntAP)
    (hS : S.IsProper) (hsub : S.carrier ⊆ (boxOneIndexAP P).carrier) :
    (indexCellBox P S).IsProper := by
  intro i
  fin_cases i
  rw [ModAP.IsProper]
  have hcardBox : (indexCellBox P S).carrier.card = S.carrier.card := by
    rw [indexCellBox_carrier, Finset.card_image_iff.mpr]
    intro x hx y hy hxy
    exact boxOneIntPoint_injective_on_indexAP P hP (hsub hx) (hsub hy) hxy
  have hScard : S.carrier.card = S.length := hS.2
  exact (boxOne_carrier_card_eq_axis_card (indexCellBox P S)).symm.trans
    (hcardBox.trans hScard)

lemma indexCells_partition {N M : Nat} [NeZero N]
    (P : Box N 1) (hP : P.IsProper) (S : Fin M → IntAP)
    (hS : IsIntAPPartition S (boxOneIndexAP P)) :
    IsBoxPartition (fun j => indexCellBox P (S j)) P := by
  have himg : P.carrier = (boxOneIndexAP P).carrier.image (boxOneIntPoint P) := by
    rw [boxOne_carrier_eq_image, IntAP.carrier, Finset.image_image]
    exact Finset.image_congr fun i _ => by simp [boxOneIndexAP, boxOneIntPoint_of_nat]
  refine ⟨fun x => ?_, fun i j hij => ?_⟩
  · simp only [himg, indexCellBox_carrier, Finset.mem_image, hS.1]
    exact ⟨fun ⟨z, ⟨j, hz⟩, h⟩ => ⟨j, z, hz, h⟩, fun ⟨j, z, hz, h⟩ => ⟨z, ⟨j, hz⟩, h⟩⟩
  · simp only [indexCellBox_carrier, Finset.disjoint_left, Finset.mem_image]
    rintro x ⟨z, hz, rfl⟩ ⟨w, hw, hwz⟩
    obtain rfl := boxOneIntPoint_injective_on_indexAP P hP (hS.cell_subset j hw)
      (hS.cell_subset i hz) hwz
    exact Finset.disjoint_left.mp (hS.2 i j hij) hz hw

lemma isMultilinear_affine_one {N : Nat} (a b : ZMod N) :
    IsMultilinear (fun x : Point N 1 => a * x 0 + b) := by
  refine ⟨fun e => if e 0 then a else b, fun x => ?_⟩
  rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp]
  simp

lemma proper_modAP_step_ne_zero_of_two_le {N : Nat}
    (P : ModAP N) (hP : P.IsProper) (hL : 2 ≤ P.length) : P.step ≠ 0 := by
  intro hstep
  have hcarrier : P.carrier = {P.start} := by
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
      (i : ZMod N) * ((S.step : ZMod N) * (P.axis 0).step) := by push_cast; ring
  rw [hcoord]
  change a * d⁻¹ * ((i : ZMod N) * d) + b = a * (i : Nat) + b
  calc
    a * d⁻¹ * ((i : ZMod N) * d) + b =
        a * (i : ZMod N) * (d⁻¹ * d) + b := by ring
    _ = a * (i : Nat) + b := by rw [inv_mul_cancel₀ hd']; ring

end LeanProofs.GowersSzemeredi.BaseCase
