import GowersSzemeredi.Proofs07CeilingPartition
import GowersSzemeredi.Proofs16BaseCaseLongBoxTransport

/-!
# Transporting an affine partition to a modular progression

A proper modular progression is identified with its integer index interval.
The existing one-dimensional box transport supplies injectivity, cardinality,
and Freiman pullback. Over a prime modulus, nonzero cell steps allow the affine
formulas in cell indices to be rewritten as affine formulas in the original
modular coordinate.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Finset

namespace LeanProofs.GowersSzemeredi

/-- A modular progression viewed as a one-dimensional box. -/
def ModAP.asBox {N : Nat} (P : ModAP N) : Box N 1 where
  axis := fun _ ↦ P
  commonDiff := P.step
  axis_step := fun _ ↦ rfl

/-- Lift a scalar domain to the one-dimensional point representation. -/
def liftScalarDomain {N : Nat} (A : Finset (ZMod N)) : Finset (Point N 1) :=
  A.map (BaseCase.pointOneEquiv N).symm.toEmbedding

@[simp] theorem mem_liftScalarDomain {N : Nat} (A : Finset (ZMod N))
    (x : Point N 1) : x ∈ liftScalarDomain A ↔ x 0 ∈ A := by
  classical
  simp [liftScalarDomain, BaseCase.pointOneEquiv]

/-- Membership in a one-dimensional box is membership of its sole coordinate. -/
theorem mem_constant_box_one {N : Nat} [NeZero N] (P : Box N 1) (x : ZMod N) :
    (fun _ : Fin 1 ↦ x) ∈ P.carrier ↔ x ∈ (P.axis 0).carrier := by
  classical
  constructor
  · intro hx
    exact (Finset.mem_filter.mp hx).2 0
  · intro hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro i
    fin_cases i
    exact hx

/-- Project a one-dimensional box partition onto the original scalar axis. -/
theorem box_one_partition_axes {N M : Nat} [NeZero N]
    (P : Box N 1) (Q : Fin M → Box N 1) (hQ : IsBoxPartition Q P) :
    IsPartition (fun j ↦ ((Q j).axis 0).carrier) (P.axis 0).carrier := by
  classical
  constructor
  · intro x
    have h := hQ.1 (fun _ : Fin 1 ↦ x)
    simpa only [mem_constant_box_one] using h
  · intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    exact Finset.disjoint_left.mp (hQ.2 i j hij)
      ((mem_constant_box_one (Q i) x).mpr hxi)
      ((mem_constant_box_one (Q j) x).mpr hxj)

/-- An affine formula in the integer cell coordinate becomes an affine
formula on the modular cell when its step is nonzero. -/
theorem indexCell_scalar_linear {N : Nat} [Fact N.Prime]
    (P : Box N 1) (S : IntAP) (A : Finset (ZMod N)) (phi : ZMod N → ZMod N)
    (hsub : S.carrier ⊆ (BaseCase.boxOneIndexAP P).carrier)
    (hstep : ((BaseCase.indexCellBox P S).axis 0).step ≠ 0)
    (hlinear : IntAPLinearOn S (BaseCase.boxOneIndexDomain P (liftScalarDomain A))
      (BaseCase.boxOneIndexMap P (fun x ↦ phi (x 0)))) :
    LinearOn (((BaseCase.indexCellBox P S).axis 0).carrier.filter fun x ↦ x ∈ A) phi := by
  classical
  obtain ⟨a, b, hab⟩ := hlinear
  let d := ((BaseCase.indexCellBox P S).axis 0).step
  let start := ((BaseCase.indexCellBox P S).axis 0).start
  refine ⟨a * d⁻¹, b - a * d⁻¹ * start, ?_⟩
  intro x hx
  obtain ⟨hxQ, hxA⟩ := Finset.mem_filter.mp hx
  have hxBox := (mem_constant_box_one (BaseCase.indexCellBox P S) x).mpr hxQ
  rw [BaseCase.indexCellBox_carrier] at hxBox
  obtain ⟨z, hzS, hzx⟩ := Finset.mem_image.mp hxBox
  rw [IntAP.carrier] at hzS
  obtain ⟨i, hi, hiz⟩ := Finset.mem_image.mp hzS
  have hpoint : BaseCase.boxOneIntPoint P (S.start + ((i : Nat) * S.step : Nat)) =
      (fun _ : Fin 1 ↦ x) := (congrArg (BaseCase.boxOneIntPoint P) hiz).trans hzx
  have hzA : S.start + ((i : Nat) * S.step : Nat) ∈
      BaseCase.boxOneIndexDomain P (liftScalarDomain A) := by
    apply Finset.mem_filter.mpr
    refine ⟨hsub (Finset.mem_image.mpr ⟨i, hi, rfl⟩), ?_⟩
    rw [hpoint, mem_liftScalarDomain]
    exact hxA
  have hvalue := hab i hzA
  have hcalc := BaseCase.indexCellAffine_value P S a b i hstep
  rw [hpoint] at hcalc
  change phi ((BaseCase.boxOneIntPoint P (S.start + ((i : Nat) * S.step : Nat))) 0) =
    a * (i : Nat) + b at hvalue
  rw [hpoint] at hvalue
  have hxeq : phi x = BaseCase.indexCellAffine P S a b (fun _ : Fin 1 ↦ x) :=
    hvalue.trans hcalc.symm
  rw [hxeq]
  dsimp only [BaseCase.indexCellAffine, d, start, BaseCase.indexCellBox]
  ring

/-- Corollary 7.11 on a proper modular progression, retaining the full
real-power lower length bound and explicit rounding-safe threshold. -/
theorem corollary_7_11_modular (N : Nat) [Fact N.Prime]
    (R : ModAP N) (A : Finset (ZMod N)) (phi : ZMod N → ZMod N) (alpha : Real)
    (hR : R.IsProper) (hl : 0 < R.length) (hα : 0 < alpha) (hαone : alpha ≤ 1)
    (hA : A ⊆ R.carrier) (hdensity : alpha * R.length ≤ A.card)
    (hfreiman : FreimanHom 8 A phi)
    (hlarge : 4096 * Real.pi / alpha ≤ (R.length : Real) ^ cor711Exponent alpha 1) :
    ∃ M : Nat, ∃ Q : Fin M → ModAP N,
      IsPartition (fun j ↦ (Q j).carrier) R.carrier ∧
      (∀ j, (Q j).step != 0 ∧ (Q j).IsProper ∧
        (R.length : Real) ^ cor711Exponent alpha 1 ≤ (Q j).length ∧
        LinearOn ((Q j).carrier.filter fun x ↦ x ∈ A) phi) := by
  classical
  let P := R.asBox
  let B := liftScalarDomain A
  let U := BaseCase.boxOneIndexAP P
  let C := BaseCase.boxOneIndexDomain P B
  let psi := BaseCase.boxOneIndexMap P (fun x ↦ phi (x 0))
  have hP : P.IsProper := fun _ ↦ hR
  have hwidth : P.width = R.length := BaseCase.boxOne_width P
  have hUlength : U.length = R.length := hwidth
  have hBsub : B ⊆ P.carrier := by
    intro x hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro i
    fin_cases i
    exact hA ((mem_liftScalarDomain A x).mp hx)
  have hCcard : C.card = A.card := by
    rw [BaseCase.boxOneIndexDomain_card P hP B, Finset.inter_eq_left.mpr hBsub]
    simp [B, liftScalarDomain]
  have hBdomain : BaseCase.pointOneDomain B = A := by
    ext x
    rw [BaseCase.mem_pointOneDomain]
    simp [B, BaseCase.pointOneEquiv]
  have hCfreiman : FreimanHom 8 C psi := by
    apply BaseCase.boxOneIndex_freiman
    change FreimanHom 8 (BaseCase.pointOneDomain B) phi
    rw [hBdomain]
    exact hfreiman
  obtain ⟨M, T, hTpart, hTcell, hTstep, hTlinear⟩ :=
    corollary_7_11_real_lower_bound N 1 U (fun _ ↦ C) (fun _ ↦ psi) alpha
      (by norm_num) hα (by simpa only [hUlength] using hl)
      (BaseCase.boxOneIndexAP_proper P)
      (fun _ ↦ ⟨BaseCase.boxOneIndexDomain_subset P B,
        by simpa only [hUlength, hCcard] using hdensity, hCfreiman⟩)
      (by simpa only [hUlength] using hlarge)
  let Q : Fin M → ModAP N := fun j ↦ (BaseCase.indexCellBox P (T j)).axis 0
  have hQproper (j : Fin M) : (Q j).IsProper :=
    BaseCase.indexCellBox_proper P hP (T j) (hTcell j).1 (hTpart.cell_subset j) 0
  have hXtwo : (2 : Real) < (R.length : Real) ^ cor711Exponent alpha 1 := by
    have hC : (2 : Real) < 4096 * Real.pi / alpha := by
      apply (lt_div_iff₀ hα).mpr
      have hpi := Real.pi_gt_three
      nlinarith
    exact hC.trans_le hlarge
  have hQstep (j : Fin M) : (Q j).step ≠ 0 :=
    BaseCase.proper_modAP_step_ne_zero_of_two_le (Q j) (hQproper j) (by
      have hlen : (2 : Real) < (T j).length :=
        hXtwo.trans_le (by simpa only [hUlength] using (hTcell j).2)
      have hlenNat : 2 < (T j).length := by exact_mod_cast hlen
      change 2 ≤ (T j).length
      omega)
  refine ⟨M, Q, ?_, ?_⟩
  · exact box_one_partition_axes P (fun j ↦ BaseCase.indexCellBox P (T j))
      (BaseCase.indexCells_partition P hP T hTpart)
  · intro j
    refine ⟨bne_iff_ne.mpr (hQstep j), hQproper j, ?_, ?_⟩
    · exact (show (R.length : Real) ^ cor711Exponent alpha 1 ≤ (T j).length by
        simpa only [hUlength] using (hTcell j).2)
    · exact indexCell_scalar_linear P (T j) A phi (hTpart.cell_subset j) (hQstep j)
        (hTlinear (0 : Fin 1) j)

end LeanProofs.GowersSzemeredi
