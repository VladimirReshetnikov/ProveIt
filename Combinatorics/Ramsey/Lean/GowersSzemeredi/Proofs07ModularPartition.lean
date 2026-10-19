import GowersSzemeredi.Proofs07CeilingPartition
import GowersSzemeredi.Proofs16BaseCaseLongBoxTransport

/-!
# Transporting an affine partition to a modular progression

A proper modular progression is identified with its integer index interval.
The existing one-dimensional box transport supplies injectivity, cardinality,
and Freiman pullback. Over a prime modulus, nonzero cell steps allow the affine
formulas in cell indices to be rewritten as affine formulas in the original
modular coordinate.

`corollary_7_11_constant_modular` and `corollary_7_11_modular` are in
`Proofs07ModularPartitionSide`, outside the final route. -/

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
  simp [liftScalarDomain, BaseCase.pointOneEquiv]

/-- Membership in a one-dimensional box is membership of its sole coordinate. -/
theorem mem_constant_box_one {N : Nat} [NeZero N] (P : Box N 1) (x : ZMod N) :
    (fun _ : Fin 1 ↦ x) ∈ P.carrier ↔ x ∈ (P.axis 0).carrier := by
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
  obtain ⟨a, b, hab⟩ := hlinear
  let d := ((BaseCase.indexCellBox P S).axis 0).step
  let start := ((BaseCase.indexCellBox P S).axis 0).start
  refine ⟨a * d⁻¹, b - a * d⁻¹ * start, fun x hx => ?_⟩
  obtain ⟨hxQ, hxA⟩ := Finset.mem_filter.mp hx
  have hxBox := (mem_constant_box_one (BaseCase.indexCellBox P S) x).mpr hxQ
  rw [BaseCase.indexCellBox_carrier] at hxBox
  -- `x` is the image of the integer `S.start + i * S.step` of the cell `S`
  obtain ⟨z, hzS, hzx⟩ := Finset.mem_image.mp hxBox
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hzS
  have hvalue := hab i (Finset.mem_filter.mpr
    ⟨hsub hzS, by rw [hzx, mem_liftScalarDomain]; exact hxA⟩)
  have hcalc := BaseCase.indexCellAffine_value P S a b i hstep
  simp only [BaseCase.boxOneIndexMap, hzx] at hvalue hcalc
  rw [hvalue, ← hcalc]
  dsimp only [BaseCase.indexCellAffine, d, start, BaseCase.indexCellBox]
  ring

end LeanProofs.GowersSzemeredi
