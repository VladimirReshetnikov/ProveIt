import PolynomialFormulas.LazardInvariantProjectionBlocks
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Constant diagonal blocks of a graded projection

The diagonal blocks in the degree-triangular Reynolds matrix have entries in
the ground field.  This file isolates the required linear algebra.  An
idempotent over a field admits a basis adapted to its range and kernel.  After
base change, the same basis diagonalizes the extended idempotent with diagonal
entries `1` and `0`, so its fixed module is visibly finite free.

No form of Quillen--Suslin is used here: the result is special to a projection
whose matrix is obtained by scalar extension from the ground field.
-/

namespace LeanProofs.PolynomialFormulas.LazardInvariantConstantBlocks

set_option autoImplicit false

open scoped TensorProduct

noncomputable section

open LazardInvariantProjectionBlocks

variable {A M : Type*} [CommRing A]
variable [AddCommGroup M] [Module A M]

/-- A finite basis of a fixed submodule, with its finite index retained as
data for the subsequent degree-block induction. -/
structure FiniteFixedBasis (p : M →ₗ[A] M) where
  Index : Type
  indexFintype : Fintype Index
  basis : Module.Basis Index A p.fixedSubmodule

/-- Conjugate an endomorphism across a linear equivalence. -/
def conjugateEnd {N : Type*} [AddCommGroup N] [Module A N]
    (e : M ≃ₗ[A] N) (p : M →ₗ[A] M) : N →ₗ[A] N :=
  e.toLinearMap.comp (p.comp e.symm.toLinearMap)

/-- Conjugation identifies the corresponding fixed submodules. -/
def conjugateFixedSubmoduleEquiv {N : Type*}
    [AddCommGroup N] [Module A N]
    (e : M ≃ₗ[A] N) (p : M →ₗ[A] M) :
    p.fixedSubmodule ≃ₗ[A] (conjugateEnd e p).fixedSubmodule where
  toFun x := ⟨e x.1, by
    rw [LinearMap.mem_fixedSubmodule_iff]
    have hx : p x.1 = x.1 := by
      rw [← LinearMap.mem_fixedSubmodule_iff]
      exact x.2
    simp [conjugateEnd, hx]⟩
  invFun y := ⟨e.symm y.1, by
    rw [LinearMap.mem_fixedSubmodule_iff]
    apply e.injective
    have hy : conjugateEnd e p y.1 = y.1 := by
      rw [← LinearMap.mem_fixedSubmodule_iff]
      exact y.2
    simpa [conjugateEnd] using hy⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' r x := by
    apply Subtype.ext
    simp

/-- Conjugation also identifies the ranges of the two endomorphisms. -/
def conjugateRangeEquiv {N : Type*}
    [AddCommGroup N] [Module A N]
    (e : M ≃ₗ[A] N) (p : M →ₗ[A] M) :
    LinearMap.range p ≃ₗ[A] LinearMap.range (conjugateEnd e p) where
  toFun x := ⟨e x.1, by
    rcases x.2 with ⟨y, hy⟩
    refine ⟨e y, ?_⟩
    simpa [conjugateEnd] using congrArg e hy⟩
  invFun y := ⟨e.symm y.1, by
    rcases y.2 with ⟨x, hx⟩
    refine ⟨e.symm x, ?_⟩
    apply e.injective
    simpa [conjugateEnd] using hx⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' r x := by
    apply Subtype.ext
    simp

/-- If an endomorphism is the identity on the left half of a basis and zero
on the right half, the left basis vectors form a basis of its fixed module. -/
def fixedSubmoduleBasisOfDiagonalBasis {L R : Type*}
    (b : Module.Basis (L ⊕ R) A M) (p : M →ₗ[A] M)
    (hp : IsIdempotentElem p)
    (hleft : ∀ i : L, p (b (Sum.inl i)) = b (Sum.inl i))
    (hright : ∀ j : R, p (b (Sum.inr j)) = 0) :
    Module.Basis L A p.fixedSubmodule := by
  let v : L → M := fun i => b (Sum.inl i)
  have hv : LinearIndependent A v :=
    b.linearIndependent.comp Sum.inl Sum.inl_injective
  let S : Submodule A M := Submodule.span A (Set.range v)
  have hrange : LinearMap.range p = S := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      rw [← b.linearCombination_repr x]
      rw [Finsupp.linearCombination_apply]
      change p ((b.repr x).support.sum fun i =>
        b.repr x i • b i) ∈ S
      rw [map_sum]
      apply Submodule.sum_mem
      intro i hi
      rw [map_smul]
      rcases i with i | j
      · rw [hleft]
        exact Submodule.smul_mem S _
          (Submodule.subset_span (Set.mem_range_self i))
      · rw [hright, smul_zero]
        exact S.zero_mem
    · apply Submodule.span_le.2
      rintro _ ⟨i, rfl⟩
      exact ⟨b (Sum.inl i), hleft i⟩
  let bs : Module.Basis L A S := Module.Basis.span hv
  exact bs.map (LinearEquiv.ofEq _ _
    (hrange.symm.trans (range_eq_fixedSubmodule p hp)))

@[simp]
theorem fixedSubmoduleBasisOfDiagonalBasis_apply {L R : Type*}
    (b : Module.Basis (L ⊕ R) A M) (p : M →ₗ[A] M)
    (hp : IsIdempotentElem p)
    (hleft : ∀ i : L, p (b (Sum.inl i)) = b (Sum.inl i))
    (hright : ∀ j : R, p (b (Sum.inr j)) = 0) (i : L) :
    (fixedSubmoduleBasisOfDiagonalBasis b p hp hleft hright i).1 =
      b (Sum.inl i) := by
  simp [fixedSubmoduleBasisOfDiagonalBasis, Module.Basis.map_apply,
    Module.Basis.coe_span_apply, LinearEquiv.coe_ofEq_apply]

section Field

variable {k V : Type*} [Field k]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- A field basis adapted to the direct-sum decomposition
`V = range p ⊕ ker p` of an idempotent. -/
def adaptedProjectionBasis (p : V →ₗ[k] V) (hp : IsIdempotentElem p) :
    Module.Basis
      (Fin (Module.finrank k (LinearMap.range p)) ⊕
        Fin (Module.finrank k (LinearMap.ker p))) k V :=
    ((Module.finBasis k (LinearMap.range p)).prod
      (Module.finBasis k (LinearMap.ker p))).map
    ((LinearMap.range p).prodEquivOfIsCompl (LinearMap.ker p)
      (LinearMap.IsIdempotentElem.isProj_range p hp).isCompl)

@[simp]
theorem adaptedProjectionBasis_apply_inl
    (p : V →ₗ[k] V) (hp : IsIdempotentElem p)
    (i : Fin (Module.finrank k (LinearMap.range p))) :
    p (adaptedProjectionBasis p hp (Sum.inl i)) =
      adaptedProjectionBasis p hp (Sum.inl i) := by
  have hi : p ((Module.finBasis k (LinearMap.range p) i).1) =
      (Module.finBasis k (LinearMap.range p) i).1 :=
    (LinearMap.IsIdempotentElem.isProj_range p hp).mem_iff_map_id.mp
      (Module.finBasis k (LinearMap.range p) i).2
  simpa [adaptedProjectionBasis, Module.Basis.map_apply,
    Submodule.coe_prodEquivOfIsCompl'] using hi

@[simp]
theorem adaptedProjectionBasis_apply_inr
    (p : V →ₗ[k] V) (hp : IsIdempotentElem p)
    (j : Fin (Module.finrank k (LinearMap.ker p))) :
    p (adaptedProjectionBasis p hp (Sum.inr j)) = 0 := by
  have hj : p ((Module.finBasis k (LinearMap.ker p) j).1) = 0 :=
    (Module.finBasis k (LinearMap.ker p) j).2
  simpa [adaptedProjectionBasis, Module.Basis.map_apply,
    Submodule.coe_prodEquivOfIsCompl'] using hj

variable (B : Type*) [CommRing B] [Algebra k B]

/-- Base change of the range/kernel-adapted field basis. -/
def baseChangedAdaptedProjectionBasis
    (p : V →ₗ[k] V) (hp : IsIdempotentElem p) :
    Module.Basis
      (Fin (Module.finrank k (LinearMap.range p)) ⊕
        Fin (Module.finrank k (LinearMap.ker p))) B (B ⊗[k] V) :=
  Algebra.TensorProduct.basis B (adaptedProjectionBasis p hp)

@[simp]
theorem baseChangedAdaptedProjectionBasis_apply
    (p : V →ₗ[k] V) (hp : IsIdempotentElem p)
    (i : Fin (Module.finrank k (LinearMap.range p)) ⊕
      Fin (Module.finrank k (LinearMap.ker p))) :
    baseChangedAdaptedProjectionBasis B p hp i =
      1 ⊗ₜ[k] adaptedProjectionBasis p hp i := by
  simpa [baseChangedAdaptedProjectionBasis] using
    Algebra.TensorProduct.basis_apply B (adaptedProjectionBasis p hp) i

/-- The scalar extension of an idempotent remains idempotent. -/
theorem baseChange_isIdempotentElem
    (p : V →ₗ[k] V) (hp : IsIdempotentElem p) :
    IsIdempotentElem (p.baseChange B) := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b v =>
      simp only [Module.End.mul_apply, LinearMap.baseChange_tmul]
      exact congrArg (fun w => b ⊗ₜ[k] w) (DFunLike.congr_fun hp.eq v)
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The fixed module of a constant idempotent matrix is finite free after
arbitrary scalar extension.  Its basis is obtained by extending an adapted
range/kernel basis from the field. -/
def constantProjectionFixedBasis
    (p : V →ₗ[k] V) (hp : IsIdempotentElem p) :
    Module.Basis (Fin (Module.finrank k (LinearMap.range p))) B
      (p.baseChange B).fixedSubmodule :=
  fixedSubmoduleBasisOfDiagonalBasis
    (baseChangedAdaptedProjectionBasis B p hp) (p.baseChange B)
    (baseChange_isIdempotentElem B p hp)
    (fun i => by
      rw [baseChangedAdaptedProjectionBasis_apply,
        LinearMap.baseChange_tmul, adaptedProjectionBasis_apply_inl])
    (fun j => by
      rw [baseChangedAdaptedProjectionBasis_apply,
        LinearMap.baseChange_tmul, adaptedProjectionBasis_apply_inr]
      simp)

@[simp]
theorem constantProjectionFixedBasis_apply
    (p : V →ₗ[k] V) (hp : IsIdempotentElem p)
    (i : Fin (Module.finrank k (LinearMap.range p))) :
    (constantProjectionFixedBasis B p hp i).1 =
      1 ⊗ₜ[k] adaptedProjectionBasis p hp (Sum.inl i) := by
  simp [constantProjectionFixedBasis]

section MatrixDescent

variable {I N : Type*} [Fintype I]
variable [AddCommGroup N] [Module B N]

local instance : DecidableEq I := Classical.decEq I

abbrev GroundCoordinateSpace := I →₀ k

/-- The canonical scalar extension of an endomorphism of a finite coordinate
space, transported back to the same coordinate type over `B`. -/
def scalarExtensionCoordinateEnd
    (p : GroundCoordinateSpace (k := k) (I := I) →ₗ[k]
      GroundCoordinateSpace (k := k) (I := I)) :
    (I →₀ B) →ₗ[B] (I →₀ B) :=
  let e := TensorProduct.finsuppScalarRight k B B I
  conjugateEnd e (p.baseChange B)

/-- Its matrix is obtained by applying `algebraMap k B` entrywise. -/
theorem scalarExtensionCoordinateEnd_toMatrix
    (p : GroundCoordinateSpace (k := k) (I := I) →ₗ[k]
      GroundCoordinateSpace (k := k) (I := I)) :
    LinearMap.toMatrix (Finsupp.basisSingleOne (R := B))
        (Finsupp.basisSingleOne (R := B))
        (scalarExtensionCoordinateEnd B p) =
      (LinearMap.toMatrix (Finsupp.basisSingleOne (R := k))
        (Finsupp.basisSingleOne (R := k)) p).map (algebraMap k B) := by
  ext i j
  simp [scalarExtensionCoordinateEnd, conjugateEnd,
    LinearMap.toMatrix_apply, LinearMap.baseChange_tmul,
    TensorProduct.finsuppScalarRight_symm_apply_single,
    TensorProduct.finsuppScalarRight_apply_tmul_apply,
    Finsupp.coe_basisSingleOne, Algebra.smul_def]

/-- A finite free fixed-module basis for the canonical scalar extension of a
constant matrix. -/
def scalarExtensionCoordinateFixedBasis
    (p : GroundCoordinateSpace (k := k) (I := I) →ₗ[k]
      GroundCoordinateSpace (k := k) (I := I))
    (hp : IsIdempotentElem p) :
    Module.Basis (Fin (Module.finrank k (LinearMap.range p))) B
      (scalarExtensionCoordinateEnd B p).fixedSubmodule :=
  (constantProjectionFixedBasis B p hp).map
    (conjugateFixedSubmoduleEquiv
      (TensorProduct.finsuppScalarRight k B B I) (p.baseChange B))

@[simp]
theorem scalarExtensionCoordinateFixedBasis_apply
    (p : GroundCoordinateSpace (k := k) (I := I) →ₗ[k]
      GroundCoordinateSpace (k := k) (I := I))
    (hp : IsIdempotentElem p)
    (i : Fin (Module.finrank k (LinearMap.range p))) :
    (scalarExtensionCoordinateFixedBasis B p hp i).1 =
      (TensorProduct.finsuppScalarRight k B B I)
        (1 ⊗ₜ[k] adaptedProjectionBasis p hp (Sum.inl i)) := by
  change (TensorProduct.finsuppScalarRight k B B I)
      (constantProjectionFixedBasis B p hp i).1 = _
  rw [constantProjectionFixedBasis_apply]

/-- Matrix descent for a constant diagonal block.  If the matrix of `q` in a
finite `B`-basis is the scalar extension of an idempotent matrix over `k`,
then `q.fixedSubmodule` has a finite basis. -/
def fixedBasisOfMatrixBaseChange
    (b : Module.Basis I B N) (q : N →ₗ[B] N)
    (p : GroundCoordinateSpace (k := k) (I := I) →ₗ[k]
      GroundCoordinateSpace (k := k) (I := I))
    (hp : IsIdempotentElem p)
    (hmatrix : LinearMap.toMatrix b b q =
      (LinearMap.toMatrix (Finsupp.basisSingleOne (R := k))
        (Finsupp.basisSingleOne (R := k)) p).map (algebraMap k B)) :
    Module.Basis (Fin (Module.finrank k (LinearMap.range p))) B
      q.fixedSubmodule := by
  let bB : Module.Basis I B (I →₀ B) := Finsupp.basisSingleOne
  let e : (I →₀ B) ≃ₗ[B] N := bB.equiv b (Equiv.refl I)
  let q' := conjugateEnd e (scalarExtensionCoordinateEnd B p)
  have hq : q' = q := by
    apply (LinearMap.toMatrix b b).injective
    calc
      LinearMap.toMatrix b b q' =
          LinearMap.toMatrix bB bB (scalarExtensionCoordinateEnd B p) := by
            ext i j
            simp [q', e, conjugateEnd, LinearMap.toMatrix_apply,
              Module.Basis.equiv, Module.Basis.equiv_apply]
      _ = (LinearMap.toMatrix (Finsupp.basisSingleOne (R := k))
          (Finsupp.basisSingleOne (R := k)) p).map (algebraMap k B) :=
            scalarExtensionCoordinateEnd_toMatrix B p
      _ = LinearMap.toMatrix b b q := hmatrix.symm
  let bc := (scalarExtensionCoordinateFixedBasis B p hp).map
    (conjugateFixedSubmoduleEquiv e (scalarExtensionCoordinateEnd B p))
  exact bc.map (LinearEquiv.ofEq _ _
    (congrArg LinearMap.fixedSubmodule hq))

@[simp]
theorem fixedBasisOfMatrixBaseChange_apply
    (b : Module.Basis I B N) (q : N →ₗ[B] N)
    (p : GroundCoordinateSpace (k := k) (I := I) →ₗ[k]
      GroundCoordinateSpace (k := k) (I := I))
    (hp : IsIdempotentElem p)
    (hmatrix : LinearMap.toMatrix b b q =
      (LinearMap.toMatrix (Finsupp.basisSingleOne (R := k))
        (Finsupp.basisSingleOne (R := k)) p).map (algebraMap k B))
    (i : Fin (Module.finrank k (LinearMap.range p))) :
    (fixedBasisOfMatrixBaseChange B b q p hp hmatrix i).1 =
      ((Finsupp.basisSingleOne (R := B)).equiv b (Equiv.refl I))
        (scalarExtensionCoordinateFixedBasis B p hp i).1 := by
  simp [fixedBasisOfMatrixBaseChange, conjugateFixedSubmoduleEquiv,
    LinearEquiv.coe_ofEq_apply]

/-- Coordinates of the descended fixed basis are the ground-field
coordinates of the adapted range basis, mapped into `B`.  This is the fact
which makes every basis vector of an equal-degree block homogeneous. -/
theorem fixedBasisOfMatrixBaseChange_repr
    (b : Module.Basis I B N) (q : N →ₗ[B] N)
    (p : GroundCoordinateSpace (k := k) (I := I) →ₗ[k]
      GroundCoordinateSpace (k := k) (I := I))
    (hp : IsIdempotentElem p)
    (hmatrix : LinearMap.toMatrix b b q =
      (LinearMap.toMatrix (Finsupp.basisSingleOne (R := k))
        (Finsupp.basisSingleOne (R := k)) p).map (algebraMap k B))
    (i : Fin (Module.finrank k (LinearMap.range p))) (j : I) :
    b.repr ((fixedBasisOfMatrixBaseChange B b q p hp hmatrix i).1) j =
      algebraMap k B (adaptedProjectionBasis p hp (Sum.inl i) j) := by
  rw [fixedBasisOfMatrixBaseChange_apply,
    scalarExtensionCoordinateFixedBasis_apply]
  simp [Module.Basis.equiv,
    TensorProduct.finsuppScalarRight_apply_tmul_apply,
    Algebra.smul_def]

end MatrixDescent

end Field

end

end LeanProofs.PolynomialFormulas.LazardInvariantConstantBlocks
