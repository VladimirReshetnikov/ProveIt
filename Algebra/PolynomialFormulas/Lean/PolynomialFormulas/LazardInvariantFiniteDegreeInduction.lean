import PolynomialFormulas.LazardInvariantConstantBlocks
import PolynomialFormulas.LazardInvariantHomogeneousCoordinates
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Finite-degree induction for a triangular projection

Let `b` be a finite basis carrying a natural-number degree.  An idempotent
whose matrix has no entries from smaller to larger degree is block upper
triangular after splitting off the minimum-degree indices.  If every
equal-degree matrix block is obtained from the ground field, that diagonal
block has a finite fixed basis by
`LazardInvariantConstantBlocks`.  The right diagonal block has fewer basis
indices, so induction and the two-block projection lemma produce a finite
basis of the full fixed module.
-/

namespace LeanProofs.PolynomialFormulas.LazardInvariantFiniteDegreeInduction

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open LazardInvariantProjectionBlocks
open LazardInvariantConstantBlocks
open LazardInvariantModule
open LazardInvariantHomogeneousCoordinates

section General

variable {k A I M : Type*} [Field k] [CommRing A] [Nontrivial A]
variable [Algebra k A]
variable [AddCommGroup M] [Module A M]

/-- A chosen index of minimum degree in a nonempty finite index type. -/
def minimumDegreeIndex [Fintype I] [Nonempty I] (degree : I → ℕ) : I :=
  (Finset.exists_min_image Finset.univ degree Finset.univ_nonempty).choose

theorem minimumDegreeIndex_le [Fintype I] [Nonempty I]
    (degree : I → ℕ) (i : I) :
    degree (minimumDegreeIndex degree) ≤ degree i :=
  (Finset.exists_min_image Finset.univ degree
    Finset.univ_nonempty).choose_spec.2 i (Finset.mem_univ i)

abbrev MinimumDegreeIndex [Fintype I] [Nonempty I]
    (degree : I → ℕ) :=
  {i : I // degree i = degree (minimumDegreeIndex degree)}

abbrev HigherDegreeIndex [Fintype I] [Nonempty I]
    (degree : I → ℕ) :=
  {i : I // degree i ≠ degree (minimumDegreeIndex degree)}

/-- Split the index type into its minimum-degree fibre and its complement. -/
def minimumDegreeSplitEquiv [Fintype I] [Nonempty I]
    (degree : I → ℕ) :
    MinimumDegreeIndex degree ⊕ HigherDegreeIndex degree ≃ I :=
  Equiv.sumCompl
    (fun i => degree i = degree (minimumDegreeIndex degree))

/-- Reindex a basis by the minimum-degree split. -/
def minimumDegreeSplitBasis [Fintype I] [Nonempty I]
    (b : Module.Basis I A M) (degree : I → ℕ) :
    Module.Basis (MinimumDegreeIndex degree ⊕ HigherDegreeIndex degree) A M :=
  b.reindex (minimumDegreeSplitEquiv degree).symm

/-- Coordinates in the split basis, separated into the two direct summands. -/
def minimumDegreeCoordinateEquiv [Fintype I] [Nonempty I]
    (b : Module.Basis I A M) (degree : I → ℕ) :
    M ≃ₗ[A]
      (MinimumDegreeIndex degree →₀ A) ×
        (HigherDegreeIndex degree →₀ A) :=
  (minimumDegreeSplitBasis b degree).repr.trans
    (Finsupp.sumFinsuppLEquivProdFinsupp A)

@[simp]
theorem minimumDegreeCoordinateEquiv_apply_low
    [Fintype I] [Nonempty I]
    (b : Module.Basis I A M) (degree : I → ℕ)
    (i : MinimumDegreeIndex degree) :
    minimumDegreeCoordinateEquiv b degree (b i.1) =
      (Finsupp.single i 1, 0) := by
  simp [minimumDegreeCoordinateEquiv, minimumDegreeSplitBasis,
    minimumDegreeSplitEquiv, Module.Basis.reindex_apply]

@[simp]
theorem minimumDegreeCoordinateEquiv_apply_high
    [Fintype I] [Nonempty I]
    (b : Module.Basis I A M) (degree : I → ℕ)
    (i : HigherDegreeIndex degree) :
    minimumDegreeCoordinateEquiv b degree (b i.1) =
      (0, Finsupp.single i 1) := by
  simp [minimumDegreeCoordinateEquiv, minimumDegreeSplitBasis,
    minimumDegreeSplitEquiv, Module.Basis.reindex_apply]

@[simp]
theorem minimumDegreeCoordinateEquiv_apply_fst
    [Fintype I] [Nonempty I]
    (b : Module.Basis I A M) (degree : I → ℕ)
    (x : M) (i : MinimumDegreeIndex degree) :
    (minimumDegreeCoordinateEquiv b degree x).1 i = b.repr x i.1 := by
  classical
  simp [minimumDegreeCoordinateEquiv, minimumDegreeSplitBasis,
    minimumDegreeSplitEquiv]

@[simp]
theorem minimumDegreeCoordinateEquiv_apply_snd
    [Fintype I] [Nonempty I]
    (b : Module.Basis I A M) (degree : I → ℕ)
    (x : M) (i : HigherDegreeIndex degree) :
    (minimumDegreeCoordinateEquiv b degree x).2 i = b.repr x i.1 := by
  classical
  simp [minimumDegreeCoordinateEquiv, minimumDegreeSplitBasis,
    minimumDegreeSplitEquiv]

@[simp]
theorem minimumDegreeCoordinateEquiv_symm_low
    [Fintype I] [Nonempty I]
    (b : Module.Basis I A M) (degree : I → ℕ)
    (i : MinimumDegreeIndex degree) (a : A) :
    (minimumDegreeCoordinateEquiv b degree).symm
        (Finsupp.single i a, 0) = a • b i.1 := by
  apply (minimumDegreeCoordinateEquiv b degree).injective
  simp

@[simp]
theorem minimumDegreeCoordinateEquiv_symm_high
    [Fintype I] [Nonempty I]
    (b : Module.Basis I A M) (degree : I → ℕ)
    (i : HigherDegreeIndex degree) (a : A) :
    (minimumDegreeCoordinateEquiv b degree).symm
        (0, Finsupp.single i a) = a • b i.1 := by
  apply (minimumDegreeCoordinateEquiv b degree).injective
  simp

/-- The projection written in minimum-degree block coordinates. -/
def minimumDegreeSplitEnd [Fintype I] [Nonempty I]
    (b : Module.Basis I A M) (degree : I → ℕ)
    (p : M →ₗ[A] M) :
    ((MinimumDegreeIndex degree →₀ A) ×
      (HigherDegreeIndex degree →₀ A)) →ₗ[A]
    ((MinimumDegreeIndex degree →₀ A) ×
      (HigherDegreeIndex degree →₀ A)) :=
  conjugateEnd (minimumDegreeCoordinateEquiv b degree) p

/-- Degree triangularity makes the minimum-degree coordinate summand stable. -/
theorem minimumDegreeSplitEnd_isUpperTriangular
    [Fintype I] [Nonempty I]
    (b : Module.Basis I A M) (degree : I → ℕ)
    (p : M →ₗ[A] M)
    (htri : ∀ i j, degree j < degree i →
      b.repr (p (b j)) i = 0) :
    IsUpperTriangular (minimumDegreeSplitEnd b degree p) := by
  rw [IsUpperTriangular]
  apply Finsupp.lhom_ext
  intro i a
  ext j
  have hji : degree i.1 < degree j.1 := by
    have hmin := minimumDegreeIndex_le degree j.1
    calc
      degree i.1 = degree (minimumDegreeIndex degree) := i.2
      _ < degree j.1 := lt_of_le_of_ne hmin (Ne.symm j.2)
  have hz := htri j.1 i.1 hji
  simp [minimumDegreeSplitEnd, conjugateEnd,
    leftDiagonalBlock, rightDiagonalBlock, minimumDegreeCoordinateEquiv,
    minimumDegreeSplitBasis, minimumDegreeSplitEquiv,
    minimumDegreeCoordinateEquiv_symm_low, hz]

/-- The left diagonal block matrix is the equal-degree submatrix of the
original endomorphism. -/
theorem leftDiagonalBlock_toMatrix_apply
    [Fintype I] [Nonempty I]
    (b : Module.Basis I A M) (degree : I → ℕ)
    [DecidableEq (MinimumDegreeIndex degree)]
    (p : M →ₗ[A] M)
    (i j : MinimumDegreeIndex degree) :
    LinearMap.toMatrix
        (Finsupp.basisSingleOne : Module.Basis
          (MinimumDegreeIndex degree) A (MinimumDegreeIndex degree →₀ A))
        (Finsupp.basisSingleOne : Module.Basis
          (MinimumDegreeIndex degree) A (MinimumDegreeIndex degree →₀ A))
        (leftDiagonalBlock (minimumDegreeSplitEnd b degree p)) i j =
      b.repr (p (b j.1)) i.1 := by
  classical
  simp [LinearMap.toMatrix_apply, minimumDegreeSplitEnd, conjugateEnd,
    leftDiagonalBlock, minimumDegreeCoordinateEquiv,
    minimumDegreeSplitBasis, minimumDegreeSplitEquiv]

/-- The same coordinate formula for the recursively retained block. -/
theorem rightDiagonalBlock_toMatrix_apply
    [Fintype I] [Nonempty I]
    (b : Module.Basis I A M) (degree : I → ℕ)
    [DecidableEq (HigherDegreeIndex degree)]
    (p : M →ₗ[A] M)
    (i j : HigherDegreeIndex degree) :
    LinearMap.toMatrix
        (Finsupp.basisSingleOne : Module.Basis
          (HigherDegreeIndex degree) A (HigherDegreeIndex degree →₀ A))
        (Finsupp.basisSingleOne : Module.Basis
          (HigherDegreeIndex degree) A (HigherDegreeIndex degree →₀ A))
        (rightDiagonalBlock (minimumDegreeSplitEnd b degree p)) i j =
      b.repr (p (b j.1)) i.1 := by
  classical
  simp [LinearMap.toMatrix_apply, minimumDegreeSplitEnd, conjugateEnd,
    rightDiagonalBlock, minimumDegreeCoordinateEquiv,
    minimumDegreeSplitBasis, minimumDegreeSplitEquiv]

section CoordinateMatrixWrapper

local instance {ι : Type*} : DecidableEq ι := Classical.decEq ι

/-- An opaque coordinate-space interface to constant-matrix descent.  Keeping
the coefficient ring abstract here prevents elaboration of a later
`SymmetricRing` specialization from unfolding its large subalgebra type. -/
def fixedCoordinateBasisOfMatrixBaseChange
    {k A I : Type*} [Field k] [CommRing A] [Algebra k A]
    [Fintype I]
    (q : (I →₀ A) →ₗ[A] (I →₀ A))
    (p₀ : (I →₀ k) →ₗ[k] (I →₀ k))
    (hp₀ : IsIdempotentElem p₀)
    (hmatrix :
      LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne q =
        (LinearMap.toMatrix Finsupp.basisSingleOne
          Finsupp.basisSingleOne p₀).map (algebraMap k A)) :
    Module.Basis (Fin (Module.finrank k (LinearMap.range p₀))) A
      q.fixedSubmodule :=
  fixedBasisOfMatrixBaseChange A Finsupp.basisSingleOne
    q p₀ hp₀ hmatrix

@[simp]
theorem fixedCoordinateBasisOfMatrixBaseChange_apply
    {k A I : Type*} [Field k] [CommRing A] [Algebra k A]
    [Fintype I]
    (q : (I →₀ A) →ₗ[A] (I →₀ A))
    (p₀ : (I →₀ k) →ₗ[k] (I →₀ k))
    (hp₀ : IsIdempotentElem p₀)
    (hmatrix :
      LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne q =
        (LinearMap.toMatrix Finsupp.basisSingleOne
          Finsupp.basisSingleOne p₀).map (algebraMap k A))
    (i : Fin (Module.finrank k (LinearMap.range p₀))) (j : I) :
    ((fixedCoordinateBasisOfMatrixBaseChange q p₀ hp₀ hmatrix i).1) j =
      algebraMap k A (adaptedProjectionBasis p₀ hp₀ (Sum.inl i) j) := by
  simpa [fixedCoordinateBasisOfMatrixBaseChange] using
    fixedBasisOfMatrixBaseChange_repr A
      (Finsupp.basisSingleOne : Module.Basis I A (I →₀ A))
      q p₀ hp₀ hmatrix i j

end CoordinateMatrixWrapper

/-- The same abstraction barrier for combining fixed bases of two projection
blocks. -/
def fixedCoordinateUpperBlockBasis
    {A L H ι κ : Type*} [CommRing A]
    [AddCommGroup L] [AddCommGroup H] [Module A L] [Module A H]
    (e : L →ₗ[A] L) (a : H →ₗ[A] L) (f : H →ₗ[A] H)
    (hcompat : Compatible e a f)
    (be : Module.Basis ι A e.fixedSubmodule)
    (bf : Module.Basis κ A f.fixedSubmodule) :
    Module.Basis (ι ⊕ κ) A (upperBlock e a f).fixedSubmodule :=
  fixedUpperBlockBasis e a f hcompat be bf

@[simp]
theorem fixedCoordinateUpperBlockBasis_apply_inl
    {A L H ι κ : Type*} [CommRing A]
    [AddCommGroup L] [AddCommGroup H] [Module A L] [Module A H]
    (e : L →ₗ[A] L) (a : H →ₗ[A] L) (f : H →ₗ[A] H)
    (hcompat : Compatible e a f)
    (be : Module.Basis ι A e.fixedSubmodule)
    (bf : Module.Basis κ A f.fixedSubmodule) (i : ι) :
    (fixedCoordinateUpperBlockBasis e a f hcompat be bf (Sum.inl i)).1 =
      ((be i).1, 0) := by
  exact fixedUpperBlockBasis_apply_inl e a f hcompat be bf i

@[simp]
theorem fixedCoordinateUpperBlockBasis_apply_inr
    {A L H ι κ : Type*} [CommRing A]
    [AddCommGroup L] [AddCommGroup H] [Module A L] [Module A H]
    (e : L →ₗ[A] L) (a : H →ₗ[A] L) (f : H →ₗ[A] H)
    (hcompat : Compatible e a f)
    (be : Module.Basis ι A e.fixedSubmodule)
    (bf : Module.Basis κ A f.fixedSubmodule) (i : κ) :
    (fixedCoordinateUpperBlockBasis e a f hcompat be bf (Sum.inr i)).1 =
      (a (bf i).1, (bf i).1) := by
  exact fixedUpperBlockBasis_apply_inr e a f hcompat be bf i

/-- The complement of a nonempty minimum-degree fibre has strictly fewer
indices. -/
theorem card_higherDegreeIndex_lt [Fintype I] [Nonempty I]
    (degree : I → ℕ) :
    Fintype.card (HigherDegreeIndex degree) < Fintype.card I := by
  have hlow : Nonempty (MinimumDegreeIndex degree) :=
    ⟨⟨minimumDegreeIndex degree, rfl⟩⟩
  have hcard := Fintype.card_congr (minimumDegreeSplitEquiv degree)
  rw [Fintype.card_sum] at hcard
  have hpos : 0 < Fintype.card (MinimumDegreeIndex degree) :=
    Fintype.card_pos
  omega

end General

universe u_k u_A u_I

/-- Finite-degree block induction.  This is the algebraic freeness core of
Lazard's Theorem 2, independent of the particular Artin basis. -/
def finiteFixedBasis_of_degreeTriangular
    {k : Type u_k} {A : Type u_A} {I : Type u_I}
    {M : Type (max u_A u_I)}
    [Field k] [CommRing A] [Nontrivial A]
    [Algebra k A] [AddCommGroup M] [Module A M] [Fintype I]
    (b : Module.Basis I A M) (degree : I → ℕ)
    (p : M →ₗ[A] M) (hp : IsIdempotentElem p)
    (htri : ∀ i j, degree j < degree i →
      b.repr (p (b j)) i = 0)
    (hconstant : ∀ i j, degree i = degree j →
      ∃ r : k, b.repr (p (b j)) i = algebraMap k A r) :
    FiniteFixedBasis p := by
  classical
  by_cases hnonempty : Nonempty I
  · letI : Nonempty I := hnonempty
    let L := MinimumDegreeIndex degree
    let H := HigherDegreeIndex degree
    letI : DecidableEq L := Classical.decEq L
    letI : DecidableEq H := Classical.decEq H
    let E := minimumDegreeCoordinateEquiv b degree
    let P := minimumDegreeSplitEnd b degree p
    have hP : IsIdempotentElem P := by
      change P * P = P
      apply LinearMap.ext
      intro x
      change E (p (E.symm (E (p (E.symm x))))) =
        E (p (E.symm x))
      rw [E.symm_apply_apply]
      exact congrArg E (LinearMap.congr_fun hp.eq (E.symm x))
    have hupper : IsUpperTriangular P :=
      minimumDegreeSplitEnd_isUpperTriangular b degree p htri
    let e := leftDiagonalBlock P
    let a := upperRightBlock P
    let f := rightDiagonalBlock P
    have hblock : P = upperBlock e a f :=
      eq_upperBlock_of_isUpperTriangular P hupper
    obtain ⟨he, hf, hcompat⟩ := by
      rw [hblock] at hP
      exact upperBlock_idempotent_components e a f hP
    let entry : L → L → k := fun i j =>
      Classical.choose (hconstant i.1 j.1 (by simp [L, i.2, j.2]))
    let p₀ : (L →₀ k) →ₗ[k] (L →₀ k) :=
      Matrix.toLin (Finsupp.basisSingleOne (R := k))
        (Finsupp.basisSingleOne (R := k)) entry
    have hmatrix :
        LinearMap.toMatrix
            (Finsupp.basisSingleOne : Module.Basis L A (L →₀ A))
            (Finsupp.basisSingleOne : Module.Basis L A (L →₀ A)) e =
          (LinearMap.toMatrix
            (Finsupp.basisSingleOne : Module.Basis L k (L →₀ k))
            (Finsupp.basisSingleOne : Module.Basis L k (L →₀ k)) p₀).map
              (algebraMap k A) := by
      ext i j
      rw [leftDiagonalBlock_toMatrix_apply]
      simpa [p₀, entry] using
        (Classical.choose_spec
          (hconstant i.1 j.1 (by simp [L, i.2, j.2])))
    have hp₀ : IsIdempotentElem p₀ := by
      apply (LinearMap.toMatrix (Finsupp.basisSingleOne (R := k))
        (Finsupp.basisSingleOne (R := k))).injective
      apply Matrix.map_injective (RingHom.injective (algebraMap k A))
      rw [LinearMap.toMatrix_mul]
      change
        ((LinearMap.toMatrix (Finsupp.basisSingleOne (R := k))
          (Finsupp.basisSingleOne (R := k)) p₀) *
          (LinearMap.toMatrix (Finsupp.basisSingleOne (R := k))
            (Finsupp.basisSingleOne (R := k)) p₀)).map
            (algebraMap k A) =
          (LinearMap.toMatrix (Finsupp.basisSingleOne (R := k))
            (Finsupp.basisSingleOne (R := k)) p₀).map
              (algebraMap k A)
      rw [Matrix.map_mul,
        ← hmatrix, ← LinearMap.toMatrix_mul]
      exact congrArg
        (LinearMap.toMatrix (Finsupp.basisSingleOne (R := A))
          (Finsupp.basisSingleOne (R := A))) he.eq
    let be := fixedBasisOfMatrixBaseChange A
      (Finsupp.basisSingleOne : Module.Basis L A (L →₀ A))
      e p₀ hp₀ hmatrix
    let bH : Module.Basis H A (H →₀ A) := Finsupp.basisSingleOne
    let degreeH : H → ℕ := fun i => degree i.1
    have htriH : ∀ i j, degreeH j < degreeH i →
        bH.repr (f (bH j)) i = 0 := by
      intro i j hij
      have h := htri i.1 j.1 hij
      have hentry := rightDiagonalBlock_toMatrix_apply b degree p i j
      rw [LinearMap.toMatrix_apply] at hentry
      have heq : bH.repr (f (bH j)) i = b.repr (p (b j.1)) i.1 := by
        simpa [bH, f, P] using hentry
      rw [heq]
      exact h
    have hconstantH : ∀ i j, degreeH i = degreeH j →
        ∃ r : k, bH.repr (f (bH j)) i = algebraMap k A r := by
      intro i j hij
      obtain ⟨r, hr⟩ := hconstant i.1 j.1 hij
      refine ⟨r, ?_⟩
      have hentry := rightDiagonalBlock_toMatrix_apply b degree p i j
      rw [LinearMap.toMatrix_apply] at hentry
      have heq : bH.repr (f (bH j)) i = b.repr (p (b j.1)) i.1 := by
        simpa [bH, f, P] using hentry
      rw [heq]
      exact hr
    let bfData := finiteFixedBasis_of_degreeTriangular
      (k := k) (A := A) (I := H) (M := H →₀ A)
      bH degreeH f hf htriH hconstantH
    letI : Fintype bfData.Index := bfData.indexFintype
    let bP₀ := fixedUpperBlockBasis e a f hcompat be bfData.basis
    let bP := bP₀.map (LinearEquiv.ofEq _ _
      (congrArg LinearMap.fixedSubmodule hblock).symm)
    have hPE : conjugateEnd E p = P := by
      change minimumDegreeSplitEnd b degree p = P
      rfl
    exact
      { Index := (Fin (Module.finrank k (LinearMap.range p₀))) ⊕
          bfData.Index
        indexFintype := inferInstance
        basis := bP.map
          (by
            rw [← hPE]
            exact (conjugateFixedSubmoduleEquiv E p).symm) }
  · letI : IsEmpty I := ⟨fun i => hnonempty ⟨i⟩⟩
    letI : Subsingleton M :=
      ⟨fun x y => b.repr.injective (Subsingleton.elim _ _)⟩
    letI : Subsingleton p.fixedSubmodule := inferInstance
    exact
      { Index := PEmpty
        indexFintype := inferInstance
        basis := Module.Basis.empty p.fixedSubmodule }
termination_by Fintype.card I
decreasing_by
  exact card_higherDegreeIndex_lt degree

section Homogeneous

variable {K τ J N : Type*} [Field K]
variable [AddCommGroup N]
variable [Module (SymmetricRing K τ) N]

/-- The strengthened output of the finite-degree induction: the fixed module
has a finite basis whose realized vectors are homogeneous and satisfy the
original ambient degree bound. -/
structure BoundedHomogeneousFixedBasis
    (p : N →ₗ[SymmetricRing K τ] N)
    (realize : N →ₗ[SymmetricRing K τ] PolynomialRing K τ)
    (degreeBound : ℕ) where
  Index : Type
  indexFintype : Fintype Index
  basis : Module.Basis Index (SymmetricRing K τ) p.fixedSubmodule
  degree : Index → ℕ
  basis_homogeneous (i : Index) :
    MvPolynomial.IsHomogeneous (realize (basis i).1) (degree i)
  degree_le (i : Index) : degree i ≤ degreeBound

/-- Combine a constant left block with an already constructed bounded
homogeneous right block without projecting the dependent recursive record at
the call site. -/
def combinedBoundedUpperBlockBasis
    {K τ L H ι : Type*} [Field K]
    [AddCommGroup L] [AddCommGroup H]
    [Module (SymmetricRing K τ) L] [Module (SymmetricRing K τ) H]
    (e : L →ₗ[SymmetricRing K τ] L)
    (a : H →ₗ[SymmetricRing K τ] L)
    (f : H →ₗ[SymmetricRing K τ] H)
    (hcompat : Compatible e a f)
    (be : Module.Basis ι (SymmetricRing K τ) e.fixedSubmodule)
    {realizeH : H →ₗ[SymmetricRing K τ] PolynomialRing K τ}
    {degreeBound : ℕ}
    (bfData : BoundedHomogeneousFixedBasis f realizeH degreeBound) :
    Module.Basis (ι ⊕ bfData.Index) (SymmetricRing K τ)
      (upperBlock e a f).fixedSubmodule :=
  fixedCoordinateUpperBlockBasis e a f hcompat be bfData.basis

@[simp]
theorem combinedBoundedUpperBlockBasis_apply_inl
    {K τ L H ι : Type*} [Field K]
    [AddCommGroup L] [AddCommGroup H]
    [Module (SymmetricRing K τ) L] [Module (SymmetricRing K τ) H]
    (e : L →ₗ[SymmetricRing K τ] L)
    (a : H →ₗ[SymmetricRing K τ] L)
    (f : H →ₗ[SymmetricRing K τ] H)
    (hcompat : Compatible e a f)
    (be : Module.Basis ι (SymmetricRing K τ) e.fixedSubmodule)
    {realizeH : H →ₗ[SymmetricRing K τ] PolynomialRing K τ}
    {degreeBound : ℕ}
    (bfData : BoundedHomogeneousFixedBasis f realizeH degreeBound) (i : ι) :
    (combinedBoundedUpperBlockBasis e a f hcompat be bfData
      (Sum.inl i)).1 = ((be i).1, 0) := by
  exact fixedCoordinateUpperBlockBasis_apply_inl
    e a f hcompat be bfData.basis i

@[simp]
theorem combinedBoundedUpperBlockBasis_apply_inr
    {K τ L H ι : Type*} [Field K]
    [AddCommGroup L] [AddCommGroup H]
    [Module (SymmetricRing K τ) L] [Module (SymmetricRing K τ) H]
    (e : L →ₗ[SymmetricRing K τ] L)
    (a : H →ₗ[SymmetricRing K τ] L)
    (f : H →ₗ[SymmetricRing K τ] H)
    (hcompat : Compatible e a f)
    (be : Module.Basis ι (SymmetricRing K τ) e.fixedSubmodule)
    {realizeH : H →ₗ[SymmetricRing K τ] PolynomialRing K τ}
    {degreeBound : ℕ}
    (bfData : BoundedHomogeneousFixedBasis f realizeH degreeBound)
    (i : bfData.Index) :
    (combinedBoundedUpperBlockBasis e a f hcompat be bfData
      (Sum.inr i)).1 = (a (bfData.basis i).1, (bfData.basis i).1) := by
  exact fixedCoordinateUpperBlockBasis_apply_inr
    e a f hcompat be bfData.basis i

/-- Transport a fixed-submodule basis back across a conjugation equality.  This
keeps the dependent casts needed for the transport behind an opaque boundary. -/
def fixedBasisOfConjugate
    {A M N ι : Type*} [CommRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (E : M ≃ₗ[A] N) (p : M →ₗ[A] M) (P : N →ₗ[A] N)
    (hPE : conjugateEnd E p = P)
    (bP : Module.Basis ι A P.fixedSubmodule) :
    Module.Basis ι A p.fixedSubmodule :=
  bP.map ((LinearEquiv.ofEq _ _
    (congrArg LinearMap.fixedSubmodule hPE).symm).trans
      (conjugateFixedSubmoduleEquiv E p).symm)

@[simp]
theorem fixedBasisOfConjugate_apply
    {A M N ι : Type*} [CommRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (E : M ≃ₗ[A] N) (p : M →ₗ[A] M) (P : N →ₗ[A] N)
    (hPE : conjugateEnd E p = P)
    (bP : Module.Basis ι A P.fixedSubmodule) (i : ι) :
    ((fixedBasisOfConjugate E p P hPE bP i).1) = E.symm (bP i).1 := by
  rfl

/-- Combine the two fixed block bases and transport the result all the way back
to the original module.  Keeping both dependent equality transports inside this
definition prevents recursive record projections from being unfolded at the
induction call site. -/
def combinedBoundedConjugateBasis
    {K τ M L H ι : Type*} [Field K]
    [AddCommGroup M] [Module (SymmetricRing K τ) M]
    [AddCommGroup L] [Module (SymmetricRing K τ) L]
    [AddCommGroup H] [Module (SymmetricRing K τ) H]
    (E : M ≃ₗ[SymmetricRing K τ] (L × H))
    (p : M →ₗ[SymmetricRing K τ] M)
    (P : (L × H) →ₗ[SymmetricRing K τ] (L × H))
    (hPE : conjugateEnd E p = P)
    (e : L →ₗ[SymmetricRing K τ] L)
    (a : H →ₗ[SymmetricRing K τ] L)
    (f : H →ₗ[SymmetricRing K τ] H)
    (hblock : P = upperBlock e a f)
    (hcompat : Compatible e a f)
    (be : Module.Basis ι (SymmetricRing K τ) e.fixedSubmodule)
    {realizeH : H →ₗ[SymmetricRing K τ] PolynomialRing K τ}
    {degreeBound : ℕ}
    (bfData : BoundedHomogeneousFixedBasis f realizeH degreeBound) :
    Module.Basis (ι ⊕ bfData.Index) (SymmetricRing K τ)
      p.fixedSubmodule :=
  fixedBasisOfConjugate E p P hPE
    ((combinedBoundedUpperBlockBasis e a f hcompat be bfData).map
      (LinearEquiv.ofEq _ _
        (congrArg LinearMap.fixedSubmodule hblock).symm))

@[simp]
theorem combinedBoundedConjugateBasis_apply_inl
    {K τ M L H ι : Type*} [Field K]
    [AddCommGroup M] [Module (SymmetricRing K τ) M]
    [AddCommGroup L] [Module (SymmetricRing K τ) L]
    [AddCommGroup H] [Module (SymmetricRing K τ) H]
    (E : M ≃ₗ[SymmetricRing K τ] (L × H))
    (p : M →ₗ[SymmetricRing K τ] M)
    (P : (L × H) →ₗ[SymmetricRing K τ] (L × H))
    (hPE : conjugateEnd E p = P)
    (e : L →ₗ[SymmetricRing K τ] L)
    (a : H →ₗ[SymmetricRing K τ] L)
    (f : H →ₗ[SymmetricRing K τ] H)
    (hblock : P = upperBlock e a f)
    (hcompat : Compatible e a f)
    (be : Module.Basis ι (SymmetricRing K τ) e.fixedSubmodule)
    {realizeH : H →ₗ[SymmetricRing K τ] PolynomialRing K τ}
    {degreeBound : ℕ}
    (bfData : BoundedHomogeneousFixedBasis f realizeH degreeBound) (i : ι) :
    ((combinedBoundedConjugateBasis E p P hPE e a f hblock hcompat be
      bfData (Sum.inl i)).1) = E.symm ((be i).1, 0) := by
  simp only [combinedBoundedConjugateBasis, fixedBasisOfConjugate_apply,
    Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    combinedBoundedUpperBlockBasis_apply_inl]

@[simp]
theorem combinedBoundedConjugateBasis_apply_inr
    {K τ M L H ι : Type*} [Field K]
    [AddCommGroup M] [Module (SymmetricRing K τ) M]
    [AddCommGroup L] [Module (SymmetricRing K τ) L]
    [AddCommGroup H] [Module (SymmetricRing K τ) H]
    (E : M ≃ₗ[SymmetricRing K τ] (L × H))
    (p : M →ₗ[SymmetricRing K τ] M)
    (P : (L × H) →ₗ[SymmetricRing K τ] (L × H))
    (hPE : conjugateEnd E p = P)
    (e : L →ₗ[SymmetricRing K τ] L)
    (a : H →ₗ[SymmetricRing K τ] L)
    (f : H →ₗ[SymmetricRing K τ] H)
    (hblock : P = upperBlock e a f)
    (hcompat : Compatible e a f)
    (be : Module.Basis ι (SymmetricRing K τ) e.fixedSubmodule)
    {realizeH : H →ₗ[SymmetricRing K τ] PolynomialRing K τ}
    {degreeBound : ℕ}
    (bfData : BoundedHomogeneousFixedBasis f realizeH degreeBound)
    (i : bfData.Index) :
    ((combinedBoundedConjugateBasis E p P hPE e a f hblock hcompat be
      bfData (Sum.inr i)).1) =
        E.symm (a (bfData.basis i).1, (bfData.basis i).1) := by
  simp only [combinedBoundedConjugateBasis, fixedBasisOfConjugate_apply,
    Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    combinedBoundedUpperBlockBasis_apply_inr]

/-- Assemble the basis, degree function, homogeneity proofs, and degree bounds
after a minimum-degree split.  This opaque constructor is kernel-checked here
and provides a transparency boundary that keeps the dependent `Sum` index out
of the recursive equation compiler. -/
opaque assembleBoundedConjugateFixedBasis
    {K τ M L H : Type*} {ι : Type} [Field K] [Fintype ι]
    [AddCommGroup M] [Module (SymmetricRing K τ) M]
    [AddCommGroup L] [Module (SymmetricRing K τ) L]
    [AddCommGroup H] [Module (SymmetricRing K τ) H]
    (E : M ≃ₗ[SymmetricRing K τ] (L × H))
    (p : M →ₗ[SymmetricRing K τ] M)
    (P : (L × H) →ₗ[SymmetricRing K τ] (L × H))
    (hPE : conjugateEnd E p = P)
    (e : L →ₗ[SymmetricRing K τ] L)
    (a : H →ₗ[SymmetricRing K τ] L)
    (f : H →ₗ[SymmetricRing K τ] H)
    (hblock : P = upperBlock e a f)
    (hcompat : Compatible e a f)
    (be : Module.Basis ι (SymmetricRing K τ) e.fixedSubmodule)
    (realize : M →ₗ[SymmetricRing K τ] PolynomialRing K τ)
    (degreeBound lowDegree : ℕ)
    {realizeH : H →ₗ[SymmetricRing K τ] PolynomialRing K τ}
    (bfData : BoundedHomogeneousFixedBasis f realizeH degreeBound)
    (hLow : ∀ i, MvPolynomial.IsHomogeneous
      (realize (E.symm ((be i).1, 0))) lowDegree)
    (hHigh : ∀ i, MvPolynomial.IsHomogeneous
      (realize (E.symm
        (a (bfData.basis i).1, (bfData.basis i).1))) (bfData.degree i))
    (hLowLe : lowDegree ≤ degreeBound) :
    BoundedHomogeneousFixedBasis p realize degreeBound := by
  letI : Fintype bfData.Index := bfData.indexFintype
  refine
    { Index := ι ⊕ bfData.Index
      indexFintype := inferInstance
      basis := combinedBoundedConjugateBasis E p P hPE e a f hblock
        hcompat be bfData
      degree := fun
        | Sum.inl _ => lowDegree
        | Sum.inr i => bfData.degree i
      basis_homogeneous := ?_
      degree_le := ?_ }
  · intro i
    rcases i with i | i
    · simpa only [combinedBoundedConjugateBasis_apply_inl] using hLow i
    · simpa only [combinedBoundedConjugateBasis_apply_inr] using hHigh i
  · intro i
    rcases i with i | i
    · exact hLowLe
    · exact bfData.degree_le i

/-- On a finite index type, summing the single-coordinate pieces of a finsupp
recovers the original finsupp. -/
theorem sum_finsupp_single_apply_eq_self
    {I R : Type*} [Fintype I] [AddCommMonoid R] (v : I →₀ R) :
    (∑ i : I, Finsupp.single i (v i)) = v := by
  classical
  ext i
  simp

/-- The right diagonal block is the high-coordinate projection of the full
endomorphism.  This identity is what transfers homogeneity to the recursive
block. -/
theorem rightDiagonalBlock_as_coordinateProjection
    [Fintype J] [Nonempty J]
    (b : Module.Basis J (SymmetricRing K τ) N)
    (degree : J → ℕ)
    (p : N →ₗ[SymmetricRing K τ] N)
    (y : HigherDegreeIndex degree →₀ SymmetricRing K τ) :
    (minimumDegreeCoordinateEquiv b degree).symm
        ((0 : MinimumDegreeIndex degree →₀ SymmetricRing K τ),
          rightDiagonalBlock
            (A := SymmetricRing K τ)
            (L := MinimumDegreeIndex degree →₀ SymmetricRing K τ)
            (H := HigherDegreeIndex degree →₀ SymmetricRing K τ)
            (minimumDegreeSplitEnd b degree p) y) =
      embeddedBasisCoordinateProjection b
        (fun i => degree i ≠ degree (minimumDegreeIndex degree))
        (p ((minimumDegreeCoordinateEquiv b degree).symm (0, y))) := by
  classical
  let E := minimumDegreeCoordinateEquiv b degree
  let keep := fun i => degree i ≠ degree (minimumDegreeIndex degree)
  let z := p (E.symm (0, y))
  apply E.injective
  rw [E.apply_symm_apply]
  apply Prod.ext
  · apply Finsupp.ext
    intro i
    change 0 = (E (embeddedBasisCoordinateProjection b keep z)).1 i
    rw [minimumDegreeCoordinateEquiv_apply_fst]
    have hrepr := embeddedBasisCoordinateProjection_repr b keep z
    rw [hrepr, Finsupp.filter_apply_neg]
    exact fun hi => hi i.2
  · apply Finsupp.ext
    intro i
    change ((minimumDegreeSplitEnd b degree p) (0, y)).2 i =
      (E (embeddedBasisCoordinateProjection b keep z)).2 i
    rw [minimumDegreeCoordinateEquiv_apply_snd]
    have hrepr := embeddedBasisCoordinateProjection_repr b keep z
    rw [hrepr, Finsupp.filter_apply_pos]
    · change (E (p (E.symm (0, y)))).2 i = b.repr z i.1
      exact minimumDegreeCoordinateEquiv_apply_snd b degree z i
    · exact i.2

end Homogeneous

universe u_K u_τ u_J

/-- Full homogeneous finite-degree induction. -/
def boundedHomogeneousFixedBasis_of_degreeTriangular
    {K : Type u_K} {τ : Type u_τ} {J : Type u_J}
    {N : Type (max u_K u_τ u_J)} [Field K] [AddCommGroup N]
    [Module (SymmetricRing K τ) N] [Fintype J]
    (b : Module.Basis J (SymmetricRing K τ) N)
    (realize : N →ₗ[SymmetricRing K τ] PolynomialRing K τ)
    (hrealize : Function.Injective realize)
    (degree : J → ℕ) (degreeBound : ℕ)
    (hb : ∀ i, MvPolynomial.IsHomogeneous
      (realize (b i)) (degree i))
    (hdegree : ∀ i, degree i ≤ degreeBound)
    (p : N →ₗ[SymmetricRing K τ] N)
    (hp : IsIdempotentElem p)
    (hpreserves : ∀ {x : N} {d : ℕ},
      MvPolynomial.IsHomogeneous (realize x) d →
        MvPolynomial.IsHomogeneous (realize (p x)) d)
    (htri : ∀ i j, degree j < degree i →
      b.repr (p (b j)) i = 0)
    (hconstant : ∀ i j, degree i = degree j →
      ∃ r : K, b.repr (p (b j)) i =
        algebraMap K (SymmetricRing K τ) r) :
    BoundedHomogeneousFixedBasis p realize degreeBound := by
  classical
  by_cases hnonempty : Nonempty J
  · letI : Nonempty J := hnonempty
    let L := MinimumDegreeIndex degree
    let H := HigherDegreeIndex degree
    letI : DecidableEq L := Classical.decEq L
    letI : DecidableEq H := Classical.decEq H
    let E := minimumDegreeCoordinateEquiv b degree
    let P :
        ((L →₀ SymmetricRing K τ) × (H →₀ SymmetricRing K τ)) →ₗ[SymmetricRing K τ]
        ((L →₀ SymmetricRing K τ) × (H →₀ SymmetricRing K τ)) :=
      minimumDegreeSplitEnd b degree p
    have hP : IsIdempotentElem P := by
      change P * P = P
      apply LinearMap.ext
      intro x
      change E (p (E.symm (E (p (E.symm x))))) =
        E (p (E.symm x))
      rw [E.symm_apply_apply]
      exact congrArg E (LinearMap.congr_fun hp.eq (E.symm x))
    have hupper : IsUpperTriangular
        (A := SymmetricRing K τ)
        (L := L →₀ SymmetricRing K τ)
        (H := H →₀ SymmetricRing K τ) P :=
      minimumDegreeSplitEnd_isUpperTriangular b degree p htri
    let e : (L →₀ SymmetricRing K τ) →ₗ[SymmetricRing K τ]
        (L →₀ SymmetricRing K τ) :=
      leftDiagonalBlock
        (A := SymmetricRing K τ)
        (L := L →₀ SymmetricRing K τ)
        (H := H →₀ SymmetricRing K τ) P
    let a : (H →₀ SymmetricRing K τ) →ₗ[SymmetricRing K τ]
        (L →₀ SymmetricRing K τ) :=
      upperRightBlock
        (A := SymmetricRing K τ)
        (L := L →₀ SymmetricRing K τ)
        (H := H →₀ SymmetricRing K τ) P
    let f : (H →₀ SymmetricRing K τ) →ₗ[SymmetricRing K τ]
        (H →₀ SymmetricRing K τ) :=
      rightDiagonalBlock
        (A := SymmetricRing K τ)
        (L := L →₀ SymmetricRing K τ)
        (H := H →₀ SymmetricRing K τ) P
    have hblock : P = upperBlock
        (A := SymmetricRing K τ)
        (L := L →₀ SymmetricRing K τ)
        (H := H →₀ SymmetricRing K τ) e a f :=
      eq_upperBlock_of_isUpperTriangular
        (A := SymmetricRing K τ)
        (L := L →₀ SymmetricRing K τ)
        (H := H →₀ SymmetricRing K τ) P hupper
    have hPblock : IsIdempotentElem (upperBlock
        (A := SymmetricRing K τ)
        (L := L →₀ SymmetricRing K τ)
        (H := H →₀ SymmetricRing K τ) e a f) :=
      hblock ▸ hP
    have he : IsIdempotentElem e := by
      apply LinearMap.ext
      intro x
      have hx := DFunLike.congr_fun hPblock.eq (x, 0)
      simpa [Module.End.mul_apply] using congrArg Prod.fst hx
    have hf : IsIdempotentElem f := by
      apply LinearMap.ext
      intro y
      have hy := DFunLike.congr_fun hPblock.eq (0, y)
      simpa [Module.End.mul_apply] using congrArg Prod.snd hy
    have hcompat : Compatible
        (A := SymmetricRing K τ)
        (L := L →₀ SymmetricRing K τ)
        (H := H →₀ SymmetricRing K τ) e a f := by
      apply LinearMap.ext
      intro y
      have hy := DFunLike.congr_fun hPblock.eq (0, y)
      simpa [Module.End.mul_apply] using congrArg Prod.fst hy
    let entry : L → L → K := fun i j =>
      Classical.choose (hconstant i.1 j.1 (by simp [L, i.2, j.2]))
    let p₀ : (L →₀ K) →ₗ[K] (L →₀ K) :=
      Matrix.toLin (Finsupp.basisSingleOne (R := K))
        (Finsupp.basisSingleOne (R := K)) entry
    have hmatrix :
        LinearMap.toMatrix
            (Finsupp.basisSingleOne : Module.Basis L (SymmetricRing K τ)
              (L →₀ SymmetricRing K τ))
            (Finsupp.basisSingleOne : Module.Basis L (SymmetricRing K τ)
              (L →₀ SymmetricRing K τ)) e =
          (LinearMap.toMatrix
            (Finsupp.basisSingleOne : Module.Basis L K (L →₀ K))
            (Finsupp.basisSingleOne : Module.Basis L K (L →₀ K)) p₀).map
              (algebraMap K (SymmetricRing K τ)) := by
      apply Matrix.ext
      intro i j
      rw [leftDiagonalBlock_toMatrix_apply]
      simpa [p₀, entry] using
        (Classical.choose_spec
          (hconstant i.1 j.1 (by simp [L, i.2, j.2])))
    have hp₀ : IsIdempotentElem p₀ := by
      apply (LinearMap.toMatrix (Finsupp.basisSingleOne (R := K))
        (Finsupp.basisSingleOne (R := K))).injective
      apply Matrix.map_injective
        (RingHom.injective (algebraMap K (SymmetricRing K τ)))
      rw [LinearMap.toMatrix_mul]
      change
        ((LinearMap.toMatrix (Finsupp.basisSingleOne (R := K))
          (Finsupp.basisSingleOne (R := K)) p₀) *
          (LinearMap.toMatrix (Finsupp.basisSingleOne (R := K))
            (Finsupp.basisSingleOne (R := K)) p₀)).map
              (algebraMap K (SymmetricRing K τ)) =
          (LinearMap.toMatrix (Finsupp.basisSingleOne (R := K))
            (Finsupp.basisSingleOne (R := K)) p₀).map
              (algebraMap K (SymmetricRing K τ))
      rw [Matrix.map_mul,
        ← hmatrix, ← LinearMap.toMatrix_mul]
      exact congrArg
        (LinearMap.toMatrix
          (Finsupp.basisSingleOne (R := SymmetricRing K τ))
          (Finsupp.basisSingleOne (R := SymmetricRing K τ))) he.eq
    let be : Module.Basis (Fin (Module.finrank K (LinearMap.range p₀)))
        (SymmetricRing K τ) e.fixedSubmodule :=
      fixedCoordinateBasisOfMatrixBaseChange e p₀ hp₀ hmatrix
    let bH : Module.Basis H (SymmetricRing K τ)
        (H →₀ SymmetricRing K τ) := Finsupp.basisSingleOne
    let degreeH : H → ℕ := fun i => degree i.1
    let inHigh : (H →₀ SymmetricRing K τ) →ₗ[SymmetricRing K τ]
        ((L →₀ SymmetricRing K τ) ×
          (H →₀ SymmetricRing K τ)) :=
      LinearMap.inr (SymmetricRing K τ)
        (L →₀ SymmetricRing K τ)
        (H →₀ SymmetricRing K τ)
    let realizeH : (H →₀ SymmetricRing K τ) →ₗ[SymmetricRing K τ]
        PolynomialRing K τ := realize.comp (E.symm.toLinearMap.comp inHigh)
    have hrealizeH : Function.Injective realizeH :=
      hrealize.comp (E.symm.injective.comp
        (LinearMap.inr_injective
          (R := SymmetricRing K τ)
          (M := L →₀ SymmetricRing K τ)
          (M₂ := H →₀ SymmetricRing K τ)))
    have hbH : ∀ i, MvPolynomial.IsHomogeneous
        (realizeH (bH i)) (degreeH i) := by
      intro i
      have harg : E.symm (inHigh (bH i)) = b i.1 := by
        change (minimumDegreeCoordinateEquiv b degree).symm
          (0, Finsupp.single i 1) = b i.1
        rw [minimumDegreeCoordinateEquiv_symm_high]
        simp
      change MvPolynomial.IsHomogeneous
        (realize (E.symm (inHigh (bH i)))) (degree i.1)
      rw [harg]
      exact hb i.1
    have hdegreeH : ∀ i, degreeH i ≤ degreeBound :=
      fun i => hdegree i.1
    have hpreservesH : ∀ {x : H →₀ SymmetricRing K τ} {d : ℕ},
        MvPolynomial.IsHomogeneous (realizeH x) d →
          MvPolynomial.IsHomogeneous (realizeH (f x)) d := by
      intro x d hx
      have hpHom : MvPolynomial.IsHomogeneous
          (realize (p (E.symm (0, x)))) d := by
        exact hpreserves (by simpa [realizeH, inHigh] using hx)
      have hproj := embeddedBasisCoordinateProjection_preserves_homogeneous
        b realize hrealize degree hb
        (fun i => degree i ≠ degree (minimumDegreeIndex degree)) hpHom
      rw [← rightDiagonalBlock_as_coordinateProjection
        b degree p x] at hproj
      simpa [realizeH, inHigh, E, f] using hproj
    have htriH : ∀ i j, degreeH j < degreeH i →
        bH.repr (f (bH j)) i = 0 := by
      intro i j hij
      have h := htri i.1 j.1 hij
      have hentry := rightDiagonalBlock_toMatrix_apply b degree p i j
      rw [LinearMap.toMatrix_apply] at hentry
      have heq : bH.repr (f (bH j)) i = b.repr (p (b j.1)) i.1 := by
        simpa [bH, f, P] using hentry
      rw [heq]
      exact h
    have hconstantH : ∀ i j, degreeH i = degreeH j →
        ∃ r : K, bH.repr (f (bH j)) i =
          algebraMap K (SymmetricRing K τ) r := by
      intro i j hij
      obtain ⟨r, hr⟩ := hconstant i.1 j.1 hij
      refine ⟨r, ?_⟩
      have hentry := rightDiagonalBlock_toMatrix_apply b degree p i j
      rw [LinearMap.toMatrix_apply] at hentry
      have heq : bH.repr (f (bH j)) i = b.repr (p (b j.1)) i.1 := by
        simpa [bH, f, P] using hentry
      rw [heq]
      exact hr
    let bfData : BoundedHomogeneousFixedBasis
        (K := K) (τ := τ) (N := H →₀ SymmetricRing K τ)
        f realizeH degreeBound :=
      boundedHomogeneousFixedBasis_of_degreeTriangular
      (K := K) (τ := τ) (J := H)
      (N := H →₀ SymmetricRing K τ)
      bH realizeH hrealizeH degreeH degreeBound hbH hdegreeH
      f hf hpreservesH htriH hconstantH
    have hPE : conjugateEnd
        (A := SymmetricRing K τ) (M := N)
        (N := (L →₀ SymmetricRing K τ) × (H →₀ SymmetricRing K τ))
        E p = P := by
      change minimumDegreeSplitEnd b degree p = P
      rfl
    refine assembleBoundedConjugateFixedBasis
      (K := K) (τ := τ) (M := N)
      (L := L →₀ SymmetricRing K τ)
      (H := H →₀ SymmetricRing K τ)
      (ι := Fin (Module.finrank K (LinearMap.range p₀)))
      (realizeH := realizeH)
      E p P hPE e a f hblock hcompat be realize degreeBound
      (degree (minimumDegreeIndex degree)) bfData ?_ ?_ ?_
    · intro i
      have hsum : realize (E.symm ((be i).1, 0)) =
          ∑ j : L, ((be i).1 j).1 * realize (b j.1) := by
        have hcoords : E.symm ((be i).1, 0) =
            ∑ j : L, (be i).1 j • b j.1 := by
          apply E.injective
          rw [E.apply_symm_apply, map_sum]
          apply Prod.ext
          · rw [Prod.fst_sum]
            simp only [map_smul, E, minimumDegreeCoordinateEquiv_apply_low,
              Prod.smul_fst, Finsupp.smul_single, smul_eq_mul, mul_one]
            exact (sum_finsupp_single_apply_eq_self (be i).1).symm
          · rw [Prod.snd_sum]
            simp only [map_smul, E, minimumDegreeCoordinateEquiv_apply_low,
              Prod.smul_snd, smul_zero, Finset.sum_const_zero]
        rw [hcoords, map_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [map_smul]
        rfl
      rw [hsum]
      apply MvPolynomial.IsHomogeneous.sum Finset.univ _
        (degree (minimumDegreeIndex degree))
      intro j hj
      have hcoeff : (be i).1 j =
          algebraMap K (SymmetricRing K τ)
            (adaptedProjectionBasis p₀ hp₀ (Sum.inl i) j) := by
        simpa [be] using fixedCoordinateBasisOfMatrixBaseChange_apply
          e p₀ hp₀ hmatrix i j
      change MvPolynomial.IsHomogeneous
        (((be i).1 j).1 * realize (b j.1))
          (degree (minimumDegreeIndex degree))
      rw [hcoeff]
      simpa [j.2] using
        (MvPolynomial.isHomogeneous_C τ
          (adaptedProjectionBasis p₀ hp₀ (Sum.inl i) j)).mul
            (hb j.1)
    · intro i
      have hfi : f (bfData.basis i).1 = (bfData.basis i).1 :=
        (bfData.basis i).2
      have hlift : E.symm
            (a (bfData.basis i).1, (bfData.basis i).1) =
          p (E.symm (0, (bfData.basis i).1)) := by
        apply E.injective
        rw [E.apply_symm_apply]
        calc
          (a (bfData.basis i).1, (bfData.basis i).1) =
              P (0, (bfData.basis i).1) := by
            rw [hblock, upperBlock_apply, map_zero, zero_add, hfi]
          _ = (conjugateEnd
                (A := SymmetricRing K τ) (M := N)
                (N := (L →₀ SymmetricRing K τ) ×
                  (H →₀ SymmetricRing K τ)) E p)
              (0, (bfData.basis i).1) := by rw [hPE]
          _ = E (p (E.symm (0, (bfData.basis i).1))) := rfl
      rw [hlift]
      exact hpreserves (by
        simpa [realizeH, inHigh] using bfData.basis_homogeneous i)
    · exact hdegree (minimumDegreeIndex degree)
  · letI : IsEmpty J := ⟨fun j => hnonempty ⟨j⟩⟩
    letI : Subsingleton N :=
      ⟨fun x y => b.repr.injective (Subsingleton.elim _ _)⟩
    letI : Subsingleton p.fixedSubmodule := inferInstance
    exact
      { Index := PEmpty
        indexFintype := inferInstance
        basis := Module.Basis.empty p.fixedSubmodule
        degree := fun i => isEmptyElim i
        basis_homogeneous := fun i => isEmptyElim i
        degree_le := fun i => isEmptyElim i }
termination_by Fintype.card J
decreasing_by
  exact card_higherDegreeIndex_lt degree

end

end LeanProofs.PolynomialFormulas.LazardInvariantFiniteDegreeInduction
