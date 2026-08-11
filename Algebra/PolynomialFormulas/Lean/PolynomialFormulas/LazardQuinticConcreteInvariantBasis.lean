import PolynomialFormulas.LazardQuinticRootInvariantOrbits
import PolynomialFormulas.LazardQuinticCoinvariantNormalForms
import PolynomialFormulas.LazardDisplayedGroebnerQuintic
import PolynomialFormulas.LazardInvariantGradedReynolds
import PolynomialFormulas.LazardInvariantLeadingTermDescent
import PolynomialFormulas.LazardQuinticInvariantHilbertRank
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The concrete six-element `F20` invariant-basis problem

This file isolates the still-missing concrete computation in Section 6 of
Lazard's paper.  The candidate family is

`1, i4, i5, i6, i7, i8`

in degrees `0, 4, 5, 6, 7, 8`.  Every candidate below is the actual orbit
polynomial from `LazardQuinticRootInvariants`, bundled as an element of the
standard `F20` invariant module.

The finite certificate interface uses the 120-element Artin basis of
`Q[x0,...,x4]` over the symmetric ring.  Specializing the symmetric
coefficients at the augmentation ideal gives a concrete 120-dimensional
rational coordinate model.  Thus the two finite checks needed by the
coinvariant route are literal rational-matrix assertions:

* a selected `6 x 6` minor of the six candidate columns has nonzero
  determinant;
* the stacked `F20` fixed-point matrix has rank `114`, hence fixed space
  dimension `6`.

The non-finite lifting argument is proved here.  Reynolds averaging makes the
passage to invariants exact, and strong induction on homogeneous degree lifts
the six coinvariant generators.  This is a genuine graded argument.  Ordinary
Nakayama over `Q[e1,...,e5]` cannot be applied globally, since the
positive-degree ideal is not contained in the Jacobson radical.

The six-by-six minor is derived below from kernel-checked sparse quotient
witnesses.  Together with the Molien upper bound, that minor determines the
fixed-space dimension and hence proves the stacked rank assertion internally.
No finite certificate or global lifting hypothesis remains in the final basis
constructor.
-/

open scoped BigOperators
open Equiv MvPolynomial Matrix

namespace LeanProofs.PolynomialFormulas.LazardQuinticConcreteInvariantBasis

open LeanProofs.PolynomialFormulas.Fin5Solvable
open LeanProofs.PolynomialFormulas.FrobeniusDummitResolvent
open LeanProofs.PolynomialFormulas.LazardInvariantModule
open LeanProofs.PolynomialFormulas.LazardInvariantArtinBasis
open LeanProofs.PolynomialFormulas.LazardInvariantArtinModuleBasis
open LeanProofs.PolynomialFormulas.LazardInvariantHomogeneousCoordinates
open LeanProofs.PolynomialFormulas.LazardInvariantGradedReynolds
open LeanProofs.PolynomialFormulas.LazardInvariantLeadingTermDescent
open LeanProofs.PolynomialFormulas.LazardQuintic
open LeanProofs.PolynomialFormulas.LazardQuinticSparseNormalFormSupport

set_option autoImplicit false

noncomputable section

abbrev FivePolynomialRing := MvPolynomial (Fin 5) ℚ

abbrev SymmetricFiveRing :=
  MvPolynomial.symmetricSubalgebra (Fin 5) ℚ

abbrev F20InvariantModule :=
  (subgroupRepresentation ℚ (Fin 5) standardF20).invariants

local instance standardF20Fintype : Fintype standardF20 :=
  Fintype.ofFinite standardF20

/-! ## The honest six candidates -/

/-- Lazard's six proposed module generators as ambient polynomials. -/
noncomputable def candidatePolynomial : Fin 6 → FivePolynomialRing :=
  ![(1 : FivePolynomialRing),
    metacyclicOrbitPolynomialOver ℚ i4Exponent,
    metacyclicOrbitPolynomialOver ℚ i5Exponent,
    metacyclicOrbitPolynomialOver ℚ i6Exponent,
    metacyclicOrbitPolynomialOver ℚ i7Exponent,
    metacyclicOrbitPolynomialOver ℚ i8Exponent]

/-- The degrees printed by Lazard for the proposed basis. -/
def candidateDegree : Fin 6 → ℕ := ![0, 4, 5, 6, 7, 8]

/-- The total weight of an exponent function. -/
def exponentWeight (d : RootExponent) : ℕ := ∑ i : Fin 5, d i

theorem exponentWeight_actExponent (g : Fin5Solvable.S5)
    (d : RootExponent) :
    exponentWeight (actExponent g d) = exponentWeight d := by
  simpa only [exponentWeight, actExponent] using Equiv.sum_comp g.symm d

/-- Every integral orbit polynomial is homogeneous in its visible exponent
weight. -/
theorem metacyclicOrbitPolynomial_isHomogeneous (d : RootExponent) :
    MvPolynomial.IsHomogeneous (metacyclicOrbitPolynomial d)
      (exponentWeight d) := by
  classical
  rw [metacyclicOrbitPolynomial, polynomialOfSupport]
  apply MvPolynomial.IsHomogeneous.sum
  intro e he
  apply MvPolynomial.isHomogeneous_monomial
  rw [Finsupp.degree_eq_sum]
  rcases Finset.mem_image.mp he with ⟨g, -, rfl⟩
  exact exponentWeight_actExponent g d

/-- Scalar extension does not change the homogeneous degree of an orbit
polynomial. -/
theorem metacyclicOrbitPolynomialOver_isHomogeneous
    (K : Type*) [CommRing K] (d : RootExponent) :
    MvPolynomial.IsHomogeneous (metacyclicOrbitPolynomialOver K d)
      (exponentWeight d) := by
  simpa [metacyclicOrbitPolynomialOver] using
    (metacyclicOrbitPolynomial_isHomogeneous d).map (Int.castRingHom K)

@[simp] theorem exponentWeight_i4 : exponentWeight i4Exponent = 4 := by decide
@[simp] theorem exponentWeight_i5 : exponentWeight i5Exponent = 5 := by decide
@[simp] theorem exponentWeight_i6 : exponentWeight i6Exponent = 6 := by decide
@[simp] theorem exponentWeight_i7 : exponentWeight i7Exponent = 7 := by decide
@[simp] theorem exponentWeight_i8 : exponentWeight i8Exponent = 8 := by decide

/-- The candidate polynomials have precisely the six displayed degrees. -/
theorem candidatePolynomial_isHomogeneous (j : Fin 6) :
    MvPolynomial.IsHomogeneous (candidatePolynomial j)
      (candidateDegree j) := by
  fin_cases j
  · simpa [candidatePolynomial, candidateDegree] using
      (MvPolynomial.isHomogeneous_one (R := ℚ) (σ := Fin 5))
  · simpa [candidatePolynomial, candidateDegree] using
      (metacyclicOrbitPolynomialOver_isHomogeneous ℚ i4Exponent)
  · simpa [candidatePolynomial, candidateDegree] using
      (metacyclicOrbitPolynomialOver_isHomogeneous ℚ i5Exponent)
  · simpa [candidatePolynomial, candidateDegree] using
      (metacyclicOrbitPolynomialOver_isHomogeneous ℚ i6Exponent)
  · simpa [candidatePolynomial, candidateDegree] using
      (metacyclicOrbitPolynomialOver_isHomogeneous ℚ i7Exponent)
  · simpa [candidatePolynomial, candidateDegree] using
      (metacyclicOrbitPolynomialOver_isHomogeneous ℚ i8Exponent)

/-- The six ambient polynomials, bundled with their already-proved `F20`
invariance. -/
noncomputable def concreteInvariant (j : Fin 6) : F20InvariantModule :=
  ⟨candidatePolynomial j, by
    rw [mem_subgroupRepresentation_invariants,
      mem_invariantSubalgebra]
    intro g
    fin_cases j
    · simp [candidatePolynomial]
    · simpa [candidatePolynomial] using
        rename_metacyclicOrbitPolynomialOver ℚ g.1 g.2 i4Exponent
    · simpa [candidatePolynomial] using
        rename_metacyclicOrbitPolynomialOver ℚ g.1 g.2 i5Exponent
    · simpa [candidatePolynomial] using
        rename_metacyclicOrbitPolynomialOver ℚ g.1 g.2 i6Exponent
    · simpa [candidatePolynomial] using
        rename_metacyclicOrbitPolynomialOver ℚ g.1 g.2 i7Exponent
    · simpa [candidatePolynomial] using
        rename_metacyclicOrbitPolynomialOver ℚ g.1 g.2 i8Exponent⟩

@[simp]
theorem concreteInvariant_val (j : Fin 6) :
    (concreteInvariant j).1 = candidatePolynomial j :=
  rfl

theorem concreteInvariant_isHomogeneous (j : Fin 6) :
    MvPolynomial.IsHomogeneous (concreteInvariant j).1
      (candidateDegree j) := by
  simpa using candidatePolynomial_isHomogeneous j

/-! ## The 120-dimensional Artin coinvariant coordinate model -/

abbrev ArtinFiveIndex := ArtinIndex 5

/-- The actual Artin basis of the ambient polynomial ring over the symmetric
coefficient ring. -/
noncomputable def artinFiveBasis :
    Module.Basis ArtinFiveIndex SymmetricFiveRing FivePolynomialRing :=
  symmetricArtinBasis ℚ 5

/-- Specialize every positive-degree symmetric coefficient to zero. -/
def symmetricAugmentation : SymmetricFiveRing →+* ℚ :=
  (MvPolynomial.constantCoeff : FivePolynomialRing →+* ℚ).comp
    (Subalgebra.val SymmetricFiveRing :
      SymmetricFiveRing →ₐ[ℚ] FivePolynomialRing).toRingHom

/-- The augmentation is also a rational algebra homomorphism. -/
def symmetricAugmentationAlgHom : SymmetricFiveRing →ₐ[ℚ] ℚ where
  toRingHom := symmetricAugmentation
  commutes' r := by
    simp [symmetricAugmentation, MvPolynomial.algebraMap_eq]

@[simp]
theorem symmetricAugmentation_algebraMap (r : ℚ) :
    symmetricAugmentation (algebraMap ℚ SymmetricFiveRing r) = r := by
  exact symmetricAugmentationAlgHom.commutes r

theorem symmetricAugmentation_eq_symmetricConstantCoeff :
    symmetricAugmentation = symmetricConstantCoeff ℚ 5 :=
  rfl

/-- One symmetric Artin coordinate of an ambient polynomial. -/
noncomputable def artinCoordinate
    (p : FivePolynomialRing) (a : ArtinFiveIndex) : SymmetricFiveRing :=
  (artinFiveBasis.repr p) a

/-- The augmentation of all 120 Artin coordinates.  This function-space is
the concrete vector-space model for the symmetric coinvariant quotient. -/
abbrev ArtinCoinvariantModel := ArtinFiveIndex → ℚ

noncomputable def artinCoinvariantCoordinates
    (p : FivePolynomialRing) : ArtinCoinvariantModel :=
  fun a ↦ symmetricAugmentation (artinCoordinate p a)

/-- Coinvariant coordinates are rational-linear.  Naming this map makes the
finite-dimensional quotient calculation usable inside the graded proof. -/
noncomputable def artinCoinvariantCoordinatesLinear :
    FivePolynomialRing →ₗ[ℚ] ArtinCoinvariantModel :=
  LinearMap.pi fun a ↦
    symmetricAugmentationAlgHom.toLinearMap.comp
      ((artinFiveBasis.coord a).restrictScalars ℚ)

@[simp]
theorem artinCoinvariantCoordinatesLinear_apply (p : FivePolynomialRing) :
    artinCoinvariantCoordinatesLinear p = artinCoinvariantCoordinates p :=
  rfl

theorem artinCoinvariantModel_finrank :
    Module.finrank ℚ ArtinCoinvariantModel = 120 := by
  rw [Module.finrank_fintype_fun_eq_card,
    LazardInvariantArtinBasis.card_artinIndex]
  norm_num

/-- The six full 120-coordinate residue vectors. -/
noncomputable def candidateCoinvariantVector
    (j : Fin 6) : ArtinCoinvariantModel :=
  artinCoinvariantCoordinates (candidatePolynomial j)

/-! ## The six explicit pivot rows -/

/-- Exponents of the six Artin rows found by exact triangular reduction.
They have degrees `0,4,5,6,7,8`, respectively. -/
def explicitPivotExponent : Fin 6 → Fin 5 → ℕ :=
  ![![0, 0, 0, 0, 0],
    ![0, 1, 2, 1, 0],
    ![0, 2, 2, 1, 0],
    ![1, 2, 2, 1, 0],
    ![2, 2, 2, 1, 0],
    ![3, 2, 2, 1, 0]]

/-- The six exponent rows bundled with the Artin staircase bounds
`a_i < 5-i`. -/
def explicitPivot : Fin 6 → ArtinFiveIndex :=
  fun j i ↦ ⟨explicitPivotExponent j i, by
    fin_cases j <;> fin_cases i <;> decide⟩

@[simp]
theorem artinDegree_explicitPivot (j : Fin 6) :
    artinDegree (explicitPivot j) = candidateDegree j := by
  fin_cases j <;> decide

/-- The diagonal values of the candidate residue minor. -/
def candidatePivotDiagonal : Fin 6 → ℚ := ![1, 2, 2, 2, 2, 4]

@[simp]
theorem candidatePivotDiagonal_ne_zero (j : Fin 6) :
    candidatePivotDiagonal j ≠ 0 := by
  fin_cases j <;> decide

/-- The exact expected result of the six finite normal-form computations. -/
def expectedCandidateResiduePivotMatrix : Matrix (Fin 6) (Fin 6) ℚ :=
  Matrix.diagonal candidatePivotDiagonal

/-! ## A concrete minor certificate for independence -/

/-- Six selected Artin rows, before augmentation. -/
noncomputable def candidateArtinMatrix
    (pivot : Fin 6 → ArtinFiveIndex) :
    Matrix (Fin 6) (Fin 6) SymmetricFiveRing :=
  fun row column ↦
    artinCoordinate (candidatePolynomial column) (pivot row)

/-- The selected `6 x 6` rational coinvariant minor. -/
noncomputable def candidateResiduePivotMatrix
    (pivot : Fin 6 → ArtinFiveIndex) : Matrix (Fin 6) (Fin 6) ℚ :=
  fun row column ↦ candidateCoinvariantVector column (pivot row)

/-- The six-by-six normal-form equality later discharged by the generated
sparse quotient witnesses. -/
def CandidateResiduePivotCertificate : Prop :=
  candidateResiduePivotMatrix explicitPivot =
    expectedCandidateResiduePivotMatrix

theorem candidateResiduePivotMatrix_det_eq_64
    (hpivot : CandidateResiduePivotCertificate) :
    (candidateResiduePivotMatrix explicitPivot).det = 64 := by
  rw [hpivot]
  simp [expectedCandidateResiduePivotMatrix, candidatePivotDiagonal,
    Fin.prod_univ_succ]
  norm_num

theorem candidateResiduePivotMatrix_det_ne_zero
    (hpivot : CandidateResiduePivotCertificate) :
    (candidateResiduePivotMatrix explicitPivot).det ≠ 0 := by
  rw [candidateResiduePivotMatrix_det_eq_64 hpivot]
  norm_num

theorem candidateResiduePivotMatrix_eq_map
    (pivot : Fin 6 → ArtinFiveIndex) :
    candidateResiduePivotMatrix pivot =
      (candidateArtinMatrix pivot).map symmetricAugmentation :=
  rfl

/-- A nonzero rational residue determinant implies that the corresponding
determinant over the symmetric ring is nonzero. -/
theorem candidateArtinMatrix_det_ne_zero_of_residue
    (pivot : Fin 6 → ArtinFiveIndex)
    (hdet : (candidateResiduePivotMatrix pivot).det ≠ 0) :
    (candidateArtinMatrix pivot).det ≠ 0 := by
  intro hzero
  apply hdet
  calc
    (candidateResiduePivotMatrix pivot).det =
        symmetricAugmentation ((candidateArtinMatrix pivot).det) := by
          rw [candidateResiduePivotMatrix_eq_map]
          exact (symmetricAugmentation.map_det _).symm
    _ = 0 := by rw [hzero, map_zero]

/-- Projection to the six selected Artin coordinates. -/
noncomputable def pivotArtinCoordinates
    (pivot : Fin 6 → ArtinFiveIndex) :
    FivePolynomialRing →ₗ[SymmetricFiveRing]
      (Fin 6 → SymmetricFiveRing) :=
  LinearMap.pi fun row ↦ (artinFiveBasis.coord (pivot row))

/-- A certified nonzero residue minor proves honest linear independence over
the full symmetric polynomial ring. -/
theorem candidatePolynomial_linearIndependent_of_residue_det
    (pivot : Fin 6 → ArtinFiveIndex)
    (hdet : (candidateResiduePivotMatrix pivot).det ≠ 0) :
    LinearIndependent SymmetricFiveRing candidatePolynomial := by
  have hfull : (candidateArtinMatrix pivot).det ≠ 0 :=
    candidateArtinMatrix_det_ne_zero_of_residue pivot hdet
  have hcolumns := Matrix.linearIndependent_cols_of_det_ne_zero hfull
  have himage : LinearIndependent SymmetricFiveRing
      (fun column ↦ pivotArtinCoordinates pivot
        (candidatePolynomial column)) := by
    have hfamily :
        (fun column ↦ pivotArtinCoordinates pivot
            (candidatePolynomial column)) =
          (candidateArtinMatrix pivot).col := by
      funext column row
      rfl
    rw [hfamily]
    exact hcolumns
  exact LinearIndependent.of_comp (pivotArtinCoordinates pivot) <| by
    simpa [Function.comp_def] using himage

/-- The same independence statement in the invariant subtype. -/
theorem concreteInvariant_linearIndependent_of_residue_det
    (pivot : Fin 6 → ArtinFiveIndex)
    (hdet : (candidateResiduePivotMatrix pivot).det ≠ 0) :
    LinearIndependent SymmetricFiveRing concreteInvariant := by
  refine LinearIndependent.of_comp F20InvariantModule.subtype ?_
  simpa [Function.comp_def] using
    candidatePolynomial_linearIndependent_of_residue_det pivot hdet

/-! ## The explicit fixed-coinvariant matrix -/

/-- Renaming a polynomial acts on its Artin coordinates by the matrix whose
columns are the renamed Artin basis vectors. -/
theorem artinCoordinate_rename_eq_sum
    (h : Equiv.Perm (Fin 5)) (p : FivePolynomialRing)
    (row : ArtinFiveIndex) :
    artinCoordinate (MvPolynomial.rename h p) row =
      ∑ column : ArtinFiveIndex,
        artinCoordinate p column *
          artinCoordinate
            (MvPolynomial.rename h (artinFiveBasis column)) row := by
  classical
  have hdecomp :
      MvPolynomial.rename h p =
        ∑ column : ArtinFiveIndex,
          artinCoordinate p column •
            MvPolynomial.rename h (artinFiveBasis column) := by
    calc
      MvPolynomial.rename h p = renameLinear ℚ (Fin 5) h p := rfl
      _ = renameLinear ℚ (Fin 5) h
          (∑ column : ArtinFiveIndex,
            artinCoordinate p column • artinFiveBasis column) := by
          exact congrArg (renameLinear ℚ (Fin 5) h) <| by
            simpa only [artinCoordinate] using
              (artinFiveBasis.sum_repr p).symm
      _ = _ := by rw [map_sum]; simp
  change artinFiveBasis.coord row (MvPolynomial.rename h p) = _
  rw [hdecomp, map_sum]
  apply Finset.sum_congr rfl
  intro column hcolumn
  rw [map_smul]
  rfl

/-- The action of one `F20` element on the Artin coinvariant coordinate
model.  Column `column` is obtained by renaming the corresponding Artin basis
polynomial and then reducing its symmetric coefficients by augmentation. -/
noncomputable def coinvariantActionMatrix (h : standardF20) :
    Matrix ArtinFiveIndex ArtinFiveIndex ℚ :=
  fun row column ↦
    symmetricAugmentation <|
      artinCoordinate (MvPolynomial.rename h.1 (artinFiveBasis column)) row

/-- The coordinate quotient really intertwines variable permutation with the
displayed finite action matrix. -/
theorem artinCoinvariantCoordinates_rename (h : standardF20)
    (p : FivePolynomialRing) :
    artinCoinvariantCoordinates (MvPolynomial.rename h.1 p) =
      coinvariantActionMatrix h *ᵥ artinCoinvariantCoordinates p := by
  classical
  funext row
  rw [artinCoinvariantCoordinates, artinCoordinate_rename_eq_sum]
  simp [artinCoinvariantCoordinates, coinvariantActionMatrix,
    Matrix.mulVec, dotProduct, map_sum, map_mul, mul_comm]

/-- Stack the twenty fixed-point systems `(rho(h) - 1) v = 0` into one
finite rational matrix. -/
noncomputable def fixedCoinvariantConstraintMatrix :
    Matrix (standardF20 × ArtinFiveIndex) ArtinFiveIndex ℚ :=
  fun row column ↦
    (coinvariantActionMatrix row.1 - 1) row.2 column

/-- The subspace cut out by the explicit stacked fixed-point matrix. -/
noncomputable def fixedCoinvariantSubspace :
    Submodule ℚ ArtinCoinvariantModel :=
  LinearMap.ker fixedCoinvariantConstraintMatrix.mulVecLin

/-- One coordinate of multiplication by the identity matrix. -/
@[simp]
theorem identityMatrix_coordinate_sum
    (v : ArtinCoinvariantModel) (row : ArtinFiveIndex) :
    (∑ column : ArtinFiveIndex,
      (1 : Matrix ArtinFiveIndex ArtinFiveIndex ℚ) row column * v column) =
        v row := by
  change ((1 : Matrix ArtinFiveIndex ArtinFiveIndex ℚ) *ᵥ v) row = v row
  rw [Matrix.one_mulVec]

/-- Literal finite equations saying that the six candidate residue columns
are fixed. -/
def CandidateFixedCoinvariantEquations : Prop :=
  ∀ j : Fin 6,
    fixedCoinvariantConstraintMatrix *ᵥ candidateCoinvariantVector j = 0

/-- Literal finite rank assertion equivalent to fixed-space dimension six. -/
def FixedCoinvariantRankCertificate : Prop :=
  fixedCoinvariantConstraintMatrix.rank = 114

/-- Every invariant has a fixed residue vector.  This is the exactness input
needed by the graded lifting proof; it is a theorem, not a certificate. -/
theorem invariant_coinvariantCoordinates_mem_fixed
    (p : F20InvariantModule) :
    artinCoinvariantCoordinates p.1 ∈ fixedCoinvariantSubspace := by
  rw [fixedCoinvariantSubspace, LinearMap.mem_ker,
    Matrix.mulVecLin_apply]
  funext row
  have hinvariant : MvPolynomial.rename row.1.1 p.1 = p.1 := p.2 row.1
  have haction := congrFun
    (artinCoinvariantCoordinates_rename row.1 p.1) row.2
  rw [hinvariant] at haction
  simpa [fixedCoinvariantConstraintMatrix, Matrix.mulVec, dotProduct,
    sub_mul, Finset.sum_sub_distrib, identityMatrix_coordinate_sum] using
      sub_eq_zero.mpr haction.symm

/-- In particular, the six candidate vectors satisfy the fixed equations
without a separate finite certificate. -/
theorem candidateFixedCoinvariantEquations :
    CandidateFixedCoinvariantEquations := by
  intro j
  exact invariant_coinvariantCoordinates_mem_fixed (concreteInvariant j)

theorem candidateCoinvariantVector_mem_fixed
    (hfixed : CandidateFixedCoinvariantEquations) (j : Fin 6) :
    candidateCoinvariantVector j ∈ fixedCoinvariantSubspace := by
  rw [fixedCoinvariantSubspace, LinearMap.mem_ker,
    Matrix.mulVecLin_apply]
  exact hfixed j

/-! ## Exactness of invariant coinvariant residues -/

/-- Multiplying an ambient polynomial by a symmetric coefficient multiplies
its coinvariant residue by the augmentation of that coefficient. -/
theorem artinCoinvariantCoordinates_smul
    (c : SymmetricFiveRing) (p : FivePolynomialRing) :
    artinCoinvariantCoordinates (c • p) =
      symmetricAugmentation c • artinCoinvariantCoordinates p := by
  funext a
  change symmetricAugmentation (artinFiveBasis.repr (c • p) a) = _
  rw [map_smul]
  change symmetricAugmentation (c * artinFiveBasis.repr p a) = _
  rw [map_mul]
  rfl

/-- The rational algebra map to itself is literally the rational cast.  This
typed form prevents scalar-tower simplification from leaving an opaque
`algebraMap ℚ ℚ` in the lift calculation. -/
@[simp]
theorem algebraMap_rat_self (r : ℚ) :
    (algebraMap ℚ ℚ) r = r :=
  map_ratCast (algebraMap ℚ ℚ) r

/-- A typed self-algebra-map reduction for the symmetric coefficient ring. -/
@[simp]
theorem algebraMap_symmetricFiveRing_self_apply (c : SymmetricFiveRing) :
    (algebraMap SymmetricFiveRing SymmetricFiveRing) c = c :=
  Algebra.algebraMap_self_apply c

/-- A rational-linear section of the coinvariant-coordinate quotient, using
the actual Artin basis and constant symmetric coefficients. -/
noncomputable def artinCoinvariantLiftLinear :
    ArtinCoinvariantModel →ₗ[ℚ] FivePolynomialRing where
  toFun v := ∑ a : ArtinFiveIndex, v a • artinFiveBasis a
  map_add' v w := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r v := by
    simp only [Pi.smul_apply, smul_smul, Finset.smul_sum,
      RingHom.id_apply]

    apply Finset.sum_congr rfl
    intro a ha
    apply congrArg (fun q : ℚ ↦ q • artinFiveBasis a)
    rw [smul_eq_mul]

/-- Augmenting the Artin coordinates of a rational multiple of one basis
vector gives the corresponding scaled Kronecker coordinate. -/
@[simp]
theorem symmetricAugmentation_repr_rational_smul_basis
    (r : ℚ) (i a : ArtinFiveIndex) :
    symmetricAugmentation
        ((artinFiveBasis.repr (r • artinFiveBasis i)) a) =
      if i = a then r else 0 := by
  rw [← IsScalarTower.algebraMap_smul SymmetricFiveRing r
    (artinFiveBasis i)]
  rw [map_smul]
  by_cases h : i = a
  · subst a
    simp only [Module.Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_eq_same]
    rw [Algebra.smul_def, mul_one,
      algebraMap_symmetricFiveRing_self_apply,
      symmetricAugmentation_algebraMap]
    simp
  · simp [Module.Basis.repr_self, Finsupp.single_apply, h]

/-- Augmentation of one pointwise coordinate of the lifted basis sum.  Keeping
the Finsupp evaluation in this small lemma avoids elaborating the entire
120-term coordinate expression inside the right-inverse proof. -/
theorem symmetricAugmentation_repr_lift_sum_coordinate
    (v : ArtinCoinvariantModel) (a : ArtinFiveIndex) :
    symmetricAugmentation
        ((∑ x : ArtinFiveIndex,
          artinFiveBasis.repr (v x • artinFiveBasis x)) a) = v a := by
  rw [Finset.sum_apply', map_sum]
  simp [symmetricAugmentation_repr_rational_smul_basis]

@[simp]
theorem artinCoinvariantCoordinates_lift
    (v : ArtinCoinvariantModel) :
    artinCoinvariantCoordinates (artinCoinvariantLiftLinear v) = v := by
  classical
  funext a
  change symmetricAugmentation
      ((artinFiveBasis.repr
        (∑ x : ArtinFiveIndex, v x • artinFiveBasis x)) a) = v a
  rw [map_sum]
  exact symmetricAugmentation_repr_lift_sum_coordinate v a

/-- Membership in the stacked kernel says separately that every group action
fixes the residue vector. -/
theorem coinvariantActionMatrix_mulVec_eq_of_mem_fixed
    (v : ArtinCoinvariantModel) (hv : v ∈ fixedCoinvariantSubspace)
    (h : standardF20) :
    coinvariantActionMatrix h *ᵥ v = v := by
  rw [fixedCoinvariantSubspace, LinearMap.mem_ker,
    Matrix.mulVecLin_apply] at hv
  funext row
  have hz := congrFun hv (h, row)
  apply sub_eq_zero.mp
  simpa [fixedCoinvariantConstraintMatrix, Matrix.mulVec, dotProduct,
    sub_mul, Finset.sum_sub_distrib, identityMatrix_coordinate_sum] using hz

local instance f20AverageCardInvertible :
    Invertible (Fintype.card standardF20 : SymmetricFiveRing) :=
  symmetricNatCastInvertible ℚ (Fin 5) (Fintype.card standardF20)
    Fintype.card_ne_zero

/-- Average an arbitrary Artin lift and bundle the result as an invariant. -/
noncomputable def averagedCoinvariantLift
    (v : ArtinCoinvariantModel) : F20InvariantModule :=
  averageToInvariants ℚ 5 standardF20 (artinCoinvariantLiftLinear v)

/-- Reynolds averaging is exact after taking coinvariant residues: averaging
a lift of a fixed residue returns that same residue. -/
theorem artinCoinvariantCoordinates_averagedCoinvariantLift
    (v : fixedCoinvariantSubspace) :
    artinCoinvariantCoordinates (averagedCoinvariantLift v).1 = v.1 := by
  classical
  change artinCoinvariantCoordinates
      ((subgroupRepresentation ℚ (Fin 5) standardF20).averageMap
        (artinCoinvariantLiftLinear v.1)) = v.1
  rw [reynolds_averageMap_apply]
  rw [artinCoinvariantCoordinates_smul]
  rw [← artinCoinvariantCoordinatesLinear_apply, map_sum]
  simp_rw [artinCoinvariantCoordinatesLinear_apply]
  simp_rw [artinCoinvariantCoordinates_rename,
    artinCoinvariantCoordinates_lift,
    coinvariantActionMatrix_mulVec_eq_of_mem_fixed v.1 v.2]
  have hinv :
      symmetricAugmentation
          (⅟(Fintype.card standardF20 : SymmetricFiveRing)) =
        (Fintype.card standardF20 : ℚ)⁻¹ := by
    change symmetricAugmentation
      (algebraMap ℚ SymmetricFiveRing
        (Fintype.card standardF20 : ℚ)⁻¹) = _
    rw [symmetricAugmentation_algebraMap]
  rw [hinv, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  simp

/-- The residue vector of an invariant, bundled into the fixed subspace. -/
noncomputable def invariantResidue (p : F20InvariantModule) :
    fixedCoinvariantSubspace :=
  ⟨artinCoinvariantCoordinates p.1,
    invariant_coinvariantCoordinates_mem_fixed p⟩

/-- Multiplication of an invariant by a symmetric polynomial, constructed
directly on the underlying polynomials.  This avoids asking elaboration to
discover the scalar action on the nested invariant submodule. -/
noncomputable def symmetricInvariantProduct
    (c : SymmetricFiveRing) (p : F20InvariantModule) :
    F20InvariantModule :=
  ⟨c.1 * p.1, by
    rw [mem_subgroupRepresentation_invariants, mem_invariantSubalgebra]
    intro h
    have hp : MvPolynomial.rename h.1 p.1 = p.1 := by
      simpa only [subgroupRepresentation_apply] using p.2 h
    rw [map_mul, c.2 h.1, hp]⟩

@[simp]
theorem symmetricInvariantProduct_val
    (c : SymmetricFiveRing) (p : F20InvariantModule) :
    (symmetricInvariantProduct c p).1 = c.1 * p.1 :=
  rfl

/-- The canonical algebra map from the symmetric subalgebra into the ambient
polynomial ring is its underlying-value inclusion. -/
@[simp]
theorem algebraMap_symmetricFiveRing_apply (c : SymmetricFiveRing) :
    (algebraMap SymmetricFiveRing FivePolynomialRing) c = c.1 :=
  rfl

/-- The residue construction is rational-linear. -/
noncomputable def invariantResidueLinear :
    F20InvariantModule →ₗ[ℚ] fixedCoinvariantSubspace where
  toFun := invariantResidue
  map_add' p q := by
    apply Subtype.ext
    simpa [invariantResidue, ← artinCoinvariantCoordinatesLinear_apply]
      using map_add artinCoinvariantCoordinatesLinear p.1 q.1
  map_smul' r p := by
    apply Subtype.ext
    simpa [invariantResidue, ← artinCoinvariantCoordinatesLinear_apply]
      using map_smul artinCoinvariantCoordinatesLinear r p.1

@[simp]
theorem invariantResidueLinear_apply (p : F20InvariantModule) :
    invariantResidueLinear p = invariantResidue p :=
  rfl

/-- Any invariant whose underlying polynomial is a symmetric product has the
corresponding augmented residue. -/
theorem invariantResidue_eq_smul_of_val_eq
    (q : F20InvariantModule) (c : SymmetricFiveRing)
    (p : F20InvariantModule) (hq : q.1 = c.1 * p.1) :
    invariantResidue q =
      symmetricAugmentation c • invariantResidue p := by
  apply Subtype.ext
  change artinCoinvariantCoordinates q.1 =
    symmetricAugmentation c • artinCoinvariantCoordinates p.1
  rw [hq]
  simpa only [Algebra.smul_def, algebraMap_symmetricFiveRing_apply] using
    artinCoinvariantCoordinates_smul c p.1

/-- Explicit symmetric multiplication descends through augmentation on
invariant residues. -/
theorem invariantResidue_symmetricInvariantProduct
    (c : SymmetricFiveRing) (p : F20InvariantModule) :
    invariantResidue (symmetricInvariantProduct c p) =
      symmetricAugmentation c • invariantResidue p := by
  exact invariantResidue_eq_smul_of_val_eq
    (symmetricInvariantProduct c p) c p rfl

/-- In characteristic zero, taking invariant residues is surjective onto the
fixed subspace of the coinvariant representation. -/
theorem invariantResidue_surjective :
    Function.Surjective invariantResidue := by
  intro v
  refine ⟨averagedCoinvariantLift v, ?_⟩
  apply Subtype.ext
  exact artinCoinvariantCoordinates_averagedCoinvariantLift v

abbrev AbstractF20BasisIndex :=
  LazardQuinticInvariantHilbertRank.abstractF20Basis.Index

local instance abstractF20BasisIndexFintype :
    Fintype AbstractF20BasisIndex :=
  LazardQuinticInvariantHilbertRank.abstractF20Basis.indexFintype

/-- Residues of the homogeneous symmetric-module basis obtained from the
general Reynolds construction. -/
noncomputable def abstractInvariantResidue
    (i : AbstractF20BasisIndex) : fixedCoinvariantSubspace :=
  invariantResidue
    (LazardQuinticInvariantHilbertRank.abstractF20Basis.basis i)

/-- Every invariant residue is a rational combination of the residues of the
abstract symmetric-module basis. -/
theorem invariantResidue_eq_abstract_sum (p : F20InvariantModule) :
    invariantResidue p =
      ∑ i : AbstractF20BasisIndex,
        symmetricAugmentation
            (LazardQuinticInvariantHilbertRank.abstractF20Basis.basis.repr p i) •
          abstractInvariantResidue i := by
  have hrepr :=
    LazardQuinticInvariantHilbertRank.abstractF20Basis.basis.sum_repr p
  have hres := congrArg invariantResidue hrepr
  rw [← hres]
  rw [← invariantResidueLinear_apply, map_sum]
  simp only [invariantResidueLinear_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply invariantResidue_eq_smul_of_val_eq
  simp only [SetLike.val_smul, Algebra.smul_def,
    algebraMap_symmetricFiveRing_apply]

/-- The abstract basis residues span every fixed coinvariant vector. -/
theorem abstractInvariantResidue_span_eq_top :
    Submodule.span ℚ (Set.range abstractInvariantResidue) = ⊤ := by
  apply top_unique
  intro v hv
  rcases invariantResidue_surjective v with ⟨p, rfl⟩
  rw [invariantResidue_eq_abstract_sum]
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self i))

/-- The Molien numerator shows that at most six vectors are needed in the
fixed coinvariant subspace. -/
theorem fixedCoinvariantSubspace_finrank_le_six :
    Module.finrank ℚ fixedCoinvariantSubspace ≤ 6 := by
  have h := finrank_le_of_span_eq_top abstractInvariantResidue_span_eq_top
  rw [LazardQuinticInvariantHilbertRank.abstractF20Basis_card] at h
  exact h

/-- Rank `114` in the 120-dimensional Artin model means that the fixed
kernel has dimension six. -/
theorem fixedCoinvariantSubspace_finrank_of_rank_certificate
    (hrank : FixedCoinvariantRankCertificate) :
    Module.finrank ℚ fixedCoinvariantSubspace = 6 := by
  have hsum := LinearMap.finrank_range_add_finrank_ker
    fixedCoinvariantConstraintMatrix.mulVecLin
  change fixedCoinvariantConstraintMatrix.rank +
      Module.finrank ℚ fixedCoinvariantSubspace =
        Module.finrank ℚ ArtinCoinvariantModel at hsum
  rw [hrank, artinCoinvariantModel_finrank] at hsum
  omega

/-- Projection of a 120-coordinate residue vector to six selected rows. -/
noncomputable def selectedCoinvariantCoordinates
    (pivot : Fin 6 → ArtinFiveIndex) :
    ArtinCoinvariantModel →ₗ[ℚ] (Fin 6 → ℚ) :=
  LinearMap.pi fun row ↦ LinearMap.proj (R := ℚ) (pivot row)

theorem candidateCoinvariantVector_linearIndependent_of_residue_det
    (pivot : Fin 6 → ArtinFiveIndex)
    (hdet : (candidateResiduePivotMatrix pivot).det ≠ 0) :
    LinearIndependent ℚ candidateCoinvariantVector := by
  have hcolumns := Matrix.linearIndependent_cols_of_det_ne_zero hdet
  have himage : LinearIndependent ℚ
      (fun column ↦ selectedCoinvariantCoordinates pivot
        (candidateCoinvariantVector column)) := by
    have hfamily :
        (fun column ↦ selectedCoinvariantCoordinates pivot
            (candidateCoinvariantVector column)) =
          (candidateResiduePivotMatrix pivot).col := by
      funext column row
      rfl
    rw [hfamily]
    exact hcolumns
  exact LinearIndependent.of_comp (selectedCoinvariantCoordinates pivot) <| by
    simpa [Function.comp_def] using himage

/-- Bundle the six candidate residues into the explicit fixed subspace. -/
noncomputable def fixedCandidateFamily
    (hfixed : CandidateFixedCoinvariantEquations) :
    Fin 6 → fixedCoinvariantSubspace :=
  fun j ↦ ⟨candidateCoinvariantVector j,
    candidateCoinvariantVector_mem_fixed hfixed j⟩

theorem fixedCandidateFamily_linearIndependent
    (pivot : Fin 6 → ArtinFiveIndex)
    (hfixed : CandidateFixedCoinvariantEquations)
    (hdet : (candidateResiduePivotMatrix pivot).det ≠ 0) :
    LinearIndependent ℚ (fixedCandidateFamily hfixed) := by
  refine LinearIndependent.of_comp fixedCoinvariantSubspace.subtype ?_
  simpa [Function.comp_def, fixedCandidateFamily] using
    candidateCoinvariantVector_linearIndependent_of_residue_det pivot hdet

/-- The two finite matrix checks imply that the six residue vectors form a
basis of the explicit fixed coinvariant subspace. -/
theorem fixedCandidateFamily_span_eq_top
    (pivot : Fin 6 → ArtinFiveIndex)
    (hfixed : CandidateFixedCoinvariantEquations)
    (hrank : FixedCoinvariantRankCertificate)
    (hdet : (candidateResiduePivotMatrix pivot).det ≠ 0) :
    Submodule.span ℚ (Set.range (fixedCandidateFamily hfixed)) = ⊤ := by
  apply LinearIndependent.span_eq_top_of_card_eq_finrank
    (fixedCandidateFamily_linearIndependent pivot hfixed hdet)
  rw [Fintype.card_fin,
    fixedCoinvariantSubspace_finrank_of_rank_certificate hrank]

/-! ## Kernel-checked sparse normal forms imply the pivot certificate -/

set_option maxRecDepth 10000 in
private theorem i4OrbitSupport_eq_formulaSupport :
    metacyclicOrbitSupport i4Exponent =
      lazardOrbitFormulaSupport 2 1 := by
  decide

set_option maxRecDepth 10000 in
private theorem i4OrbitExponent_injective :
    Function.Injective (lazardOrbitExponent 2 1) := by
  decide

private theorem metacyclicOrbitValue_i4_formula
    {K : Type*} [CommRing K] (x : Fin 5 → K) :
    metacyclicOrbitValue i4Exponent x = lazardOrbitFormula 2 1 x := by
  exact metacyclicOrbitValue_eq_lazardOrbitFormula x i4Exponent 2 1
    i4OrbitSupport_eq_formulaSupport i4OrbitExponent_injective

/-- Evaluating an integral multivariable polynomial at the ambient variables
is exactly coefficient extension from `ℤ` to `ℚ`. -/
private theorem eval₂_intCast_X_eq_map
    (p : MvPolynomial (Fin 5) ℤ) :
    MvPolynomial.eval₂ (Int.castRingHom FivePolynomialRing)
        (fun i ↦ MvPolynomial.X i) p =
      MvPolynomial.map (Int.castRingHom ℚ) p := by
  have hcast :
      Int.castRingHom FivePolynomialRing =
        (MvPolynomial.C : ℚ →+* FivePolynomialRing).comp
          (Int.castRingHom ℚ) := by
    ext z
    simp
  change MvPolynomial.eval₂Hom (Int.castRingHom FivePolynomialRing)
      (fun i ↦ MvPolynomial.X i) p =
    MvPolynomial.map (Int.castRingHom ℚ) p
  rw [hcast, MvPolynomial.map_eq_eval₂Hom_C_comp]

private theorem metacyclicOrbitValue_X (d : RootExponent) :
    metacyclicOrbitValue d (fun i ↦ MvPolynomial.X i) =
      metacyclicOrbitPolynomialOver ℚ d := by
  change MvPolynomial.eval₂ (Int.castRingHom FivePolynomialRing)
      (fun i ↦ MvPolynomial.X i) (metacyclicOrbitPolynomial d) =
    MvPolynomial.map (Int.castRingHom ℚ) (metacyclicOrbitPolynomial d)
  exact eval₂_intCast_X_eq_map (metacyclicOrbitPolynomial d)

/-- The six generated sparse sources are exactly `1,i4,...,i8`, not merely
lookalike polynomials used by an external computation. -/
theorem candidateSource_eval_eq_candidatePolynomial (j : Fin 6) :
    SparsePolynomial.eval
        (LazardQuinticCoinvariantNormalForms.candidateSource j)
        (fun i ↦ MvPolynomial.X i) = candidatePolynomial j := by
  fin_cases j
  · simp [candidatePolynomial,
      LazardQuinticCoinvariantNormalForms.candidateSource,
      SparsePolynomial.eval, SparseTerm.eval]
  · simp only [candidatePolynomial,
      LazardQuinticCoinvariantNormalForms.candidateSource]
    rw [← metacyclicOrbitValue_X i4Exponent,
      metacyclicOrbitValue_i4_formula]
    simp [candidatePolynomial,
      LazardQuinticCoinvariantNormalForms.candidateSource,
      SparsePolynomial.eval, SparseTerm.eval, lazardOrbitFormula]
    ring
  · simp only [candidatePolynomial,
      LazardQuinticCoinvariantNormalForms.candidateSource]
    rw [← metacyclicOrbitValue_X i5Exponent,
      metacyclicOrbitValue_i5]
    simp [candidatePolynomial,
      LazardQuinticCoinvariantNormalForms.candidateSource,
      SparsePolynomial.eval, SparseTerm.eval, lazardOrbitFormula]
    ring
  · simp only [candidatePolynomial,
      LazardQuinticCoinvariantNormalForms.candidateSource]
    rw [← metacyclicOrbitValue_X i6Exponent,
      metacyclicOrbitValue_i6]
    simp [candidatePolynomial,
      LazardQuinticCoinvariantNormalForms.candidateSource,
      SparsePolynomial.eval, SparseTerm.eval, lazardOrbitFormula]
    ring
  · simp only [candidatePolynomial,
      LazardQuinticCoinvariantNormalForms.candidateSource]
    rw [← metacyclicOrbitValue_X i7Exponent,
      metacyclicOrbitValue_i7]
    simp [candidatePolynomial,
      LazardQuinticCoinvariantNormalForms.candidateSource,
      SparsePolynomial.eval, SparseTerm.eval, lazardOrbitFormula]
    ring
  · simp only [candidatePolynomial,
      LazardQuinticCoinvariantNormalForms.candidateSource]
    rw [← metacyclicOrbitValue_X i8Exponent,
      metacyclicOrbitValue_i8]
    simp [candidatePolynomial,
      LazardQuinticCoinvariantNormalForms.candidateSource,
      SparsePolynomial.eval, SparseTerm.eval, lazardOrbitFormula]
    ring

/-- Set the formal elementary-symmetric variables to zero while retaining
the five root variables. -/
def zeroFormalCoefficientSpecialization :
    LazardDisplayedGroebnerQuintic.Ambient →+* FivePolynomialRing :=
  MvPolynomial.eval₂Hom
    ((MvPolynomial.C : ℚ →+* FivePolynomialRing).comp
      (MvPolynomial.constantCoeff :
        LazardDisplayedGroebnerQuintic.Coeff →+* ℚ))
    (fun i ↦ MvPolynomial.X i)

@[simp]
theorem zeroFormalCoefficientSpecialization_C
    (c : LazardDisplayedGroebnerQuintic.Coeff) :
    zeroFormalCoefficientSpecialization (MvPolynomial.C c) =
      MvPolynomial.C (MvPolynomial.constantCoeff c) := by
  simp [zeroFormalCoefficientSpecialization]

@[simp]
theorem zeroFormalCoefficientSpecialization_X (i : Fin 5) :
    zeroFormalCoefficientSpecialization (MvPolynomial.X i) =
      (MvPolynomial.X i : FivePolynomialRing) := by
  simp [zeroFormalCoefficientSpecialization]

private theorem zeroFormalCoefficientSpecialization_esymm (k : ℕ) :
    zeroFormalCoefficientSpecialization
        (MvPolynomial.esymm (Fin 5)
          LazardDisplayedGroebnerQuintic.Coeff k) =
      MvPolynomial.esymm (Fin 5) ℚ k := by
  simp [zeroFormalCoefficientSpecialization, MvPolynomial.esymm]

private theorem zeroFormalCoefficientSpecialization_vietaRelation
    (i : Fin 5) :
    zeroFormalCoefficientSpecialization
        (LazardDisplayedGroebnerQuintic.vietaRelation i) =
      MvPolynomial.esymm (Fin 5) ℚ (i.1 + 1) := by
  rw [LazardDisplayedGroebnerQuintic.vietaRelation, map_sub,
    zeroFormalCoefficientSpecialization_esymm]
  simp [LazardDisplayedGroebnerQuintic.e,
    zeroFormalCoefficientSpecialization]

private theorem zeroFormalCoefficientSpecialization_displayedJ
    (i : Fin 5) :
    zeroFormalCoefficientSpecialization
        (LazardDisplayedGroebnerQuintic.displayedJ i) =
      SparsePolynomial.eval
        (LazardQuinticCoinvariantNormalForms.relation i)
        (fun j ↦ MvPolynomial.X j) := by
  fin_cases i <;>
    simp [zeroFormalCoefficientSpecialization,
      LazardDisplayedGroebnerQuintic.displayedJ,
      LazardDisplayedGroebnerQuintic.x,
      LazardDisplayedGroebnerQuintic.e,
      LazardQuinticCoinvariantNormalForms.relation,
      SparsePolynomial.eval, SparseTerm.eval] <;>
    ring

/-- Each sparse triangular relation is an explicit polynomial combination
of the five positive-degree elementary symmetric polynomials. -/
theorem sparseRelation_eq_esymmCombination (i : Fin 5) :
    SparsePolynomial.eval
        (LazardQuinticCoinvariantNormalForms.relation i)
        (fun j ↦ MvPolynomial.X j) =
      ∑ k : Fin 5,
        zeroFormalCoefficientSpecialization
            (LazardDisplayedGroebnerQuintic.jToVieta i k) *
          MvPolynomial.esymm (Fin 5) ℚ (k.1 + 1) := by
  have h := congrArg zeroFormalCoefficientSpecialization
    (LazardDisplayedGroebnerQuintic.displayedJ_eq_vieta_combination i)
  rw [map_sum] at h
  simpa [map_mul, zeroFormalCoefficientSpecialization_displayedJ,
    zeroFormalCoefficientSpecialization_vietaRelation] using h

/-- The `k`th elementary symmetric polynomial, bundled as a scalar in the
full symmetric coefficient ring. -/
noncomputable def elementarySymmetricScalar (k : Fin 5) :
    SymmetricFiveRing :=
  LazardDisplayedGroebnerQuintic.coefficientEquiv
    (MvPolynomial.X k)

@[simp]
theorem elementarySymmetricScalar_val (k : Fin 5) :
    (elementarySymmetricScalar k).1 =
      MvPolynomial.esymm (Fin 5) ℚ (k.1 + 1) := by
  exact LazardDisplayedGroebnerQuintic.coefficientSpecialization_X k

@[simp]
theorem symmetricAugmentation_elementarySymmetricScalar (k : Fin 5) :
    symmetricAugmentation (elementarySymmetricScalar k) = 0 := by
  rw [symmetricAugmentation_eq_symmetricConstantCoeff]
  apply symmetricConstantCoeff_eq_zero_of_isHomogeneous_pos ℚ 5
  · rw [elementarySymmetricScalar_val]
    exact LazardQuinticInvariantHilbertRank.esymm_isHomogeneous (k.1 + 1)
  · exact Nat.zero_lt_succ k.1

/-- Multiplication by a positive-degree elementary symmetric scalar vanishes
after augmentation of every Artin coordinate. -/
theorem artinCoinvariantCoordinates_mul_esymm_eq_zero
    (p : FivePolynomialRing) (k : Fin 5) :
    artinCoinvariantCoordinates
        (p * MvPolynomial.esymm (Fin 5) ℚ (k.1 + 1)) = 0 := by
  have hscalar :
      p * MvPolynomial.esymm (Fin 5) ℚ (k.1 + 1) =
        elementarySymmetricScalar k • p := by
    calc
      p * MvPolynomial.esymm (Fin 5) ℚ (k.1 + 1) =
          p * (elementarySymmetricScalar k).1 := by
        rw [elementarySymmetricScalar_val]
      _ = (elementarySymmetricScalar k).1 * p := mul_comm _ _
      _ = elementarySymmetricScalar k • p := by
        rw [Algebra.smul_def, algebraMap_symmetricFiveRing_apply]
  rw [hscalar]
  funext a
  change symmetricAugmentation
      (artinFiveBasis.repr (elementarySymmetricScalar k • p) a) = 0
  rw [map_smul]
  change symmetricAugmentation
      (elementarySymmetricScalar k * artinFiveBasis.repr p a) = 0
  rw [map_mul, symmetricAugmentation_elementarySymmetricScalar, zero_mul]

/-- Every multiple of a generated triangular relation has zero residue. -/
theorem artinCoinvariantCoordinates_mul_sparseRelation_eq_zero
    (p : FivePolynomialRing) (i : Fin 5) :
    artinCoinvariantCoordinates
        (p * SparsePolynomial.eval
          (LazardQuinticCoinvariantNormalForms.relation i)
          (fun j ↦ MvPolynomial.X j)) = 0 := by
  classical
  rw [sparseRelation_eq_esymmCombination, Finset.mul_sum]
  rw [← artinCoinvariantCoordinatesLinear_apply, map_sum]
  apply Finset.sum_eq_zero
  intro k hk
  rw [artinCoinvariantCoordinatesLinear_apply]
  convert artinCoinvariantCoordinates_mul_esymm_eq_zero
    (p * zeroFormalCoefficientSpecialization
      (LazardDisplayedGroebnerQuintic.jToVieta i k)) k using 1 <;>
    ring

/-- Convert the five-field executable exponent record into the ordinary
finitely-supported exponent used by `MvPolynomial`. -/
def powersExponent (a : Powers) : Fin 5 →₀ ℕ :=
  Finsupp.single 0 a.p0 + Finsupp.single 1 a.p1 +
    Finsupp.single 2 a.p2 + Finsupp.single 3 a.p3 +
      Finsupp.single 4 a.p4

@[simp]
theorem powersExponent_apply (a : Powers) (i : Fin 5) :
    powersExponent a i =
      ![a.p0, a.p1, a.p2, a.p3, a.p4] i := by
  fin_cases i <;> simp [powersExponent]

/-- Read an Artin index back into the executable five-field record. -/
def powersOfArtin (a : ArtinFiveIndex) : Powers :=
  ⟨(a 0).1, (a 1).1, (a 2).1, (a 3).1, (a 4).1⟩

@[simp]
theorem powersDegree_powersOfArtin (a : ArtinFiveIndex) :
    LazardQuinticCoinvariantNormalForms.powersDegree (powersOfArtin a) =
      artinDegree a := by
  simp [LazardQuinticCoinvariantNormalForms.powersDegree,
    powersOfArtin, artinDegree, Fin.sum_univ_succ]
  omega

/-- Bundle an executable exponent satisfying the staircase inequalities as
an Artin index. -/
def artinIndexOfPowers (a : Powers)
    (ha : LazardQuinticCoinvariantNormalForms.IsStandardPowers a) :
    ArtinFiveIndex :=
  fun i ↦ ⟨powersExponent a i, by
    rcases ha with ⟨h0, h1, h2, h3, h4⟩
    fin_cases i
    · simpa using h0
    · simpa using h1
    · simpa using h2
    · simpa using h3
    · simpa using h4⟩

@[simp]
theorem artinExponent_artinIndexOfPowers (a : Powers)
    (ha : LazardQuinticCoinvariantNormalForms.IsStandardPowers a) :
    artinExponent (artinIndexOfPowers a ha) = powersExponent a := by
  apply Finsupp.ext
  intro i
  simp [artinIndexOfPowers]

@[simp]
theorem artinDegree_artinIndexOfPowers (a : Powers)
    (ha : LazardQuinticCoinvariantNormalForms.IsStandardPowers a) :
    artinDegree (artinIndexOfPowers a ha) =
      LazardQuinticCoinvariantNormalForms.powersDegree a := by
  simp [artinDegree, artinIndexOfPowers,
    LazardQuinticCoinvariantNormalForms.powersDegree,
    Fin.sum_univ_succ]
  omega

private theorem sparseTerm_eval_X_eq_monomial (t : SparseTerm) :
    SparseTerm.eval t (fun i ↦ (MvPolynomial.X i : FivePolynomialRing)) =
      MvPolynomial.monomial (powersExponent t.powers) (t.coeff : ℚ) := by
  change MvPolynomial.C (t.coeff : ℚ) * MvPolynomial.X 0 ^ t.powers.p0 *
      MvPolynomial.X 1 ^ t.powers.p1 *
      MvPolynomial.X 2 ^ t.powers.p2 *
      MvPolynomial.X 3 ^ t.powers.p3 *
      MvPolynomial.X 4 ^ t.powers.p4 = _
  simp only [MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.C_mul_monomial, MvPolynomial.monomial_mul, mul_one]
  congr 1

/-- Extensionality for the executable five-field exponent record. -/
private theorem powers_ext {a b : Powers}
    (h0 : a.p0 = b.p0) (h1 : a.p1 = b.p1)
    (h2 : a.p2 = b.p2) (h3 : a.p3 = b.p3)
    (h4 : a.p4 = b.p4) : a = b := by
  cases a
  cases b
  simp_all

private theorem artinIndexOfPowers_eq_iff
    (a : Powers)
    (ha : LazardQuinticCoinvariantNormalForms.IsStandardPowers a)
    (b : ArtinFiveIndex) :
    artinIndexOfPowers a ha = b ↔ a = powersOfArtin b := by
  constructor
  · intro h
    have h0 := congrArg (fun z : ArtinFiveIndex ↦ (z 0).1) h
    have h1 := congrArg (fun z : ArtinFiveIndex ↦ (z 1).1) h
    have h2 := congrArg (fun z : ArtinFiveIndex ↦ (z 2).1) h
    have h3 := congrArg (fun z : ArtinFiveIndex ↦ (z 3).1) h
    apply powers_ext
    · simpa [artinIndexOfPowers, powersOfArtin, powersExponent] using h0
    · simpa [artinIndexOfPowers, powersOfArtin, powersExponent] using h1
    · simpa [artinIndexOfPowers, powersOfArtin, powersExponent] using h2
    · simpa [artinIndexOfPowers, powersOfArtin, powersExponent] using h3
    · change a.p4 = (b 4).1
      have ha4 : a.p4 < 1 := ha.2.2.2.2
      have hb4 : (b 4).1 < 1 := by simpa using (b 4).2
      omega
  · intro h
    subst a
    funext i
    apply Fin.ext
    fin_cases i <;> simp [artinIndexOfPowers, powersOfArtin, powersExponent]

/-- One standard sparse term has exactly one nonzero augmented Artin
coordinate, with the sign forced by the recursively constructed basis. -/
theorem artinCoinvariantCoordinates_sparseTerm
    (t : SparseTerm)
    (ht : LazardQuinticCoinvariantNormalForms.IsStandardPowers t.powers)
    (a : ArtinFiveIndex) :
    artinCoinvariantCoordinates
        (SparseTerm.eval t (fun i ↦ MvPolynomial.X i)) a =
      if t.powers = powersOfArtin a then
        ((-1 : ℚ) ^
          LazardQuinticCoinvariantNormalForms.powersDegree t.powers) *
            (t.coeff : ℚ)
      else 0 := by
  classical
  let b := artinIndexOfPowers t.powers ht
  let c : ℚ :=
    (-1 : ℚ) ^ LazardQuinticCoinvariantNormalForms.powersDegree t.powers *
      (t.coeff : ℚ)
  have hterm :
      SparseTerm.eval t (fun i ↦ MvPolynomial.X i) =
        algebraMap ℚ SymmetricFiveRing c • artinFiveBasis b := by
    rw [sparseTerm_eval_X_eq_monomial]
    change MvPolynomial.monomial (powersExponent t.powers) (t.coeff : ℚ) =
      MvPolynomial.C c * symmetricArtinBasis ℚ 5 b
    rw [symmetricArtinBasis_apply_eq_monomial,
      artinExponent_artinIndexOfPowers,
      artinDegree_artinIndexOfPowers, MvPolynomial.C_mul_monomial]
    congr 1
    symm
    change c *
      (-1 : ℚ) ^ LazardQuinticCoinvariantNormalForms.powersDegree t.powers =
        (t.coeff : ℚ)
    dsimp [c]
    calc
      ((-1 : ℚ) ^
          LazardQuinticCoinvariantNormalForms.powersDegree t.powers *
            (t.coeff : ℚ)) *
          (-1 : ℚ) ^
            LazardQuinticCoinvariantNormalForms.powersDegree t.powers =
        ((-1 : ℚ) ^
            LazardQuinticCoinvariantNormalForms.powersDegree t.powers *
          (-1 : ℚ) ^
            LazardQuinticCoinvariantNormalForms.powersDegree t.powers) *
              (t.coeff : ℚ) := by ring
      _ = (t.coeff : ℚ) := by
        rw [← pow_add,
          (Even.add_self
            (LazardQuinticCoinvariantNormalForms.powersDegree
              t.powers)).neg_one_pow,
          one_mul]
  rw [hterm]
  change symmetricAugmentation
    (artinFiveBasis.repr
      (algebraMap ℚ SymmetricFiveRing c • artinFiveBasis b) a) = _
  rw [map_smul]
  simp only [Finsupp.smul_apply, artinFiveBasis.repr_self_apply]
  by_cases hba : b = a
  · rw [if_pos hba]
    have hpower : t.powers = powersOfArtin a :=
      (artinIndexOfPowers_eq_iff t.powers ht a).mp hba
    simp [hpower, c]
  · rw [if_neg hba]
    have hpower : t.powers ≠ powersOfArtin a := by
      exact fun h ↦ hba ((artinIndexOfPowers_eq_iff t.powers ht a).mpr h)
    simp [hpower]

/-- For a standard sparse polynomial, augmented Artin coordinates are its
literal signed sparse coefficients. -/
theorem artinCoinvariantCoordinates_sparsePolynomial
    (q : SparsePolynomial)
    (hq : ∀ t ∈ q,
      LazardQuinticCoinvariantNormalForms.IsStandardPowers t.powers)
    (a : ArtinFiveIndex) :
    artinCoinvariantCoordinates
        (SparsePolynomial.eval q (fun i ↦ MvPolynomial.X i)) a =
      (LazardQuinticCoinvariantNormalForms.signedCoefficient q
        (powersOfArtin a) : ℚ) := by
  induction q with
  | nil =>
      simpa [SparsePolynomial.eval,
        LazardQuinticCoinvariantNormalForms.signedCoefficient,
        LazardQuinticCoinvariantNormalForms.sparseCoefficient,
        ← artinCoinvariantCoordinatesLinear_apply]
  | cons t q ih =>
      have ht := hq t (by simp)
      have hq' : ∀ u ∈ q,
          LazardQuinticCoinvariantNormalForms.IsStandardPowers u.powers := by
        intro u hu
        exact hq u (by simp [hu])
      rw [SparsePolynomial.eval]
      rw [← artinCoinvariantCoordinatesLinear_apply, map_add,
        artinCoinvariantCoordinatesLinear_apply,
        artinCoinvariantCoordinatesLinear_apply,
        Pi.add_apply,
        artinCoinvariantCoordinates_sparseTerm t ht a,
        ih hq']
      by_cases hpower : t.powers = powersOfArtin a
      · simp [LazardQuinticCoinvariantNormalForms.signedCoefficient,
          LazardQuinticCoinvariantNormalForms.sparseCoefficient,
          hpower] <;> ring
      · simp [LazardQuinticCoinvariantNormalForms.signedCoefficient,
          LazardQuinticCoinvariantNormalForms.sparseCoefficient,
          hpower] <;> ring

/-- The generated quotient witnesses show that each candidate and its sparse
normal form have identical augmented Artin coordinates. -/
theorem candidatePolynomial_residue_eq_normalForm (j : Fin 6) :
    artinCoinvariantCoordinates (candidatePolynomial j) =
      artinCoinvariantCoordinates
        (SparsePolynomial.eval
          (LazardQuinticCoinvariantNormalForms.normalForm j)
          (fun i ↦ MvPolynomial.X i)) := by
  have heval := LazardQuinticCoinvariantNormalForms.eval_reconstructed j
    (fun i ↦ (MvPolynomial.X i : FivePolynomialRing))
  have hsource :
      artinCoinvariantCoordinates (candidatePolynomial j) =
        artinCoinvariantCoordinates
          (SparsePolynomial.eval
            (LazardQuinticCoinvariantNormalForms.reconstructed j)
            (fun i ↦ MvPolynomial.X i)) := by
    rw [← candidateSource_eval_eq_candidatePolynomial]
    exact congrArg artinCoinvariantCoordinates heval
  have hreconstructed :
      artinCoinvariantCoordinates
          (SparsePolynomial.eval
            (LazardQuinticCoinvariantNormalForms.reconstructed j)
            (fun i ↦ MvPolynomial.X i)) =
        artinCoinvariantCoordinates
          (SparsePolynomial.eval
            (LazardQuinticCoinvariantNormalForms.normalForm j)
            (fun i ↦ MvPolynomial.X i)) := by
    change artinCoinvariantCoordinatesLinear
        (SparsePolynomial.eval
          (LazardQuinticCoinvariantNormalForms.reconstructed j)
          (fun i ↦ MvPolynomial.X i)) =
      artinCoinvariantCoordinatesLinear
        (SparsePolynomial.eval
          (LazardQuinticCoinvariantNormalForms.normalForm j)
          (fun i ↦ MvPolynomial.X i))
    rw [LazardQuinticCoinvariantNormalForms.reconstructed,
      SparsePolynomial.eval_add, map_add]
    have hrelations :
        artinCoinvariantCoordinatesLinear
            (SparsePolynomial.eval (SparsePolynomial.sum [
              (LazardQuinticCoinvariantNormalForms.quotient j 0).mul
                (LazardQuinticCoinvariantNormalForms.relation 0),
              (LazardQuinticCoinvariantNormalForms.quotient j 1).mul
                (LazardQuinticCoinvariantNormalForms.relation 1),
              (LazardQuinticCoinvariantNormalForms.quotient j 2).mul
                (LazardQuinticCoinvariantNormalForms.relation 2),
              (LazardQuinticCoinvariantNormalForms.quotient j 3).mul
                (LazardQuinticCoinvariantNormalForms.relation 3),
              (LazardQuinticCoinvariantNormalForms.quotient j 4).mul
                (LazardQuinticCoinvariantNormalForms.relation 4)])
              (fun i ↦ MvPolynomial.X i)) = 0 := by
      simp [map_add, artinCoinvariantCoordinatesLinear_apply,
        artinCoinvariantCoordinates_mul_sparseRelation_eq_zero]
    rw [hrelations, add_zero]
  exact hsource.trans hreconstructed

@[simp]
theorem powersOfArtin_explicitPivot (row : Fin 6) :
    powersOfArtin (explicitPivot row) =
      LazardQuinticCoinvariantNormalForms.explicitPivotPowers row := by
  fin_cases row <;> rfl

/-- The sparse signed-coefficient certificate gives the six-by-six diagonal
residue values in the actual symmetric Artin basis. -/
theorem candidateCoinvariantVector_explicitPivot_computed
    (row column : Fin 6) :
    candidateCoinvariantVector column (explicitPivot row) =
      if row = column then candidatePivotDiagonal row else 0 := by
  rw [candidateCoinvariantVector, candidatePolynomial_residue_eq_normalForm]
  rw [artinCoinvariantCoordinates_sparsePolynomial
    (LazardQuinticCoinvariantNormalForms.normalForm column)
    (LazardQuinticCoinvariantNormalForms.normalForm_standard column)
    (explicitPivot row), powersOfArtin_explicitPivot]
  rw [LazardQuinticCoinvariantNormalForms.signedCoefficient_normalForm_explicitPivot]
  fin_cases row <;> fin_cases column <;>
    norm_num [candidatePivotDiagonal,
      LazardQuinticCoinvariantNormalForms.expectedPivotDiagonal]

/-- The selected candidate minor is proved from kernel-checked sparse
quotient witnesses; it is no longer a caller-supplied certificate. -/
theorem candidateResiduePivotCertificate :
    CandidateResiduePivotCertificate := by
  ext row column
  simpa [candidateResiduePivotMatrix,
    expectedCandidateResiduePivotMatrix, Matrix.diagonal_apply] using
      candidateCoinvariantVector_explicitPivot_computed row column

/-- The six explicit, independent candidate residues and the Molien upper
bound determine the fixed coinvariant dimension exactly. -/
theorem fixedCoinvariantSubspace_finrank :
    Module.finrank ℚ fixedCoinvariantSubspace = 6 := by
  have hdet := candidateResiduePivotMatrix_det_ne_zero
    candidateResiduePivotCertificate
  have hlower : 6 ≤ Module.finrank ℚ fixedCoinvariantSubspace := by
    simpa using
      (fixedCandidateFamily_linearIndependent explicitPivot
        candidateFixedCoinvariantEquations hdet).fintype_card_le_finrank
  exact le_antisymm fixedCoinvariantSubspace_finrank_le_six hlower

/-- The former rank certificate is now a theorem, derived from Reynolds
exactness, the Molien numerator, and the six kernel-checked pivot residues. -/
theorem fixedCoinvariantRankCertificate :
    FixedCoinvariantRankCertificate := by
  have hsum := LinearMap.finrank_range_add_finrank_ker
    fixedCoinvariantConstraintMatrix.mulVecLin
  change fixedCoinvariantConstraintMatrix.rank +
      Module.finrank ℚ fixedCoinvariantSubspace =
        Module.finrank ℚ ArtinCoinvariantModel at hsum
  rw [fixedCoinvariantSubspace_finrank,
    artinCoinvariantModel_finrank] at hsum
  have hsub := congrArg (fun n : ℕ ↦ n - 6) hsum
  norm_num [Nat.add_sub_cancel] at hsub
  exact hsub

/-! ## Exact Reynolds lifting by homogeneous degree -/

/-- A homogeneous polynomial has no coinvariant coordinate in a different
Artin degree.  Above the degree the Artin coordinate itself vanishes; below
it the symmetric coefficient has positive degree and augmentation zero. -/
theorem artinCoinvariantCoordinates_eq_zero_of_degree_ne
    {p : FivePolynomialRing} {d : ℕ}
    (hp : MvPolynomial.IsHomogeneous p d) (a : ArtinFiveIndex)
    (hne : artinDegree a ≠ d) :
    artinCoinvariantCoordinates p a = 0 := by
  by_cases hhigh : d < artinDegree a
  · have hcoordinate := repr_eq_zero_of_degree_lt
      artinFiveBasis artinDegree
      (symmetricArtinBasis_isHomogeneous ℚ 5) hp a hhigh
    simp [artinCoinvariantCoordinates, artinCoordinate, hcoordinate]
  · have hle : artinDegree a ≤ d := Nat.le_of_not_gt hhigh
    have hlow : artinDegree a < d := lt_of_le_of_ne hle hne
    have hcoordinate := repr_isHomogeneous
      artinFiveBasis artinDegree
      (symmetricArtinBasis_isHomogeneous ℚ 5) hp a hle
    change symmetricConstantCoeff ℚ 5 (artinFiveBasis.repr p a) = 0
    exact symmetricConstantCoeff_eq_zero_of_isHomogeneous_pos ℚ 5
      hcoordinate (Nat.sub_pos_of_lt hlow)

/-- The finite hypotheses turn the six fixed residue vectors into a basis. -/
noncomputable def fixedCandidateBasis
    (hrank : FixedCoinvariantRankCertificate)
    (hpivot : CandidateResiduePivotCertificate) :
    Module.Basis (Fin 6) ℚ fixedCoinvariantSubspace := by
  let hfixed := candidateFixedCoinvariantEquations
  let hdet := candidateResiduePivotMatrix_det_ne_zero hpivot
  exact Module.Basis.mk
    (fixedCandidateFamily_linearIndependent explicitPivot hfixed hdet)
    (fixedCandidateFamily_span_eq_top explicitPivot hfixed hrank hdet).ge

@[simp]
theorem fixedCandidateBasis_apply
    (hrank : FixedCoinvariantRankCertificate)
    (hpivot : CandidateResiduePivotCertificate) (j : Fin 6) :
    fixedCandidateBasis hrank hpivot j =
      fixedCandidateFamily candidateFixedCoinvariantEquations j := by
  simp [fixedCandidateBasis]

/-- Rational coordinates of an invariant residue in the six-candidate
basis. -/
noncomputable def residueCoefficient
    (hrank : FixedCoinvariantRankCertificate)
    (hpivot : CandidateResiduePivotCertificate)
    (p : F20InvariantModule) (j : Fin 6) : ℚ :=
  (fixedCandidateBasis hrank hpivot).repr (invariantResidue p) j

theorem candidateCoinvariantVector_explicitPivot
    (hpivot : CandidateResiduePivotCertificate) (row column : Fin 6) :
    candidateCoinvariantVector column (explicitPivot row) =
      if row = column then candidatePivotDiagonal row else 0 := by
  have hentry := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℚ ↦
    M row column) hpivot
  simpa [candidateResiduePivotMatrix,
    expectedCandidateResiduePivotMatrix, Matrix.diagonal_apply] using hentry

/-- In a homogeneous invariant, only the candidate of the same degree can
have a nonzero residue-basis coefficient.  The explicit diagonal pivot makes
this degree separation completely transparent. -/
theorem residueCoefficient_eq_zero_of_degree_ne
    (hrank : FixedCoinvariantRankCertificate)
    (hpivot : CandidateResiduePivotCertificate)
    {p : F20InvariantModule} {d : ℕ}
    (hp : MvPolynomial.IsHomogeneous p.1 d) (j : Fin 6)
    (hdegree : candidateDegree j ≠ d) :
    residueCoefficient hrank hpivot p j = 0 := by
  classical
  let B := fixedCandidateBasis hrank hpivot
  have hsum := congrArg
    (fun v : fixedCoinvariantSubspace ↦ v.1 (explicitPivot j))
    (B.sum_repr (invariantResidue p))
  have hpivotEquation :
      residueCoefficient hrank hpivot p j * candidatePivotDiagonal j =
        artinCoinvariantCoordinates p.1 (explicitPivot j) := by
    simpa [B, residueCoefficient, invariantResidue,
      fixedCandidateBasis_apply, fixedCandidateFamily,
      candidateCoinvariantVector_explicitPivot hpivot,
      smul_eq_mul] using hsum
  have hresidueZero :
      artinCoinvariantCoordinates p.1 (explicitPivot j) = 0 :=
    artinCoinvariantCoordinates_eq_zero_of_degree_ne hp
      (explicitPivot j) (by
        simpa [artinDegree_explicitPivot] using hdegree)
  have hproduct :
      residueCoefficient hrank hpivot p j * candidatePivotDiagonal j = 0 :=
    hpivotEquation.trans hresidueZero
  exact (mul_eq_zero.mp hproduct).resolve_right
    (candidatePivotDiagonal_ne_zero j)

/-- Lift the residue of an invariant by the six concrete invariants, using
ground-field constants as symmetric coefficients. -/
noncomputable def residueLift
    (hrank : FixedCoinvariantRankCertificate)
    (hpivot : CandidateResiduePivotCertificate)
    (p : F20InvariantModule) : F20InvariantModule :=
  ∑ j : Fin 6,
    symmetricInvariantProduct
      (algebraMap ℚ SymmetricFiveRing
        (residueCoefficient hrank hpivot p j))
      (concreteInvariant j)

theorem symmetricInvariantProduct_mem
    (S : Submodule SymmetricFiveRing F20InvariantModule)
    (c : SymmetricFiveRing) {p : F20InvariantModule} (hp : p ∈ S) :
    symmetricInvariantProduct c p ∈ S := by
  convert S.smul_mem c hp using 1
  apply Subtype.ext
  simp only [symmetricInvariantProduct_val, SetLike.val_smul,
    Algebra.smul_def, algebraMap_symmetricFiveRing_apply]

theorem residueLift_mem_span
    (hrank : FixedCoinvariantRankCertificate)
    (hpivot : CandidateResiduePivotCertificate)
    (p : F20InvariantModule) :
    residueLift hrank hpivot p ∈
      Submodule.span SymmetricFiveRing (Set.range concreteInvariant) := by
  classical
  apply Submodule.sum_mem
  intro j hj
  apply symmetricInvariantProduct_mem
  exact Submodule.subset_span (Set.mem_range_self j)

/-- The lift has exactly the same residue vector as the original invariant. -/
theorem artinCoinvariantCoordinates_residueLift
    (hrank : FixedCoinvariantRankCertificate)
    (hpivot : CandidateResiduePivotCertificate)
    (p : F20InvariantModule) :
    artinCoinvariantCoordinates (residueLift hrank hpivot p).1 =
      artinCoinvariantCoordinates p.1 := by
  classical
  let B := fixedCandidateBasis hrank hpivot
  have hsum :
      (∑ j : Fin 6,
        residueCoefficient hrank hpivot p j •
          invariantResidue (concreteInvariant j)) =
        invariantResidue p := by
    simpa [B, residueCoefficient, fixedCandidateBasis_apply,
      fixedCandidateFamily, invariantResidue,
      candidateCoinvariantVector] using
        B.sum_repr (invariantResidue p)
  have hlift :
      invariantResidue (residueLift hrank hpivot p) =
        invariantResidue p := by
    rw [← invariantResidueLinear_apply, residueLift, map_sum]
    simp only [invariantResidueLinear_apply,
      invariantResidue_symmetricInvariantProduct,
      symmetricAugmentation_algebraMap]
    exact hsum
  exact congrArg Subtype.val hlift

/-- For a homogeneous invariant, its canonical residue lift is homogeneous
of the same degree. -/
theorem residueLift_isHomogeneous
    (hrank : FixedCoinvariantRankCertificate)
    (hpivot : CandidateResiduePivotCertificate)
    {p : F20InvariantModule} {d : ℕ}
    (hp : MvPolynomial.IsHomogeneous p.1 d) :
    MvPolynomial.IsHomogeneous (residueLift hrank hpivot p).1 d := by
  classical
  change MvPolynomial.IsHomogeneous
    (∑ j : Fin 6,
      (algebraMap ℚ SymmetricFiveRing
        (residueCoefficient hrank hpivot p j)).1 *
        (concreteInvariant j).1) d
  apply MvPolynomial.IsHomogeneous.sum Finset.univ
  intro j hj
  by_cases hdegree : candidateDegree j = d
  · simpa [MvPolynomial.algebraMap_eq, hdegree] using
      (concreteInvariant_isHomogeneous j).C_mul
        (residueCoefficient hrank hpivot p j)
  · rw [residueCoefficient_eq_zero_of_degree_ne
      hrank hpivot hp j hdegree]
    simp [MvPolynomial.isHomogeneous_zero]

/-- Reynolds averaging of an Artin basis vector is invariant and preserves
its Artin degree. -/
noncomputable def averagedArtinInvariant
    (a : ArtinFiveIndex) : F20InvariantModule :=
  averageToInvariants ℚ 5 standardF20 (artinFiveBasis a)

theorem averagedArtinInvariant_isHomogeneous (a : ArtinFiveIndex) :
    MvPolynomial.IsHomogeneous (averagedArtinInvariant a).1
      (artinDegree a) := by
  change MvPolynomial.IsHomogeneous
    ((subgroupRepresentation ℚ (Fin 5) standardF20).averageMap
      (artinFiveBasis a)) (artinDegree a)
  exact reynolds_preserves_homogeneous_charZero ℚ (Fin 5) standardF20
    (symmetricArtinBasis_isHomogeneous ℚ 5 a)

/-- A homogeneous invariant with zero coinvariant residue is generated by
lower-degree averaged Artin vectors.  This is the exact Reynolds step behind
Lazard's graded argument. -/
theorem zero_residue_mem_span_of_lower_degrees
    {r : F20InvariantModule} {d : ℕ}
    (hr : MvPolynomial.IsHomogeneous r.1 d)
    (hresidue : artinCoinvariantCoordinates r.1 = 0)
    (hlower : ∀ a : ArtinFiveIndex, artinDegree a < d →
      averagedArtinInvariant a ∈
        Submodule.span SymmetricFiveRing (Set.range concreteInvariant)) :
    r ∈ Submodule.span SymmetricFiveRing (Set.range concreteInvariant) := by
  classical
  have havgExpansion :
      r = ∑ a : ArtinFiveIndex,
        symmetricInvariantProduct (artinCoordinate r.1 a)
          (averagedArtinInvariant a) := by
    calc
      r = averageToInvariants ℚ 5 standardF20 r.1 :=
        (averageToInvariants_of_invariant ℚ 5 standardF20 r).symm
      _ = averageToInvariants ℚ 5 standardF20
          (∑ a : ArtinFiveIndex,
            (artinFiveBasis.repr r.1) a • artinFiveBasis a) := by
          rw [artinFiveBasis.sum_repr]
      _ = _ := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro a ha
        set_option synthInstance.maxHeartbeats 200000 in
          exact map_smul (averageToInvariants ℚ 5 standardF20)
            (artinCoordinate r.1 a) (artinFiveBasis a)
  rw [havgExpansion]
  apply Submodule.sum_mem
  intro a ha
  by_cases hlow : artinDegree a < d
  · exact symmetricInvariantProduct_mem _ _ (hlower a hlow)
  · have hle : d ≤ artinDegree a := Nat.le_of_not_gt hlow
    have hcoordinate : artinCoordinate r.1 a = 0 := by
      by_cases hstrict : d < artinDegree a
      · exact repr_eq_zero_of_degree_lt
          artinFiveBasis artinDegree
          (symmetricArtinBasis_isHomogeneous ℚ 5) hr a hstrict
      · have heq : artinDegree a = d := by omega
        have hhomogeneous :
            MvPolynomial.IsHomogeneous (artinCoordinate r.1 a).1 0 := by
          have h := repr_isHomogeneous artinFiveBasis artinDegree
            (symmetricArtinBasis_isHomogeneous ℚ 5) hr a heq.le
          change MvPolynomial.IsHomogeneous
            (artinFiveBasis.repr r.1 a).1 0
          simpa only [heq, Nat.sub_self] using h
        obtain ⟨c, hc⟩ :=
          eq_algebraMap_of_isHomogeneous_zero ℚ 5 hhomogeneous
        have hconstant : symmetricAugmentation (artinCoordinate r.1 a) = 0 := by
          have := congrFun hresidue a
          simpa [artinCoinvariantCoordinates] using this
        have hcZero : c = 0 := by
          rw [hc, symmetricAugmentation_algebraMap] at hconstant
          exact hconstant
        rw [hc, hcZero, map_zero]
    have hzero :
        symmetricInvariantProduct 0 (averagedArtinInvariant a) = 0 := by
      apply Subtype.ext
      simp [symmetricInvariantProduct]
    rw [hcoordinate, hzero]
    exact Submodule.zero_mem _

/-- Every homogeneous `F20` invariant is generated by Lazard's six concrete
invariants.  The induction is on ordinary total degree, not on a localization
or a Jacobson-radical argument. -/
theorem homogeneousInvariant_mem_concrete_span
    (hrank : FixedCoinvariantRankCertificate)
    (hpivot : CandidateResiduePivotCertificate) :
    ∀ (d : ℕ) (p : F20InvariantModule),
      MvPolynomial.IsHomogeneous p.1 d →
      p ∈ Submodule.span SymmetricFiveRing (Set.range concreteInvariant) := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro p hp
      let q := residueLift hrank hpivot p
      let r : F20InvariantModule := p - q
      have hqSpan : q ∈
          Submodule.span SymmetricFiveRing (Set.range concreteInvariant) :=
        residueLift_mem_span hrank hpivot p
      have hqHomogeneous : MvPolynomial.IsHomogeneous q.1 d :=
        residueLift_isHomogeneous hrank hpivot hp
      have hrHomogeneous : MvPolynomial.IsHomogeneous r.1 d := by
        exact hp.sub hqHomogeneous
      have hrResidue : artinCoinvariantCoordinates r.1 = 0 := by
        change artinCoinvariantCoordinates (p.1 - q.1) = 0
        rw [← artinCoinvariantCoordinatesLinear_apply,
          map_sub, artinCoinvariantCoordinatesLinear_apply,
          artinCoinvariantCoordinatesLinear_apply,
          artinCoinvariantCoordinates_residueLift hrank hpivot p,
          sub_self]
      have hrSpan : r ∈
          Submodule.span SymmetricFiveRing (Set.range concreteInvariant) :=
        zero_residue_mem_span_of_lower_degrees hrHomogeneous hrResidue
          (fun a ha ↦ ih (artinDegree a) ha
            (averagedArtinInvariant a)
            (averagedArtinInvariant_isHomogeneous a))
      have hpEq : p = r + q := by
        change p = p - q + q
        exact (sub_add_cancel p q).symm
      rw [hpEq]
      exact Submodule.add_mem _ hrSpan hqSpan

/-- Homogeneous components of an invariant remain invariant. -/
noncomputable def invariantHomogeneousComponent
    (d : ℕ) (p : F20InvariantModule) : F20InvariantModule :=
  ⟨MvPolynomial.homogeneousComponent d p.1, by
    rw [mem_subgroupRepresentation_invariants, mem_invariantSubalgebra]
    intro h
    have hp : MvPolynomial.rename h.1 p.1 = p.1 := by
      simpa only [subgroupRepresentation_apply] using p.2 h
    rw [rename_homogeneousComponent, hp]⟩

theorem invariantHomogeneousComponent_isHomogeneous
    (d : ℕ) (p : F20InvariantModule) :
    MvPolynomial.IsHomogeneous (invariantHomogeneousComponent d p).1 d :=
  MvPolynomial.homogeneousComponent_isHomogeneous d p.1

/-- The genuine graded lifting bridge.  Once the two finite rational matrix
checks hold, the six concrete invariants span the entire invariant module. -/
theorem gradedInvariantLifting
    (hrank : FixedCoinvariantRankCertificate)
    (hpivot : CandidateResiduePivotCertificate) :
    ⊤ ≤ Submodule.span SymmetricFiveRing (Set.range concreteInvariant) := by
  intro p hpTop
  have hsum :
      (∑ d ∈ Finset.range (p.1.totalDegree + 1),
        invariantHomogeneousComponent d p) = p := by
    apply Subtype.ext
    simpa only [AddSubmonoidClass.coe_finsetSum,
      invariantHomogeneousComponent] using
        MvPolynomial.sum_homogeneousComponent p.1
  rw [← hsum]
  apply Submodule.sum_mem
  intro d hd
  exact homogeneousInvariant_mem_concrete_span hrank hpivot d
    (invariantHomogeneousComponent d p)
    (invariantHomogeneousComponent_isHomogeneous d p)

/-- The six displayed invariants form the claimed module basis.  Both finite
coinvariant calculations and the Reynolds/Molien dimension argument are now
proved internally, so this constructor has no certificate parameter. -/
noncomputable def concreteInvariantBasis :
    Module.Basis (Fin 6) SymmetricFiveRing F20InvariantModule := by
  let hrank := fixedCoinvariantRankCertificate
  let hpivot := candidateResiduePivotCertificate
  have hdet := candidateResiduePivotMatrix_det_ne_zero hpivot
  apply Module.Basis.mk
    (concreteInvariant_linearIndependent_of_residue_det explicitPivot hdet)
  exact gradedInvariantLifting hrank hpivot

/-- The basis constructor above has exactly Lazard's displayed family as its
vectors.  This paper-facing equation rules out reading the rank-six result as
the mere existence of some abstract six-element basis. -/
@[simp]
theorem concreteInvariantBasis_apply (j : Fin 6) :
    concreteInvariantBasis j = concreteInvariant j := by
  simp [concreteInvariantBasis]

end

end LeanProofs.PolynomialFormulas.LazardQuinticConcreteInvariantBasis
