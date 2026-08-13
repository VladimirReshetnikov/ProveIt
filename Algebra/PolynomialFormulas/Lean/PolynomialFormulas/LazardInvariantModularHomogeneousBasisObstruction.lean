import PolynomialFormulas.LazardInvariantModularHomogeneousBasisHilbert
import PolynomialFormulas.LazardInvariantModularCyclicDegreeSevenIndexApply
import PolynomialFormulas.LazardInvariantModularProductBridge
import PolynomialFormulas.LazardInvariantModularQuotientObstruction
import Mathlib.Tactic

/-!
# The semantic homogeneous-basis obstruction for the modular C6 action

The upstream Hilbert calculation shows that a hypothetical Lazard-bounded
homogeneous invariant basis has exactly sixteen vectors in degree seven.
This module proves the missing semantic bridge: modulo the positive
elementary-symmetric products, every degree-seven orbit-coordinate residue
is spanned by the sixteen corresponding basis residues.  The independently
certified seventeen test classes then contradict the compact
`literalTestClass_not_spanned_by_sixteen` theorem.
-/

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularHomogeneousBasisObstruction

open scoped BigOperators
open Finset MvPolynomial
open Module

open LazardDualQuotientCertificate
open LazardInvariantModule
open LazardInvariantGradedReynolds
open LazardInvariantHomogeneousCoordinates
open LazardInvariantMolienCoefficients
open LazardInvariantModularCounterexample
open LazardInvariantModularDualCertificate
open LazardInvariantModularOrbitCoordinates
open LazardInvariantModularProductBridge
open LazardInvariantModularCyclicInvariants

set_option autoImplicit false

noncomputable section

section HypotheticalBasis

variable (B : HomogeneousInvariantBasis F3 (Fin 6) cyclicSix
  (lazardDegreeBound 6))

local instance semanticBridgeBasisIndexFintype : Fintype B.Index :=
  B.indexFintype

/-! ## Positive symmetric degree and the sixteen surviving residues -/

/- Every index used by the 132-coordinate realization is one of the
canonical degree-seven orbit representatives. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem degreeSevenRepresentative_mem_orbitRepresentatives :
    ∀ i : Fin 132,
      degreeSevenRepresentative i ∈ (orbitRepresentatives 7).toFinset := by
  intro i
  rw [← degreeSevenIndexEquivOrbitRepresentative_apply_val i]
  exact (degreeSevenIndexEquivOrbitRepresentative i).2

/-- Package a coordinate column as the corresponding canonical orbit
representative subtype. -/
def degreeSevenRepresentativeSubtype (i : Fin 132) :
    OrbitRepresentative 7 :=
  ⟨degreeSevenRepresentative i,
    degreeSevenRepresentative_mem_orbitRepresentatives i⟩

/-- Every polynomial produced by the 132-coordinate realization is
homogeneous of degree seven. -/
theorem degreeSevenOrbitCoordinateMap_isHomogeneous
    (v : DegreeSevenCoordinates) :
    (degreeSevenOrbitCoordinateMap v).IsHomogeneous 7 := by
  classical
  rw [degreeSevenOrbitCoordinateMap, Fintype.linearCombination_apply]
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  simpa [Algebra.smul_def, algebraMap_eq, degreeSevenOrbitPolynomial,
    degreeSevenRepresentativeSubtype] using
    (cyclicOrbitPolynomial_isHomogeneous (7 : Fin 8)
      (degreeSevenRepresentativeSubtype i)).C_mul (v i)

/-- Every polynomial produced by the 132-coordinate realization is fixed by
the explicit six-cycle. -/
theorem degreeSevenOrbitCoordinateMap_fixed (v : DegreeSevenCoordinates) :
    cycleSixRenameLinear (degreeSevenOrbitCoordinateMap v) =
      degreeSevenOrbitCoordinateMap v := by
  classical
  rw [degreeSevenOrbitCoordinateMap, Fintype.linearCombination_apply,
    map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul]
  exact congrArg (fun p : SixPolynomialRing => v i • p)
    (cyclicOrbitPolynomial_fixed (7 : Fin 8)
      (degreeSevenRepresentativeSubtype i))

/-- The coordinate realization bundled as an element of the actual invariant
module. -/
def degreeSevenCoordinateInvariant (v : DegreeSevenCoordinates) :
    C6InvariantModule :=
  ⟨degreeSevenOrbitCoordinateMap v,
    (mem_cyclicSix_invariantSubalgebra_iff
      (degreeSevenOrbitCoordinateMap v)).mpr (by
        simpa only [cycleSixRenameLinear_apply] using
          degreeSevenOrbitCoordinateMap_fixed v)⟩

@[simp]
theorem degreeSevenCoordinateInvariant_coe (v : DegreeSevenCoordinates) :
    (degreeSevenCoordinateInvariant v).1 = degreeSevenOrbitCoordinateMap v :=
  rfl

/-- A nonconstant elementary-symmetric tower vector of total degree seven
lies in the intrinsic positive symmetric-parameter subspace. -/
theorem fieldInvariantBasis_mem_degreeSevenPositiveSymmetricModuleSubspace
    (j : (Fin 6 →₀ ℕ) × B.Index)
    (hdegree : fieldInvariantBasisDegree B j = 7)
    (hexponent : j.1 ≠ 0) :
    (fieldInvariantBasis B j).1 ∈
      degreeSevenPositiveSymmetricModuleSubspace := by
  rcases Finsupp.ne_iff.mp hexponent with ⟨i, hi⟩
  let a' := j.1 - Finsupp.single i 1
  let q : C6InvariantModule := fieldInvariantBasis B (a', j.2)
  have hweight := Finsupp.weight_sub_single_add
    (w := elementaryVariableWeight) hi
  have hqdegree : fieldInvariantBasisDegree B (a', j.2) = 6 - i.1 := by
    dsimp [a', fieldInvariantBasisDegree] at hweight ⊢
    dsimp [elementaryVariableWeight] at hweight
    dsimp [fieldInvariantBasisDegree] at hdegree
    omega
  have hqhomogeneous : q.1.IsHomogeneous (6 - i.1) := by
    simpa [q, hqdegree] using
      fieldInvariantBasis_isHomogeneous B (a', j.2)
  have hqfixed : q.1 ∈ cyclicOrbitSumSubspace (6 - i.1) := by
    rw [cyclicOrbitSumSubspace_eq_cyclicFixedHomogeneousSubspace
      (⟨6 - i.1, by omega⟩ : Fin 8)]
    rw [mem_cyclicFixedHomogeneousSubspace_iff]
    exact ⟨hqhomogeneous, q.2⟩
  apply (le_iSup
    (fun k : Fin 6 =>
      (cyclicOrbitSumSubspace (6 - k.1)).map
        (elementaryMulLinear (k.1 + 1))) i)
  refine ⟨q.1, hqfixed, ?_⟩
  change MvPolynomial.esymm (Fin 6) F3 (i.1 + 1) * q.1 =
    (fieldInvariantBasis B j).1
  rw [show q = fieldInvariantBasis B (a', j.2) from rfl]
  rw [fieldInvariantBasis]
  simp_rw [Module.Basis.smulTower_apply]
  dsimp [a']
  change
    MvPolynomial.esymm (Fin 6) F3 (i.1 + 1) *
        ((elementarySymmetricMonomialBasisSix
          (j.1 - Finsupp.single i 1)).1 * (B.basis j.2).1) =
      (elementarySymmetricMonomialBasisSix j.1).1 * (B.basis j.2).1
  rw [elementarySymmetricMonomialBasisSix_factor j.1 i hi]
  ring

/-- Hypothetical basis vectors of degree seven. -/
abbrev DegreeSevenHypotheticalBasisIndex :=
  {i : B.Index // B.degree i = 7}

/-- The part of an invariant retaining precisely the zero-elementary-exponent
tower coordinates whose hypothetical basis degree is seven. -/
noncomputable def degreeSevenFreePart (x : C6InvariantModule) :
    C6InvariantModule :=
  (fieldInvariantBasis B).repr.symm
    (((fieldInvariantBasis B).repr x).filter
      (fun j => j.1 = 0 ∧ B.degree j.2 = 7))

/-- The part retaining tower coordinates with nonzero elementary exponent. -/
noncomputable def degreeSevenPositivePart (x : C6InvariantModule) :
    C6InvariantModule :=
  (fieldInvariantBasis B).repr.symm
    (((fieldInvariantBasis B).repr x).filter (fun j => j.1 ≠ 0))

/-- Coordinate formula for the degree-seven free part. -/
theorem fieldInvariantBasis_repr_degreeSevenFreePart
    (x : C6InvariantModule) (j : (Fin 6 →₀ ℕ) × B.Index) :
    (fieldInvariantBasis B).repr (degreeSevenFreePart B x) j =
      if j.1 = 0 ∧ B.degree j.2 = 7 then
        (fieldInvariantBasis B).repr x j else 0 := by
  classical
  rw [degreeSevenFreePart, (fieldInvariantBasis B).repr.apply_symm_apply]
  rfl

/-- Coordinate formula for the positive-exponent part. -/
theorem fieldInvariantBasis_repr_degreeSevenPositivePart
    (x : C6InvariantModule) (j : (Fin 6 →₀ ℕ) × B.Index) :
    (fieldInvariantBasis B).repr (degreeSevenPositivePart B x) j =
      if j.1 ≠ 0 then (fieldInvariantBasis B).repr x j else 0 := by
  classical
  rw [degreeSevenPositivePart, (fieldInvariantBasis B).repr.apply_symm_apply]
  rfl

/-- A homogeneous degree-seven invariant is the sum of its sixteen possible
free residues and its positive symmetric-parameter part. -/
theorem degreeSevenFreePart_add_positivePart
    (x : C6InvariantModule) (hx : x.1.IsHomogeneous 7) :
    degreeSevenFreePart B x + degreeSevenPositivePart B x = x := by
  apply (fieldInvariantBasis B).repr.injective
  ext j
  rw [map_add, Finsupp.add_apply,
    fieldInvariantBasis_repr_degreeSevenFreePart,
    fieldInvariantBasis_repr_degreeSevenPositivePart]
  by_cases hc : (fieldInvariantBasis B).repr x j = 0
  · simp [hc]
  have hdegree : fieldInvariantBasisDegree B j = 7 := by
    by_contra hne
    exact hc (fieldInvariantBasis_repr_eq_zero_of_degree_ne B hx j hne)
  by_cases hj : j.1 = 0
  · have hbdegree : B.degree j.2 = 7 := by
      simpa [fieldInvariantBasisDegree, hj] using hdegree
    simp [hj, hbdegree]
  · simp [hj]

/-- The positive-exponent part of a degree-seven invariant belongs to the
literal positive symmetric-parameter subspace. -/
theorem degreeSevenPositivePart_mem
    (x : C6InvariantModule) (hx : x.1.IsHomogeneous 7) :
    (degreeSevenPositivePart B x).1 ∈
      degreeSevenPositiveSymmetricModuleSubspace := by
  classical
  let c := ((fieldInvariantBasis B).repr x).filter (fun j => j.1 ≠ 0)
  change ((fieldInvariantBasis B).repr.symm c).1 ∈
    degreeSevenPositiveSymmetricModuleSubspace
  rw [Module.Basis.repr_symm_apply, Finsupp.linearCombination_apply]
  have hval :
      (c.sum fun j r => r • fieldInvariantBasis B j).1 =
        c.sum fun j r => r • (fieldInvariantBasis B j).1 := by
    simp only [Finsupp.sum, AddSubmonoidClass.coe_finsetSum,
      SetLike.val_smul_of_tower]
  rw [hval, Finsupp.sum]
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  have hcfilter : c j ≠ 0 := Finsupp.mem_support_iff.mp hj
  have hjpos : j.1 ≠ 0 := by
    by_contra hzero
    apply hcfilter
    simp [c, hzero]
  have hc : (fieldInvariantBasis B).repr x j ≠ 0 :=
    by simpa [c, hjpos] using hcfilter
  have hdegree : fieldInvariantBasisDegree B j = 7 := by
    by_contra hne
    exact hc (fieldInvariantBasis_repr_eq_zero_of_degree_ne B hx j hne)
  exact fieldInvariantBasis_mem_degreeSevenPositiveSymmetricModuleSubspace
    B j hdegree hjpos

/-- Subtracting the sixteen-coordinate free part leaves an element of the
positive symmetric-parameter subspace. -/
theorem sub_degreeSevenFreePart_mem
    (x : C6InvariantModule) (hx : x.1.IsHomogeneous 7) :
    x.1 - (degreeSevenFreePart B x).1 ∈
      degreeSevenPositiveSymmetricModuleSubspace := by
  have hdecomp := congrArg Subtype.val
    (degreeSevenFreePart_add_positivePart B x hx)
  have hpositive := degreeSevenPositivePart_mem B x hx
  rw [← hdecomp]
  simpa [add_sub_cancel_left] using hpositive

/-! ## Transport to the already certified literal quotient -/

/-- Reuse the compact literal quotient from
`LazardInvariantModularQuotientObstruction`. -/
abbrev LiteralDegreeSevenProductSubspace :=
  LazardInvariantModularQuotientObstruction.LiteralDegreeSevenProductSubspace

abbrev LiteralDegreeSevenQuotient :=
  LazardInvariantModularQuotientObstruction.LiteralDegreeSevenQuotient

/-- The image subspace of the coordinate rows is exactly the intrinsic
positive symmetric-parameter space. -/
theorem literalDegreeSevenProductSubspace_eq_positive :
    LiteralDegreeSevenProductSubspace =
      degreeSevenPositiveSymmetricModuleSubspace :=
  degreeSevenProductSubspace_map_eq_positiveSymmetricModuleSubspace

/-- The forced degree-seven count gives an explicit equivalence with sixteen
labels. -/
noncomputable def degreeSevenHypotheticalBasisIndexEquivFin :
    DegreeSevenHypotheticalBasisIndex B ≃ Fin 16 :=
  Finite.equivFinOfCardEq (by
    simpa [hypotheticalBasisDegreeCount] using
      hypotheticalBasisDegreeCount_seven B)

/-- The sixteen quotient classes which would survive under hypothetical
homogeneous freeness. -/
noncomputable def sixteenLiteralGenerators (j : Fin 16) :
    LiteralDegreeSevenQuotient :=
  LiteralDegreeSevenProductSubspace.mkQ
    (B.basis ((degreeSevenHypotheticalBasisIndexEquivFin B).symm j).1).1

/-- The free part of any invariant has quotient class in the span of the
sixteen surviving generators. -/
theorem degreeSevenFreePart_class_mem_sixteenSpan (x : C6InvariantModule) :
    LiteralDegreeSevenProductSubspace.mkQ (degreeSevenFreePart B x).1 ∈
      Submodule.span F3 (Set.range (sixteenLiteralGenerators B)) := by
  classical
  let c := ((fieldInvariantBasis B).repr x).filter
    (fun j => j.1 = 0 ∧ B.degree j.2 = 7)
  change LiteralDegreeSevenProductSubspace.mkQ
    ((fieldInvariantBasis B).repr.symm c).1 ∈ _
  rw [Module.Basis.repr_symm_apply, Finsupp.linearCombination_apply]
  have hval :
      (c.sum fun j r => r • fieldInvariantBasis B j).1 =
        c.sum fun j r => r • (fieldInvariantBasis B j).1 := by
    simp only [Finsupp.sum, AddSubmonoidClass.coe_finsetSum,
      SetLike.val_smul_of_tower]
  rw [hval]
  simp only [map_finsuppSum, map_smul]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  apply Submodule.subset_span
  have hc : c i ≠ 0 := Finsupp.mem_support_iff.mp hi
  have hkeep : i.1 = 0 ∧ B.degree i.2 = 7 := by
    by_contra hnot
    apply hc
    simp [c, hnot]
  rcases i with ⟨a, i⟩
  rcases hkeep with ⟨ha, hdegree⟩
  change a = 0 at ha
  change B.degree i = 7 at hdegree
  subst a
  let i' : DegreeSevenHypotheticalBasisIndex B := ⟨i, hdegree⟩
  refine ⟨degreeSevenHypotheticalBasisIndexEquivFin B i', ?_⟩
  simp [sixteenLiteralGenerators, i']

/-- Every degree-seven orbit-coordinate class lies in the span of the
sixteen residues forced by hypothetical homogeneous freeness. -/
theorem degreeSevenOrbitClass_mem_sixteenSpan (v : DegreeSevenCoordinates) :
    LiteralDegreeSevenProductSubspace.mkQ
        (degreeSevenOrbitCoordinateMap v) ∈
      Submodule.span F3 (Set.range (sixteenLiteralGenerators B)) := by
  let x := degreeSevenCoordinateInvariant v
  have hx : x.1.IsHomogeneous 7 := by
    simpa [x] using degreeSevenOrbitCoordinateMap_isHomogeneous v
  have hresidual :
      x.1 - (degreeSevenFreePart B x).1 ∈
        LiteralDegreeSevenProductSubspace := by
    rw [literalDegreeSevenProductSubspace_eq_positive]
    exact sub_degreeSevenFreePart_mem B x hx
  have hquotient :
      LiteralDegreeSevenProductSubspace.mkQ x.1 =
        LiteralDegreeSevenProductSubspace.mkQ
          (degreeSevenFreePart B x).1 :=
    (Submodule.Quotient.eq LiteralDegreeSevenProductSubspace).mpr hresidual
  change LiteralDegreeSevenProductSubspace.mkQ x.1 ∈
    Submodule.span F3 (Set.range (sixteenLiteralGenerators B))
  rw [hquotient]
  exact degreeSevenFreePart_class_mem_sixteenSpan B x

/-- The semantic bridge requested by the modular counterexample:
a hypothetical homogeneous symmetric-module basis produces sixteen literal
quotient classes spanning every degree-seven orbit-coordinate residue. -/
theorem degreeSeven_residue_span_of_homogeneousInvariantBasis
    (B : HomogeneousInvariantBasis F3 (Fin 6) cyclicSix
      (lazardDegreeBound 6)) :
    ∃ generators : Fin 16 → LiteralDegreeSevenQuotient,
      ∀ v : DegreeSevenCoordinates,
        LiteralDegreeSevenProductSubspace.mkQ
            (degreeSevenOrbitCoordinateMap v) ∈
          Submodule.span F3 (Set.range generators) := by
  exact ⟨sixteenLiteralGenerators B,
    degreeSevenOrbitClass_mem_sixteenSpan B⟩

/-- In particular, all seventeen independently certified literal test
classes lie in the span forced by the hypothetical basis. -/
theorem literalTestClass_mem_sixteenSpan (j : Fin 17) :
    LazardInvariantModularQuotientObstruction.literalTestClass j ∈
      Submodule.span F3 (Set.range (sixteenLiteralGenerators B)) := by
  simpa [
    LazardInvariantModularQuotientObstruction.literalTestClass,
    LazardInvariantModularQuotientObstruction.coordinateQuotientToLiteralQuotient,
    Submodule.mapQ_apply] using
      degreeSevenOrbitClass_mem_sixteenSpan B (testVector j)

/-! ## Final contradiction -/

/-- The regular `C6` invariant ring over `ZMod 3` admits no homogeneous
free basis over the symmetric polynomials with Lazard's advertised degree
bound.  The compact obstruction closes the contradiction after the semantic
bridge above supplies its sixteen generators. -/
theorem no_lazardHomogeneousInvariantBasis :
    ¬ Nonempty (HomogeneousInvariantBasis F3 (Fin 6) cyclicSix
      (lazardDegreeBound 6)) := by
  rintro ⟨B⟩
  exact
    (LazardInvariantModularQuotientObstruction.literalTestClass_not_spanned_by_sixteen
        (sixteenLiteralGenerators B))
      (literalTestClass_mem_sixteenSpan B)

end HypotheticalBasis

/-- Characteristic three satisfies the paper's printed global exclusions
`char ≠ 2,5`. -/
theorem F3_satisfies_lazardPrintedCharacteristicExclusions :
    (2 : F3) ≠ 0 ∧ (5 : F3) ≠ 0 := by
  decide

/-- The counterexample packaged in the exact scope needed to refute the
arbitrary-degree form of the printed theorem. -/
theorem regularC6_counterexample_with_printedCharacteristicExclusions :
    (2 : F3) ≠ 0 ∧ (5 : F3) ≠ 0 ∧
      ¬ Nonempty (HomogeneousInvariantBasis F3 (Fin 6) cyclicSix
        (lazardDegreeBound 6)) := by
  exact ⟨F3_satisfies_lazardPrintedCharacteristicExclusions.1,
    F3_satisfies_lazardPrintedCharacteristicExclusions.2,
    no_lazardHomogeneousInvariantBasis⟩

/-- Fully closed semantic package for the counterexample: the displayed
subgroup really is `C6`, the field really has characteristic three while
satisfying the paper's two printed exclusions, and the genuine invariant
module admits no advertised bounded homogeneous finite-free basis. -/
theorem regularC6_closedSemanticCounterexample :
    Fintype.card cyclicSix = 6 ∧
      (3 : F3) = 0 ∧
      (2 : F3) ≠ 0 ∧
      (5 : F3) ≠ 0 ∧
      ¬ Nonempty (HomogeneousInvariantBasis F3 (Fin 6) cyclicSix
        (lazardDegreeBound 6)) := by
  exact ⟨cyclicSix_card, by decide,
    F3_satisfies_lazardPrintedCharacteristicExclusions.1,
    F3_satisfies_lazardPrintedCharacteristicExclusions.2,
    no_lazardHomogeneousInvariantBasis⟩

end

end LeanProofs.PolynomialFormulas.LazardInvariantModularHomogeneousBasisObstruction
