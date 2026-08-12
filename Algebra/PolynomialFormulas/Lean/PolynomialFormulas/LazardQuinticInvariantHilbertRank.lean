import PolynomialFormulas.LazardInvariantMolienNumeratorSeries
import PolynomialFormulas.LazardInvariantLeadingTermDescent
import PolynomialFormulas.LazardDisplayedGroebnerQuintic
import Mathlib.RingTheory.AlgebraTower
import Mathlib.Data.Finsupp.Weight

/-!
# The rank-six consequence of the `F20` Molien numerator

This file connects the direct formal-power-series Molien identity to the
homogeneous invariant basis constructed by Reynolds induction.  If `B` is
that basis over the symmetric ring, then

* monomials in the elementary symmetric polynomials form a rational basis of
  the symmetric ring;
* `elementarySymmetricMonomialBasis.smulTower B.basis` is therefore a
  rational basis of the full invariant module;
* its vector `(a,i)` is homogeneous of degree
  `a.weight (fun j => j+1) + B.degree i`.

Restricting this basis degree by degree identifies the honest invariant
Hilbert series with

`(sum_i X^(B.degree i)) * product_{j=1}^5 (1-X^j)^(-1)`.

Multiplication by the symmetric denominator and the already-proved Molien
identity then show that the basis-degree series is exactly
`1+X^4+X^5+X^6+X^7+X^8`.  In particular `B` has six elements.  No matrix-rank
certificate is used.
-/

open scoped BigOperators
open MvPolynomial

namespace LeanProofs.PolynomialFormulas.LazardQuinticInvariantHilbertRank

open LeanProofs.PolynomialFormulas.Fin5Solvable
open LeanProofs.PolynomialFormulas.LazardInvariantModule
open LeanProofs.PolynomialFormulas.LazardInvariantGradedReynolds
open LeanProofs.PolynomialFormulas.LazardInvariantMolienCoefficients
open LeanProofs.PolynomialFormulas.LazardInvariantMolienNumeratorSeries

set_option autoImplicit false

noncomputable section

abbrev FivePolynomialRing := MvPolynomial (Fin 5) ℚ

abbrev SymmetricFiveRing :=
  MvPolynomial.symmetricSubalgebra (Fin 5) ℚ

abbrev F20InvariantModule :=
  (subgroupRepresentation ℚ (Fin 5) standardF20).invariants

abbrev F20HomogeneousPiece (d : ℕ) :=
  (homogeneousSubgroupRepresentation ℚ (Fin 5) standardF20 d).invariants

local instance standardF20Fintype : Fintype standardF20 :=
  Fintype.ofFinite standardF20

/-- Elementary symmetric generator `e_(i+1)` has ordinary root degree
`i+1`. -/
def elementaryWeight (i : Fin 5) : ℕ := i.1 + 1

@[simp]
theorem elementaryWeight_ne_zero (i : Fin 5) : elementaryWeight i ≠ 0 := by
  simp [elementaryWeight]

/-- The monomial basis in abstract elementary-symmetric variables,
transported to the actual symmetric subalgebra. -/
noncomputable def elementarySymmetricMonomialBasis :
    Module.Basis (Fin 5 →₀ ℕ) ℚ SymmetricFiveRing :=
  (MvPolynomial.basisMonomials (Fin 5) ℚ).map
    LazardDisplayedGroebnerQuintic.coefficientEquiv.toLinearEquiv

@[simp]
theorem elementarySymmetricMonomialBasis_apply (a : Fin 5 →₀ ℕ) :
    elementarySymmetricMonomialBasis a =
      LazardDisplayedGroebnerQuintic.coefficientEquiv
        (MvPolynomial.monomial a 1) := by
  simp [elementarySymmetricMonomialBasis, Module.Basis.map_apply]

/-- Elementary symmetric polynomials are homogeneous in their defining
degree. -/
theorem esymm_isHomogeneous (k : ℕ) :
    MvPolynomial.IsHomogeneous
      (MvPolynomial.esymm (Fin 5) ℚ k) k := by
  classical
  rw [MvPolynomial.esymm]
  apply MvPolynomial.IsHomogeneous.sum
  intro t ht
  have hcard : t.card = k := (Finset.mem_powersetCard.mp ht).2
  have hprod := MvPolynomial.IsHomogeneous.prod t
    (fun i : Fin 5 ↦ MvPolynomial.X i)
    (fun _i ↦ 1)
    (fun i hi ↦ MvPolynomial.isHomogeneous_X ℚ i)
  simpa [Finset.sum_const, hcard] using hprod

/-- A monomial in `e₁,...,e₅` has the expected weighted degree. -/
theorem elementarySymmetricMonomialBasis_isHomogeneous
    (a : Fin 5 →₀ ℕ) :
    MvPolynomial.IsHomogeneous
      (elementarySymmetricMonomialBasis a).1
      (Finsupp.weight elementaryWeight a) := by
  classical
  rw [elementarySymmetricMonomialBasis_apply]
  change MvPolynomial.IsHomogeneous
    (MvPolynomial.esymmAlgHomMonomial (Fin 5) a 1)
      (Finsupp.weight elementaryWeight a)
  rw [MvPolynomial.esymmAlgHomMonomial,
    MvPolynomial.esymmAlgHom_apply, MvPolynomial.aeval_monomial]
  simp only [map_one, one_mul]
  have hprod := MvPolynomial.IsHomogeneous.prod a.support
    (fun i : Fin 5 ↦ MvPolynomial.esymm (Fin 5) ℚ (i.1 + 1) ^ a i)
    (fun i ↦ (i.1 + 1) * a i)
    (fun i hi ↦ (esymm_isHomogeneous (i.1 + 1)).pow (a i))
  have hdegree :
      (∑ i ∈ a.support, (i.1 + 1) * a i) =
        Finsupp.weight elementaryWeight a := by
    rw [Finsupp.weight_apply, Finsupp.sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [elementaryWeight, nsmul_eq_mul, mul_comm]
  simpa only [Finsupp.prod, hdegree] using hprod

/-- The concrete homogeneous invariant basis produced by Lazard's Theorem 2
machinery. -/
noncomputable def abstractF20Basis :
    HomogeneousInvariantBasis ℚ (Fin 5) standardF20
      (lazardDegreeBound 5) :=
  lazardHomogeneousInvariantBasis ℚ 5 standardF20

local instance abstractF20BasisIndexFintype :
    Fintype abstractF20Basis.Index :=
  abstractF20Basis.indexFintype

/-- Extend the symmetric-module invariant basis along the rational monomial
basis of its coefficient ring. -/
noncomputable def rationalInvariantBasis :
    Module.Basis ((Fin 5 →₀ ℕ) × abstractF20Basis.Index)
      ℚ F20InvariantModule :=
  elementarySymmetricMonomialBasis.smulTower abstractF20Basis.basis

/-- Degree of one rational basis vector. -/
def rationalInvariantBasisDegree
    (j : (Fin 5 →₀ ℕ) × abstractF20Basis.Index) : ℕ :=
  Finsupp.weight elementaryWeight j.1 + abstractF20Basis.degree j.2

/-- Every vector in the rational tower basis is homogeneous in its displayed
degree. -/
theorem rationalInvariantBasis_isHomogeneous
    (j : (Fin 5 →₀ ℕ) × abstractF20Basis.Index) :
    MvPolynomial.IsHomogeneous (rationalInvariantBasis j).1
      (rationalInvariantBasisDegree j) := by
  rw [rationalInvariantBasis, Module.Basis.smulTower_apply]
  change MvPolynomial.IsHomogeneous
    ((elementarySymmetricMonomialBasis j.1).1 *
      (abstractF20Basis.basis j.2).1)
    (Finsupp.weight elementaryWeight j.1 + abstractF20Basis.degree j.2)
  exact (elementarySymmetricMonomialBasis_isHomogeneous j.1).mul
    (abstractF20Basis.basis_homogeneous j.2)

/-- Homogeneous components, restricted to the invariant module. -/
noncomputable def invariantHomogeneousComponentLinear (d : ℕ) :
    F20InvariantModule →ₗ[ℚ] F20InvariantModule where
  toFun p := ⟨MvPolynomial.homogeneousComponent d p.1, by
    rw [mem_subgroupRepresentation_invariants, mem_invariantSubalgebra]
    intro h
    rw [rename_homogeneousComponent]
    simpa only [subgroupRepresentation_apply] using
      congrArg (MvPolynomial.homogeneousComponent d) (p.2 h)⟩
  map_add' p q := by
    apply Subtype.ext
    exact map_add (MvPolynomial.homogeneousComponent d) p.1 q.1
  map_smul' r p := by
    apply Subtype.ext
    simpa only [SetLike.val_smul_of_tower, Algebra.smul_def,
      algebraMap_eq, RingHom.id_apply] using
        MvPolynomial.homogeneousComponent_C_mul p.1 d r

theorem invariantHomogeneousComponentLinear_eq_self
    {p : F20InvariantModule} {d : ℕ}
    (hp : MvPolynomial.IsHomogeneous p.1 d) :
    invariantHomogeneousComponentLinear d p = p := by
  apply Subtype.ext
  exact MvPolynomial.homogeneousComponent_eq_self hp

@[simp]
theorem invariantHomogeneousComponentLinear_rationalInvariantBasis
    (d : ℕ)
    (j : (Fin 5 →₀ ℕ) × abstractF20Basis.Index) :
    invariantHomogeneousComponentLinear d (rationalInvariantBasis j) =
      if d = rationalInvariantBasisDegree j then
        rationalInvariantBasis j else 0 := by
  apply Subtype.ext
  change MvPolynomial.homogeneousComponent d
      (rationalInvariantBasis j).1 = _
  rw [MvPolynomial.homogeneousComponent_of_mem
    (rationalInvariantBasis_isHomogeneous j)]
  split_ifs <;> rfl

/-- Coordinatewise diagonal form of homogeneous-component projection in the
rational tower basis. -/
theorem rationalInvariantBasis_repr_homogeneousComponent
    (d : ℕ) (p : F20InvariantModule)
    (j : (Fin 5 →₀ ℕ) × abstractF20Basis.Index) :
    rationalInvariantBasis.repr
        (invariantHomogeneousComponentLinear d p) j =
      if d = rationalInvariantBasisDegree j then
        rationalInvariantBasis.repr p j else 0 := by
  classical
  let lhs : F20InvariantModule →ₗ[ℚ] ℚ :=
    (rationalInvariantBasis.coord j).comp
      (invariantHomogeneousComponentLinear d)
  let rhs : F20InvariantModule →ₗ[ℚ] ℚ :=
    if d = rationalInvariantBasisDegree j then
      rationalInvariantBasis.coord j else 0
  have hmaps : lhs = rhs := by
    apply rationalInvariantBasis.ext
    intro k
    by_cases hdk : d = rationalInvariantBasisDegree k
    · by_cases hkj : k = j
      · subst k
        simp [lhs, rhs, hdk]
      · simp only [lhs, rhs, LinearMap.comp_apply,
          invariantHomogeneousComponentLinear_rationalInvariantBasis,
          hdk, if_pos, Module.Basis.coord_apply,
          Module.Basis.repr_self, Finsupp.single_apply, hkj, if_false]
        split_ifs <;> simp [hkj]
    · by_cases hkj : k = j
      · subst k
        simp [lhs, rhs, hdk]
      · simp only [lhs, rhs, LinearMap.comp_apply,
          invariantHomogeneousComponentLinear_rationalInvariantBasis,
          hdk, if_false, Module.Basis.coord_apply,
          Module.Basis.repr_self, Finsupp.single_apply, hkj]
        split_ifs <;> simp [hkj]
  have hp := LinearMap.congr_fun hmaps p
  dsimp [lhs, rhs] at hp
  by_cases hd : d = rationalInvariantBasisDegree j
  · rw [if_pos hd] at hp ⊢
    simpa only [Module.Basis.coord_apply] using hp
  · rw [if_neg hd] at hp ⊢
    simpa using hp

/-- A homogeneous invariant has no rational-basis coordinate in another
degree. -/
theorem rationalInvariantBasis_repr_eq_zero_of_degree_ne
    {p : F20InvariantModule} {d : ℕ}
    (hp : MvPolynomial.IsHomogeneous p.1 d)
    (j : (Fin 5 →₀ ℕ) × abstractF20Basis.Index)
    (hne : rationalInvariantBasisDegree j ≠ d) :
    rationalInvariantBasis.repr p j = 0 := by
  have hcomponent := rationalInvariantBasis_repr_homogeneousComponent d p j
  rw [invariantHomogeneousComponentLinear_eq_self hp] at hcomponent
  simpa [hne, Ne.symm hne] using hcomponent

/-- Indices of rational basis vectors in one fixed degree. -/
abbrev RationalInvariantDegreeIndex (d : ℕ) :=
  {j : (Fin 5 →₀ ℕ) × abstractF20Basis.Index //
    rationalInvariantBasisDegree j = d}

/-- Forget the homogeneous-submodule wrapper while retaining invariance. -/
def homogeneousPieceToInvariantLinear (d : ℕ) :
    F20HomogeneousPiece d →ₗ[ℚ] F20InvariantModule where
  toFun p := ⟨p.1.1, by
    rw [mem_subgroupRepresentation_invariants, mem_invariantSubalgebra]
    intro h
    exact congrArg Subtype.val (p.2 h)⟩
  map_add' p q := rfl
  map_smul' r p := rfl

set_option maxRecDepth 10000 in
/-- Linear combination of precisely the rational basis vectors in degree
`d`, bundled into the homogeneous invariant piece. -/
noncomputable def degreeCombinationLinear (d : ℕ) :
    (RationalInvariantDegreeIndex d →₀ ℚ) →ₗ[ℚ]
      F20HomogeneousPiece d where
  toFun c := by
    let extended :=
      (Finsupp.lmapDomain ℚ ℚ
        (fun j : RationalInvariantDegreeIndex d ↦ j.1)) c
    let v : F20InvariantModule := rationalInvariantBasis.repr.symm extended
    refine ⟨⟨v.1, ?_⟩, ?_⟩
    · rw [show v = Finsupp.linearCombination ℚ
      (fun j : RationalInvariantDegreeIndex d ↦
        rationalInvariantBasis j.1) c by
      change rationalInvariantBasis.repr.symm
          (Finsupp.mapDomain
            (fun j : RationalInvariantDegreeIndex d ↦ j.1) c) = _
      rw [Module.Basis.repr_symm_apply,
        Finsupp.linearCombination_mapDomain]
      rfl]
      rw [Finsupp.linearCombination_apply]
      rw [MvPolynomial.mem_homogeneousSubmodule]
      have hval :
          (c.sum fun j r ↦ r • rationalInvariantBasis j.1).1 =
            c.sum fun j r ↦
              MvPolynomial.C r * (rationalInvariantBasis j.1).1 := by
        simp only [Finsupp.sum, AddSubmonoidClass.coe_finsetSum,
          SetLike.val_smul_of_tower, Algebra.smul_def, algebraMap_eq]
      rw [hval]
      rw [Finsupp.sum]
      apply MvPolynomial.IsHomogeneous.sum
      intro j hj
      change MvPolynomial.IsHomogeneous
        (MvPolynomial.C (c j) * (rationalInvariantBasis j.1).1) d
      simpa [j.2] using
        (rationalInvariantBasis_isHomogeneous j.1).C_mul (c j)
    · intro h
      apply Subtype.ext
      exact v.2 h
  map_add' c e := by
    apply Subtype.ext
    apply Subtype.ext
    simp [Finsupp.lmapDomain_apply]
  map_smul' r c := by
    apply Subtype.ext
    apply Subtype.ext
    simp [Finsupp.lmapDomain_apply]

/-- Coordinates of a homogeneous invariant, restricted to the matching
degree indices. -/
noncomputable def degreeCoordinatesLinear (d : ℕ) :
    F20HomogeneousPiece d →ₗ[ℚ]
      (RationalInvariantDegreeIndex d →₀ ℚ) :=
  (Finsupp.lcomapDomain
    (fun j : RationalInvariantDegreeIndex d ↦ j.1)
    Subtype.val_injective).comp
      (rationalInvariantBasis.repr.toLinearMap.comp
        (homogeneousPieceToInvariantLinear d))

/-- Restricting and re-extending the global coordinates loses nothing on a
homogeneous invariant. -/
theorem degreeCombinationLinear_leftInverse (d : ℕ) :
    Function.LeftInverse (degreeCombinationLinear d)
      (degreeCoordinatesLinear d) := by
  intro p
  apply Subtype.ext
  apply Subtype.ext
  let pinv := homogeneousPieceToInvariantLinear d p
  let c := rationalInvariantBasis.repr pinv
  have hsupp : (c.support : Set
      ((Fin 5 →₀ ℕ) × abstractF20Basis.Index)) ⊆
      Set.range (fun j : RationalInvariantDegreeIndex d ↦ j.1) := by
    intro j hj
    have hc : c j ≠ 0 := Finsupp.mem_support_iff.mp hj
    have hdegree : rationalInvariantBasisDegree j = d := by
      by_contra hne
      exact hc (rationalInvariantBasis_repr_eq_zero_of_degree_ne
        ((MvPolynomial.mem_homogeneousSubmodule d p.1.1).mp p.1.2) j hne)
    exact ⟨⟨j, hdegree⟩, rfl⟩
  have hextend := Finsupp.mapDomain_comapDomain
    (fun j : RationalInvariantDegreeIndex d ↦ j.1)
    Subtype.val_injective c hsupp
  have hv :
      rationalInvariantBasis.repr.symm
        ((Finsupp.lmapDomain ℚ ℚ
          (fun j : RationalInvariantDegreeIndex d ↦ j.1))
          ((Finsupp.lcomapDomain (R := ℚ) (M := ℚ)
            (fun j : RationalInvariantDegreeIndex d ↦ j.1)
            Subtype.val_injective) c)) = pinv := by
    rw [Finsupp.lmapDomain_apply, Finsupp.lcomapDomain_apply, hextend]
    exact rationalInvariantBasis.repr.symm_apply_apply pinv
  exact congrArg (fun z : F20InvariantModule ↦ z.1) hv

/-- Re-extending and restricting a degree-indexed coordinate vector is the
identity. -/
theorem degreeCoordinatesLinear_leftInverse (d : ℕ) :
    Function.LeftInverse (degreeCoordinatesLinear d)
      (degreeCombinationLinear d) := by
  intro c
  have htoInvariant :
      homogeneousPieceToInvariantLinear d
          (degreeCombinationLinear d c) =
        rationalInvariantBasis.repr.symm
          (Finsupp.mapDomain
            (fun j : RationalInvariantDegreeIndex d ↦ j.1) c) := by
    apply Subtype.ext
    rfl
  ext j
  simp only [degreeCoordinatesLinear, LinearMap.comp_apply,
    Finsupp.lcomapDomain_apply, Finsupp.comapDomain_apply]
  rw [htoInvariant]
  change
    (rationalInvariantBasis.repr
      (rationalInvariantBasis.repr.symm
        (Finsupp.mapDomain
          (fun k : RationalInvariantDegreeIndex d ↦ k.1) c))) j.1 = c j
  rw [rationalInvariantBasis.repr.apply_symm_apply]
  exact Finsupp.mapDomain_apply Subtype.val_injective c j

/-- Exact coordinate equivalence for one homogeneous invariant piece. -/
noncomputable def homogeneousPieceCoordinateEquiv (d : ℕ) :
    F20HomogeneousPiece d ≃ₗ[ℚ]
      (RationalInvariantDegreeIndex d →₀ ℚ) :=
  { degreeCoordinatesLinear d with
    invFun := degreeCombinationLinear d
    left_inv := degreeCombinationLinear_leftInverse d
    right_inv := degreeCoordinatesLinear_leftInverse d }

/-- The degree-`d` slice of the rational tower basis. -/
noncomputable def homogeneousInvariantPieceBasis (d : ℕ) :
    Module.Basis (RationalInvariantDegreeIndex d) ℚ
      (F20HomogeneousPiece d) :=
  Module.Basis.ofRepr (homogeneousPieceCoordinateEquiv d)

/-- The degree-index type is finite. -/
noncomputable def rationalInvariantDegreeIndexFintype (d : ℕ) :
    Fintype (RationalInvariantDegreeIndex d) := by
  let E := {a : Fin 5 →₀ ℕ // Finsupp.weight elementaryWeight a ≤ d}
  letI : Fintype E :=
    (Finsupp.finite_of_nat_weight_le elementaryWeight
      elementaryWeight_ne_zero d).fintype
  let target := E × abstractF20Basis.Index
  let embed : RationalInvariantDegreeIndex d → target := fun j ↦
    (⟨j.1.1, by
      have := j.2
      simp [rationalInvariantBasisDegree] at this
      omega⟩, j.1.2)
  exact Fintype.ofInjective embed (by
    intro j k h
    dsimp [embed] at h
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg
        (fun z : E × abstractF20Basis.Index ↦ z.1.1) h
    · exact congrArg
        (fun z : E × abstractF20Basis.Index ↦ z.2) h)

/-- Coefficients of the invariant Hilbert series count the rational tower
basis vectors in that degree. -/
theorem f20InvariantHilbertSeries_coeff_eq_degreeIndexCard (d : ℕ) :
    PowerSeries.coeff d f20InvariantHilbertSeries =
      (Nat.card (RationalInvariantDegreeIndex d) : ℚ) := by
  letI := rationalInvariantDegreeIndexFintype d
  change PowerSeries.coeff d
      (homogeneousInvariantHilbertSeries (Fin 5) standardF20) = _
  rw [homogeneousInvariantHilbertSeries, PowerSeries.coeff_mk]
  rw [Module.finrank_eq_card_basis (homogeneousInvariantPieceBasis d)]
  norm_cast
  exact Fintype.card_eq_nat_card

/-! ## The basis-degree generating series -/

/-- Generating polynomial of the degrees of the abstract symmetric-module
basis. -/
def abstractBasisDegreeSeries : PowerSeries ℚ :=
  ∑ i : abstractF20Basis.Index,
    PowerSeries.X ^ abstractF20Basis.degree i

/-- Generating series for monomials in elementary symmetric polynomials. -/
def elementarySymmetricHilbertSeries : PowerSeries ℚ :=
  weightedDegreeSeries (Fin 5) elementaryWeight

theorem elementarySymmetricHilbertSeries_eq_geometricProduct :
    elementarySymmetricHilbertSeries =
      ∏ i : Fin 5, geometricStepSeries (elementaryWeight i) := by
  exact weightedDegreeSeries_eq_prod_geometricStep
    elementaryWeight elementaryWeight_ne_zero

/-- Finitely supported exponent vectors and ordinary functions carry the
same weighted-degree condition. -/
noncomputable def finsuppWeightedDegreeEquiv (d : ℕ) :
    {a : Fin 5 →₀ ℕ // Finsupp.weight elementaryWeight a = d} ≃
      WeightedDegree (Fin 5) elementaryWeight d where
  toFun a := ⟨fun i ↦ a.1 i, by
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype,
      elementaryWeight, nsmul_eq_mul, mul_comm] using a.2⟩
  invFun q := ⟨Finsupp.equivFunOnFinite.symm q.1, by
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype,
      elementaryWeight, nsmul_eq_mul, mul_comm] using q.2⟩
  left_inv a := by
    apply Subtype.ext
    exact Finsupp.equivFunOnFinite.symm_apply_apply a.1
  right_inv q := by
    apply Subtype.ext
    exact Finsupp.equivFunOnFinite.apply_symm_apply q.1

theorem elementarySymmetricHilbertSeries_coeff (d : ℕ) :
    PowerSeries.coeff d elementarySymmetricHilbertSeries =
      (Nat.card
        {a : Fin 5 →₀ ℕ // Finsupp.weight elementaryWeight a = d} : ℚ) := by
  rw [elementarySymmetricHilbertSeries, weightedDegreeSeries,
    PowerSeries.coeff_mk]
  norm_cast
  exact (Nat.card_congr (finsuppWeightedDegreeEquiv d)).symm

/-- Split a rational degree index into its invariant-basis index and its
elementary-symmetric exponent. -/
noncomputable def degreeIndexEquivSigma (d : ℕ) :
    RationalInvariantDegreeIndex d ≃
      Σ i : abstractF20Basis.Index,
        {a : Fin 5 →₀ ℕ //
          Finsupp.weight elementaryWeight a + abstractF20Basis.degree i = d} where
  toFun j := ⟨j.1.2, ⟨j.1.1, j.2⟩⟩
  invFun j := ⟨(j.2.1, j.1), j.2.2⟩
  left_inv j := rfl
  right_inv j := rfl

private theorem shiftedWeightCard (d : ℕ) (i : abstractF20Basis.Index) :
    Nat.card {a : Fin 5 →₀ ℕ //
        Finsupp.weight elementaryWeight a + abstractF20Basis.degree i = d} =
      if abstractF20Basis.degree i ≤ d then
        Nat.card {a : Fin 5 →₀ ℕ //
          Finsupp.weight elementaryWeight a =
            d - abstractF20Basis.degree i}
      else 0 := by
  by_cases hi : abstractF20Basis.degree i ≤ d
  · rw [if_pos hi]
    apply Nat.card_congr
    apply Equiv.setCongr
    ext a
    change (Finsupp.weight elementaryWeight a +
      abstractF20Basis.degree i = d) ↔
        Finsupp.weight elementaryWeight a =
          d - abstractF20Basis.degree i
    omega
  · rw [if_neg hi]
    haveI : IsEmpty {a : Fin 5 →₀ ℕ //
        Finsupp.weight elementaryWeight a + abstractF20Basis.degree i = d} :=
      ⟨fun a ↦ (hi (by omega)).elim⟩
    exact Nat.card_of_isEmpty

/-- The honest invariant Hilbert series is the free homogeneous-basis series
times the Hilbert series of the symmetric coefficient ring. -/
theorem f20InvariantHilbertSeries_eq_basisDegree_mul_elementary :
    f20InvariantHilbertSeries =
      abstractBasisDegreeSeries * elementarySymmetricHilbertSeries := by
  letI (i : abstractF20Basis.Index) (d : ℕ) :
      Finite {a : Fin 5 →₀ ℕ //
        Finsupp.weight elementaryWeight a + abstractF20Basis.degree i = d} :=
    ((Finsupp.finite_of_nat_weight_le elementaryWeight
      elementaryWeight_ne_zero d).subset (by
        intro a ha
        change Finsupp.weight elementaryWeight a ≤ d
        change Finsupp.weight elementaryWeight a +
          abstractF20Basis.degree i = d at ha
        omega)).to_subtype
  ext d
  rw [f20InvariantHilbertSeries_coeff_eq_degreeIndexCard,
    abstractBasisDegreeSeries, Finset.sum_mul, map_sum]
  simp_rw [PowerSeries.coeff_X_pow_mul']
  rw [Nat.card_congr (degreeIndexEquivSigma d), Nat.card_sigma]
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [shiftedWeightCard]
  by_cases hid : abstractF20Basis.degree i ≤ d
  · rw [if_pos hid, if_pos hid,
      elementarySymmetricHilbertSeries_coeff]
  · rw [if_neg hid, if_neg hid]
    norm_num

/-- The elementary-symmetric Hilbert series is inverse to the displayed
symmetric denominator. -/
theorem elementarySymmetricHilbertSeries_mul_denominator :
    elementarySymmetricHilbertSeries * symmetricDenominatorSeries = 1 := by
  rw [elementarySymmetricHilbertSeries_eq_geometricProduct]
  rw [show (∏ i : Fin 5, geometricStepSeries (elementaryWeight i)) =
      geometricStepSeries 1 * geometricStepSeries 2 *
        geometricStepSeries 3 * geometricStepSeries 4 *
          geometricStepSeries 5 by
    simp [Fin.prod_univ_succ, elementaryWeight]
    ring]
  rw [show symmetricDenominatorSeries =
      (1 - PowerSeries.X ^ 1) * (1 - PowerSeries.X ^ 2) *
        (1 - PowerSeries.X ^ 3) * (1 - PowerSeries.X ^ 4) *
          (1 - PowerSeries.X ^ 5) by
    simp [symmetricDenominatorSeries, stepDenominator]]
  have h1 : geometricStepSeries 1 * (1 - PowerSeries.X ^ 1) = 1 := by
    simpa [stepDenominator] using
      geometricStepSeries_mul_stepDenominator 1 (by decide)
  have h2 : geometricStepSeries 2 * (1 - PowerSeries.X ^ 2) = 1 := by
    simpa [stepDenominator] using
      geometricStepSeries_mul_stepDenominator 2 (by decide)
  have h3 : geometricStepSeries 3 * (1 - PowerSeries.X ^ 3) = 1 := by
    simpa [stepDenominator] using
      geometricStepSeries_mul_stepDenominator 3 (by decide)
  have h4 : geometricStepSeries 4 * (1 - PowerSeries.X ^ 4) = 1 := by
    simpa [stepDenominator] using
      geometricStepSeries_mul_stepDenominator 4 (by decide)
  have h5 : geometricStepSeries 5 * (1 - PowerSeries.X ^ 5) = 1 := by
    simpa [stepDenominator] using
      geometricStepSeries_mul_stepDenominator 5 (by decide)
  calc
    geometricStepSeries 1 * geometricStepSeries 2 *
        geometricStepSeries 3 * geometricStepSeries 4 *
        geometricStepSeries 5 *
      ((1 - PowerSeries.X ^ 1) * (1 - PowerSeries.X ^ 2) *
        (1 - PowerSeries.X ^ 3) * (1 - PowerSeries.X ^ 4) *
        (1 - PowerSeries.X ^ 5)) =
      (geometricStepSeries 1 * (1 - PowerSeries.X ^ 1)) *
        (geometricStepSeries 2 * (1 - PowerSeries.X ^ 2)) *
        (geometricStepSeries 3 * (1 - PowerSeries.X ^ 3)) *
        (geometricStepSeries 4 * (1 - PowerSeries.X ^ 4)) *
        (geometricStepSeries 5 * (1 - PowerSeries.X ^ 5)) := by ring
    _ = 1 := by rw [h1, h2, h3, h4, h5]; simp

/-- The abstract basis-degree series is exactly Lazard's six-term
numerator. -/
theorem abstractBasisDegreeSeries_eq_f20MolienNumeratorSeries :
    abstractBasisDegreeSeries = f20MolienNumeratorSeries := by
  calc
    abstractBasisDegreeSeries = abstractBasisDegreeSeries * 1 := by simp
    _ = abstractBasisDegreeSeries *
        (elementarySymmetricHilbertSeries * symmetricDenominatorSeries) := by
      rw [elementarySymmetricHilbertSeries_mul_denominator]
    _ = (abstractBasisDegreeSeries * elementarySymmetricHilbertSeries) *
        symmetricDenominatorSeries := by ring
    _ = f20InvariantHilbertSeries * symmetricDenominatorSeries := by
      rw [f20InvariantHilbertSeries_eq_basisDegree_mul_elementary]
    _ = f20MolienNumeratorSeries :=
      f20InvariantHilbertSeries_mul_symmetricDenominator

/-- Coefficientwise, the abstract basis has one generator in degrees
`0,4,5,6,7,8` and none in every other degree. -/
theorem abstractF20Basis_degree_count (d : ℕ) :
    Nat.card {i : abstractF20Basis.Index // abstractF20Basis.degree i = d} =
      if d = 0 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 then 1 else 0 := by
  classical
  have hcoeff := congrArg (PowerSeries.coeff d)
    abstractBasisDegreeSeries_eq_f20MolienNumeratorSeries
  rw [abstractBasisDegreeSeries, map_sum] at hcoeff
  simp only [PowerSeries.coeff_X_pow] at hcoeff
  rw [Finset.sum_boole] at hcoeff
  rw [← Fintype.card_subtype
      (fun i : abstractF20Basis.Index ↦ d = abstractF20Basis.degree i),
    Fintype.card_eq_nat_card] at hcoeff
  have hsymm :
      Nat.card {i : abstractF20Basis.Index // d = abstractF20Basis.degree i} =
        Nat.card {i : abstractF20Basis.Index // abstractF20Basis.degree i = d} := by
    apply Nat.card_congr
    apply Equiv.setCongr
    ext i
    exact eq_comm
  rw [hsymm] at hcoeff
  simp only [f20MolienNumeratorSeries, map_add,
    PowerSeries.coeff_one, PowerSeries.coeff_X_pow] at hcoeff
  by_cases h0 : d = 0 <;> by_cases h4 : d = 4 <;>
    by_cases h5 : d = 5 <;> by_cases h6 : d = 6 <;>
    by_cases h7 : d = 7 <;> by_cases h8 : d = 8 <;>
    simp [h0, h4, h5, h6, h7, h8] at hcoeff ⊢ <;>
    exact_mod_cast hcoeff

/-- The homogeneous invariant basis constructed by Reynolds induction has
exactly six elements. -/
theorem abstractF20Basis_card : Fintype.card abstractF20Basis.Index = 6 := by
  let degreeFin : abstractF20Basis.Index → Fin 11 := fun i ↦
    ⟨abstractF20Basis.degree i, by
      have h := abstractF20Basis.degree_le i
      norm_num [lazardDegreeBound] at h ⊢
      omega⟩
  let e : abstractF20Basis.Index ≃
      Σ d : Fin 11, {i : abstractF20Basis.Index // degreeFin i = d} :=
    (Equiv.sigmaFiberEquiv degreeFin).symm
  have hcard := Nat.card_congr e
  rw [Nat.card_eq_fintype_card, Nat.card_sigma] at hcard
  have hfiber (d : Fin 11) :
      Nat.card {i : abstractF20Basis.Index // degreeFin i = d} =
        Nat.card {i : abstractF20Basis.Index //
          abstractF20Basis.degree i = d.1} := by
    apply Nat.card_congr
    apply Equiv.setCongr
    ext i
    simp [degreeFin, Fin.ext_iff]
  simp_rw [hfiber] at hcard
  have hsum :
      (∑ d : Fin 11,
        Nat.card {i : abstractF20Basis.Index //
          abstractF20Basis.degree i = d.1}) = 6 := by
    simp_rw [abstractF20Basis_degree_count]
    decide
  omega

end

end LeanProofs.PolynomialFormulas.LazardQuinticInvariantHilbertRank
