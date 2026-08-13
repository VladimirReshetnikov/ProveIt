import PolynomialFormulas.LazardInvariantModularCyclicInvariants
import PolynomialFormulas.LazardInvariantModularHomogeneousBasisOrbitCounts
import PolynomialFormulas.LazardInvariantMolienCoefficients
import PolynomialFormulas.LazardInvariantGradedReynolds
import PolynomialFormulas.LazardInvariantHomogeneousCoordinates
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Finsupp.Weight
import Mathlib.RingTheory.AlgebraTower
import Mathlib.Tactic

/-!
# The bounded Hilbert calculation for the modular regular C6 action

Assuming a finite homogeneous basis of the regular-six-cycle invariant
module over the symmetric polynomial ring, this module extends that basis
along the elementary-symmetric monomial basis and restricts the resulting
field basis degree by degree.  Comparison with the semantic cyclic-orbit
basis yields the Hilbert convolution through degree seven and forces the
basis-degree counts

`1, 0, 2, 5, 8, 11, 17, 16`.

In particular, every hypothetical Lazard-bounded homogeneous basis has
exactly sixteen degree-seven vectors.  The quotient-semantic contradiction
is deliberately kept in the smaller downstream obstruction module.
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

abbrev SixPolynomialRing := MvPolynomial (Fin 6) F3

abbrev SymmetricSixRing :=
  MvPolynomial.symmetricSubalgebra (Fin 6) F3

abbrev C6InvariantModule :=
  (subgroupRepresentation F3 (Fin 6) cyclicSix).invariants

abbrev C6HomogeneousPiece (d : ℕ) :=
  (homogeneousSubgroupRepresentation F3 (Fin 6) cyclicSix d).invariants

/-! ## Exact dimensions of the concrete homogeneous fixed spaces -/

/-- The generic semantic C6 reconstruction already separates canonical
orbit representatives uniformly in every degree at most seven. -/
theorem orbitRepresentative_mem_orbit_iff (d : Fin 8) :
    ∀ r s : OrbitRepresentative d.1,
      s.1 ∈ cyclicOrbitSupport r.1 ↔ r = s := by
  exact LazardInvariantModularCyclicInvariants.orbitRepresentative_mem_orbit_iff d

/-- Coordinate realization by the canonical cyclic orbit sums in degree
`d`. -/
def cyclicOrbitCoordinateMap (d : ℕ) :
    (OrbitRepresentative d → F3) →ₗ[F3] SixPolynomialRing :=
  Fintype.linearCombination F3
    (fun r : OrbitRepresentative d => cyclicOrbitPolynomial r.1)

/-- Coefficient recovery at the canonical representative. -/
theorem coeff_cyclicOrbitCoordinateMap (d : Fin 8)
    (v : OrbitRepresentative d.1 → F3)
    (s : OrbitRepresentative d.1) :
    (cyclicOrbitCoordinateMap d.1 v).coeff
        (Finsupp.equivFunOnFinite.symm s.1) = v s := by
  classical
  change
    (MvPolynomial.lcoeff F3 (Finsupp.equivFunOnFinite.symm s.1))
      (cyclicOrbitCoordinateMap d.1 v) = v s
  rw [cyclicOrbitCoordinateMap, Fintype.linearCombination_apply, map_sum]
  simp [coeff_cyclicOrbitPolynomial,
    orbitRepresentative_mem_orbit_iff d, eq_comm]

/-- The canonical orbit-coordinate realization is injective. -/
theorem cyclicOrbitCoordinateMap_injective (d : Fin 8) :
    Function.Injective (cyclicOrbitCoordinateMap d.1) := by
  intro v w hvw
  funext s
  have hcoeff := congrArg
    (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm s.1)) hvw
  simpa only [coeff_cyclicOrbitCoordinateMap] using hcoeff

/-- Canonical orbit sums are linearly independent in every degree at most
seven. -/
theorem cyclicOrbitPolynomial_linearIndependent (d : Fin 8) :
    LinearIndependent F3
      (fun r : OrbitRepresentative d.1 => cyclicOrbitPolynomial r.1) := by
  rw [linearIndependent_iff_injective_fintypeLinearCombination]
  exact cyclicOrbitCoordinateMap_injective d

/-- `List.eraseDups` is semantically duplicate-free for every lawful Boolean
equality, so no degree-by-degree computation is needed here. -/
private theorem eraseDups_nodup_semantic {α : Type*}
    [BEq α] [LawfulBEq α] :
    ∀ l : List α, l.eraseDups.Nodup
  | [] => by simp
  | a :: as => by
      rw [List.eraseDups_cons]
      apply List.nodup_cons.mpr
      constructor
      · intro ha
        rw [List.mem_eraseDups] at ha
        simp at ha
      · exact eraseDups_nodup_semantic
          (as.filter fun b => !b == a)
termination_by l => l.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ as)

theorem orbitRepresentatives_nodup (d : Fin 8) :
    (orbitRepresentatives d.1).Nodup := by
  rw [orbitRepresentatives]
  exact eraseDups_nodup_semantic _

/-- The subtype cardinal of canonical representatives is the executable
orbit count. -/
theorem orbitRepresentative_card_eq_invariantOrbitCount (d : Fin 8) :
    Fintype.card (OrbitRepresentative d.1) = invariantOrbitCount d.1 := by
  rw [Fintype.card_coe,
    List.toFinset_card_of_nodup (orbitRepresentatives_nodup d)]
  rfl

/-- The actual fixed homogeneous subspace has the explicit orbit count as
its dimension. -/
theorem cyclicFixedHomogeneousSubspace_finrank (d : Fin 8) :
    finrank F3 (cyclicFixedHomogeneousSubspace d.1) =
      invariantOrbitCount d.1 := by
  rw [← cyclicOrbitSumSubspace_eq_cyclicFixedHomogeneousSubspace d,
    cyclicOrbitSumSubspace,
    finrank_span_eq_card (cyclicOrbitPolynomial_linearIndependent d),
    orbitRepresentative_card_eq_invariantOrbitCount]

/-- The representation-theoretic homogeneous invariant subtype is the same
vector space as the intersection definition used by the explicit cyclic
orbit development. -/
def c6HomogeneousPieceEquivFixed (d : ℕ) :
    C6HomogeneousPiece d ≃ₗ[F3] cyclicFixedHomogeneousSubspace d where
  toFun p := ⟨p.1.1, by
    rw [mem_cyclicFixedHomogeneousSubspace_iff]
    refine ⟨p.1.2, ?_⟩
    rw [mem_invariantSubalgebra]
    intro h
    exact congrArg Subtype.val (p.2 h)⟩
  invFun p := ⟨⟨p.1, p.2.1⟩, by
    rw [mem_homogeneousSubgroupRepresentation_invariants]
    intro h
    exact (mem_invariantSubalgebra F3 (Fin 6) cyclicSix p.1).mp
      ((mem_cyclicFixedHomogeneousSubspace_iff d p.1).mp p.2).2 h⟩
  left_inv p := by rfl
  right_inv p := by rfl
  map_add' p q := by rfl
  map_smul' r p := by rfl

/-- Hence the standard homogeneous invariant piece has the same explicit
dimension. -/
theorem c6HomogeneousPiece_finrank (d : Fin 8) :
    finrank F3 (C6HomogeneousPiece d.1) = invariantOrbitCount d.1 := by
  rw [LinearEquiv.finrank_eq (c6HomogeneousPieceEquivFixed d.1),
    cyclicFixedHomogeneousSubspace_finrank]

/-! ## The elementary-symmetric tower basis -/

/-- Elementary symmetric generator `e_(i+1)` has root degree `i+1`. -/
def elementaryVariableWeight (i : Fin 6) : ℕ := i.1 + 1

@[simp]
theorem elementaryVariableWeight_ne_zero (i : Fin 6) :
    elementaryVariableWeight i ≠ 0 := by
  simp [elementaryVariableWeight]

/-- The abstract monomial basis transported through the elementary-symmetric
algebra equivalence. -/
noncomputable def elementarySymmetricMonomialBasisSix :
    Module.Basis (Fin 6 →₀ ℕ) F3 SymmetricSixRing :=
  (MvPolynomial.basisMonomials (Fin 6) F3).map
    (MvPolynomial.esymmAlgEquiv (Fin 6) F3 (by simp)).toLinearEquiv

@[simp]
theorem elementarySymmetricMonomialBasisSix_apply (a : Fin 6 →₀ ℕ) :
    elementarySymmetricMonomialBasisSix a =
      MvPolynomial.esymmAlgEquiv (Fin 6) F3 (by simp)
        (MvPolynomial.monomial a 1) := by
  simp [elementarySymmetricMonomialBasisSix, Module.Basis.map_apply]

/-- Elementary symmetric polynomials are homogeneous in their defining
degree. -/
theorem esymmSix_isHomogeneous (k : ℕ) :
    MvPolynomial.IsHomogeneous
      (MvPolynomial.esymm (Fin 6) F3 k) k := by
  classical
  rw [MvPolynomial.esymm]
  apply MvPolynomial.IsHomogeneous.sum
  intro t ht
  have hcard : t.card = k := (Finset.mem_powersetCard.mp ht).2
  have hprod := MvPolynomial.IsHomogeneous.prod t
    (fun i : Fin 6 => MvPolynomial.X i)
    (fun _i => 1)
    (fun i _hi => MvPolynomial.isHomogeneous_X F3 i)
  simpa [Finset.sum_const, hcard] using hprod

/-- An elementary-symmetric monomial has its expected weighted degree. -/
theorem elementarySymmetricMonomialBasisSix_isHomogeneous
    (a : Fin 6 →₀ ℕ) :
    MvPolynomial.IsHomogeneous
      (elementarySymmetricMonomialBasisSix a).1
      (Finsupp.weight elementaryVariableWeight a) := by
  classical
  rw [elementarySymmetricMonomialBasisSix_apply]
  change MvPolynomial.IsHomogeneous
    (MvPolynomial.esymmAlgHomMonomial (Fin 6) a 1)
      (Finsupp.weight elementaryVariableWeight a)
  rw [MvPolynomial.esymmAlgHomMonomial,
    MvPolynomial.esymmAlgHom_apply, MvPolynomial.aeval_monomial]
  simp only [map_one, one_mul]
  have hprod := MvPolynomial.IsHomogeneous.prod a.support
    (fun i : Fin 6 =>
      MvPolynomial.esymm (Fin 6) F3 (i.1 + 1) ^ a i)
    (fun i => (i.1 + 1) * a i)
    (fun i _hi => (esymmSix_isHomogeneous (i.1 + 1)).pow (a i))
  have hdegree :
      (∑ i ∈ a.support, (i.1 + 1) * a i) =
        Finsupp.weight elementaryVariableWeight a := by
    rw [Finsupp.weight_apply, Finsupp.sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [elementaryVariableWeight, nsmul_eq_mul, mul_comm]
  simpa only [Finsupp.prod, hdegree] using hprod

/-- Removing one positive exponent factors the corresponding elementary
symmetric generator from an elementary-symmetric monomial. -/
theorem elementarySymmetricMonomialBasisSix_factor
    (a : Fin 6 →₀ ℕ) (i : Fin 6) (hi : a i ≠ 0) :
    (elementarySymmetricMonomialBasisSix a).1 =
      MvPolynomial.esymm (Fin 6) F3 (i.1 + 1) *
        (elementarySymmetricMonomialBasisSix
          (a - Finsupp.single i 1)).1 := by
  rw [elementarySymmetricMonomialBasisSix_apply,
    elementarySymmetricMonomialBasisSix_apply]
  have ha := Finsupp.sub_add_single_one_cancel hi
  conv_lhs => rw [← ha]
  rw [MvPolynomial.monomial_add_single, pow_one, map_mul]
  simp [MvPolynomial.esymmAlgEquiv, MvPolynomial.esymmAlgHom,
    mul_comm]

section HypotheticalBasis

variable (B : HomogeneousInvariantBasis F3 (Fin 6) cyclicSix
  (lazardDegreeBound 6))

local instance hypotheticalBasisIndexFintype : Fintype B.Index :=
  B.indexFintype

/-- Extend a hypothetical symmetric-module basis along the field basis of
the symmetric coefficient ring. -/
noncomputable def fieldInvariantBasis :
    Module.Basis ((Fin 6 →₀ ℕ) × B.Index) F3 C6InvariantModule :=
  elementarySymmetricMonomialBasisSix.smulTower B.basis

/-- Degree of a field-basis vector in the tower basis. -/
def fieldInvariantBasisDegree
    (j : (Fin 6 →₀ ℕ) × B.Index) : ℕ :=
  Finsupp.weight elementaryVariableWeight j.1 + B.degree j.2

/-- Every field-basis vector has the displayed degree. -/
theorem fieldInvariantBasis_isHomogeneous
    (j : (Fin 6 →₀ ℕ) × B.Index) :
    MvPolynomial.IsHomogeneous (fieldInvariantBasis B j).1
      (fieldInvariantBasisDegree B j) := by
  rw [fieldInvariantBasis, Module.Basis.smulTower_apply]
  change MvPolynomial.IsHomogeneous
    ((elementarySymmetricMonomialBasisSix j.1).1 *
      (B.basis j.2).1)
    (Finsupp.weight elementaryVariableWeight j.1 + B.degree j.2)
  exact (elementarySymmetricMonomialBasisSix_isHomogeneous j.1).mul
    (B.basis_homogeneous j.2)

/-- The zero elementary exponent recovers the original hypothetical basis
vector. -/
@[simp]
theorem fieldInvariantBasis_zero_apply (i : B.Index) :
    fieldInvariantBasis B (0, i) = B.basis i := by
  rw [fieldInvariantBasis, Module.Basis.smulTower_apply]
  have hzero : elementarySymmetricMonomialBasisSix (0 : Fin 6 →₀ ℕ) = 1 := by
    rw [elementarySymmetricMonomialBasisSix_apply,
      MvPolynomial.monomial_zero', MvPolynomial.C_1]
    simpa only [MvPolynomial.esymmAlgEquiv_apply] using
      map_one (MvPolynomial.esymmAlgHom (Fin 6) F3 6)
  rw [hzero]
  apply Subtype.ext
  simp only [SetLike.val_smul_of_tower, Algebra.smul_def, map_one, one_mul]

/-! ### Restriction of the tower basis to one homogeneous degree -/

/-- Homogeneous components restricted to the invariant module. -/
noncomputable def invariantHomogeneousComponentLinear (d : ℕ) :
    C6InvariantModule →ₗ[F3] C6InvariantModule where
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
    {p : C6InvariantModule} {d : ℕ}
    (hp : MvPolynomial.IsHomogeneous p.1 d) :
    invariantHomogeneousComponentLinear d p = p := by
  apply Subtype.ext
  exact MvPolynomial.homogeneousComponent_eq_self hp

@[simp]
theorem invariantHomogeneousComponentLinear_fieldInvariantBasis
    (d : ℕ) (j : (Fin 6 →₀ ℕ) × B.Index) :
    invariantHomogeneousComponentLinear d (fieldInvariantBasis B j) =
      if d = fieldInvariantBasisDegree B j then
        fieldInvariantBasis B j else 0 := by
  apply Subtype.ext
  change MvPolynomial.homogeneousComponent d
      (fieldInvariantBasis B j).1 = _
  rw [MvPolynomial.homogeneousComponent_of_mem
    (fieldInvariantBasis_isHomogeneous B j)]
  split_ifs <;> rfl

/-- Diagonal coordinate formula for homogeneous projection. -/
theorem fieldInvariantBasis_repr_homogeneousComponent
    (d : ℕ) (p : C6InvariantModule)
    (j : (Fin 6 →₀ ℕ) × B.Index) :
    (fieldInvariantBasis B).repr
        (invariantHomogeneousComponentLinear d p) j =
      if d = fieldInvariantBasisDegree B j then
        (fieldInvariantBasis B).repr p j else 0 := by
  classical
  let lhs : C6InvariantModule →ₗ[F3] F3 :=
    ((fieldInvariantBasis B).coord j).comp
      (invariantHomogeneousComponentLinear d)
  let rhs : C6InvariantModule →ₗ[F3] F3 :=
    if d = fieldInvariantBasisDegree B j then
      (fieldInvariantBasis B).coord j else 0
  have hmaps : lhs = rhs := by
    apply (fieldInvariantBasis B).ext
    intro k
    by_cases hdk : d = fieldInvariantBasisDegree B k
    · by_cases hkj : k = j
      · subst k
        simp [lhs, rhs, hdk]
      · simp only [lhs, rhs, LinearMap.comp_apply,
          invariantHomogeneousComponentLinear_fieldInvariantBasis,
          hdk, if_pos, Module.Basis.coord_apply,
          Module.Basis.repr_self, Finsupp.single_apply, hkj, if_false]
        split_ifs <;> simp [hkj]
    · by_cases hkj : k = j
      · subst k
        simp [lhs, rhs, hdk]
      · simp only [lhs, rhs, LinearMap.comp_apply,
          invariantHomogeneousComponentLinear_fieldInvariantBasis,
          hdk, if_false, Module.Basis.coord_apply,
          Module.Basis.repr_self, Finsupp.single_apply, hkj]
        split_ifs <;> simp [hkj]
  have hp := LinearMap.congr_fun hmaps p
  dsimp [lhs, rhs] at hp
  by_cases hd : d = fieldInvariantBasisDegree B j
  · rw [if_pos hd] at hp ⊢
    simpa only [Module.Basis.coord_apply] using hp
  · rw [if_neg hd] at hp ⊢
    simpa using hp

/-- A homogeneous invariant has zero tower coordinate in every other
degree. -/
theorem fieldInvariantBasis_repr_eq_zero_of_degree_ne
    {p : C6InvariantModule} {d : ℕ}
    (hp : MvPolynomial.IsHomogeneous p.1 d)
    (j : (Fin 6 →₀ ℕ) × B.Index)
    (hne : fieldInvariantBasisDegree B j ≠ d) :
    (fieldInvariantBasis B).repr p j = 0 := by
  have hcomponent :=
    fieldInvariantBasis_repr_homogeneousComponent B d p j
  rw [invariantHomogeneousComponentLinear_eq_self hp] at hcomponent
  simpa [hne, Ne.symm hne] using hcomponent

/-- Tower-basis indices of total degree `d`. -/
abbrev FieldInvariantDegreeIndex (d : ℕ) :=
  {j : (Fin 6 →₀ ℕ) × B.Index //
    fieldInvariantBasisDegree B j = d}

/-- Forget the homogeneous wrapper while retaining invariance. -/
def homogeneousPieceToInvariantLinear (d : ℕ) :
    C6HomogeneousPiece d →ₗ[F3] C6InvariantModule where
  toFun p := ⟨p.1.1, by
    rw [mem_subgroupRepresentation_invariants, mem_invariantSubalgebra]
    intro h
    exact congrArg Subtype.val (p.2 h)⟩
  map_add' p q := rfl
  map_smul' r p := rfl

set_option maxRecDepth 10000 in
/-- Assemble a vector from coordinates supported on tower-basis vectors of
one degree. -/
noncomputable def degreeCombinationLinear (d : ℕ) :
    (FieldInvariantDegreeIndex B d →₀ F3) →ₗ[F3]
      C6HomogeneousPiece d where
  toFun c := by
    let extended :=
      (Finsupp.lmapDomain F3 F3
        (fun j : FieldInvariantDegreeIndex B d => j.1)) c
    let v : C6InvariantModule := (fieldInvariantBasis B).repr.symm extended
    refine ⟨⟨v.1, ?_⟩, ?_⟩
    · rw [show v = Finsupp.linearCombination F3
        (fun j : FieldInvariantDegreeIndex B d =>
          fieldInvariantBasis B j.1) c by
        change (fieldInvariantBasis B).repr.symm
            (Finsupp.mapDomain
              (fun j : FieldInvariantDegreeIndex B d => j.1) c) = _
        rw [Module.Basis.repr_symm_apply,
          Finsupp.linearCombination_mapDomain]
        rfl]
      rw [Finsupp.linearCombination_apply]
      rw [MvPolynomial.mem_homogeneousSubmodule]
      have hval :
          (c.sum fun j r => r • fieldInvariantBasis B j.1).1 =
            c.sum fun j r =>
              MvPolynomial.C r * (fieldInvariantBasis B j.1).1 := by
        simp only [Finsupp.sum, AddSubmonoidClass.coe_finsetSum,
          SetLike.val_smul_of_tower, Algebra.smul_def, algebraMap_eq]
      rw [hval]
      rw [Finsupp.sum]
      apply MvPolynomial.IsHomogeneous.sum
      intro j hj
      change MvPolynomial.IsHomogeneous
        (MvPolynomial.C (c j) * (fieldInvariantBasis B j.1).1) d
      simpa [j.2] using
        (fieldInvariantBasis_isHomogeneous B j.1).C_mul (c j)
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

/-- Restrict global tower coordinates to one homogeneous degree. -/
noncomputable def degreeCoordinatesLinear (d : ℕ) :
    C6HomogeneousPiece d →ₗ[F3]
      (FieldInvariantDegreeIndex B d →₀ F3) :=
  (Finsupp.lcomapDomain
    (fun j : FieldInvariantDegreeIndex B d => j.1)
    Subtype.val_injective).comp
      ((fieldInvariantBasis B).repr.toLinearMap.comp
        (homogeneousPieceToInvariantLinear d))

/-- Restriction followed by extension is the identity on a homogeneous
invariant. -/
theorem degreeCombinationLinear_leftInverse (d : ℕ) :
    Function.LeftInverse (degreeCombinationLinear B d)
      (degreeCoordinatesLinear B d) := by
  intro p
  apply Subtype.ext
  apply Subtype.ext
  let pinv := homogeneousPieceToInvariantLinear d p
  let c := (fieldInvariantBasis B).repr pinv
  have hsupp : (c.support : Set ((Fin 6 →₀ ℕ) × B.Index)) ⊆
      Set.range (fun j : FieldInvariantDegreeIndex B d => j.1) := by
    intro j hj
    have hc : c j ≠ 0 := Finsupp.mem_support_iff.mp hj
    have hdegree : fieldInvariantBasisDegree B j = d := by
      by_contra hne
      exact hc (fieldInvariantBasis_repr_eq_zero_of_degree_ne
        B ((MvPolynomial.mem_homogeneousSubmodule d p.1.1).mp p.1.2) j hne)
    exact ⟨⟨j, hdegree⟩, rfl⟩
  have hextend := Finsupp.mapDomain_comapDomain
    (fun j : FieldInvariantDegreeIndex B d => j.1)
    Subtype.val_injective c hsupp
  have hv :
      (fieldInvariantBasis B).repr.symm
        ((Finsupp.lmapDomain F3 F3
          (fun j : FieldInvariantDegreeIndex B d => j.1))
          ((Finsupp.lcomapDomain (R := F3) (M := F3)
            (fun j : FieldInvariantDegreeIndex B d => j.1)
            Subtype.val_injective) c)) = pinv := by
    rw [Finsupp.lmapDomain_apply, Finsupp.lcomapDomain_apply, hextend]
    exact (fieldInvariantBasis B).repr.symm_apply_apply pinv
  exact congrArg (fun z : C6InvariantModule => z.1) hv

/-- Extension followed by restriction is the identity on degree-indexed
coordinates. -/
theorem degreeCoordinatesLinear_leftInverse (d : ℕ) :
    Function.LeftInverse (degreeCoordinatesLinear B d)
      (degreeCombinationLinear B d) := by
  intro c
  have htoInvariant :
      homogeneousPieceToInvariantLinear d
          (degreeCombinationLinear B d c) =
        (fieldInvariantBasis B).repr.symm
          (Finsupp.mapDomain
            (fun j : FieldInvariantDegreeIndex B d => j.1) c) := by
    apply Subtype.ext
    rfl
  ext j
  simp only [degreeCoordinatesLinear, LinearMap.comp_apply,
    Finsupp.lcomapDomain_apply, Finsupp.comapDomain_apply]
  rw [htoInvariant]
  change
    ((fieldInvariantBasis B).repr
      ((fieldInvariantBasis B).repr.symm
        (Finsupp.mapDomain
          (fun k : FieldInvariantDegreeIndex B d => k.1) c))) j.1 = c j
  rw [(fieldInvariantBasis B).repr.apply_symm_apply]
  exact Finsupp.mapDomain_apply Subtype.val_injective c j

/-- Exact coordinate equivalence for one homogeneous invariant piece. -/
noncomputable def homogeneousPieceCoordinateEquiv (d : ℕ) :
    C6HomogeneousPiece d ≃ₗ[F3]
      (FieldInvariantDegreeIndex B d →₀ F3) :=
  { degreeCoordinatesLinear B d with
    invFun := degreeCombinationLinear B d
    left_inv := degreeCombinationLinear_leftInverse B d
    right_inv := degreeCoordinatesLinear_leftInverse B d }

/-- Basis of a homogeneous piece obtained by restricting the tower basis. -/
noncomputable def homogeneousInvariantPieceBasis (d : ℕ) :
    Module.Basis (FieldInvariantDegreeIndex B d) F3
      (C6HomogeneousPiece d) :=
  Module.Basis.ofRepr (homogeneousPieceCoordinateEquiv B d)

/-- The fixed-degree tower-index type is finite. -/
noncomputable def fieldInvariantDegreeIndexFintype (d : ℕ) :
    Fintype (FieldInvariantDegreeIndex B d) := by
  let E := {a : Fin 6 →₀ ℕ //
    Finsupp.weight elementaryVariableWeight a ≤ d}
  letI : Fintype E :=
    (Finsupp.finite_of_nat_weight_le elementaryVariableWeight
      elementaryVariableWeight_ne_zero d).fintype
  let target := E × B.Index
  let embed : FieldInvariantDegreeIndex B d → target := fun j =>
    (⟨j.1.1, by
      have := j.2
      simp [fieldInvariantBasisDegree] at this
      omega⟩, j.1.2)
  exact Fintype.ofInjective embed (by
    intro j k h
    dsimp [embed] at h
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun z : E × B.Index => z.1.1) h
    · exact congrArg (fun z : E × B.Index => z.2) h)

/-- Dimension of a homogeneous piece equals the cardinal of the matching
tower indices. -/
theorem c6HomogeneousPiece_finrank_eq_degreeIndexCard (d : ℕ) :
    finrank F3 (C6HomogeneousPiece d) =
      Nat.card (FieldInvariantDegreeIndex B d) := by
  letI := fieldInvariantDegreeIndexFintype B d
  rw [Module.finrank_eq_card_basis (homogeneousInvariantPieceBasis B d)]
  exact Fintype.card_eq_nat_card

/-- Comparing the tower basis with the explicit cyclic orbit basis gives the
bounded Hilbert coefficient identity. -/
theorem fieldInvariantDegreeIndex_card_eq_orbitCount (d : Fin 8) :
    Nat.card (FieldInvariantDegreeIndex B d.1) =
      invariantOrbitCount d.1 := by
  rw [← c6HomogeneousPiece_finrank_eq_degreeIndexCard B d.1,
    c6HomogeneousPiece_finrank d]

/-! ## The bounded Hilbert convolution -/

/-- Elementary-symmetric exponent vectors of one weighted degree. -/
abbrev ElementaryWeightIndex (d : ℕ) :=
  {a : Fin 6 →₀ ℕ //
    Finsupp.weight elementaryVariableWeight a = d}

noncomputable instance elementaryWeightIndexFintype (d : ℕ) :
    Fintype (ElementaryWeightIndex d) :=
  (Finsupp.finite_of_nat_weight_eq elementaryVariableWeight
    elementaryVariableWeight_ne_zero d).fintype

/-- A fully finite presentation of a weighted exponent vector in degree at
most seven.  Coordinate `i` has the sharp bound `d / (i+1)`, reducing the
largest closed cardinality check from `8^6` candidates to 768. -/
abbrev BoundedElementaryWeightIndex (d : Fin 8) :=
  {a : ∀ i : Fin 6, Fin (d.1 / (i.1 + 1) + 1) //
    ∑ i : Fin 6, (i.1 + 1) * (a i).1 = d.1}

/-- Equivalence from the ordinary finitely supported exponent type to the
closed bounded type used for the eight numerical checks. -/
noncomputable def elementaryWeightIndexEquivBounded (d : Fin 8) :
    ElementaryWeightIndex d.1 ≃ BoundedElementaryWeightIndex d where
  toFun a := ⟨fun i => ⟨a.1 i, by
    have hterm :
        (i.1 + 1) * a.1 i ≤
          ∑ j : Fin 6, (j.1 + 1) * a.1 j := by
      exact Finset.single_le_sum
        (fun j _ => Nat.zero_le ((j.1 + 1) * a.1 j))
        (Finset.mem_univ i)
    have hmul : a.1 i * (i.1 + 1) ≤ d.1 := by
      calc
        a.1 i * (i.1 + 1) = (i.1 + 1) * a.1 i := Nat.mul_comm _ _
        _ ≤ ∑ j : Fin 6, (j.1 + 1) * a.1 j := hterm
        _ = d.1 := by
          simpa [Finsupp.weight_apply, Finsupp.sum_fintype,
            elementaryVariableWeight, nsmul_eq_mul, mul_comm] using a.2
    exact Nat.lt_succ_iff.mpr
      ((Nat.le_div_iff_mul_le (by omega)).mpr hmul)⟩, by
      simpa [Finsupp.weight_apply, Finsupp.sum_fintype,
        elementaryVariableWeight, nsmul_eq_mul, mul_comm] using a.2⟩
  invFun a :=
    ⟨Finsupp.equivFunOnFinite.symm (fun i => (a.1 i).1), by
      simpa [Finsupp.weight_apply, Finsupp.sum_fintype,
        elementaryVariableWeight, nsmul_eq_mul, mul_comm] using a.2⟩
  left_inv a := by
    apply Subtype.ext
    exact Finsupp.equivFunOnFinite.symm_apply_apply a.1
  right_inv a := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    rfl

/-! The coefficient-ring Hilbert function in degrees zero through seven is
`1,1,2,3,5,7,11,14`. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem elementaryWeightIndex_card_closed_zero :
    Nat.card (ElementaryWeightIndex 0) = 1 := by
  change Nat.card (ElementaryWeightIndex (0 : Fin 8).1) = 1
  rw [Nat.card_congr
      (elementaryWeightIndexEquivBounded (0 : Fin 8)),
    Nat.card_eq_fintype_card]
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem elementaryWeightIndex_card_closed_one :
    Nat.card (ElementaryWeightIndex 1) = 1 := by
  change Nat.card (ElementaryWeightIndex (1 : Fin 8).1) = 1
  rw [Nat.card_congr
      (elementaryWeightIndexEquivBounded (1 : Fin 8)),
    Nat.card_eq_fintype_card]
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem elementaryWeightIndex_card_closed_two :
    Nat.card (ElementaryWeightIndex 2) = 2 := by
  change Nat.card (ElementaryWeightIndex (2 : Fin 8).1) = 2
  rw [Nat.card_congr
      (elementaryWeightIndexEquivBounded (2 : Fin 8)),
    Nat.card_eq_fintype_card]
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem elementaryWeightIndex_card_closed_three :
    Nat.card (ElementaryWeightIndex 3) = 3 := by
  change Nat.card (ElementaryWeightIndex (3 : Fin 8).1) = 3
  rw [Nat.card_congr
      (elementaryWeightIndexEquivBounded (3 : Fin 8)),
    Nat.card_eq_fintype_card]
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem elementaryWeightIndex_card_closed_four :
    Nat.card (ElementaryWeightIndex 4) = 5 := by
  change Nat.card (ElementaryWeightIndex (4 : Fin 8).1) = 5
  rw [Nat.card_congr
      (elementaryWeightIndexEquivBounded (4 : Fin 8)),
    Nat.card_eq_fintype_card]
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem elementaryWeightIndex_card_closed_five :
    Nat.card (ElementaryWeightIndex 5) = 7 := by
  change Nat.card (ElementaryWeightIndex (5 : Fin 8).1) = 7
  rw [Nat.card_congr
      (elementaryWeightIndexEquivBounded (5 : Fin 8)),
    Nat.card_eq_fintype_card]
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem elementaryWeightIndex_card_closed_six :
    Nat.card (ElementaryWeightIndex 6) = 11 := by
  change Nat.card (ElementaryWeightIndex (6 : Fin 8).1) = 11
  rw [Nat.card_congr
      (elementaryWeightIndexEquivBounded (6 : Fin 8)),
    Nat.card_eq_fintype_card]
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem elementaryWeightIndex_card_closed_seven :
    Nat.card (ElementaryWeightIndex 7) = 14 := by
  change Nat.card (ElementaryWeightIndex (7 : Fin 8).1) = 14
  rw [Nat.card_congr
      (elementaryWeightIndexEquivBounded (7 : Fin 8)),
    Nat.card_eq_fintype_card]
  decide

theorem elementaryWeightIndex_card (d : Fin 8) :
    Nat.card (ElementaryWeightIndex d.1) =
      ![1, 1, 2, 3, 5, 7, 11, 14] d := by
  fin_cases d
  · exact elementaryWeightIndex_card_closed_zero
  · exact elementaryWeightIndex_card_closed_one
  · exact elementaryWeightIndex_card_closed_two
  · exact elementaryWeightIndex_card_closed_three
  · exact elementaryWeightIndex_card_closed_four
  · exact elementaryWeightIndex_card_closed_five
  · exact elementaryWeightIndex_card_closed_six
  · exact elementaryWeightIndex_card_closed_seven

@[simp]
theorem elementaryWeightIndex_card_zero :
    Nat.card (ElementaryWeightIndex 0) = 1 := by
  simpa using elementaryWeightIndex_card (0 : Fin 8)

@[simp]
theorem elementaryWeightIndex_fintype_card_zero :
    Fintype.card (ElementaryWeightIndex 0) = 1 := by
  simpa [Nat.card_eq_fintype_card] using elementaryWeightIndex_card_zero

@[simp]
theorem elementaryWeightIndex_card_one :
    Nat.card (ElementaryWeightIndex 1) = 1 := by
  simpa using elementaryWeightIndex_card (1 : Fin 8)

@[simp]
theorem elementaryWeightIndex_fintype_card_one :
    Fintype.card (ElementaryWeightIndex 1) = 1 := by
  simpa [Nat.card_eq_fintype_card] using elementaryWeightIndex_card_one

@[simp]
theorem elementaryWeightIndex_card_two :
    Nat.card (ElementaryWeightIndex 2) = 2 := by
  simpa using elementaryWeightIndex_card (2 : Fin 8)

@[simp]
theorem elementaryWeightIndex_fintype_card_two :
    Fintype.card (ElementaryWeightIndex 2) = 2 := by
  simpa [Nat.card_eq_fintype_card] using elementaryWeightIndex_card_two

@[simp]
theorem elementaryWeightIndex_card_three :
    Nat.card (ElementaryWeightIndex 3) = 3 := by
  simpa using elementaryWeightIndex_card (3 : Fin 8)

@[simp]
theorem elementaryWeightIndex_fintype_card_three :
    Fintype.card (ElementaryWeightIndex 3) = 3 := by
  simpa [Nat.card_eq_fintype_card] using elementaryWeightIndex_card_three

@[simp]
theorem elementaryWeightIndex_card_four :
    Nat.card (ElementaryWeightIndex 4) = 5 := by
  simpa using elementaryWeightIndex_card (4 : Fin 8)

@[simp]
theorem elementaryWeightIndex_fintype_card_four :
    Fintype.card (ElementaryWeightIndex 4) = 5 := by
  simpa [Nat.card_eq_fintype_card] using elementaryWeightIndex_card_four

@[simp]
theorem elementaryWeightIndex_card_five :
    Nat.card (ElementaryWeightIndex 5) = 7 := by
  simpa using elementaryWeightIndex_card (5 : Fin 8)

@[simp]
theorem elementaryWeightIndex_fintype_card_five :
    Fintype.card (ElementaryWeightIndex 5) = 7 := by
  simpa [Nat.card_eq_fintype_card] using elementaryWeightIndex_card_five

@[simp]
theorem elementaryWeightIndex_card_six :
    Nat.card (ElementaryWeightIndex 6) = 11 := by
  simpa using elementaryWeightIndex_card (6 : Fin 8)

@[simp]
theorem elementaryWeightIndex_fintype_card_six :
    Fintype.card (ElementaryWeightIndex 6) = 11 := by
  simpa [Nat.card_eq_fintype_card] using elementaryWeightIndex_card_six

@[simp]
theorem elementaryWeightIndex_card_seven :
    Nat.card (ElementaryWeightIndex 7) = 14 := by
  simpa using elementaryWeightIndex_card (7 : Fin 8)

@[simp]
theorem elementaryWeightIndex_fintype_card_seven :
    Fintype.card (ElementaryWeightIndex 7) = 14 := by
  simpa [Nat.card_eq_fintype_card] using elementaryWeightIndex_card_seven

/-- Split a fixed total-degree tower index into its hypothetical basis index
and elementary-symmetric exponent. -/
noncomputable def degreeIndexEquivSigma (d : ℕ) :
    FieldInvariantDegreeIndex B d ≃
      Σ i : B.Index,
        {a : Fin 6 →₀ ℕ //
          Finsupp.weight elementaryVariableWeight a + B.degree i = d} where
  toFun j := ⟨j.1.2, ⟨j.1.1, j.2⟩⟩
  invFun j := ⟨(j.2.1, j.1), j.2.2⟩
  left_inv j := rfl
  right_inv j := rfl

private theorem shiftedWeightCard (d : ℕ) (i : B.Index) :
    Nat.card {a : Fin 6 →₀ ℕ //
        Finsupp.weight elementaryVariableWeight a + B.degree i = d} =
      if B.degree i ≤ d then
        Nat.card (ElementaryWeightIndex (d - B.degree i))
      else 0 := by
  by_cases hi : B.degree i ≤ d
  · rw [if_pos hi]
    apply Nat.card_congr
    apply Equiv.setCongr
    ext a
    change (Finsupp.weight elementaryVariableWeight a + B.degree i = d) ↔
      Finsupp.weight elementaryVariableWeight a = d - B.degree i
    omega
  · rw [if_neg hi]
    haveI : IsEmpty {a : Fin 6 →₀ ℕ //
        Finsupp.weight elementaryVariableWeight a + B.degree i = d} :=
      ⟨fun a => (hi (by omega)).elim⟩
    exact Nat.card_of_isEmpty

/-- First form of the bounded Hilbert convolution, summed over hypothetical
basis vectors. -/
theorem fieldInvariantDegreeIndex_card_eq_sum (d : ℕ) :
    Nat.card (FieldInvariantDegreeIndex B d) =
      ∑ i : B.Index,
        if B.degree i ≤ d then
          Nat.card (ElementaryWeightIndex (d - B.degree i))
        else 0 := by
  letI (i : B.Index) :
      Finite {a : Fin 6 →₀ ℕ //
        Finsupp.weight elementaryVariableWeight a + B.degree i = d} :=
    ((Finsupp.finite_of_nat_weight_le elementaryVariableWeight
      elementaryVariableWeight_ne_zero d).subset (by
        intro a ha
        change Finsupp.weight elementaryVariableWeight a ≤ d
        change Finsupp.weight elementaryVariableWeight a + B.degree i = d at ha
        omega)).to_subtype
  rw [Nat.card_congr (degreeIndexEquivSigma B d), Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  exact shiftedWeightCard B d i

/-- The advertised degree bound `15` packaged as a finite degree label. -/
def hypotheticalBasisDegreeFin (i : B.Index) : Fin 16 :=
  ⟨B.degree i, by
    have h := B.degree_le i
    norm_num [lazardDegreeBound] at h ⊢
    omega⟩

/-- Number of hypothetical homogeneous basis vectors in degree `d`. -/
def hypotheticalBasisDegreeCount (d : ℕ) : ℕ :=
  Nat.card {i : B.Index // B.degree i = d}

/-- Regroup a finite sum over the hypothetical basis by its degree. -/
theorem sum_by_hypotheticalBasisDegree (f : ℕ → ℕ) :
    (∑ i : B.Index, f (B.degree i)) =
      ∑ e : Fin 16, hypotheticalBasisDegreeCount B e.1 * f e.1 := by
  classical
  rw [← Fintype.sum_fiberwise (hypotheticalBasisDegreeFin B)
    (fun i : B.Index => f (B.degree i))]
  apply Finset.sum_congr rfl
  intro e he
  have hdegree (i : {i : B.Index // hypotheticalBasisDegreeFin B i = e}) :
      B.degree i.1 = e.1 :=
    congrArg Fin.val i.2
  simp_rw [hdegree]
  rw [Finset.sum_const, nsmul_eq_mul]
  congr 1
  rw [hypotheticalBasisDegreeCount, Nat.card_eq_fintype_card]
  apply Fintype.card_congr
  apply Equiv.setCongr
  ext i
  change hypotheticalBasisDegreeFin B i = e ↔ B.degree i = e.1
  exact Fin.ext_iff

/-- Degree-fiber form of the bounded Hilbert convolution. -/
theorem fieldInvariantDegreeIndex_card_convolution (d : ℕ) :
    Nat.card (FieldInvariantDegreeIndex B d) =
      ∑ e : Fin 16,
        hypotheticalBasisDegreeCount B e.1 *
          (if e.1 ≤ d then
            Nat.card (ElementaryWeightIndex (d - e.1)) else 0) := by
  rw [fieldInvariantDegreeIndex_card_eq_sum B d]
  exact sum_by_hypotheticalBasisDegree B
    (fun e => if e ≤ d then
      Nat.card (ElementaryWeightIndex (d - e)) else 0)

/-- Semantic bounded Hilbert recurrence: the explicit orbit count equals the
convolution forced by every hypothetical homogeneous free basis. -/
theorem invariantOrbitCount_eq_hypotheticalBasis_convolution (d : Fin 8) :
    invariantOrbitCount d.1 =
      ∑ e : Fin 16,
        hypotheticalBasisDegreeCount B e.1 *
          (if e.1 ≤ d.1 then
            Nat.card (ElementaryWeightIndex (d.1 - e.1)) else 0) := by
  rw [← fieldInvariantDegreeIndex_card_eq_orbitCount B d,
    fieldInvariantDegreeIndex_card_convolution B]

/-! ### The eight forced basis-degree counts -/

@[simp]
theorem hypotheticalBasisDegreeCount_zero :
    hypotheticalBasisDegreeCount B 0 = 1 := by
  have h := invariantOrbitCount_eq_hypotheticalBasis_convolution B (0 : Fin 8)
  norm_num [Fin.sum_univ_succ] at h
  omega

@[simp]
theorem hypotheticalBasisDegreeCount_one :
    hypotheticalBasisDegreeCount B 1 = 0 := by
  have h := invariantOrbitCount_eq_hypotheticalBasis_convolution B (1 : Fin 8)
  norm_num [Fin.sum_univ_succ,
    hypotheticalBasisDegreeCount_zero B] at h
  omega

@[simp]
theorem hypotheticalBasisDegreeCount_two :
    hypotheticalBasisDegreeCount B 2 = 2 := by
  have h := invariantOrbitCount_eq_hypotheticalBasis_convolution B (2 : Fin 8)
  norm_num [Fin.sum_univ_succ,
    hypotheticalBasisDegreeCount_zero B,
    hypotheticalBasisDegreeCount_one B] at h
  omega

@[simp]
theorem hypotheticalBasisDegreeCount_three :
    hypotheticalBasisDegreeCount B 3 = 5 := by
  have h := invariantOrbitCount_eq_hypotheticalBasis_convolution B (3 : Fin 8)
  norm_num [Fin.sum_univ_succ,
    hypotheticalBasisDegreeCount_zero B,
    hypotheticalBasisDegreeCount_one B,
    hypotheticalBasisDegreeCount_two B] at h
  omega

@[simp]
theorem hypotheticalBasisDegreeCount_four :
    hypotheticalBasisDegreeCount B 4 = 8 := by
  have h := invariantOrbitCount_eq_hypotheticalBasis_convolution B (4 : Fin 8)
  norm_num [Fin.sum_univ_succ,
    hypotheticalBasisDegreeCount_zero B,
    hypotheticalBasisDegreeCount_one B,
    hypotheticalBasisDegreeCount_two B,
    hypotheticalBasisDegreeCount_three B] at h
  omega

@[simp]
theorem hypotheticalBasisDegreeCount_five :
    hypotheticalBasisDegreeCount B 5 = 11 := by
  have h := invariantOrbitCount_eq_hypotheticalBasis_convolution B (5 : Fin 8)
  norm_num [Fin.sum_univ_succ,
    hypotheticalBasisDegreeCount_zero B,
    hypotheticalBasisDegreeCount_one B,
    hypotheticalBasisDegreeCount_two B,
    hypotheticalBasisDegreeCount_three B,
    hypotheticalBasisDegreeCount_four B] at h
  omega

@[simp]
theorem hypotheticalBasisDegreeCount_six :
    hypotheticalBasisDegreeCount B 6 = 17 := by
  have h := invariantOrbitCount_eq_hypotheticalBasis_convolution B (6 : Fin 8)
  norm_num [Fin.sum_univ_succ,
    hypotheticalBasisDegreeCount_zero B,
    hypotheticalBasisDegreeCount_one B,
    hypotheticalBasisDegreeCount_two B,
    hypotheticalBasisDegreeCount_three B,
    hypotheticalBasisDegreeCount_four B,
    hypotheticalBasisDegreeCount_five B] at h
  omega

/-- The degree-seven coefficient forced by homogeneous freeness is exactly
sixteen. -/
@[simp]
theorem hypotheticalBasisDegreeCount_seven :
    hypotheticalBasisDegreeCount B 7 = 16 := by
  have h := invariantOrbitCount_eq_hypotheticalBasis_convolution B (7 : Fin 8)
  norm_num [Fin.sum_univ_succ,
    hypotheticalBasisDegreeCount_zero B,
    hypotheticalBasisDegreeCount_one B,
    hypotheticalBasisDegreeCount_two B,
    hypotheticalBasisDegreeCount_three B,
    hypotheticalBasisDegreeCount_four B,
    hypotheticalBasisDegreeCount_five B,
    hypotheticalBasisDegreeCount_six B,
    cyclicSix_degreeSeven_orbit_count] at h
  omega

end HypotheticalBasis

end

end LeanProofs.PolynomialFormulas.LazardInvariantModularHomogeneousBasisObstruction
