import PolynomialFormulas.LazardQuinticF20Molien
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.RepresentationTheory.Character
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic

/-!
# Coefficientwise Molien formula for permutation invariants

This file supplies the representation-theoretic bridge which is absent from
`LazardQuinticF20Molien`.  For every degree `d`, the homogeneous polynomials of
degree `d` have their literal monomial basis, indexed by exponent vectors of
total degree `d`.  A permutation of the variables permutes that basis.
Consequently its trace is the number of exponent vectors which it fixes.
Character averaging then identifies the average of these fixed-monomial
counts with the dimension of the homogeneous invariant subspace.

Thus `coefficientwise_molien` is an honest coefficientwise Molien theorem for
finite permutation groups.  No Hilbert-series or rational-function identity
is assumed by it.

The last part packages the resulting Hilbert series as a formal power series
and identifies the four fixed-exponent series belonging to the `F₂₀` cycle
types with

`(1-X)^{-5}`, `(1-X^5)^{-1}`,
`((1-X)(1-X^2)^2)^{-1}`, and
`((1-X)(1-X^4))^{-1}`.

It then combines this honest Hilbert-series class sum with the independently
checked rational-function simplification in `LazardQuinticF20Molien`.
-/

namespace LeanProofs.PolynomialFormulas.LazardInvariantMolienCoefficients

open Equiv MvPolynomial
open LeanProofs.PolynomialFormulas.Fin5TransitiveC5
open LeanProofs.PolynomialFormulas.Fin5Solvable

set_option autoImplicit false

noncomputable section

/-- Exponent vectors indexing the monomials of total degree `d`. -/
abbrev DegreeExponent (σ : Type*) (d : ℕ) :=
  {a : σ →₀ ℕ // a.degree = d}

noncomputable instance degreeExponentFintype
    (σ : Type*) [Finite σ] (d : ℕ) : Fintype (DegreeExponent σ d) :=
  (Finsupp.finite_of_degree_eq d).fintype

/-- The literal monomial basis of the degree-`d` homogeneous piece. -/
def homogeneousMonomialBasis
    (k σ : Type*) [Field k] [Finite σ] (d : ℕ) :
    Module.Basis (DegreeExponent σ d) k
      (MvPolynomial.homogeneousSubmodule σ k d) := by
  let b := MvPolynomial.basisRestrictSupport k
    {a : σ →₀ ℕ | a.degree = d}
  exact b.map (LinearEquiv.ofEq _ _
    (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported σ k d).symm)

@[simp]
theorem homogeneousMonomialBasis_apply
    (k σ : Type*) [Field k] [Finite σ] (d : ℕ)
    (a : DegreeExponent σ d) :
    (homogeneousMonomialBasis k σ d a).1 =
      MvPolynomial.monomial a.1 1 := by
  change ((LinearEquiv.ofEq _ _
    (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported σ k d).symm)
      ((MvPolynomial.basisRestrictSupport k
        {a : σ →₀ ℕ | a.degree = d}) a)).1 = _
  rw [LinearEquiv.coe_ofEq_apply]
  change AddMonoidAlgebra.ofCoeff
    ((((Finsupp.supportedEquivFinsupp (R := k)
      {a : σ →₀ ℕ | a.degree = d}).symm
      (Finsupp.single a 1)) :
        Finsupp.supported k k {a : σ →₀ ℕ | a.degree = d}).1) = _
  rw [Finsupp.supportedEquivFinsupp_symm_single,
    AddMonoidAlgebra.ofCoeff_single]
  rfl

@[simp]
theorem homogeneousMonomialBasis_repr_apply
    (k σ : Type*) [Field k] [Finite σ] (d : ℕ)
    (p : MvPolynomial.homogeneousSubmodule σ k d)
    (a : DegreeExponent σ d) :
    (homogeneousMonomialBasis k σ d).repr p a =
      MvPolynomial.coeff a.1 p.1 := by
  rfl

noncomputable instance homogeneousSubmoduleFinite
    (k σ : Type*) [Field k] [Finite σ] (d : ℕ) :
    Module.Finite k (MvPolynomial.homogeneousSubmodule σ k d) :=
  Module.Finite.of_basis (homogeneousMonomialBasis k σ d)

/-- A variable permutation acts on degree-`d` exponent vectors by renaming
their coordinates. -/
def exponentPerm {σ : Type*} (g : Equiv.Perm σ) (d : ℕ) :
    Equiv.Perm (DegreeExponent σ d) where
  toFun a := ⟨a.1.mapDomain g,
    (Finsupp.degree_mapDomain g a.1).trans a.2⟩
  invFun a :=
    ⟨a.1.mapDomain g.symm,
      (Finsupp.degree_mapDomain g.symm a.1).trans a.2⟩
  left_inv a := by
    apply Subtype.ext
    change (a.1.mapDomain g).mapDomain g.symm = a.1
    rw [← Finsupp.mapDomain_comp, g.symm_comp_self, Finsupp.mapDomain_id]
  right_inv a := by
    apply Subtype.ext
    change (a.1.mapDomain g.symm).mapDomain g = a.1
    rw [← Finsupp.mapDomain_comp, g.self_comp_symm, Finsupp.mapDomain_id]

@[simp]
theorem exponentPerm_apply_val {σ : Type*} (g : Equiv.Perm σ) (d : ℕ)
    (a : DegreeExponent σ d) :
    (exponentPerm g d a).1 = a.1.mapDomain g :=
  rfl

@[simp]
theorem exponentPerm_one {σ : Type*} (d : ℕ) :
    exponentPerm (1 : Equiv.Perm σ) d = 1 := by
  apply Equiv.ext
  intro a
  apply Subtype.ext
  simp [exponentPerm]

@[simp]
theorem exponentPerm_mul {σ : Type*} (g h : Equiv.Perm σ) (d : ℕ) :
    exponentPerm (g * h) d = exponentPerm g d * exponentPerm h d := by
  apply Equiv.ext
  intro a
  apply Subtype.ext
  simp [exponentPerm, ← Finsupp.mapDomain_comp]

/-- Coordinate form of the assertion that an exponent vector is fixed by a
variable permutation. -/
theorem exponentPerm_eq_self_iff {σ : Type*}
    (g : Equiv.Perm σ) (d : ℕ) (a : DegreeExponent σ d) :
    exponentPerm g d a = a ↔
      ∀ i, a.1 (g.symm i) = a.1 i := by
  constructor
  · intro h i
    have hval := congrArg Subtype.val h
    simpa only [exponentPerm_apply_val,
      Finsupp.mapDomain_equiv_apply] using
        congrArg (fun z : σ →₀ ℕ ↦ z i) hval
  · intro h
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    simpa only [exponentPerm_apply_val,
      Finsupp.mapDomain_equiv_apply] using h i

/-- The number of degree-`d` monomials fixed by a variable permutation. -/
def fixedExponentCount {σ : Type*} [Finite σ]
    (g : Equiv.Perm σ) (d : ℕ) : ℕ :=
  (Function.fixedPoints (exponentPerm g d)).ncard

/-- Renaming, restricted to one finite homogeneous piece. -/
def homogeneousRenameLinear
    (k σ : Type*) [Field k] [Finite σ]
    (g : Equiv.Perm σ) (d : ℕ) :
    MvPolynomial.homogeneousSubmodule σ k d →ₗ[k]
      MvPolynomial.homogeneousSubmodule σ k d where
  toFun p := ⟨MvPolynomial.rename g p.1, p.2.rename_isHomogeneous⟩
  map_add' p q := by
    apply Subtype.ext
    exact map_add (MvPolynomial.rename g) p.1 q.1
  map_smul' r p := by
    apply Subtype.ext
    simp

@[simp]
theorem homogeneousRenameLinear_apply
    (k σ : Type*) [Field k] [Finite σ]
    (g : Equiv.Perm σ) (d : ℕ)
    (p : MvPolynomial.homogeneousSubmodule σ k d) :
    (homogeneousRenameLinear k σ g d p).1 = MvPolynomial.rename g p.1 :=
  rfl

/-- The action of the whole permutation group on a homogeneous piece. -/
def homogeneousPermutationRepresentation
    (k σ : Type*) [Field k] [Finite σ] (d : ℕ) :
    Representation k (Equiv.Perm σ)
      (MvPolynomial.homogeneousSubmodule σ k d) where
  toFun g := homogeneousRenameLinear k σ g d
  map_one' := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    simp [homogeneousRenameLinear]
  map_mul' g h := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    simp [homogeneousRenameLinear, MvPolynomial.rename_rename]

/-- The action of a permutation subgroup on a homogeneous piece. -/
def homogeneousSubgroupRepresentation
    (k σ : Type*) [Field k] [Finite σ]
    (H : Subgroup (Equiv.Perm σ)) (d : ℕ) :
    Representation k H (MvPolynomial.homogeneousSubmodule σ k d) where
  toFun g := homogeneousRenameLinear k σ g.1 d
  map_one' := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    simp [homogeneousRenameLinear]
  map_mul' g h := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    simp [homogeneousRenameLinear, MvPolynomial.rename_rename]

@[simp]
theorem mem_homogeneousSubgroupRepresentation_invariants
    (k σ : Type*) [Field k] [Finite σ]
    (H : Subgroup (Equiv.Perm σ)) (d : ℕ)
    (p : MvPolynomial.homogeneousSubmodule σ k d) :
    p ∈ (homogeneousSubgroupRepresentation k σ H d).invariants ↔
      ∀ h : H, MvPolynomial.rename h.1 p.1 = p.1 :=
  by
    rw [Representation.mem_invariants]
    constructor
    · intro hp h
      exact congrArg Subtype.val (hp h)
    · intro hp h
      apply Subtype.ext
      exact hp h

/-- In the monomial basis, homogeneous renaming is the transpose of the
permutation matrix on exponent vectors. -/
theorem homogeneousRenameLinear_toMatrix
    (k σ : Type*) [Field k] [Fintype σ] [DecidableEq σ]
    (g : Equiv.Perm σ) (d : ℕ) :
    LinearMap.toMatrix (homogeneousMonomialBasis k σ d)
        (homogeneousMonomialBasis k σ d)
        (homogeneousRenameLinear k σ g d) =
      ((exponentPerm g d).permMatrix k).transpose := by
  classical
  ext i j
  simp [LinearMap.toMatrix_apply, MvPolynomial.rename_monomial,
    Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Subtype.ext_iff, eq_comm]

/-- The character on the degree-`d` piece is exactly the number of fixed
degree-`d` monomials. -/
theorem homogeneousRenameLinear_trace
    (k σ : Type*) [Field k] [Fintype σ] [DecidableEq σ]
    (g : Equiv.Perm σ) (d : ℕ) :
    LinearMap.trace k (MvPolynomial.homogeneousSubmodule σ k d)
        (homogeneousRenameLinear k σ g d) =
      (fixedExponentCount g d : k) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace k
    (homogeneousMonomialBasis k σ d),
    homogeneousRenameLinear_toMatrix, Matrix.trace_transpose,
    Matrix.trace_permutation]
  rfl

@[simp]
theorem homogeneousPermutationCharacter_apply
    (k σ : Type*) [Field k] [Fintype σ] [DecidableEq σ]
    (g : Equiv.Perm σ) (d : ℕ) :
    (homogeneousPermutationRepresentation k σ d).character g =
      (fixedExponentCount g d : k) :=
  homogeneousRenameLinear_trace k σ g d

@[simp]
theorem homogeneousSubgroupCharacter_apply
    (k σ : Type*) [Field k] [Fintype σ] [DecidableEq σ]
    (H : Subgroup (Equiv.Perm σ)) (g : H) (d : ℕ) :
    (homogeneousSubgroupRepresentation k σ H d).character g =
      (fixedExponentCount g.1 d : k) :=
  homogeneousRenameLinear_trace k σ g.1 d

/-- Fixed-monomial counts depend only on cycle type.  This is obtained from
the character's conjugacy invariance, rather than supplied as a separate
cycle-index certificate. -/
theorem fixedExponentCount_eq_of_cycleType_eq
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    {g h : Equiv.Perm σ} (d : ℕ)
    (hcycle : g.cycleType = h.cycleType) :
    fixedExponentCount g d = fixedExponentCount h d := by
  classical
  obtain ⟨c, hc⟩ := isConj_iff.mp
    (Equiv.Perm.isConj_iff_cycleType_eq.mpr hcycle)
  have hchar := Representation.char_conj
    (homogeneousPermutationRepresentation ℚ σ d) g c
  rw [hc, homogeneousPermutationCharacter_apply,
    homogeneousPermutationCharacter_apply] at hchar
  exact_mod_cast hchar.symm

/-- Coefficientwise Molien theorem for a finite permutation group.  The
right-hand side is the dimension of the literal invariant subspace in degree
`d`; the left-hand side is the average trace, rewritten as fixed-monomial
counts. -/
theorem coefficientwise_molien
    (k σ : Type*) [Field k] [Fintype σ] [DecidableEq σ]
    (H : Subgroup (Equiv.Perm σ)) [Fintype H]
    [Invertible (Nat.card H : k)] (d : ℕ) :
    (Nat.card H : k)⁻¹ *
        ∑ g : H, (fixedExponentCount g.1 d : k) =
      Module.finrank k
        (homogeneousSubgroupRepresentation k σ H d).invariants := by
  simpa only [homogeneousSubgroupCharacter_apply] using
    Representation.card_inv_mul_sum_char_eq_finrank
      (homogeneousSubgroupRepresentation k σ H d)

/-- The Hilbert series whose coefficient in degree `d` is the dimension of
the invariant homogeneous piece. -/
def homogeneousInvariantHilbertSeries
    (σ : Type*) [Fintype σ]
    (H : Subgroup (Equiv.Perm σ)) [Fintype H] : PowerSeries ℚ :=
  PowerSeries.mk fun d ↦
    Module.finrank ℚ
      (homogeneousSubgroupRepresentation ℚ σ H d).invariants

/-- The fixed-monomial generating series of one permutation. -/
def fixedExponentSeries
    {σ : Type*} [Fintype σ] (g : Equiv.Perm σ) : PowerSeries ℚ :=
  PowerSeries.mk fun d ↦ (fixedExponentCount g d : ℚ)

/-! ## Weighted degree series -/

/-- Assignments of nonnegative integers whose weighted total is `d`.  These
are the parameters attached to the cycles of a fixed permutation: one
parameter per cycle, with the cycle length as its weight. -/
abbrev WeightedDegree (ι : Type*) [Fintype ι]
    (w : ι → ℕ) (d : ℕ) :=
  {q : ι → ℕ // ∑ i, w i * q i = d}

/-- The formal series which counts weighted nonnegative assignments. -/
def weightedDegreeSeries (ι : Type*) [Fintype ι]
    (w : ι → ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun d ↦ (Nat.card (WeightedDegree ι w d) : ℚ)

/-- `1 + X^m + X^(2m) + ...`, constructed by substituting `X^m` into the
ordinary geometric series. -/
def geometricStepSeries (m : ℕ) : PowerSeries ℚ :=
  PowerSeries.subst (PowerSeries.X ^ m : PowerSeries ℚ)
    (PowerSeries.mk (1 : ℕ → ℚ))

@[simp]
theorem coeff_geometricStepSeries (m : ℕ) (hm : m ≠ 0) (d : ℕ) :
    PowerSeries.coeff d (geometricStepSeries m) =
      if m ∣ d then 1 else 0 := by
  simp [geometricStepSeries, PowerSeries.coeff_subst_X_pow hm]

/-- The step-`m` geometric series is an actual inverse of `1 - X^m`. -/
theorem geometricStepSeries_mul_one_sub_X_pow
    (m : ℕ) (hm : m ≠ 0) :
    geometricStepSeries m * (1 - PowerSeries.X ^ m) = 1 := by
  let a : PowerSeries ℚ := PowerSeries.X ^ m
  have ha : PowerSeries.HasSubst a := PowerSeries.HasSubst.X_pow hm
  have hone : PowerSeries.subst a (1 : PowerSeries ℚ) = 1 := by
    rw [← congrFun (PowerSeries.coe_substAlgHom ha) 1]
    exact map_one _
  have hX : PowerSeries.subst a (PowerSeries.X : PowerSeries ℚ) = a :=
    PowerSeries.subst_X ha
  change PowerSeries.subst a (PowerSeries.mk (1 : ℕ → ℚ)) * (1 - a) = 1
  calc
    _ = PowerSeries.subst a (PowerSeries.mk (1 : ℕ → ℚ)) *
        (PowerSeries.subst a (1 : PowerSeries ℚ) -
          PowerSeries.subst a PowerSeries.X) := by rw [hone, hX]
    _ = PowerSeries.subst a (PowerSeries.mk (1 : ℕ → ℚ)) *
        PowerSeries.subst a ((1 : PowerSeries ℚ) - PowerSeries.X) := by
      congr 1
      exact (PowerSeries.subst_sub ha (1 : PowerSeries ℚ) PowerSeries.X).symm
    _ = PowerSeries.subst a
        (PowerSeries.mk (1 : ℕ → ℚ) *
          ((1 : PowerSeries ℚ) - PowerSeries.X)) :=
      (PowerSeries.subst_mul ha _ _).symm
    _ = PowerSeries.subst a (1 : PowerSeries ℚ) :=
      congrArg (PowerSeries.subst a)
        (PowerSeries.mk_one_mul_one_sub_eq_one ℚ)
    _ = 1 := hone

/-- Multiplying every coordinate by its weight identifies weighted
assignments with the divisible points of the ordinary antidiagonal. -/
noncomputable def weightedDegreeEquivDivisibleAntidiagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℕ)
    (hw : ∀ i, w i ≠ 0) (d : ℕ) :
    WeightedDegree ι w d ≃
      {l : ι →₀ ℕ //
        l ∈ (Finset.finsuppAntidiag Finset.univ d).filter
          (fun l ↦ ∀ i, w i ∣ l i)} := by
  classical
  refine
    { toFun := fun q ↦ ?_
      invFun := fun l ↦ ?_
      left_inv := fun q ↦ ?_
      right_inv := fun l ↦ ?_ }
  ·
    let l : ι →₀ ℕ :=
      Finsupp.equivFunOnFinite.symm (fun i ↦ w i * q.1 i)
    refine ⟨l, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · rw [Finset.mem_finsuppAntidiag]
      refine ⟨?_, by simp⟩
      simpa [l] using q.2
    · intro i
      change w i ∣ w i * q.1 i
      exact dvd_mul_right _ _
  ·
    refine ⟨fun i ↦ l.1 i / w i, ?_⟩
    have hmem := Finset.mem_filter.mp l.2
    have hsum := (Finset.mem_finsuppAntidiag.mp hmem.1).1
    calc
      ∑ i, w i * (l.1 i / w i) = ∑ i, l.1 i := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact Nat.mul_div_cancel' (hmem.2 i)
      _ = d := hsum
  ·
    apply Subtype.ext
    funext i
    change (w i * q.1 i) / w i = q.1 i
    simpa [mul_comm] using
      Nat.mul_div_cancel_left (q.1 i) (Nat.pos_of_ne_zero (hw i))
  ·
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    change w i * (l.1 i / w i) = l.1 i
    exact Nat.mul_div_cancel' ((Finset.mem_filter.mp l.2).2 i)

/-- The generating function of weighted nonnegative assignments is the
product of its one-coordinate geometric series. -/
theorem weightedDegreeSeries_eq_prod_geometricStep
    {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℕ)
    (hw : ∀ i, w i ≠ 0) :
    weightedDegreeSeries ι w =
      ∏ i, geometricStepSeries (w i) := by
  classical
  ext d
  rw [weightedDegreeSeries, PowerSeries.coeff_mk,
    PowerSeries.coeff_prod]
  have hprod (l : ι →₀ ℕ) :
      (∏ i ∈ Finset.univ,
          PowerSeries.coeff (l i) (geometricStepSeries (w i))) =
        (if ∀ i, w i ∣ l i then 1 else 0 : ℚ) := by
    by_cases hdiv : ∀ i, w i ∣ l i
    · simp [coeff_geometricStepSeries, hw, hdiv]
    · obtain ⟨i, hi⟩ := not_forall.mp hdiv
      rw [Finset.prod_eq_zero (Finset.mem_univ i)]
      · simp [hdiv]
      · rw [coeff_geometricStepSeries (w i) (hw i) (l i)]
        simp [hi]
  simp_rw [hprod]
  rw [Finset.sum_boole]
  haveI : Fintype (WeightedDegree ι w d) :=
    Fintype.ofEquiv _
      (weightedDegreeEquivDivisibleAntidiagonal w hw d).symm
  norm_cast
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
    (Nat.card_congr
      (weightedDegreeEquivDivisibleAntidiagonal w hw d))

/-- A degreewise equivalence between fixed exponents and weighted
assignments promotes directly to an equality of their counting series. -/
theorem fixedExponentSeries_eq_weightedDegreeSeries_of_equiv
    {σ ι : Type*} [Fintype σ] [Fintype ι]
    (g : Equiv.Perm σ) (w : ι → ℕ)
    (e : ∀ d, Function.fixedPoints (exponentPerm g d) ≃
      WeightedDegree ι w d) :
    fixedExponentSeries g = weightedDegreeSeries ι w := by
  ext d
  rw [fixedExponentSeries, weightedDegreeSeries,
    PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  norm_cast
  change Nat.card (Function.fixedPoints (exponentPerm g d)) =
    Nat.card (WeightedDegree ι w d)
  exact Nat.card_congr (e d)

/-- The cycle-index average of the fixed-monomial series. -/
def averagedFixedExponentSeries
    (σ : Type*) [Fintype σ]
    (H : Subgroup (Equiv.Perm σ)) [Fintype H] : PowerSeries ℚ :=
  PowerSeries.C (Nat.card H : ℚ)⁻¹ *
    ∑ g : H, fixedExponentSeries g.1

/-- Formal-series version of the coefficientwise Molien theorem. -/
theorem homogeneousInvariantHilbertSeries_eq_average
    (σ : Type*) [Fintype σ] [DecidableEq σ]
    (H : Subgroup (Equiv.Perm σ)) [Fintype H] :
    homogeneousInvariantHilbertSeries σ H =
      averagedFixedExponentSeries σ H := by
  letI : Invertible (Nat.card H : ℚ) :=
    invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  ext d
  rw [homogeneousInvariantHilbertSeries, PowerSeries.coeff_mk,
    averagedFixedExponentSeries, PowerSeries.coeff_C_mul]
  simp only [map_sum, PowerSeries.coeff_mk, fixedExponentSeries]
  exact (coefficientwise_molien ℚ σ H d).symm

local instance standardF20Fintype : Fintype standardF20 :=
  Fintype.ofFinite standardF20

/-- The `F₂₀` invariant Hilbert series, before simplifying its four
cycle-type contributions. -/
abbrev f20InvariantHilbertSeries : PowerSeries ℚ :=
  homogeneousInvariantHilbertSeries (Fin 5) standardF20

/-- A coefficient of the `F₂₀` Hilbert series is the literal average of
the twenty fixed-monomial counts. -/
theorem f20_hilbert_coefficient_eq_average (d : ℕ) :
    PowerSeries.coeff d f20InvariantHilbertSeries =
      (20 : ℚ)⁻¹ *
        ∑ g : standardF20, (fixedExponentCount g.1 d : ℚ) := by
  letI : Invertible (Nat.card standardF20 : ℚ) :=
    invertibleOfNonzero (by
      rw [natCard_standardF20]
      norm_num)
  change PowerSeries.coeff d
      (homogeneousInvariantHilbertSeries (Fin 5) standardF20) = _
  rw [homogeneousInvariantHilbertSeries, PowerSeries.coeff_mk,
    ← coefficientwise_molien ℚ (Fin 5) standardF20 d,
    natCard_standardF20]
  norm_num

/-! ## The four `F₂₀` cycle classes -/

abbrev S5 := Equiv.Perm (Fin 5)

/-- A convenient representative of cycle type `1 2²`. -/
def twoTwoRepresentative : S5 :=
  Equiv.swap 0 1 * Equiv.swap 2 3

/-- A convenient representative of cycle type `1 4`. -/
def oneFourRepresentative : S5 :=
  Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3

@[simp]
theorem cycleType_one : (1 : S5).cycleType = 0 := by
  simp

@[simp]
theorem cycleType_fiveCycle : fiveCycle.cycleType = {5} := by
  change (finRotate 5).cycleType = {5}
  exact cycleType_finRotate_of_le (by omega)

set_option maxRecDepth 100000 in
@[simp]
theorem cycleType_twoTwoRepresentative :
    twoTwoRepresentative.cycleType = {2, 2} := by
  decide

set_option maxRecDepth 100000 in
@[simp]
theorem cycleType_oneFourRepresentative :
    oneFourRepresentative.cycleType = {4} := by
  decide

/-! ## Fixed exponents of the four representatives -/

/-- Cycle lengths, one per independent exponent parameter, for the identity
class. -/
def identityWeights : Fin 5 → ℕ := fun _ ↦ 1

/-- The unique cycle length of a five-cycle. -/
def fiveCycleWeights : Fin 1 → ℕ := fun _ ↦ 5

/-- Cycle lengths `2, 2, 1` for the double-transposition class. -/
def twoTwoWeights : Fin 3 → ℕ := ![2, 2, 1]

/-- Cycle lengths `4, 1` for the four-cycle class. -/
def oneFourWeights : Fin 2 → ℕ := ![4, 1]

private theorem sum_fin_five (f : Fin 5 → ℕ) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 := by
  simp [Fin.sum_univ_succ, add_assoc]

set_option maxRecDepth 100000 in
private theorem fiveCycle_symm_table :
    fiveCycle.symm 0 = 4 ∧
      fiveCycle.symm 1 = 0 ∧
      fiveCycle.symm 2 = 1 ∧
      fiveCycle.symm 3 = 2 ∧
      fiveCycle.symm 4 = 3 := by
  decide

set_option maxRecDepth 100000 in
private theorem twoTwoRepresentative_symm_table :
    twoTwoRepresentative.symm 0 = 1 ∧
      twoTwoRepresentative.symm 1 = 0 ∧
      twoTwoRepresentative.symm 2 = 3 ∧
      twoTwoRepresentative.symm 3 = 2 ∧
      twoTwoRepresentative.symm 4 = 4 := by
  decide

set_option maxRecDepth 100000 in
private theorem oneFourRepresentative_symm_table :
    oneFourRepresentative.symm 0 = 3 ∧
      oneFourRepresentative.symm 1 = 0 ∧
      oneFourRepresentative.symm 2 = 1 ∧
      oneFourRepresentative.symm 3 = 2 ∧
      oneFourRepresentative.symm 4 = 4 := by
  decide

private theorem fiveCycle_fixed_coordinates {d : ℕ}
    (a : DegreeExponent (Fin 5) d)
    (ha : exponentPerm fiveCycle d a = a) :
    ∀ i, a.1 i = a.1 0 := by
  have h := (exponentPerm_eq_self_iff fiveCycle d a).mp ha
  rcases fiveCycle_symm_table with ⟨h0, h1, h2, h3, _h4⟩
  have e0 := h (0 : Fin 5)
  have e1 := h (1 : Fin 5)
  have e2 := h (2 : Fin 5)
  have e3 := h (3 : Fin 5)
  rw [h0] at e0
  rw [h1] at e1
  rw [h2] at e2
  rw [h3] at e3
  intro i
  fin_cases i
  · rfl
  · exact e1.symm
  · exact e2.symm.trans e1.symm
  · exact e3.symm.trans (e2.symm.trans e1.symm)
  · exact e0

private theorem twoTwo_fixed_coordinates {d : ℕ}
    (a : DegreeExponent (Fin 5) d)
    (ha : exponentPerm twoTwoRepresentative d a = a) :
    a.1 1 = a.1 0 ∧ a.1 3 = a.1 2 := by
  have h := (exponentPerm_eq_self_iff twoTwoRepresentative d a).mp ha
  rcases twoTwoRepresentative_symm_table with
    ⟨h0, _h1, h2, _h3, _h4⟩
  have e0 := h (0 : Fin 5)
  have e2 := h (2 : Fin 5)
  rw [h0] at e0
  rw [h2] at e2
  exact ⟨e0, e2⟩

private theorem oneFour_fixed_coordinates {d : ℕ}
    (a : DegreeExponent (Fin 5) d)
    (ha : exponentPerm oneFourRepresentative d a = a) :
    a.1 1 = a.1 0 ∧ a.1 2 = a.1 0 ∧ a.1 3 = a.1 0 := by
  have h := (exponentPerm_eq_self_iff oneFourRepresentative d a).mp ha
  rcases oneFourRepresentative_symm_table with
    ⟨_h0, h1, h2, h3, _h4⟩
  have e1 := h (1 : Fin 5)
  have e2 := h (2 : Fin 5)
  have e3 := h (3 : Fin 5)
  rw [h1] at e1
  rw [h2] at e2
  rw [h3] at e3
  exact ⟨e1.symm, e2.symm.trans e1.symm,
    e3.symm.trans (e2.symm.trans e1.symm)⟩

/-- For the identity, the five coordinates themselves are the five
weight-one cycle parameters. -/
noncomputable def identityFixedExponentEquiv (d : ℕ) :
    Function.fixedPoints (exponentPerm (1 : S5) d) ≃
      WeightedDegree (Fin 5) identityWeights d where
  toFun a := ⟨fun i ↦ a.1.1 i, by
    simpa [identityWeights, Finsupp.degree_eq_sum] using a.1.2⟩
  invFun q := by
    let a : DegreeExponent (Fin 5) d :=
      ⟨Finsupp.equivFunOnFinite.symm q.1, by
        rw [Finsupp.degree_eq_sum]
        simpa [identityWeights] using q.2⟩
    refine ⟨a, Function.mem_fixedPoints_iff.mpr ?_⟩
    simp [a]
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    rfl
  right_inv q := by
    apply Subtype.ext
    funext i
    rfl

/-- A fixed exponent vector for the five-cycle is constant, hence is
determined by one parameter of weight five. -/
noncomputable def fiveCycleFixedExponentEquiv (d : ℕ) :
    Function.fixedPoints (exponentPerm fiveCycle d) ≃
      WeightedDegree (Fin 1) fiveCycleWeights d where
  toFun a := ⟨fun _ ↦ a.1.1 0, by
    have ha := Function.mem_fixedPoints_iff.mp a.2
    have hc := fiveCycle_fixed_coordinates a.1 ha
    have hdeg : ∑ i, a.1.1 i = d := by
      simpa only [Finsupp.degree_eq_sum] using a.1.2
    rw [sum_fin_five] at hdeg
    have hweighted : 5 * a.1.1 0 = d := by
      have h1 := hc (1 : Fin 5)
      have h2 := hc (2 : Fin 5)
      have h3 := hc (3 : Fin 5)
      have h4 := hc (4 : Fin 5)
      omega
    simpa [fiveCycleWeights, Fin.sum_univ_succ] using hweighted⟩
  invFun q := by
    let a : DegreeExponent (Fin 5) d :=
      ⟨Finsupp.equivFunOnFinite.symm (fun _ ↦ q.1 0), by
        rw [Finsupp.degree_eq_sum, sum_fin_five]
        have hq : 5 * q.1 0 = d := by
          simpa [fiveCycleWeights, Fin.sum_univ_succ] using q.2
        simp only [Finsupp.coe_equivFunOnFinite_symm]
        omega⟩
    refine ⟨a, Function.mem_fixedPoints_iff.mpr ?_⟩
    apply (exponentPerm_eq_self_iff fiveCycle d a).mpr
    intro i
    rfl
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    have ha := Function.mem_fixedPoints_iff.mp a.2
    exact (fiveCycle_fixed_coordinates a.1 ha i).symm
  right_inv q := by
    apply Subtype.ext
    funext i
    fin_cases i
    rfl

/-- A fixed exponent vector for `(0 1)(2 3)` has parameters at coordinates
`0`, `2`, and `4`, of weights `2`, `2`, and `1`. -/
noncomputable def twoTwoFixedExponentEquiv (d : ℕ) :
    Function.fixedPoints (exponentPerm twoTwoRepresentative d) ≃
      WeightedDegree (Fin 3) twoTwoWeights d where
  toFun a := ⟨![a.1.1 0, a.1.1 2, a.1.1 4], by
    have ha := Function.mem_fixedPoints_iff.mp a.2
    rcases twoTwo_fixed_coordinates a.1 ha with ⟨h01, h23⟩
    have hdeg : ∑ i, a.1.1 i = d := by
      simpa only [Finsupp.degree_eq_sum] using a.1.2
    rw [sum_fin_five] at hdeg
    have hweighted :
        2 * a.1.1 0 + 2 * a.1.1 2 + a.1.1 4 = d := by
      omega
    simpa [twoTwoWeights, Fin.sum_univ_succ, add_assoc] using hweighted⟩
  invFun q := by
    let a : DegreeExponent (Fin 5) d :=
      ⟨Finsupp.equivFunOnFinite.symm
          ![q.1 0, q.1 0, q.1 1, q.1 1, q.1 2], by
        rw [Finsupp.degree_eq_sum, sum_fin_five]
        have hq : 2 * q.1 0 + 2 * q.1 1 + q.1 2 = d := by
          simpa [twoTwoWeights, Fin.sum_univ_succ, add_assoc] using q.2
        simp only [Finsupp.coe_equivFunOnFinite_symm]
        simp
        omega⟩
    refine ⟨a, Function.mem_fixedPoints_iff.mpr ?_⟩
    apply (exponentPerm_eq_self_iff twoTwoRepresentative d a).mpr
    intro i
    rcases twoTwoRepresentative_symm_table with
      ⟨h0, h1, h2, h3, h4⟩
    fin_cases i <;> simp [h0, h1, h2, h3, h4, a]
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    have ha := Function.mem_fixedPoints_iff.mp a.2
    rcases twoTwo_fixed_coordinates a.1 ha with ⟨h01, h23⟩
    fin_cases i <;> simp [h01, h23]
  right_inv q := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl

/-- A fixed exponent vector for `(0 1 2 3)` has parameters at coordinates
`0` and `4`, of weights `4` and `1`. -/
noncomputable def oneFourFixedExponentEquiv (d : ℕ) :
    Function.fixedPoints (exponentPerm oneFourRepresentative d) ≃
      WeightedDegree (Fin 2) oneFourWeights d where
  toFun a := ⟨![a.1.1 0, a.1.1 4], by
    have ha := Function.mem_fixedPoints_iff.mp a.2
    rcases oneFour_fixed_coordinates a.1 ha with ⟨h1, h2, h3⟩
    have hdeg : ∑ i, a.1.1 i = d := by
      simpa only [Finsupp.degree_eq_sum] using a.1.2
    rw [sum_fin_five] at hdeg
    have hweighted : 4 * a.1.1 0 + a.1.1 4 = d := by
      omega
    simpa [oneFourWeights, Fin.sum_univ_succ] using hweighted⟩
  invFun q := by
    let a : DegreeExponent (Fin 5) d :=
      ⟨Finsupp.equivFunOnFinite.symm
          ![q.1 0, q.1 0, q.1 0, q.1 0, q.1 1], by
        rw [Finsupp.degree_eq_sum, sum_fin_five]
        have hq : 4 * q.1 0 + q.1 1 = d := by
          simpa [oneFourWeights, Fin.sum_univ_succ] using q.2
        simp only [Finsupp.coe_equivFunOnFinite_symm]
        simp
        omega⟩
    refine ⟨a, Function.mem_fixedPoints_iff.mpr ?_⟩
    apply (exponentPerm_eq_self_iff oneFourRepresentative d a).mpr
    intro i
    rcases oneFourRepresentative_symm_table with
      ⟨h0, h1, h2, h3, h4⟩
    fin_cases i <;> simp [h0, h1, h2, h3, h4, a]
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    have ha := Function.mem_fixedPoints_iff.mp a.2
    rcases oneFour_fixed_coordinates a.1 ha with ⟨h1, h2, h3⟩
    fin_cases i <;> simp [h1, h2, h3]
  right_inv q := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl

/-- The identity contribution is `(1-X)⁻⁵`. -/
theorem fixedExponentSeries_one :
    fixedExponentSeries (1 : S5) = geometricStepSeries 1 ^ 5 := by
  calc
    fixedExponentSeries (1 : S5) =
        weightedDegreeSeries (Fin 5) identityWeights :=
      fixedExponentSeries_eq_weightedDegreeSeries_of_equiv
        (1 : S5) identityWeights identityFixedExponentEquiv
    _ = ∏ i : Fin 5, geometricStepSeries (identityWeights i) :=
      weightedDegreeSeries_eq_prod_geometricStep identityWeights (by simp [identityWeights])
    _ = geometricStepSeries 1 ^ 5 := by
      simp [identityWeights]

/-- The five-cycle contribution is `(1-X⁵)⁻¹`. -/
theorem fixedExponentSeries_fiveCycle :
    fixedExponentSeries fiveCycle = geometricStepSeries 5 := by
  calc
    fixedExponentSeries fiveCycle =
        weightedDegreeSeries (Fin 1) fiveCycleWeights :=
      fixedExponentSeries_eq_weightedDegreeSeries_of_equiv
        fiveCycle fiveCycleWeights fiveCycleFixedExponentEquiv
    _ = ∏ i : Fin 1, geometricStepSeries (fiveCycleWeights i) :=
      weightedDegreeSeries_eq_prod_geometricStep fiveCycleWeights
        (by simp [fiveCycleWeights])
    _ = geometricStepSeries 5 := by
      simp [fiveCycleWeights]

/-- The `1+2+2` contribution is
`(1-X)⁻¹ (1-X²)⁻²`. -/
theorem fixedExponentSeries_twoTwoRepresentative :
    fixedExponentSeries twoTwoRepresentative =
      geometricStepSeries 1 * geometricStepSeries 2 ^ 2 := by
  calc
    fixedExponentSeries twoTwoRepresentative =
        weightedDegreeSeries (Fin 3) twoTwoWeights :=
      fixedExponentSeries_eq_weightedDegreeSeries_of_equiv
        twoTwoRepresentative twoTwoWeights twoTwoFixedExponentEquiv
    _ = ∏ i : Fin 3, geometricStepSeries (twoTwoWeights i) :=
      weightedDegreeSeries_eq_prod_geometricStep twoTwoWeights
        (by intro i; fin_cases i <;> norm_num [twoTwoWeights])
    _ = geometricStepSeries 1 * geometricStepSeries 2 ^ 2 := by
      simp [twoTwoWeights, Fin.prod_univ_succ, pow_two,
        mul_comm, mul_left_comm]

/-- The `1+4` contribution is `(1-X)⁻¹ (1-X⁴)⁻¹`. -/
theorem fixedExponentSeries_oneFourRepresentative :
    fixedExponentSeries oneFourRepresentative =
      geometricStepSeries 1 * geometricStepSeries 4 := by
  calc
    fixedExponentSeries oneFourRepresentative =
        weightedDegreeSeries (Fin 2) oneFourWeights :=
      fixedExponentSeries_eq_weightedDegreeSeries_of_equiv
        oneFourRepresentative oneFourWeights oneFourFixedExponentEquiv
    _ = ∏ i : Fin 2, geometricStepSeries (oneFourWeights i) :=
      weightedDegreeSeries_eq_prod_geometricStep oneFourWeights
        (by intro i; fin_cases i <;> norm_num [oneFourWeights])
    _ = geometricStepSeries 1 * geometricStepSeries 4 := by
      simp [oneFourWeights, Fin.prod_univ_succ, mul_comm]

private theorem cycleTypeFilters_disjoint
    {m n : Multiset ℕ} (hmn : m ≠ n) :
    Disjoint
      (LazardQuinticF20Molien.f20ElementsOfCycleType m)
      (LazardQuinticF20Molien.f20ElementsOfCycleType n) := by
  rw [Finset.disjoint_left]
  intro g hgm hgn
  apply hmn
  exact ((Finset.mem_filter.mp hgm).2).symm.trans
    (Finset.mem_filter.mp hgn).2

private theorem f20Elements_eq_cycleType_union :
    f20Elements =
      ((LazardQuinticF20Molien.f20ElementsOfCycleType 0 ∪
        LazardQuinticF20Molien.f20ElementsOfCycleType {5}) ∪
        LazardQuinticF20Molien.f20ElementsOfCycleType {2, 2}) ∪
        LazardQuinticF20Molien.f20ElementsOfCycleType {4} := by
  ext g
  constructor
  · intro hg
    rcases LazardQuinticF20Molien.f20_cycle_types_exhaustive g hg with
      h0 | h5 | h22 | h4
    · simp only [Finset.mem_union,
        LazardQuinticF20Molien.f20ElementsOfCycleType,
        Finset.mem_filter]
      exact Or.inl (Or.inl (Or.inl ⟨hg, h0⟩))
    · simp only [Finset.mem_union,
        LazardQuinticF20Molien.f20ElementsOfCycleType,
        Finset.mem_filter]
      exact Or.inl (Or.inl (Or.inr ⟨hg, h5⟩))
    · simp only [Finset.mem_union,
        LazardQuinticF20Molien.f20ElementsOfCycleType,
        Finset.mem_filter]
      exact Or.inl (Or.inr ⟨hg, h22⟩)
    · simp only [Finset.mem_union,
        LazardQuinticF20Molien.f20ElementsOfCycleType,
        Finset.mem_filter]
      exact Or.inr ⟨hg, h4⟩
  · simp only [Finset.mem_union,
      LazardQuinticF20Molien.f20ElementsOfCycleType,
      Finset.mem_filter]
    rintro (((⟨hg, _⟩ | ⟨hg, _⟩) | ⟨hg, _⟩) | ⟨hg, _⟩) <;>
      exact hg

/-- Replace a sum over the subgroup subtype by the checked, computable
twenty-element `Finset` used by the class-count calculation. -/
theorem sum_standardF20_eq_f20Elements (f : S5 → ℚ) :
    (∑ g : standardF20, f g.1) = ∑ g ∈ f20Elements, f g := by
  classical
  calc
    (∑ g : standardF20, f g.1) =
        ∑ g : {g : S5 // g ∈ f20Elements}, f g.1 :=
      Fintype.sum_equiv standardF20EquivElements _ _ (fun _ ↦ rfl)
    _ = ∑ g ∈ f20Elements, f g := by
      exact Finset.sum_coe_sort f20Elements f

/-- The finite class-count aggregation step.  The summand is not replaced by
an assumed class function: `fixedExponentCount_eq_of_cycleType_eq` proves
that it is constant on each of the four filters. -/
theorem f20Elements_sum_fixedExponentCount (d : ℕ) :
    (∑ g ∈ f20Elements, (fixedExponentCount g d : ℚ)) =
      (fixedExponentCount (1 : S5) d : ℚ) +
        4 * fixedExponentCount fiveCycle d +
        5 * fixedExponentCount twoTwoRepresentative d +
        10 * fixedExponentCount oneFourRepresentative d := by
  classical
  let S0 := LazardQuinticF20Molien.f20ElementsOfCycleType 0
  let S5c := LazardQuinticF20Molien.f20ElementsOfCycleType {5}
  let S22 := LazardQuinticF20Molien.f20ElementsOfCycleType {2, 2}
  let S4 := LazardQuinticF20Molien.f20ElementsOfCycleType {4}
  have h05 : Disjoint S0 S5c :=
    cycleTypeFilters_disjoint (by decide)
  have h0_22 : Disjoint S0 S22 :=
    cycleTypeFilters_disjoint (by decide)
  have h5_22 : Disjoint S5c S22 :=
    cycleTypeFilters_disjoint (by decide)
  have h0_4 : Disjoint S0 S4 :=
    cycleTypeFilters_disjoint (by decide)
  have h5_4 : Disjoint S5c S4 :=
    cycleTypeFilters_disjoint (by decide)
  have h22_4 : Disjoint S22 S4 :=
    cycleTypeFilters_disjoint (by decide)
  have h05_22 : Disjoint (S0 ∪ S5c) S22 :=
    Finset.disjoint_union_left.mpr ⟨h0_22, h5_22⟩
  have h0522_4 : Disjoint ((S0 ∪ S5c) ∪ S22) S4 :=
    Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_left.mpr ⟨h0_4, h5_4⟩, h22_4⟩
  have hsum0 :
      (∑ g ∈ S0, (fixedExponentCount g d : ℚ)) =
        fixedExponentCount (1 : S5) d := by
    calc
      (∑ g ∈ S0, (fixedExponentCount g d : ℚ)) =
          ∑ _g ∈ S0, (fixedExponentCount (1 : S5) d : ℚ) := by
        apply Finset.sum_congr rfl
        intro g hg
        exact_mod_cast fixedExponentCount_eq_of_cycleType_eq d
          ((Finset.mem_filter.mp hg).2.trans cycleType_one.symm)
      _ = fixedExponentCount (1 : S5) d := by
        rcases LazardQuinticF20Molien.f20_cycle_class_counts with
          ⟨hc, _, _, _⟩
        rw [Finset.sum_const, nsmul_eq_mul]
        have hcard : S0.card = 1 := by simpa [S0] using hc
        rw [hcard]
        norm_num
  have hsum5 :
      (∑ g ∈ S5c, (fixedExponentCount g d : ℚ)) =
        4 * fixedExponentCount fiveCycle d := by
    calc
      (∑ g ∈ S5c, (fixedExponentCount g d : ℚ)) =
          ∑ _g ∈ S5c, (fixedExponentCount fiveCycle d : ℚ) := by
        apply Finset.sum_congr rfl
        intro g hg
        exact_mod_cast fixedExponentCount_eq_of_cycleType_eq d
          ((Finset.mem_filter.mp hg).2.trans cycleType_fiveCycle.symm)
      _ = 4 * fixedExponentCount fiveCycle d := by
        rcases LazardQuinticF20Molien.f20_cycle_class_counts with
          ⟨_, hc, _, _⟩
        rw [Finset.sum_const, nsmul_eq_mul]
        have hcard : S5c.card = 4 := by simpa [S5c] using hc
        rw [hcard]
        norm_num
  have hsum22 :
      (∑ g ∈ S22, (fixedExponentCount g d : ℚ)) =
        5 * fixedExponentCount twoTwoRepresentative d := by
    calc
      (∑ g ∈ S22, (fixedExponentCount g d : ℚ)) =
          ∑ _g ∈ S22,
            (fixedExponentCount twoTwoRepresentative d : ℚ) := by
        apply Finset.sum_congr rfl
        intro g hg
        exact_mod_cast fixedExponentCount_eq_of_cycleType_eq d
          ((Finset.mem_filter.mp hg).2.trans
            cycleType_twoTwoRepresentative.symm)
      _ = 5 * fixedExponentCount twoTwoRepresentative d := by
        rcases LazardQuinticF20Molien.f20_cycle_class_counts with
          ⟨_, _, hc, _⟩
        rw [Finset.sum_const, nsmul_eq_mul]
        have hcard : S22.card = 5 := by simpa [S22] using hc
        rw [hcard]
        norm_num
  have hsum4 :
      (∑ g ∈ S4, (fixedExponentCount g d : ℚ)) =
        10 * fixedExponentCount oneFourRepresentative d := by
    calc
      (∑ g ∈ S4, (fixedExponentCount g d : ℚ)) =
          ∑ _g ∈ S4,
            (fixedExponentCount oneFourRepresentative d : ℚ) := by
        apply Finset.sum_congr rfl
        intro g hg
        exact_mod_cast fixedExponentCount_eq_of_cycleType_eq d
          ((Finset.mem_filter.mp hg).2.trans
            cycleType_oneFourRepresentative.symm)
      _ = 10 * fixedExponentCount oneFourRepresentative d := by
        rcases LazardQuinticF20Molien.f20_cycle_class_counts with
          ⟨_, _, _, hc⟩
        rw [Finset.sum_const, nsmul_eq_mul]
        have hcard : S4.card = 10 := by simpa [S4] using hc
        rw [hcard]
        norm_num
  rw [f20Elements_eq_cycleType_union,
    Finset.sum_union h0522_4, Finset.sum_union h05_22,
    Finset.sum_union h05, hsum0, hsum5, hsum22, hsum4]

/-- The invariant Hilbert coefficient after grouping all twenty elements by
their checked cycle types. -/
theorem f20_hilbert_coefficient_cycle_class_formula (d : ℕ) :
    PowerSeries.coeff d f20InvariantHilbertSeries =
      (20 : ℚ)⁻¹ *
        ((fixedExponentCount (1 : S5) d : ℚ) +
          4 * fixedExponentCount fiveCycle d +
          5 * fixedExponentCount twoTwoRepresentative d +
          10 * fixedExponentCount oneFourRepresentative d) := by
  rw [f20_hilbert_coefficient_eq_average]
  congr 1
  calc
    (∑ g : standardF20, (fixedExponentCount g.1 d : ℚ)) =
        ∑ g ∈ f20Elements, (fixedExponentCount g d : ℚ) :=
      sum_standardF20_eq_f20Elements
        (fun g ↦ (fixedExponentCount g d : ℚ))
    _ = _ := f20Elements_sum_fixedExponentCount d

/-- The class-count formula as an equality of whole formal power series. -/
theorem f20InvariantHilbertSeries_eq_fixed_class_sum :
    f20InvariantHilbertSeries =
      PowerSeries.C (20 : ℚ)⁻¹ *
        (fixedExponentSeries (1 : S5) +
          PowerSeries.C 4 * fixedExponentSeries fiveCycle +
          PowerSeries.C 5 * fixedExponentSeries twoTwoRepresentative +
          PowerSeries.C 10 * fixedExponentSeries oneFourRepresentative) := by
  ext d
  rw [f20_hilbert_coefficient_cycle_class_formula,
    PowerSeries.coeff_C_mul]
  simp only [map_add, PowerSeries.coeff_C_mul,
    fixedExponentSeries, PowerSeries.coeff_mk]

/-- The complete formal-power-series Molien formula for the standard
`F₂₀` action.  Each `geometricStepSeries m` is proved above to be the inverse
of `1-X^m`, so this is literally the four-term class sum printed by Lazard. -/
theorem f20InvariantHilbertSeries_eq_geometric_class_sum :
    f20InvariantHilbertSeries =
      PowerSeries.C (20 : ℚ)⁻¹ *
        (geometricStepSeries 1 ^ 5 +
          PowerSeries.C 4 * geometricStepSeries 5 +
          PowerSeries.C 5 *
            (geometricStepSeries 1 * geometricStepSeries 2 ^ 2) +
          PowerSeries.C 10 *
            (geometricStepSeries 1 * geometricStepSeries 4)) := by
  rw [f20InvariantHilbertSeries_eq_fixed_class_sum,
    fixedExponentSeries_one, fixedExponentSeries_fiveCycle,
    fixedExponentSeries_twoTwoRepresentative,
    fixedExponentSeries_oneFourRepresentative]

/-- The honest Hilbert-series class sum and the independently checked
rational-function simplification to Lazard's numerator, packaged together. -/
theorem f20_hilbert_series_and_rational_numerator :
    f20InvariantHilbertSeries =
        PowerSeries.C (20 : ℚ)⁻¹ *
          (geometricStepSeries 1 ^ 5 +
            PowerSeries.C 4 * geometricStepSeries 5 +
            PowerSeries.C 5 *
              (geometricStepSeries 1 * geometricStepSeries 2 ^ 2) +
            PowerSeries.C 10 *
              (geometricStepSeries 1 * geometricStepSeries 4)) ∧
      LazardQuinticF20Molien.f20MolienClassSumAt
          (RatFunc.X : RatFunc ℚ) =
        LazardQuinticF20Molien.f20MolienNumeratorAt
            (RatFunc.X : RatFunc ℚ) /
          LazardQuinticF20Molien.f20SymmetricDenominatorAt
            (RatFunc.X : RatFunc ℚ) :=
  ⟨f20InvariantHilbertSeries_eq_geometric_class_sum,
    LazardQuinticF20Molien.f20_molien_class_sum_identity⟩

/-- This theorem records, in one kernel-checkable statement, the two halves
of the Section 6 Molien calculation at one coefficient: invariant
coefficients are averaged traces, and Lazard's printed class sum has the
printed numerator as a rational function.  The whole-series strengthening is
`f20_hilbert_series_and_rational_numerator`. -/
theorem coefficientwise_molien_and_f20_rational_numerator (d : ℕ) :
    PowerSeries.coeff d f20InvariantHilbertSeries =
        (20 : ℚ)⁻¹ *
          ∑ g : standardF20, (fixedExponentCount g.1 d : ℚ) ∧
      LazardQuinticF20Molien.f20MolienClassSumAt
          (RatFunc.X : RatFunc ℚ) =
        LazardQuinticF20Molien.f20MolienNumeratorAt
            (RatFunc.X : RatFunc ℚ) /
          LazardQuinticF20Molien.f20SymmetricDenominatorAt
            (RatFunc.X : RatFunc ℚ) :=
  ⟨f20_hilbert_coefficient_eq_average d,
    LazardQuinticF20Molien.f20_molien_class_sum_identity⟩

end

end LeanProofs.PolynomialFormulas.LazardInvariantMolienCoefficients
