import PolynomialFormulas.FrobeniusDummitResolvent
import Mathlib.FieldTheory.PolynomialGaloisGroup

/-!
# Chapman's scalar-resolvent collision argument over an arbitrary base field

The rational specialization obtains invertibility of five from
characteristic zero. Lazard's claim has the sharper hypothesis
`(5 : F) ≠ 0`. This file proves the no-collision and scalar-resolvent
separability argument over any base field, conditional only on the explicit
root tuple and five-cycle endomorphism used by the argument.
-/

open scoped BigOperators Polynomial
open Equiv Polynomial

namespace LeanProofs.PolynomialFormulas.FrobeniusDummitResolvent

open LeanProofs.PolynomialFormulas.Fin5Solvable
open LeanProofs.PolynomialFormulas.Fin5TransitiveC5

set_option autoImplicit false

/-- Chapman's center equation descends the distinguished root to an
arbitrary base field when five is invertible there. -/
theorem chapman_center_mem_range_of_collisions_over
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    (h5 : (5 : F) ≠ 0) (r : Fin 5 → L) (hr : Function.Injective r)
    (h12 : thetaValue r 1 = thetaValue r 2)
    (h34 : thetaValue r 3 = thetaValue r 4)
    (hsum : r 0 + r 1 + r 2 + r 3 + r 4 ∈
      Set.range (algebraMap F L)) :
    r 1 ∈ Set.range (algebraMap F L) := by
  obtain ⟨q, hq⟩ := hsum
  have h5L : (5 : L) ≠ 0 := by
    have h5map : algebraMap F L (5 : F) ≠ 0 :=
      (map_ne_zero_iff (algebraMap F L) (algebraMap F L).injective).mpr h5
    simpa only [map_ofNat] using h5map
  refine ⟨q / 5, ?_⟩
  calc
    algebraMap F L (q / 5) =
        algebraMap F L q / algebraMap F L 5 := by
      simp only [div_eq_mul_inv, _root_.map_mul, _root_.map_inv₀]
    _ = algebraMap F L q / (5 : L) := by rw [map_ofNat]
    _ = r 1 := by
      apply (div_eq_iff h5L).2
      have hc :=
        chapman_five_mul_center_of_thetaValue_collisions r hr h12 h34
      rw [← hq] at hc
      simpa [mul_comm] using hc.symm

/-- Irreducibility excludes Chapman's collision pair over an arbitrary base
field. -/
theorem not_chapman_collisions_of_irreducible_quintic_over
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    (h5 : (5 : F) ≠ 0) (p : Polynomial F) (hp : Irreducible p)
    (hdeg : p.natDegree = 5) (r : Fin 5 → L)
    (hr : Function.Injective r)
    (hroot : (p.map (algebraMap F L)).IsRoot (r 1))
    (hsum : r 0 + r 1 + r 2 + r 3 + r 4 ∈
      Set.range (algebraMap F L)) :
    ¬(thetaValue r 1 = thetaValue r 2 ∧
      thetaValue r 3 = thetaValue r 4) := by
  rintro ⟨h12, h34⟩
  obtain ⟨q, hq⟩ :=
    chapman_center_mem_range_of_collisions_over h5 r hr h12 h34 hsum
  apply hp.not_isRoot_of_natDegree_ne_one (by omega : p.natDegree ≠ 1)
  rw [Polynomial.IsRoot]
  have hz : algebraMap F L (p.eval q) = 0 := by
    calc
      algebraMap F L (p.eval q) =
          (p.map (algebraMap F L)).eval (algebraMap F L q) := by
        rw [Polynomial.eval_map]
        exact (Polynomial.eval₂_at_apply (algebraMap F L) q).symm
      _ = (p.map (algebraMap F L)).eval (r 1) := by rw [hq]
      _ = 0 := by simpa [Polynomial.IsRoot] using hroot
  exact (algebraMap F L).injective (by simpa using hz)

/-- A five-cycle endomorphism propagates any collision to Chapman's forbidden
pair, making all six theta values distinct. -/
theorem thetaValue_injective_of_fiveCycle_action_over
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    (h5 : (5 : F) ≠ 0) (p : Polynomial F) (hp : Irreducible p)
    (hdeg : p.natDegree = 5) (r : Fin 5 → L)
    (hr : Function.Injective r)
    (hroot : (p.map (algebraMap F L)).IsRoot (r 1))
    (hsum : r 0 + r 1 + r 2 + r 3 + r 4 ∈
      Set.range (algebraMap F L))
    (σ : L →+* L) (hσ : ∀ k, σ (r k) = r (fiveCycle k)) :
    Function.Injective (thetaValue r) := by
  intro i j hij
  by_contra hne
  have hstep : ∀ a b,
      thetaValue r a = thetaValue r b →
        thetaValue r (Fin5TransitiveC5.fiveCycleOnRepresentatives a) =
          thetaValue r
            (Fin5TransitiveC5.fiveCycleOnRepresentatives b) := by
    intro a b hab
    have hm := congrArg σ hab
    rw [map_thetaValue_fiveCycle r σ hσ a,
      map_thetaValue_fiveCycle r σ hσ b] at hm
    exact hm
  have hcollisions :=
    fiveCycle_collision_propagates (thetaValue r) hstep hne hij
  exact (not_chapman_collisions_of_irreducible_quintic_over
    h5 p hp hdeg r hr hroot hsum) hcollisions

/-- The literal six-factor scalar resolvent is separable under the same
field-generic Chapman hypotheses. -/
theorem scalarResolvent_separable_of_irreducible_fiveCycle_action_over
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    (h5 : (5 : F) ≠ 0) (p : Polynomial F) (hp : Irreducible p)
    (hdeg : p.natDegree = 5) (r : Fin 5 → L)
    (hr : Function.Injective r)
    (hroot : (p.map (algebraMap F L)).IsRoot (r 1))
    (hsum : r 0 + r 1 + r 2 + r 3 + r 4 ∈
      Set.range (algebraMap F L))
    (σ : L →+* L) (hσ : ∀ k, σ (r k) = r (fiveCycle k)) :
    (scalarResolvent r).Separable := by
  rw [scalarResolvent_eq_prod, Polynomial.separable_prod_X_sub_C_iff]
  exact thetaValue_injective_of_fiveCycle_action_over
    h5 p hp hdeg r hr hroot hsum σ hσ

/-! ## Canonical splitting-field specialization

The hypotheses in the preceding theorem are not extra mathematical
assumptions for an irreducible quintic.  In the canonical splitting field,
irreducibility makes the Galois action on the roots transitive.  Since the
root set has five elements, Cauchy's theorem supplies an element acting as a
five-cycle; a noncomputable reindexing conjugates that action to the literal
`fiveCycle` used above.  There is no distinguished root ordering or
distinguished Galois element, so the result is necessarily existential rather
than canonical data in the computational sense.

The normality and splitting hypotheses needed below are supplied by
`p.SplittingField`.  Separability follows from irreducibility, degree five,
and `(5 : F) ≠ 0`; this includes arbitrary positive characteristic other
than five.
-/

/-- An irreducible quintic is separable whenever five is nonzero in the base
field.  The coefficient of degree four in its derivative is five times the
leading coefficient. -/
theorem irreducible_quintic_separable_of_five_ne_zero
    {F : Type*} [Field F] (h5 : (5 : F) ≠ 0) {p : Polynomial F}
    (hp : Irreducible p) (hdeg : p.natDegree = 5) : p.Separable := by
  rw [Polynomial.separable_iff_derivative_ne_zero hp]
  intro hder
  have hcoeff := congrArg (fun q : Polynomial F ↦ q.coeff 4) hder
  norm_num [Polynomial.coeff_derivative] at hcoeff
  have hp5 : p.coeff 5 ≠ 0 := by
    rw [← hdeg, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp.ne_zero
  exact hcoeff.elim hp5 h5

/-- A noncomputable ordering of all five roots in the canonical splitting
field. -/
noncomputable def splittingRootEquivOver
    {F : Type*} [Field F] (h5 : (5 : F) ≠ 0) (p : Polynomial F)
    (hp : Irreducible p) (hdeg : p.natDegree = 5) :
    p.rootSet p.SplittingField ≃ Fin 5 :=
  Fintype.equivOfCardEq
    ((card_rootSet_eq_natDegree
      (irreducible_quintic_separable_of_five_ne_zero h5 hp hdeg)
      (SplittingField.splits p)).trans hdeg)

/-- The faithful permutation representation on the chosen ordering of the
five roots. -/
noncomputable def splittingRootPermutationHomOver
    {F : Type*} [Field F] (h5 : (5 : F) ≠ 0) (p : Polynomial F)
    (hp : Irreducible p) (hdeg : p.natDegree = 5) : p.Gal →* S5 :=
  (splittingRootEquivOver h5 p hp hdeg).permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom p.Gal (p.rootSet p.SplittingField))

/-- The image of the splitting-field Galois group in `S₅`. -/
noncomputable def splittingRootPermutationGroupOver
    {F : Type*} [Field F] (h5 : (5 : F) ≠ 0) (p : Polynomial F)
    (hp : Irreducible p) (hdeg : p.natDegree = 5) : Subgroup S5 :=
  (splittingRootPermutationHomOver h5 p hp hdeg).range

theorem splittingRootPermutationHomOver_injective
    {F : Type*} [Field F] (h5 : (5 : F) ≠ 0) (p : Polynomial F)
    (hp : Irreducible p) (hdeg : p.natDegree = 5) :
    Function.Injective (splittingRootPermutationHomOver h5 p hp hdeg) := by
  intro σ τ hστ
  apply Gal.ext
  intro x hx
  let y : p.rootSet p.SplittingField := ⟨x, hx⟩
  have hperm :
      MulAction.toPermHom p.Gal (p.rootSet p.SplittingField) σ =
        MulAction.toPermHom p.Gal (p.rootSet p.SplittingField) τ :=
    (splittingRootEquivOver h5 p hp hdeg).permCongrHom.injective hστ
  have hy := Equiv.congr_fun hperm y
  exact congrArg Subtype.val hy

/-- Irreducibility makes the permutation image transitive. -/
theorem splittingRootPermutationGroupOver_isPretransitive
    {F : Type*} [Field F] (h5 : (5 : F) ≠ 0) (p : Polynomial F)
    (hp : Irreducible p) (hdeg : p.natDegree = 5) :
    MulAction.IsPretransitive
      (splittingRootPermutationGroupOver h5 p hp hdeg) (Fin 5) := by
  letI : p.IsSplittingField F p.SplittingField :=
    Polynomial.IsSplittingField.splittingField p
  letI : IsGalois F p.SplittingField :=
    IsGalois.of_separable_splitting_field
      (irreducible_quintic_separable_of_five_ne_zero h5 hp hdeg)
  constructor
  intro x y
  let e := splittingRootEquivOver h5 p hp hdeg
  let x' : p.rootSet p.SplittingField := e.symm x
  let y' : p.rootSet p.SplittingField := e.symm y
  letI : MulAction.IsPretransitive p.Gal
      (p.rootSet p.SplittingField) := by
    constructor
    intro a b
    have ha := minpoly.eq_of_irreducible hp (mem_rootSet.mp a.2).2
    have hb := minpoly.eq_of_irreducible hp (mem_rootSet.mp b.2).2
    obtain ⟨g, hg⟩ :=
      (Normal.minpoly_eq_iff_mem_orbit p.SplittingField).mp
        (hb.symm.trans ha)
    exact ⟨g, Subtype.ext hg⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq p.Gal x' y'
  let g' : splittingRootPermutationGroupOver h5 p hp hdeg :=
    ⟨splittingRootPermutationHomOver h5 p hp hdeg g, ⟨g, rfl⟩⟩
  refine ⟨g', ?_⟩
  change splittingRootPermutationHomOver h5 p hp hdeg g x = y
  change e
    ((MulAction.toPermHom p.Gal (p.rootSet p.SplittingField) g)
      (e.symm x)) = y
  change e (g • x') = y
  rw [hg]
  exact e.apply_symm_apply y

/-- The chosen ordered root tuple. -/
noncomputable def splittingRootTupleOver
    {F : Type*} [Field F] (h5 : (5 : F) ≠ 0) (p : Polynomial F)
    (hp : Irreducible p) (hdeg : p.natDegree = 5) :
    Fin 5 → p.SplittingField :=
  fun i ↦ (splittingRootEquivOver h5 p hp hdeg).symm i

theorem gal_maps_splittingRootTupleOver
    {F : Type*} [Field F] (h5 : (5 : F) ≠ 0) (p : Polynomial F)
    (hp : Irreducible p) (hdeg : p.natDegree = 5)
    (σ : p.Gal) (i : Fin 5) :
    σ (splittingRootTupleOver h5 p hp hdeg i) =
      splittingRootTupleOver h5 p hp hdeg
        (splittingRootPermutationHomOver h5 p hp hdeg σ i) := by
  change σ ((splittingRootEquivOver h5 p hp hdeg).symm i :
      p.SplittingField) =
    ((splittingRootEquivOver h5 p hp hdeg).symm
      ((splittingRootEquivOver h5 p hp hdeg)
        (σ • (splittingRootEquivOver h5 p hp hdeg).symm i)) :
          p.SplittingField)
  rw [(splittingRootEquivOver h5 p hp hdeg).symm_apply_apply]
  rfl

theorem splittingRootTupleOver_injective
    {F : Type*} [Field F] (h5 : (5 : F) ≠ 0) (p : Polynomial F)
    (hp : Irreducible p) (hdeg : p.natDegree = 5) :
    Function.Injective (splittingRootTupleOver h5 p hp hdeg) := by
  intro i j hij
  apply (splittingRootEquivOver h5 p hp hdeg).symm.injective
  apply Subtype.ext
  exact hij

theorem splittingRootTupleOver_isRoot
    {F : Type*} [Field F] (h5 : (5 : F) ≠ 0) (p : Polynomial F)
    (hp : Irreducible p) (hdeg : p.natDegree = 5) (i : Fin 5) :
    (p.map (algebraMap F p.SplittingField)).IsRoot
      (splittingRootTupleOver h5 p hp hdeg i) := by
  rw [Polynomial.IsRoot.def, eval_map, ← aeval_def]
  exact (mem_rootSet.mp
    ((splittingRootEquivOver h5 p hp hdeg).symm i).property).2

/-- The sum of the chosen roots belongs to the base field: every Galois
automorphism merely permutes the tuple, and the fixed field of the canonical
separable splitting extension is the base field. -/
theorem splittingRootTupleOver_sum_mem_range
    {F : Type*} [Field F] (h5 : (5 : F) ≠ 0) (p : Polynomial F)
    (hp : Irreducible p) (hdeg : p.natDegree = 5) :
    (∑ i : Fin 5, splittingRootTupleOver h5 p hp hdeg i) ∈
      Set.range (algebraMap F p.SplittingField) := by
  letI : p.IsSplittingField F p.SplittingField :=
    Polynomial.IsSplittingField.splittingField p
  letI : FiniteDimensional F p.SplittingField :=
    IsSplittingField.finiteDimensional p.SplittingField p
  letI : IsGalois F p.SplittingField :=
    IsGalois.of_separable_splitting_field
      (irreducible_quintic_separable_of_five_ne_zero h5 hp hdeg)
  rw [IsGalois.mem_range_algebraMap_iff_fixed]
  intro σ
  rw [map_sum]
  calc
    (∑ i : Fin 5, σ (splittingRootTupleOver h5 p hp hdeg i)) =
        ∑ i : Fin 5, splittingRootTupleOver h5 p hp hdeg
          (splittingRootPermutationHomOver h5 p hp hdeg σ i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact gal_maps_splittingRootTupleOver h5 p hp hdeg σ i
    _ = ∑ i : Fin 5, splittingRootTupleOver h5 p hp hdeg i :=
      Equiv.sum_comp (splittingRootPermutationHomOver h5 p hp hdeg σ)
        (splittingRootTupleOver h5 p hp hdeg)

/-- For every irreducible quintic under `5 ≠ 0`, the canonical splitting
field contains an ordered list of all five distinct roots and a Galois
automorphism acting on that ordering as the literal standard five-cycle.

Both witnesses use classical choice.  The theorem asserts existence, not a
canonical algorithm selecting them. -/
theorem exists_splittingField_fiveCycle_root_data_of_irreducible_quintic
    {F : Type*} [Field F] (h5 : (5 : F) ≠ 0) (p : Polynomial F)
    (hp : Irreducible p) (hdeg : p.natDegree = 5) :
    ∃ (r : Fin 5 → p.SplittingField) (σ : p.Gal),
      Function.Injective r ∧
      (∀ k, (p.map (algebraMap F p.SplittingField)).IsRoot (r k)) ∧
      r 0 + r 1 + r 2 + r 3 + r 4 ∈
        Set.range (algebraMap F p.SplittingField) ∧
      ∀ k, σ (r k) = r (fiveCycle k) := by
  let H := splittingRootPermutationGroupOver h5 p hp hdeg
  letI : MulAction.IsPretransitive H (Fin 5) :=
    splittingRootPermutationGroupOver_isPretransitive h5 p hp hdeg
  obtain ⟨g, hg⟩ := exists_map_conj_standardC5_le_of_pretransitive H
  have hcycle : g * fiveCycle * g⁻¹ ∈ H := by
    apply hg
    exact ⟨fiveCycle, Subgroup.mem_zpowers fiveCycle,
      MulAut.conj_apply g fiveCycle⟩
  obtain ⟨σ, hσ⟩ := hcycle
  let r₀ := splittingRootTupleOver h5 p hp hdeg
  let r : Fin 5 → p.SplittingField := fun i ↦ r₀ (g i)
  have hr : Function.Injective r :=
    (splittingRootTupleOver_injective h5 p hp hdeg).comp g.injective
  have hroots : ∀ k,
      (p.map (algebraMap F p.SplittingField)).IsRoot (r k) :=
    fun k ↦ splittingRootTupleOver_isRoot h5 p hp hdeg (g k)
  have hsum : r 0 + r 1 + r 2 + r 3 + r 4 ∈
      Set.range (algebraMap F p.SplittingField) := by
    have hsum' : (∑ i : Fin 5, r i) ∈
        Set.range (algebraMap F p.SplittingField) := by
      rw [show (∑ i : Fin 5, r i) = ∑ i : Fin 5, r₀ i by
        exact Equiv.sum_comp g r₀]
      exact splittingRootTupleOver_sum_mem_range h5 p hp hdeg
    simpa [Fin.sum_univ_succ, r, add_assoc] using hsum'
  have hcycle' : ∀ k, σ (r k) = r (fiveCycle k) := by
    intro k
    rw [gal_maps_splittingRootTupleOver h5 p hp hdeg σ (g k)]
    change r₀ ((splittingRootPermutationHomOver h5 p hp hdeg σ) (g k)) = _
    rw [hσ]
    simp
    rfl
  exact ⟨r, σ, hr, hroots, hsum, hcycle'⟩

/-- Literal scalar-resolvent separability for an arbitrary irreducible
degree-five polynomial over a field in which five is nonzero. -/
theorem exists_scalarResolvent_separable_of_irreducible_quintic_over
    {F : Type*} [Field F] (h5 : (5 : F) ≠ 0) (p : Polynomial F)
    (hp : Irreducible p) (hdeg : p.natDegree = 5) :
    ∃ r : Fin 5 → p.SplittingField, (scalarResolvent r).Separable := by
  obtain ⟨r, σ, hr, hroots, hsum, hcycle⟩ :=
    exists_splittingField_fiveCycle_root_data_of_irreducible_quintic
      h5 p hp hdeg
  refine ⟨r, ?_⟩
  exact scalarResolvent_separable_of_irreducible_fiveCycle_action_over
    h5 p hp hdeg r hr (hroots 1) hsum σ.toRingHom hcycle

end LeanProofs.PolynomialFormulas.FrobeniusDummitResolvent
