import PolynomialFormulas.LazardQuinticCoherentAlternateInvariant
import PolynomialFormulas.LazardQuinticCoherentAlternateRadicalTower
import PolynomialFormulas.LazardQuinticDeterminantBridge
import PolynomialFormulas.LazardQuinticInvariantDescent
import PolynomialFormulas.LazardQuinticInvariantSystemMap
import PolynomialFormulas.LazardQuinticRootOrderingF20
import PolynomialFormulas.LazardGeneralResolventExplicit

/-!
# Galois descent for the corrected alternate Lazard projections

The denominator-safe alternate radical tower reconstructs the roots from four
corrected projection values.  Its generic field theorem quite properly asks
that those four values belong to the coefficient field.  This file discharges
that premise in the situation in which it is actually used.

There are three layers.

* In any finite Galois overfield containing both the ordered roots and a
  primitive fifth root, an `F20` action on the roots makes every corrected
  projection Galois fixed.  The image of the primitive root is *derived* to
  be one of its four primitive powers; it is not an extra action certificate.
* `LazardGeneralResolventExplicit.RootTuplePresentation`, a base-field theta
  value, and injectivity of the six theta values derive that `F20` action for
  the representative-selected root ordering in a common overfield.
* For an irreducible depressed rational quintic, the existing
  `exists_rootOrdering_with_standardF20_galois_action` theorem supplies the
  selected ordering directly.  The final theorem constructs its rational
  invariant data and invokes the complete alternate radical tower without any
  caller-supplied projection-membership hypotheses.

The rational final theorem is stated in the canonical splitting field when
that field itself contains a primitive fifth root.  The preceding common-
overfield theorem is the interface to use when the primitive root is present
only after passing to a finite Galois compositum.
-/

open Polynomial

namespace LeanProofs.PolynomialFormulas.LazardQuintic

open IntermediateField
open Fin5Solvable FrobeniusDummitResolvent
open ComputableDummitCoefficients
open LeanProofs.PolynomialFormulas.LazardOptimality
open QuinticScalarResolventCriterion

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable local instance {α : Type*} : DecidableEq α := Classical.decEq α

/-! ## Naturality and the four possible images of `omega` -/

section PrimitiveFifthRootImages

variable {K : Type*} [Field K] [CharZero K]

/-- Transport a packaged primitive fifth root through an injective field map. -/
def FifthRootOfUnity.mapRingHom
    {L : Type*} [Field L]
    (omega : FifthRootOfUnity K) (f : K →+* L) : FifthRootOfUnity L where
  value := f omega.value
  primitive := omega.primitive.map_of_injective f.injective

@[simp] theorem FifthRootOfUnity.mapRingHom_value
    {L : Type*} [Field L]
    (omega : FifthRootOfUnity K) (f : K →+* L) :
    (omega.mapRingHom f).value = f omega.value :=
  rfl

/-- Iterating the already-proved square-generator invariance gives invariance
under the fourth primitive power. -/
theorem rootCoherentAlternateProjectionValues_fourth
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootCoherentAlternateProjectionValues omega.fourth x =
      rootCoherentAlternateProjectionValues omega x := by
  rw [← FifthRootOfUnity.squared_squared]
  exact (rootCoherentAlternateProjectionValues_squared omega.squared x).trans
    (rootCoherentAlternateProjectionValues_squared omega x)

/-- A third iteration has exponent `2^3 = 8 = 3 (mod 5)`. -/
theorem rootCoherentAlternateProjectionValues_cubed
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootCoherentAlternateProjectionValues omega.cubed x =
      rootCoherentAlternateProjectionValues omega x := by
  rw [← FifthRootOfUnity.squared_squared_squared]
  exact
    (rootCoherentAlternateProjectionValues_squared
      omega.squared.squared x).trans
      ((rootCoherentAlternateProjectionValues_squared omega.squared x).trans
        (rootCoherentAlternateProjectionValues_squared omega x))

/-- Corrected projection values commute with scalar extension.  This is the
root-value version of `map_coherentAlternateCoordinatePolynomial`. -/
theorem map_rootCoherentAlternateProjectionValues
    {L : Type*} [Field L] [CharZero L]
    (f : K →+* L) (omega : FifthRootOfUnity K)
    (x : Fin 5 → K) (j : Fin 4) :
    f (rootCoherentAlternateProjectionValues omega x j) =
      rootCoherentAlternateProjectionValues (omega.mapRingHom f)
        (fun k ↦ f (x k)) j := by
  calc
    f (rootCoherentAlternateProjectionValues omega x j) =
        f (MvPolynomial.eval x
          (coherentAlternateCoordinatePolynomial omega j)) := by
      rw [eval_coherentAlternateCoordinatePolynomial]
    _ = MvPolynomial.eval (f ∘ x)
        (MvPolynomial.map f
          (coherentAlternateCoordinatePolynomial omega j)) :=
      MvPolynomial.map_eval f x _
    _ = MvPolynomial.eval (f ∘ x)
        (coherentAlternateCoordinatePolynomial (omega.mapRingHom f) j) := by
      rw [map_coherentAlternateCoordinatePolynomial f omega
        (omega.mapRingHom f) (by rfl) j]
    _ = rootCoherentAlternateProjectionValues (omega.mapRingHom f)
        (fun k ↦ f (x k)) j := by
      rw [eval_coherentAlternateCoordinatePolynomial]
      rfl

/-- An automorphism sends a primitive fifth root to exactly one of its four
primitive powers.  The impossible exponent zero is eliminated by coprimality,
not by a caller-supplied cyclotomic-action certificate. -/
theorem FifthRootOfUnity.mapRingHom_algEquiv_cases
    {F : Type*} [Field F] [Algebra F K]
    (omega : FifthRootOfUnity K) (sigma : K ≃ₐ[F] K) :
    omega.mapRingHom sigma.toRingHom = omega ∨
    omega.mapRingHom sigma.toRingHom = omega.squared ∨
      omega.mapRingHom sigma.toRingHom = omega.cubed ∨
      omega.mapRingHom sigma.toRingHom = omega.fourth := by
  exact omega.primitive_cases (omega.mapRingHom sigma.toRingHom)

/-- Consequently every Galois image of the primitive fifth root gives the
same corrected projection vector. -/
theorem rootCoherentAlternateProjectionValues_mapRingHom_algEquiv
    {F : Type*} [Field F] [Algebra F K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K)
    (sigma : K ≃ₐ[F] K) :
    rootCoherentAlternateProjectionValues
        (omega.mapRingHom sigma.toRingHom) x =
      rootCoherentAlternateProjectionValues omega x := by
  rcases omega.mapRingHom_algEquiv_cases sigma with h | h
  · rw [h]
  rcases h with h | h
  · rw [h]
    exact rootCoherentAlternateProjectionValues_squared omega x
  rcases h with h | h
  · rw [h]
    exact rootCoherentAlternateProjectionValues_cubed omega x
  · rw [h]
    exact rootCoherentAlternateProjectionValues_fourth omega x

end PrimitiveFifthRootImages

/-! ## Fixed-field descent from an `F20` root action -/

section CommonGaloisDescent

variable {F K : Type*} [Field F] [Field K] [CharZero K] [Algebra F K]

/-- The corrected coordinate is fixed by a Galois automorphism whenever that
automorphism permutes the ordered roots through the standard `F20`. -/
theorem rootCoherentAlternateProjectionValue_fixed_of_standardF20_action
    (omega : FifthRootOfUnity K) (x : Fin 5 → K)
    (hrootAction : ∀ sigma : K ≃ₐ[F] K,
      ∃ g : Fin5Solvable.S5, g ∈ standardF20 ∧
        ∀ k : Fin 5, sigma (x k) = x (g k))
    (j : Fin 4) (sigma : K ≃ₐ[F] K) :
    sigma (rootCoherentAlternateProjectionValues omega x j) =
      rootCoherentAlternateProjectionValues omega x j := by
  obtain ⟨g, hg, haction⟩ := hrootAction sigma
  let omegaSigma : FifthRootOfUnity K :=
    omega.mapRingHom sigma.toRingHom
  calc
    sigma (rootCoherentAlternateProjectionValues omega x j) =
        rootCoherentAlternateProjectionValues omegaSigma
          (fun k ↦ sigma (x k)) j :=
      map_rootCoherentAlternateProjectionValues sigma.toRingHom omega x j
    _ = rootCoherentAlternateProjectionValues omegaSigma
        (permuteRootTuple x g) j := by
      rw [show (fun k ↦ sigma (x k)) = permuteRootTuple x g by
        funext k
        exact haction k]
    _ = rootCoherentAlternateProjectionValues omegaSigma x j :=
      congrFun
        (rootCoherentAlternateProjectionValues_permute_of_mem_standardF20
          omegaSigma x g hg) j
    _ = rootCoherentAlternateProjectionValues omega x j :=
      congrFun
        (rootCoherentAlternateProjectionValues_mapRingHom_algEquiv
          omega x sigma) j

/-- Fixed-field descent for each of the four corrected values in an arbitrary
finite Galois common overfield. -/
theorem rootCoherentAlternateProjectionValue_mem_range_of_standardF20_action
    [FiniteDimensional F K] [IsGalois F K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K)
    (hrootAction : ∀ sigma : K ≃ₐ[F] K,
      ∃ g : Fin5Solvable.S5, g ∈ standardF20 ∧
        ∀ k : Fin 5, sigma (x k) = x (g k))
    (j : Fin 4) :
    rootCoherentAlternateProjectionValues omega x j ∈
      Set.range (algebraMap F K) := by
  rw [IsGalois.mem_range_algebraMap_iff_fixed]
  intro sigma
  exact rootCoherentAlternateProjectionValue_fixed_of_standardF20_action
    omega x hrootAction j sigma

/-- Intermediate-field form consumed by the radical-tower API. -/
theorem rootCoherentAlternateProjectionValue_mem_bot_of_standardF20_action
    [FiniteDimensional F K] [IsGalois F K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K)
    (hrootAction : ∀ sigma : K ≃ₐ[F] K,
      ∃ g : Fin5Solvable.S5, g ∈ standardF20 ∧
        ∀ k : Fin 5, sigma (x k) = x (g k))
    (j : Fin 4) :
    rootCoherentAlternateProjectionValues omega x j ∈
      (⊥ : IntermediateField F K) := by
  obtain ⟨a, ha⟩ :=
    rootCoherentAlternateProjectionValue_mem_range_of_standardF20_action
      omega x hrootAction j
  rw [← ha]
  exact (⊥ : IntermediateField F K).algebraMap_mem a

/-- Generic fixed-field descent for the invariant-membership package used by
the radical tower.  A depressed root presentation supplies the invariant
relations.  Nonsingularity of Figure 3 then propagates a base-field `i4` to
all five invariant coordinates, which are descended coordinatewise through
the finite Galois fixed-field theorem.  The eight radicand memberships are
then the scalar-extension theorem `radicalInvariantDataIn_bot_map`; no
caller-supplied membership certificate remains. -/
theorem radicalInvariantDataIn_bot_of_depressed_root_i4
    [CharZero F] [FiniteDimensional F K] [IsGalois F K]
    (c : DepressedQuintic F) (x : Fin 5 → K)
    (hc : depressedOfRoots x = c.map (algebraMap F K))
    (hsum : elementaryTuple x 0 = 0)
    (hdet : (invariantSystemMatrix c).det ≠ 0)
    (hi4 : ∃ q : F, algebraMap F K q = (rootInvariants x).i4) :
    RadicalInvariantDataIn F K (⊥ : IntermediateField F K)
      (depressedOfRoots x) (rootInvariants x) := by
  let phi := algebraMap F K
  let i0 := rootInvariants x
  have hrelations : InvariantRelations (c.map phi) i0 := by
    dsimp only [i0]
    rw [← hc]
    exact rootInvariantRelations x hsum
  have hdetK : (invariantSystemMatrix (c.map phi)).det ≠ 0 :=
    invariantSystemMatrix_det_ne_zero_map c phi hdet
  have hcoeff (sigma : K ≃ₐ[F] K) :
      (c.map phi).map sigma.toRingHom = c.map phi := by
    cases c
    simp [DepressedQuintic.map, phi]
  obtain ⟨q4, hq4⟩ := hi4
  change phi q4 = i0.i4 at hq4
  have hi4fixed (sigma : K ≃ₐ[F] K) : sigma i0.i4 = i0.i4 := by
    rw [← hq4]
    exact sigma.commutes q4
  have hfixed (sigma : K ≃ₐ[F] K) : i0.map sigma.toRingHom = i0 :=
    hrelations.map_eq_self_of_i4_fixed hdetK sigma.toRingHom
      (hcoeff sigma) (hi4fixed sigma)
  have hcoord (coord : Invariants K → K)
      (hmap : ∀ (j : Invariants K) (sigma : K ≃ₐ[F] K),
        coord (j.map sigma.toRingHom) = sigma (coord j)) :
      coord i0 ∈ Set.range (algebraMap F K) := by
    rw [IsGalois.mem_range_algebraMap_iff_fixed]
    intro sigma
    rw [← hmap i0 sigma, hfixed sigma]
  have hi5 := hcoord Invariants.i5 (by intro j sigma; rfl)
  have hi6 := hcoord Invariants.i6 (by intro j sigma; rfl)
  have hi7 := hcoord Invariants.i7 (by intro j sigma; rfl)
  have hi8 := hcoord Invariants.i8 (by intro j sigma; rfl)
  obtain ⟨q5, hq5⟩ := hi5
  obtain ⟨q6, hq6⟩ := hi6
  obtain ⟨q7, hq7⟩ := hi7
  obtain ⟨q8, hq8⟩ := hi8
  let j : Invariants F := ⟨q4, q5, q6, q7, q8⟩
  have hj : j.map phi = i0 := by
    generalize hroot : rootInvariants x = i0
    cases i0
    simp only [j, Invariants.map] at hq4 hq5 hq6 hq7 hq8 ⊢
    simp_all [i0]
    exact ⟨hq5, hq6, hq7, hq8⟩
  rw [hc]
  change RadicalInvariantDataIn F K (⊥ : IntermediateField F K)
    (c.map phi) i0
  rw [← hj]
  exact radicalInvariantDataIn_bot_map F K c j

/-- Adjoining a primitive fifth root is itself one fifth-radical step. -/
theorem fifthRootOfUnity_adjoin_isRadical
    (omega : FifthRootOfUnity K) :
    IsRadicalExtension F K (⊥ : IntermediateField F K) F⟮omega.value⟯ := by
  have hpow : omega.value ^ 5 ∈ (⊥ : IntermediateField F K) := by
    rw [omega.primitive.pow_eq_one]
    exact one_mem _
  have h :=
    (isRadicalExtension_refl F K (⊥ : IntermediateField F K)).adjoin_fifth
      F K omega.value hpow
  simpa using h

/-- The direct adapter requested by the alternate radical tower: in a finite
Galois field with standard-`F20` root action, neither the four projection
membership facts nor radicality of the primitive-root adjunction is supplied
by the caller. -/
theorem rootCoherentAlternate_radical_contains_and_reconstructs_of_standardF20_action
    [DecidableEq K] [FiniteDimensional F K] [IsGalois F K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K)
    (hsum : elementaryTuple x 0 = 0)
    (hinjective : Function.Injective x)
    (hepsilon : rootEpsilon omega x ≠ 0)
    (hdata : RadicalInvariantDataIn F K (⊥ : IntermediateField F K)
      (depressedOfRoots x) (rootInvariants x))
    (hrootAction : ∀ sigma : K ≃ₐ[F] K,
      ∃ g : Fin5Solvable.S5, g ∈ standardF20 ∧
        ∀ k : Fin 5, sigma (x k) = x (g k)) :
    let d := rootCoherentAlternateFourierCertificate
      omega x hsum hinjective hepsilon
    IsRadicalExtension F K (⊥ : IntermediateField F K)
        (d.generatedFieldWithRootOfUnity F K
          (⊥ : IntermediateField F K) omega) ∧
      (∀ k : Fin 5,
        d.solve omega k ∈ d.generatedFieldWithRootOfUnity F K
          (⊥ : IntermediateField F K) omega) ∧
      (fun k ↦ d.solve omega k) =
        reversedRootTuple
          (rootsForBranch x
            (correctedQuadraticBranch
              (depressedOfRoots x) (rootInvariants x)
              (rootQuadraticTriple omega x))) := by
  exact rootCoherentAlternate_radical_contains_and_reconstructs
    F (⊥ : IntermediateField F K) omega x hsum hinjective hepsilon hdata
      (fun j ↦
        rootCoherentAlternateProjectionValue_mem_bot_of_standardF20_action
          omega x hrootAction j)
      (fifthRootOfUnity_adjoin_isRadical omega)

/-- Version of the common-Galois theorem in which the remaining invariant
membership package is itself descended from a depressed base presentation,
a base-field `i4`, and the nonsingular Figure-3 system. -/
theorem
    rootCoherentAlternate_radical_contains_and_reconstructs_of_depressed_root_i4
    [CharZero F] [DecidableEq K] [FiniteDimensional F K] [IsGalois F K]
    (c : DepressedQuintic F) (omega : FifthRootOfUnity K) (x : Fin 5 → K)
    (hc : depressedOfRoots x = c.map (algebraMap F K))
    (hsum : elementaryTuple x 0 = 0)
    (hdet : (invariantSystemMatrix c).det ≠ 0)
    (hi4 : ∃ q : F, algebraMap F K q = (rootInvariants x).i4)
    (hinjective : Function.Injective x)
    (hepsilon : rootEpsilon omega x ≠ 0)
    (hrootAction : ∀ sigma : K ≃ₐ[F] K,
      ∃ g : Fin5Solvable.S5, g ∈ standardF20 ∧
        ∀ k : Fin 5, sigma (x k) = x (g k)) :
    let d := rootCoherentAlternateFourierCertificate
      omega x hsum hinjective hepsilon
    IsRadicalExtension F K (⊥ : IntermediateField F K)
        (d.generatedFieldWithRootOfUnity F K
          (⊥ : IntermediateField F K) omega) ∧
      (∀ k : Fin 5,
        d.solve omega k ∈ d.generatedFieldWithRootOfUnity F K
          (⊥ : IntermediateField F K) omega) ∧
      (fun k ↦ d.solve omega k) =
        reversedRootTuple
          (rootsForBranch x
            (correctedQuadraticBranch
              (depressedOfRoots x) (rootInvariants x)
              (rootQuadraticTriple omega x))) := by
  have hdata := radicalInvariantDataIn_bot_of_depressed_root_i4
    c x hc hsum hdet hi4
  exact
    rootCoherentAlternate_radical_contains_and_reconstructs_of_standardF20_action
      omega x hsum hinjective hepsilon hdata hrootAction

end CommonGaloisDescent

/-! ## Deriving the `F20` action from a literal common-overfield presentation -/

section CommonOverfieldPresentation

variable {F K : Type*} [Field F] [Field K] [CharZero K] [Algebra F K]
variable [FiniteDimensional F K] [IsGalois F K]

/-- Reorder a literal root presentation by the representative selected by a
base-field theta value. -/
def selectedCommonRootTuple
    (roots : Fin 5 → K) (i : Fin 6) : Fin 5 → K :=
  fun k ↦ roots (FrobeniusDummitResolvent.representative i k)

/-- Common-overfield analogue of
`exists_rootOrdering_with_standardF20_galois_action`: the root permutation is
derived from `RootTuplePresentation`, and a base theta value conjugates it
into the standard `F20`. -/
theorem selectedCommonRootTuple_standardF20_galois_action
    (p : F[X]) (roots : Fin 5 → K)
    (presentation : LazardGeneralResolventExplicit.RootTuplePresentation p roots)
    (i : Fin 6)
    (hthetaBase : ∃ q : F,
      algebraMap F K q = thetaValue roots i)
    (hthetaInjective : Function.Injective (thetaValue roots)) :
    ∀ sigma : K ≃ₐ[F] K,
      ∃ g : Fin5Solvable.S5, g ∈ standardF20 ∧
        ∀ k : Fin 5,
          sigma (selectedCommonRootTuple roots i k) =
            selectedCommonRootTuple roots i (g k) := by
  intro sigma
  let raw : Fin5Solvable.S5 :=
    LazardGeneralResolventExplicit.rootTupleAction p roots presentation sigma
  let g : Fin5Solvable.S5 :=
    (FrobeniusDummitResolvent.representative i)⁻¹ * raw *
      FrobeniusDummitResolvent.representative i
  have hfixed : sigma (thetaValue roots i) = thetaValue roots i := by
    obtain ⟨q, hq⟩ := hthetaBase
    rw [← hq]
    exact sigma.commutes q
  obtain ⟨j, hrename⟩ := rename_thetaOrbit_exists raw i
  have hmap : sigma (thetaValue roots i) = thetaValue roots j := by
    exact map_thetaValue_of_maps_roots sigma.toRingHom roots roots raw i j
      (LazardGeneralResolventExplicit.rootTupleAction_equivariant
        p roots presentation sigma) hrename
  have hji : j = i :=
    hthetaInjective (hmap.symm.trans hfixed)
  subst j
  have hmemConjugate :
      raw ∈ standardF20.map
        (MulAut.conj
          (FrobeniusDummitResolvent.representative i)).toMonoidHom :=
    (rename_thetaOrbit_eq_self_iff_mem_conjugate raw i).1 hrename
  rw [Subgroup.mem_map_equiv] at hmemConjugate
  change
    (FrobeniusDummitResolvent.representative i)⁻¹ * raw *
        FrobeniusDummitResolvent.representative i ∈ standardF20
    at hmemConjugate
  have hg : g ∈ standardF20 := by
    exact hmemConjugate
  refine ⟨g, hg, ?_⟩
  intro k
  change sigma
      (roots (FrobeniusDummitResolvent.representative i k)) =
    roots (FrobeniusDummitResolvent.representative i (g k))
  rw [LazardGeneralResolventExplicit.rootTupleAction_equivariant
    p roots presentation sigma]
  congr 1
  simp [g, raw]

/-- Thus every corrected coordinate of the representative-selected common
root tuple belongs to the original coefficient field. -/
theorem selectedCommonRootTuple_projection_mem_bot
    (p : F[X]) (roots : Fin 5 → K)
    (presentation : LazardGeneralResolventExplicit.RootTuplePresentation p roots)
    (i : Fin 6)
    (hthetaBase : ∃ q : F,
      algebraMap F K q = thetaValue roots i)
    (hthetaInjective : Function.Injective (thetaValue roots))
    (omega : FifthRootOfUnity K) (j : Fin 4) :
    rootCoherentAlternateProjectionValues omega
        (selectedCommonRootTuple roots i) j ∈
      (⊥ : IntermediateField F K) := by
  exact rootCoherentAlternateProjectionValue_mem_bot_of_standardF20_action
    omega (selectedCommonRootTuple roots i)
      (selectedCommonRootTuple_standardF20_galois_action
        p roots presentation i hthetaBase hthetaInjective) j

/-- Full common-overfield radical reconstruction with the four projection
memberships derived from the root presentation and selected theta value. -/
theorem selectedCommonRootTuple_radical_contains_and_reconstructs
    [DecidableEq K]
    (p : F[X]) (roots : Fin 5 → K)
    (presentation : LazardGeneralResolventExplicit.RootTuplePresentation p roots)
    (i : Fin 6)
    (hthetaBase : ∃ q : F,
      algebraMap F K q = thetaValue roots i)
    (hthetaInjective : Function.Injective (thetaValue roots))
    (omega : FifthRootOfUnity K)
    (hsum : elementaryTuple (selectedCommonRootTuple roots i) 0 = 0)
    (hepsilon : rootEpsilon omega (selectedCommonRootTuple roots i) ≠ 0)
    (hdata : RadicalInvariantDataIn F K (⊥ : IntermediateField F K)
      (depressedOfRoots (selectedCommonRootTuple roots i))
      (rootInvariants (selectedCommonRootTuple roots i))) :
    let x := selectedCommonRootTuple roots i
    let d := rootCoherentAlternateFourierCertificate
      omega x hsum
        ((presentation.nodup).comp
          (FrobeniusDummitResolvent.representative i).injective)
        hepsilon
    IsRadicalExtension F K (⊥ : IntermediateField F K)
        (d.generatedFieldWithRootOfUnity F K
          (⊥ : IntermediateField F K) omega) ∧
      (∀ k : Fin 5,
        d.solve omega k ∈ d.generatedFieldWithRootOfUnity F K
          (⊥ : IntermediateField F K) omega) ∧
      (fun k ↦ d.solve omega k) =
        reversedRootTuple
          (rootsForBranch x
            (correctedQuadraticBranch
              (depressedOfRoots x) (rootInvariants x)
              (rootQuadraticTriple omega x))) := by
  let x := selectedCommonRootTuple roots i
  have hx : Function.Injective x :=
    presentation.nodup.comp
      (FrobeniusDummitResolvent.representative i).injective
  exact
    rootCoherentAlternate_radical_contains_and_reconstructs_of_standardF20_action
      omega x hsum hx hepsilon hdata
        (selectedCommonRootTuple_standardF20_galois_action
          p roots presentation i hthetaBase hthetaInjective)

/-- Depressed-base specialization of the common-overfield wrapper with no
`hdata` premise.  The base-field theta value supplies the descended `i4`;
the preceding fixed-field theorem supplies the remaining invariant
coordinates and hence the complete radical-membership package. -/
theorem
    selectedCommonRootTuple_radical_contains_and_reconstructs_of_depressed_base
    [CharZero F] [DecidableEq K]
    (c : DepressedQuintic F) (roots : Fin 5 → K)
    (presentation :
      LazardGeneralResolventExplicit.RootTuplePresentation c.polynomial roots)
    (i : Fin 6)
    (hthetaBase : ∃ q : F,
      algebraMap F K q = thetaValue roots i)
    (hthetaInjective : Function.Injective (thetaValue roots))
    (omega : FifthRootOfUnity K)
    (hc : depressedOfRoots (selectedCommonRootTuple roots i) =
      c.map (algebraMap F K))
    (hsum : elementaryTuple (selectedCommonRootTuple roots i) 0 = 0)
    (hdet : (invariantSystemMatrix c).det ≠ 0)
    (hepsilon : rootEpsilon omega (selectedCommonRootTuple roots i) ≠ 0) :
    let x := selectedCommonRootTuple roots i
    let d := rootCoherentAlternateFourierCertificate
      omega x hsum
        ((presentation.nodup).comp
          (FrobeniusDummitResolvent.representative i).injective)
        hepsilon
    IsRadicalExtension F K (⊥ : IntermediateField F K)
        (d.generatedFieldWithRootOfUnity F K
          (⊥ : IntermediateField F K) omega) ∧
      (∀ k : Fin 5,
        d.solve omega k ∈ d.generatedFieldWithRootOfUnity F K
          (⊥ : IntermediateField F K) omega) ∧
      (fun k ↦ d.solve omega k) =
        reversedRootTuple
          (rootsForBranch x
            (correctedQuadraticBranch
              (depressedOfRoots x) (rootInvariants x)
              (rootQuadraticTriple omega x))) := by
  let x := selectedCommonRootTuple roots i
  have hx : Function.Injective x :=
    presentation.nodup.comp
      (FrobeniusDummitResolvent.representative i).injective
  have hi4 : ∃ q : F, algebraMap F K q = (rootInvariants x).i4 := by
    obtain ⟨q, hq⟩ := hthetaBase
    refine ⟨q, ?_⟩
    change algebraMap F K q =
      thetaFormula
        (fun k ↦ roots (FrobeniusDummitResolvent.representative i k))
    rw [← thetaValue_eq_thetaFormula]
    exact hq
  exact
    rootCoherentAlternate_radical_contains_and_reconstructs_of_depressed_root_i4
      c omega x hc hsum hdet hi4 hx hepsilon
        (selectedCommonRootTuple_standardF20_galois_action
          c.polynomial roots presentation i hthetaBase hthetaInjective)

end CommonOverfieldPresentation

/-! ## Rational resolvent-root specialization -/

noncomputable section

/-- The rational resolvent-selected ordering has all four corrected
projections in the rational bottom field.  This is the small direct bridge
that removes `hprojections` from callers using `RootOrderingF20`. -/
theorem exists_rootOrdering_with_coherentAlternateProjection_descent
    (c : DepressedQuintic ℚ) (hp : Irreducible c.polynomial)
    (hq : ∃ q : ℚ, (resolventPolynomial c).IsRoot q)
    (omega : FifthRootOfUnity c.polynomial.SplittingField) :
    ∃ x : Fin 5 → c.polynomial.SplittingField,
      Function.Injective x ∧
      elementaryTuple x = depressedElementary
        (c.map (algebraMap ℚ c.polynomial.SplittingField)) ∧
      (∃ q : ℚ, algebraMap ℚ c.polynomial.SplittingField q =
        (rootInvariants x).i4) ∧
    ∀ j : Fin 4,
        rootCoherentAlternateProjectionValues omega x j ∈
          (⊥ : IntermediateField ℚ c.polynomial.SplittingField) := by
  letI : DecidableEq c.polynomial.SplittingField := Classical.decEq _
  letI : c.polynomial.IsSplittingField ℚ c.polynomial.SplittingField :=
    Polynomial.IsSplittingField.splittingField c.polynomial
  letI : FiniteDimensional ℚ c.polynomial.SplittingField :=
    IsSplittingField.finiteDimensional c.polynomial.SplittingField c.polynomial
  haveI : IsGalois ℚ c.polynomial.SplittingField :=
    IsGalois.of_separable_splitting_field hp.separable
  obtain ⟨x, hx, helementary, hi4, hrootAction⟩ :=
    exists_rootOrdering_with_standardF20_galois_action c hp hq
  have htest : IsGalois ℚ c.polynomial.SplittingField := inferInstance
  refine ⟨x, hx, helementary, hi4, ?_⟩
  intro j
  exact @rootCoherentAlternateProjectionValue_mem_bot_of_standardF20_action
    ℚ c.polynomial.SplittingField inferInstance inferInstance inferInstance
      inferInstance inferInstance htest omega x hrootAction j

/-- Actual rational resolvent-solvable application.  The theorem selects one
ordered root tuple, derives its complete rational invariant tuple, derives
all four corrected projection descents, builds the two-square/four-fifth
tower, and proves exact reconstruction.  In particular, neither
`hprojections` nor a cyclotomic-action certificate occurs in the statement. -/
theorem exists_resolventRoot_coherentAlternate_radical_contains_and_reconstructs
    (c : DepressedQuintic ℚ) (hp : Irreducible c.polynomial)
    (hq : ∃ q : ℚ, (resolventPolynomial c).IsRoot q)
    (omega : FifthRootOfUnity c.polynomial.SplittingField) :
    ∃ (x : Fin 5 → c.polynomial.SplittingField)
        (j : Invariants ℚ)
        (d : CoherentAlternateFourierCertificate
          (depressedOfRoots x) (rootInvariants x)),
      Function.Injective x ∧
      elementaryTuple x = depressedElementary
        (c.map (algebraMap ℚ c.polynomial.SplittingField)) ∧
      InvariantRelations c j ∧
      j.map (algebraMap ℚ c.polynomial.SplittingField) = rootInvariants x ∧
      IsRadicalExtension ℚ c.polynomial.SplittingField
          (⊥ : IntermediateField ℚ c.polynomial.SplittingField)
          (d.generatedFieldWithRootOfUnity ℚ c.polynomial.SplittingField
            (⊥ : IntermediateField ℚ c.polynomial.SplittingField) omega) ∧
      (∀ k : Fin 5,
        d.solve omega k ∈
          d.generatedFieldWithRootOfUnity ℚ c.polynomial.SplittingField
            (⊥ : IntermediateField ℚ c.polynomial.SplittingField) omega) ∧
      (fun k ↦ d.solve omega k) =
        reversedRootTuple
          (rootsForBranch x
        (correctedQuadraticBranch
              (depressedOfRoots x) (rootInvariants x)
              (rootQuadraticTriple omega x))) := by
  letI : DecidableEq c.polynomial.SplittingField := Classical.decEq _
  letI : c.polynomial.IsSplittingField ℚ c.polynomial.SplittingField :=
    Polynomial.IsSplittingField.splittingField c.polynomial
  letI : FiniteDimensional ℚ c.polynomial.SplittingField :=
    IsSplittingField.finiteDimensional c.polynomial.SplittingField c.polynomial
  letI : IsGalois ℚ c.polynomial.SplittingField :=
    IsGalois.of_separable_splitting_field hp.separable
  obtain ⟨x, hx, helementary, hi4, hrootAction⟩ :=
    exists_rootOrdering_with_standardF20_galois_action c hp hq
  let phi := algebraMap ℚ c.polynomial.SplittingField
  have hsum : elementaryTuple x 0 = 0 := by
    rw [helementary]
    simp [depressedElementary]
  have hc : depressedOfRoots x = c.map phi :=
    depressedOfRoots_eq_of_elementaryTuple_eq (c.map phi) x helementary
  have hrelations : InvariantRelations (c.map phi) (rootInvariants x) := by
    rw [← hc]
    exact rootInvariantRelations x hsum
  have hdet : (invariantSystemMatrix (c.map phi)).det ≠ 0 :=
    invariantSystemMatrix_det_ne_zero_map c phi
      (invariantSystemMatrix_det_ne_zero c hp)
  obtain ⟨j, hj, hjmap⟩ :=
    exists_rational_invariants_of_i4_rational c hp (rootInvariants x)
      hrelations hdet hi4
  have hdata : RadicalInvariantDataIn ℚ c.polynomial.SplittingField
      (⊥ : IntermediateField ℚ c.polynomial.SplittingField)
      (depressedOfRoots x) (rootInvariants x) := by
    rw [hc, ← hjmap]
    exact radicalInvariantDataIn_bot_map
      ℚ c.polynomial.SplittingField c j
  have hepsilon : rootEpsilon omega x ≠ 0 :=
    rootEpsilon_ne_zero_of_elementaryTuple_eq c hp x helementary omega
  let d := rootCoherentAlternateFourierCertificate
    omega x hsum hx hepsilon
  have htower :=
    rootCoherentAlternate_radical_contains_and_reconstructs_of_standardF20_action
      omega x hsum hx hepsilon hdata hrootAction
  exact ⟨x, j, d, hx, helementary, hj, hjmap, by simpa [d] using htower⟩

end

end LeanProofs.PolynomialFormulas.LazardQuintic
