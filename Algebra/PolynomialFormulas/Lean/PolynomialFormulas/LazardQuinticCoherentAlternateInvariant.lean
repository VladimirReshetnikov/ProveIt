import PolynomialFormulas.LazardQuinticRootAlternateRecovery
import PolynomialFormulas.LazardQuinticSectionFiveCombinedAction
import PolynomialFormulas.LazardQuinticConcreteInvariantBasis
import PolynomialFormulas.LazardInvariantModule
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.Cyclotomic.Gal

/-!
# The corrected alternate projections as invariant polynomials

The root-level generator calculations alone say only that the *values* of
the corrected alternate projections are unchanged by root reorderings.  This
file constructs the corresponding multivariate polynomials over the field
containing the chosen primitive fifth root and uses polynomial funextensionality
to bundle every coordinate in the `F20` invariant subalgebra.

This is not yet coefficient-field descent.  The coefficients of the
polynomials below live in the ambient field containing `omega`.  To invoke
the concrete rational six-element basis one still needs either:

* a proof that these coefficients descend to the intended coefficient field,
  or
* a scalar-extension theorem transporting the rational concrete basis to
  the field containing `omega`.
-/

open scoped BigOperators
open MvPolynomial Matrix

namespace LeanProofs.PolynomialFormulas.LazardQuintic

open Fin5Solvable FrobeniusDummitResolvent
open LeanProofs.PolynomialFormulas.LazardInvariantModule
open LeanProofs.PolynomialFormulas.LazardQuinticConcreteInvariantBasis

set_option autoImplicit false

/- The concrete basis is built from the explicit scalar action on the nested
   invariant submodule.  Supplying that action locally avoids an expensive
   and ambiguous search through the many subtype scalar instances. -/
noncomputable local instance coherentAlternateInvariantSMul :
    SMul SymmetricFiveRing F20InvariantModule :=
  F20InvariantModule.module.toSMul

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- The corrected projection vector is independent of the Galois-generator
change `omega ↦ omega²`. -/
theorem rootCoherentAlternateProjectionValues_squared
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootCoherentAlternateProjectionValues omega.squared x =
      rootCoherentAlternateProjectionValues omega x := by
  change
    coherentAlternateProjections
        (rootQuadraticTriple omega.squared x).epsilon
        (rootQuadraticTriple omega.squared x).t
        (rootQuadraticTriple omega.squared x).u
        (rootFourierFifthOrbit omega.squared x) = _
  rw [rootQuadraticTriple_squared, rootFourierFifthOrbit_squared]
  exact coherentAlternateProjections_branchTriple_sourceForBranch
    (rootQuadraticTriple omega x) (rootFourierFifthOrbit omega x)
    .rotateNegate

abbrev AlternateRootPolynomial (K : Type*) [CommRing K] :=
  MvPolynomial (Fin 5) K

def alternateRootTPrimePolynomial : AlternateRootPolynomial K :=
  (X 0 - X 1) * (X 1 - X 2) * (X 2 - X 3) *
    (X 3 - X 4) * (X 4 - X 0)

def alternateRootUPrimePolynomial : AlternateRootPolynomial K :=
  (X 0 - X 2) * (X 1 - X 3) * (X 2 - X 4) *
    (X 3 - X 0) * (X 4 - X 1)

def alternateRootEpsilonProductPolynomial : AlternateRootPolynomial K :=
  (X 1 - X 2 - X 3 + X 4) *
    (X 2 - X 3 - X 4 + X 0) *
    (X 3 - X 4 - X 0 + X 1) *
    (X 4 - X 0 - X 1 + X 2) *
    (X 0 - X 1 - X 2 + X 3)

def alternateRootEpsilonPolynomial
    (omega : FifthRootOfUnity K) : AlternateRootPolynomial K :=
  C (fifthRootDiscriminantFactor omega) *
    alternateRootEpsilonProductPolynomial

def alternateRootTPolynomial
    (omega : FifthRootOfUnity K) : AlternateRootPolynomial K :=
  C (omega.value - omega.value ^ 4) * alternateRootTPrimePolynomial +
    C (omega.value ^ 2 - omega.value ^ 3) * alternateRootUPrimePolynomial

def alternateRootFormulaUPolynomial
    (omega : FifthRootOfUnity K) : AlternateRootPolynomial K :=
  -(C (omega.value ^ 2 - omega.value ^ 3) *
      alternateRootTPrimePolynomial -
    C (omega.value - omega.value ^ 4) * alternateRootUPrimePolynomial)

def alternateRootFourierP1Polynomial
    (omega : FifthRootOfUnity K) : AlternateRootPolynomial K :=
  X 0 + C omega.value * X 1 + C (omega.value ^ 2) * X 2 +
    C (omega.value ^ 3) * X 3 + C (omega.value ^ 4) * X 4

def alternateRootFourierP2Polynomial
    (omega : FifthRootOfUnity K) : AlternateRootPolynomial K :=
  X 0 + C (omega.value ^ 2) * X 1 + C (omega.value ^ 4) * X 2 +
    C omega.value * X 3 + C (omega.value ^ 3) * X 4

def alternateRootFourierP3Polynomial
    (omega : FifthRootOfUnity K) : AlternateRootPolynomial K :=
  X 0 + C (omega.value ^ 3) * X 1 + C omega.value * X 2 +
    C (omega.value ^ 4) * X 3 + C (omega.value ^ 2) * X 4

def alternateRootFourierP4Polynomial
    (omega : FifthRootOfUnity K) : AlternateRootPolynomial K :=
  X 0 + C (omega.value ^ 4) * X 1 + C (omega.value ^ 3) * X 2 +
    C (omega.value ^ 2) * X 3 + C omega.value * X 4

/-- The four corrected alternate projection polynomials, before bundling
them with their invariance proofs. -/
def coherentAlternateCoordinatePolynomial
    (omega : FifthRootOfUnity K) : Fin 4 → AlternateRootPolynomial K :=
  let epsilon := alternateRootEpsilonPolynomial omega
  let t := alternateRootTPolynomial omega
  let u := alternateRootFormulaUPolynomial omega
  let s0 := alternateRootFourierP1Polynomial omega ^ 5
  let s1 := alternateRootFourierP2Polynomial omega ^ 5
  let s2 := alternateRootFourierP4Polynomial omega ^ 5
  let s3 := alternateRootFourierP3Polynomial omega ^ 5
  ![s0 + s1 + s2 + s3,
    epsilon * (s0 - s1 + s2 - s3),
    t * s0 - u * s1 - t * s2 + u * s3,
    epsilon * ((-t + 2 * u) * s0 + (-2 * t - u) * s1 +
      (t - 2 * u) * s2 + (2 * t + u) * s3)]

@[simp] theorem eval_alternateRootTPrimePolynomial (x : Fin 5 → K) :
    eval x alternateRootTPrimePolynomial = rootTPrime x := by
  simp [alternateRootTPrimePolynomial, rootTPrime]

@[simp] theorem eval_alternateRootUPrimePolynomial (x : Fin 5 → K) :
    eval x alternateRootUPrimePolynomial = rootUPrime x := by
  simp [alternateRootUPrimePolynomial, rootUPrime]

@[simp] theorem eval_alternateRootEpsilonProductPolynomial
    (x : Fin 5 → K) :
    eval x alternateRootEpsilonProductPolynomial = rootEpsilonProduct x := by
  simp [alternateRootEpsilonProductPolynomial, rootEpsilonProduct]

@[simp] theorem eval_alternateRootEpsilonPolynomial
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    eval x (alternateRootEpsilonPolynomial omega) = rootEpsilon omega x := by
  simp [alternateRootEpsilonPolynomial, rootEpsilon]

@[simp] theorem eval_alternateRootTPolynomial
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    eval x (alternateRootTPolynomial omega) = rootT omega x := by
  simp [alternateRootTPolynomial, rootT]

@[simp] theorem eval_alternateRootFormulaUPolynomial
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    eval x (alternateRootFormulaUPolynomial omega) =
      rootFormulaU omega x := by
  simp [alternateRootFormulaUPolynomial, rootFormulaU, rootU]

@[simp] theorem eval_alternateRootFourierP1Polynomial
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    eval x (alternateRootFourierP1Polynomial omega) =
      rootFourierP1 omega x := by
  simp [alternateRootFourierP1Polynomial, rootFourierP1]

@[simp] theorem eval_alternateRootFourierP2Polynomial
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    eval x (alternateRootFourierP2Polynomial omega) =
      rootFourierP2 omega x := by
  simp [alternateRootFourierP2Polynomial, rootFourierP2]

@[simp] theorem eval_alternateRootFourierP3Polynomial
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    eval x (alternateRootFourierP3Polynomial omega) =
      rootFourierP3 omega x := by
  simp [alternateRootFourierP3Polynomial, rootFourierP3]

@[simp] theorem eval_alternateRootFourierP4Polynomial
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    eval x (alternateRootFourierP4Polynomial omega) =
      rootFourierP4 omega x := by
  simp [alternateRootFourierP4Polynomial, rootFourierP4]

/-- Evaluation of the explicit polynomial vector is the root-defined
corrected projection vector. -/
@[simp] theorem eval_coherentAlternateCoordinatePolynomial
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) (j : Fin 4) :
    eval x (coherentAlternateCoordinatePolynomial omega j) =
      rootCoherentAlternateProjectionValues omega x j := by
  fin_cases j <;>
    simp [coherentAlternateCoordinatePolynomial,
      rootCoherentAlternateProjectionValues, coherentAlternateProjections,
      coherentAlternateProjectionMatrix, rootFourierFifthOrbit,
      Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;> ring

/-- Polynomial-level independence of the generator change
`omega ↦ omega²`.  This is the Galois-symmetry input needed for rational
coefficient descent, but a fixed-field theorem is still required to turn it
into an element of `ℚ[x₀,…,x₄]`. -/
theorem coherentAlternateCoordinatePolynomial_squared
    (omega : FifthRootOfUnity K) (j : Fin 4) :
    coherentAlternateCoordinatePolynomial omega.squared j =
      coherentAlternateCoordinatePolynomial omega j := by
  apply MvPolynomial.funext
  intro x
  rw [eval_coherentAlternateCoordinatePolynomial,
    eval_coherentAlternateCoordinatePolynomial]
  exact congrFun (rootCoherentAlternateProjectionValues_squared omega x) j

/-- The explicit coordinate polynomial commutes with coefficient maps that
carry one chosen primitive fifth root to another. -/
theorem map_coherentAlternateCoordinatePolynomial
    {L : Type*} [Field L] [CharZero L]
    (f : K →+* L) (omegaK : FifthRootOfUnity K)
    (omegaL : FifthRootOfUnity L)
    (homega : f omegaK.value = omegaL.value) (j : Fin 4) :
    MvPolynomial.map f (coherentAlternateCoordinatePolynomial omegaK j) =
      coherentAlternateCoordinatePolynomial omegaL j := by
  fin_cases j <;>
    simp [coherentAlternateCoordinatePolynomial,
      alternateRootEpsilonPolynomial,
      alternateRootEpsilonProductPolynomial,
      alternateRootTPolynomial, alternateRootFormulaUPolynomial,
      alternateRootTPrimePolynomial, alternateRootUPrimePolynomial,
      alternateRootFourierP1Polynomial,
      alternateRootFourierP2Polynomial,
      alternateRootFourierP3Polynomial,
      alternateRootFourierP4Polynomial,
      fifthRootDiscriminantFactor, homega] <;> ring

/-- Hence any base-field automorphism sending `omega` to `omega²` fixes the
entire corrected coordinate polynomial coefficientwise. -/
theorem map_coherentAlternateCoordinatePolynomial_eq_self
    {F : Type*} [Field F] [Algebra F K]
    (sigma : K ≃ₐ[F] K) (omega : FifthRootOfUnity K)
    (homega : sigma omega.value = omega.value ^ 2) (j : Fin 4) :
    MvPolynomial.map sigma.toRingHom
        (coherentAlternateCoordinatePolynomial omega j) =
      coherentAlternateCoordinatePolynomial omega j := by
  calc
    MvPolynomial.map sigma.toRingHom
        (coherentAlternateCoordinatePolynomial omega j) =
        coherentAlternateCoordinatePolynomial omega.squared j :=
      map_coherentAlternateCoordinatePolynomial sigma.toRingHom omega
        omega.squared homega j
    _ = coherentAlternateCoordinatePolynomial omega j :=
      coherentAlternateCoordinatePolynomial_squared omega j

/-- Coefficientwise form of the preceding fixed-polynomial theorem. -/
theorem coherentAlternateCoordinateCoefficient_fixed
    {F : Type*} [Field F] [Algebra F K]
    (sigma : K ≃ₐ[F] K) (omega : FifthRootOfUnity K)
    (homega : sigma omega.value = omega.value ^ 2)
    (j : Fin 4) (d : Fin 5 →₀ ℕ) :
    sigma (MvPolynomial.coeff d
      (coherentAlternateCoordinatePolynomial omega j)) =
      MvPolynomial.coeff d
        (coherentAlternateCoordinatePolynomial omega j) := by
  have h := congrArg (MvPolynomial.coeff d)
    (map_coherentAlternateCoordinatePolynomial_eq_self
      sigma omega homega j)
  simpa [MvPolynomial.coeff_map] using h

section CoefficientwiseDescent

variable {F : Type*} [Field F] [Algebra F K]

/-- In a finite Galois extension, a fixed element lies in the base field as
soon as the chosen automorphism generates every base-field automorphism. -/
theorem fixed_mem_range_of_cyclic_generator
    [FiniteDimensional F K] [IsGalois F K]
    (sigma : K ≃ₐ[F] K)
    (hgenerator : ∀ tau : K ≃ₐ[F] K, ∃ n : ℕ, tau = sigma ^ n)
    {z : K} (hz : sigma z = z) :
    z ∈ Set.range (algebraMap F K) := by
  rw [IsGalois.mem_range_algebraMap_iff_fixed]
  intro tau
  obtain ⟨n, rfl⟩ := hgenerator tau
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, hz, ih]

/-- Choose a base-field representative for each coefficient of a polynomial
whose coefficients are all known to lie in the range of `algebraMap`. -/
noncomputable def descendedCoefficient
    (p : MvPolynomial (Fin 5) K)
    (hcoeff : ∀ d, ∃ a : F, algebraMap F K a = p.coeff d)
    (d : Fin 5 →₀ ℕ) : F :=
  Classical.choose (hcoeff d)

theorem algebraMap_descendedCoefficient
    (p : MvPolynomial (Fin 5) K)
    (hcoeff : ∀ d, ∃ a : F, algebraMap F K a = p.coeff d)
    (d : Fin 5 →₀ ℕ) :
    algebraMap F K (descendedCoefficient p hcoeff d) = p.coeff d :=
  Classical.choose_spec (hcoeff d)

/-- Coefficientwise descent of a finite polynomial. -/
noncomputable def descendPolynomial
    (p : MvPolynomial (Fin 5) K)
    (hcoeff : ∀ d, ∃ a : F, algebraMap F K a = p.coeff d) :
    MvPolynomial (Fin 5) F :=
  ∑ d ∈ p.support, monomial d (descendedCoefficient p hcoeff d)

/-- Mapping the descended polynomial back to the extension recovers the
original polynomial exactly. -/
theorem map_descendPolynomial
    (p : MvPolynomial (Fin 5) K)
    (hcoeff : ∀ d, ∃ a : F, algebraMap F K a = p.coeff d) :
    MvPolynomial.map (algebraMap F K)
        (descendPolynomial p hcoeff) = p := by
  classical
  rw [descendPolynomial]
  simp only [map_sum, map_monomial,
    algebraMap_descendedCoefficient]
  exact p.support_sum_monomial_coeff

/-- Exact conditional fixed-field descent for a corrected coordinate.

The hypothesis says precisely that the fixed elements of the chosen
cyclotomic generator lie in the base field.  For the actual degree-four
cyclotomic extension this follows from the statement that the automorphism
`omega ↦ omega²` generates the full Galois group; that concrete fixed-field
identification is the remaining external field-theory input. -/
noncomputable def descendedCoherentAlternateCoordinate
    (sigma : K ≃ₐ[F] K) (omega : FifthRootOfUnity K)
    (homega : sigma omega.value = omega.value ^ 2)
    (hfixed : ∀ z : K, sigma z = z →
      z ∈ Set.range (algebraMap F K))
    (j : Fin 4) : MvPolynomial (Fin 5) F :=
  descendPolynomial (coherentAlternateCoordinatePolynomial omega j)
    (fun d ↦ hfixed _
      (coherentAlternateCoordinateCoefficient_fixed
        sigma omega homega j d))

theorem map_descendedCoherentAlternateCoordinate
    (sigma : K ≃ₐ[F] K) (omega : FifthRootOfUnity K)
    (homega : sigma omega.value = omega.value ^ 2)
    (hfixed : ∀ z : K, sigma z = z →
      z ∈ Set.range (algebraMap F K))
    (j : Fin 4) :
    MvPolynomial.map (algebraMap F K)
        (descendedCoherentAlternateCoordinate sigma omega homega hfixed j) =
      coherentAlternateCoordinatePolynomial omega j :=
  map_descendPolynomial _ _

end CoefficientwiseDescent

/-- Each corrected coordinate is an honest polynomial invariant over the
field containing the chosen fifth root. -/
noncomputable def coherentAlternateCoordinateInvariant
    (omega : FifthRootOfUnity K) (j : Fin 4) :
    invariantSubalgebra K (Fin 5) standardF20 :=
  ⟨coherentAlternateCoordinatePolynomial omega j, by
    intro g
    apply MvPolynomial.funext
    intro x
    rw [MvPolynomial.eval_rename,
      eval_coherentAlternateCoordinatePolynomial,
      eval_coherentAlternateCoordinatePolynomial]
    change rootCoherentAlternateProjectionValues omega
      (permuteRootTuple x (g : Fin5Solvable.S5)) j =
        rootCoherentAlternateProjectionValues omega x j
    exact congrFun
      (rootCoherentAlternateProjectionValues_permute_of_mem_standardF20
        omega x g.1 g.2) j⟩

/-- Descent preserves `F20` invariance because coefficient extension is
injective and commutes with variable renaming. -/
theorem descendedCoherentAlternateCoordinate_rename
    {F : Type*} [Field F] [Algebra F K]
    (sigma : K ≃ₐ[F] K) (omega : FifthRootOfUnity K)
    (homega : sigma omega.value = omega.value ^ 2)
    (hfixed : ∀ z : K, sigma z = z →
      z ∈ Set.range (algebraMap F K))
    (j : Fin 4) (g : standardF20) :
    MvPolynomial.rename g.1
        (descendedCoherentAlternateCoordinate
          sigma omega homega hfixed j) =
      descendedCoherentAlternateCoordinate
        sigma omega homega hfixed j := by
  apply MvPolynomial.map_injective (algebraMap F K)
    (algebraMap F K).injective
  simp only [MvPolynomial.map_rename,
    map_descendedCoherentAlternateCoordinate]
  exact (coherentAlternateCoordinateInvariant omega j).2 g

/-- The conditionally descended coordinate bundled over the base field. -/
noncomputable def descendedCoherentAlternateInvariant
    {F : Type*} [Field F] [Algebra F K]
    (sigma : K ≃ₐ[F] K) (omega : FifthRootOfUnity K)
    (homega : sigma omega.value = omega.value ^ 2)
    (hfixed : ∀ z : K, sigma z = z →
      z ∈ Set.range (algebraMap F K))
    (j : Fin 4) : invariantSubalgebra F (Fin 5) standardF20 :=
  ⟨descendedCoherentAlternateCoordinate sigma omega homega hfixed j,
    descendedCoherentAlternateCoordinate_rename
      sigma omega homega hfixed j⟩

/-- For `F = ℚ`, the descended polynomial is an element of the exact module
on which `concreteInvariantBasis` is defined. -/
noncomputable def descendedCoherentAlternateRationalInvariant
    [Algebra ℚ K]
    (sigma : K ≃ₐ[ℚ] K) (omega : FifthRootOfUnity K)
    (homega : sigma omega.value = omega.value ^ 2)
    (hfixed : ∀ z : K, sigma z = z →
      z ∈ Set.range (algebraMap ℚ K))
    (j : Fin 4) : F20InvariantModule :=
  ⟨descendedCoherentAlternateCoordinate sigma omega homega hfixed j,
    descendedCoherentAlternateCoordinate_rename
      sigma omega homega hfixed j⟩

/-- The six concrete symmetric coefficients of a descended corrected
coordinate. -/
noncomputable def descendedCoherentAlternateConcreteCoordinates
    [Algebra ℚ K]
    (sigma : K ≃ₐ[ℚ] K) (omega : FifthRootOfUnity K)
    (homega : sigma omega.value = omega.value ^ 2)
    (hfixed : ∀ z : K, sigma z = z →
      z ∈ Set.range (algebraMap ℚ K))
    (j : Fin 4) : Fin 6 → SymmetricFiveRing :=
  concreteInvariantBasis.repr
    (descendedCoherentAlternateRationalInvariant
      sigma omega homega hfixed j)

/-- Once the fixed-field hypothesis is supplied, the concrete six-element
basis expresses every corrected coordinate with no degree-15 expansion. -/
theorem descendedCoherentAlternateConcreteExpansion
    [Algebra ℚ K]
    (sigma : K ≃ₐ[ℚ] K) (omega : FifthRootOfUnity K)
    (homega : sigma omega.value = omega.value ^ 2)
    (hfixed : ∀ z : K, sigma z = z →
      z ∈ Set.range (algebraMap ℚ K))
    (j : Fin 4) :
    (∑ k : Fin 6,
        descendedCoherentAlternateConcreteCoordinates
            sigma omega homega hfixed j k •
          concreteInvariantBasis k) =
      descendedCoherentAlternateRationalInvariant
        sigma omega homega hfixed j := by
  exact concreteInvariantBasis.sum_repr
    (descendedCoherentAlternateRationalInvariant
      sigma omega homega hfixed j)

/-- Strongest conditional end-to-end descent/basis bridge.  The only
cyclotomic input left explicit is that the automorphism sending `omega` to
`omega²` generates the finite Galois group. -/
theorem exists_rational_concreteExpansion_of_cyclotomicGenerator
    [Algebra ℚ K] [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (sigma : K ≃ₐ[ℚ] K) (omega : FifthRootOfUnity K)
    (homega : sigma omega.value = omega.value ^ 2)
    (hgenerator : ∀ tau : K ≃ₐ[ℚ] K,
      ∃ n : ℕ, tau = sigma ^ n)
    (j : Fin 4) :
    ∃ p : F20InvariantModule,
      MvPolynomial.map (algebraMap ℚ K) p.1 =
          coherentAlternateCoordinatePolynomial omega j ∧
        ∃ c : Fin 6 → SymmetricFiveRing,
          (∑ k : Fin 6, c k • concreteInvariantBasis k) = p := by
  let hfixed : ∀ z : K, sigma z = z →
      z ∈ Set.range (algebraMap ℚ K) :=
    fun _ hz ↦ fixed_mem_range_of_cyclic_generator
      sigma hgenerator hz
  let p := descendedCoherentAlternateRationalInvariant
    sigma omega homega hfixed j
  refine ⟨p, ?_, ?_⟩
  · exact map_descendedCoherentAlternateCoordinate
      sigma omega homega hfixed j
  · refine ⟨fun k ↦ concreteInvariantBasis.repr p k, ?_⟩
    exact concreteInvariantBasis.sum_repr p

@[simp] theorem coherentAlternateCoordinateInvariant_val
    (omega : FifthRootOfUnity K) (j : Fin 4) :
    (coherentAlternateCoordinateInvariant omega j).1 =
      coherentAlternateCoordinatePolynomial omega j :=
  rfl

end

/-! ## Concrete fifth-cyclotomic instantiation -/

section ConcreteFifthCyclotomic

open Polynomial IsCyclotomicExtension
open scoped Cyclotomic

abbrev FifthCyclotomicField := CyclotomicField 5 ℚ

local instance fifthConductor_neZero : NeZero (5 : ℚ) := ⟨by norm_num⟩
local instance fifthPrime : Fact (Nat.Prime 5) := ⟨by decide⟩
noncomputable local instance fifthCyclotomicField_isCyclotomicExtension :
    IsCyclotomicExtension {5} ℚ FifthCyclotomicField :=
  CyclotomicField.isCyclotomicExtension 5 ℚ
noncomputable local instance fifthCyclotomicField_isGalois :
    IsGalois ℚ FifthCyclotomicField :=
  IsCyclotomicExtension.isGalois {5} ℚ FifthCyclotomicField

/-- Mathlib's chosen primitive root in the fifth cyclotomic field. -/
noncomputable def fifthCyclotomicOmega :
    FifthRootOfUnity FifthCyclotomicField where
  value := zeta 5 ℚ FifthCyclotomicField
  primitive := zeta_spec 5 ℚ FifthCyclotomicField

theorem fifthCyclotomicPolynomial_irreducible :
    Irreducible (Polynomial.cyclotomic 5 ℚ) :=
  Polynomial.cyclotomic.irreducible_rat (by norm_num)

/-- The unit `2 mod 5`, which generates `(ZMod 5)ˣ`. -/
def fifthUnitTwo : (ZMod 5)ˣ :=
  ZMod.unitOfCoprime 2 (by decide)

/-- The standard cyclotomic identification of the Galois group with
`(ZMod 5)ˣ`. -/
noncomputable def fifthCyclotomicAutEquivPow :
    (FifthCyclotomicField ≃ₐ[ℚ] FifthCyclotomicField) ≃* (ZMod 5)ˣ :=
  IsCyclotomicExtension.autEquivPow FifthCyclotomicField
    fifthCyclotomicPolynomial_irreducible

/-- The automorphism corresponding to exponent two. -/
noncomputable def fifthCyclotomicSquareAut :
    FifthCyclotomicField ≃ₐ[ℚ] FifthCyclotomicField :=
  fifthCyclotomicAutEquivPow.symm fifthUnitTwo

/-- The chosen automorphism really sends the chosen primitive root to its
square. -/
theorem fifthCyclotomicSquareAut_omega :
    fifthCyclotomicSquareAut fifthCyclotomicOmega.value =
      fifthCyclotomicOmega.value ^ 2 := by
  let hzeta := zeta_spec 5 ℚ FifthCyclotomicField
  have hspec := hzeta.autToPow_spec ℚ fifthCyclotomicSquareAut
  have hpow :
      hzeta.autToPow ℚ fifthCyclotomicSquareAut = fifthUnitTwo := by
    simpa [fifthCyclotomicAutEquivPow, fifthCyclotomicSquareAut] using
      fifthCyclotomicAutEquivPow.apply_symm_apply fifthUnitTwo
  rw [hpow] at hspec
  have hval : (fifthUnitTwo : ZMod 5).val = 2 := by
    rw [show (fifthUnitTwo : ZMod 5) = 2 by
      simp [fifthUnitTwo, ZMod.coe_unitOfCoprime]]
    rw [ZMod.val_ofNat]
  rw [hval] at hspec
  simpa [fifthCyclotomicOmega] using hspec.symm

/-- Kernel computation in the four-element concrete unit group. -/
theorem fifthUnitTwo_zpowers_eq_top :
    Subgroup.zpowers fifthUnitTwo = ⊤ := by
  apply Subgroup.eq_top_of_card_eq
  rw [Nat.card_zpowers]
  have horder : orderOf fifthUnitTwo = 4 := by
    apply orderOf_eq_of_pow_and_pow_div_prime (n := 4)
    · norm_num
    · ext
      change (2 : ZMod 5) ^ 4 = 1
      decide
    · intro p hp hdiv
      have hp_le : p ≤ 4 := Nat.le_of_dvd (by norm_num) hdiv
      interval_cases p
      · norm_num at hp
      · norm_num at hp
      · change fifthUnitTwo ^ 2 ≠ (1 : (ZMod 5)ˣ)
        intro h
        have hv := congrArg (fun u : (ZMod 5)ˣ => (u : ZMod 5)) h
        have hv' : (2 : ZMod 5) ^ 2 = 1 := by
          simpa [fifthUnitTwo, ZMod.coe_unitOfCoprime] using hv
        exact (by decide : ¬ ((2 : ZMod 5) ^ 2 = 1)) hv'
      · norm_num at hdiv
      · norm_num at hp
  rw [horder]
  norm_num [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime (by norm_num : Nat.Prime 5)]

/-- Consequently the square automorphism generates the full fifth
cyclotomic Galois group. -/
theorem fifthCyclotomicSquareAut_generator
    (tau : FifthCyclotomicField ≃ₐ[ℚ] FifthCyclotomicField) :
    ∃ n : ℕ, tau = fifthCyclotomicSquareAut ^ n := by
  let e := fifthCyclotomicAutEquivPow
  have hz : e tau ∈ Subgroup.zpowers fifthUnitTwo := by
    rw [fifthUnitTwo_zpowers_eq_top]
    trivial
  have hp : e tau ∈ Submonoid.powers fifthUnitTwo :=
    mem_powers_iff_mem_zpowers.mpr hz
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp hp
  refine ⟨n, ?_⟩
  apply e.injective
  simpa [e, fifthCyclotomicSquareAut] using hn.symm

theorem fifthCyclotomicSquareAut_fixed_mem_range
    {z : FifthCyclotomicField}
    (hz : fifthCyclotomicSquareAut z = z) :
    z ∈ Set.range (algebraMap ℚ FifthCyclotomicField) :=
  fixed_mem_range_of_cyclic_generator fifthCyclotomicSquareAut
    fifthCyclotomicSquareAut_generator hz

/-- The actual rational invariant obtained by coefficientwise descent in
the canonical fifth cyclotomic field. -/
noncomputable def fifthCyclotomicRationalCoordinate
    (j : Fin 4) : F20InvariantModule :=
  descendedCoherentAlternateRationalInvariant
    fifthCyclotomicSquareAut fifthCyclotomicOmega
    fifthCyclotomicSquareAut_omega
    (fun _ hz ↦ fifthCyclotomicSquareAut_fixed_mem_range hz) j

theorem map_fifthCyclotomicRationalCoordinate (j : Fin 4) :
    MvPolynomial.map (algebraMap ℚ FifthCyclotomicField)
        (fifthCyclotomicRationalCoordinate j).1 =
      coherentAlternateCoordinatePolynomial fifthCyclotomicOmega j :=
  map_descendedCoherentAlternateCoordinate
    fifthCyclotomicSquareAut fifthCyclotomicOmega
    fifthCyclotomicSquareAut_omega
    (fun _ hz ↦ fifthCyclotomicSquareAut_fixed_mem_range hz) j

/-- Its canonical coefficients in Lazard's six concrete invariants. -/
noncomputable def fifthCyclotomicConcreteCoordinates
    (j : Fin 4) : Fin 6 → SymmetricFiveRing :=
  concreteInvariantBasis.repr (fifthCyclotomicRationalCoordinate j)

theorem fifthCyclotomicConcreteExpansion (j : Fin 4) :
    (∑ k : Fin 6,
        fifthCyclotomicConcreteCoordinates j k •
          concreteInvariantBasis k) =
      fifthCyclotomicRationalCoordinate j :=
  concreteInvariantBasis.sum_repr (fifthCyclotomicRationalCoordinate j)

/-- Unconditional rational descent and six-basis expansion for the corrected
alternate coordinates in the canonical fifth cyclotomic field. -/
theorem exists_fifthCyclotomic_rationalConcreteExpansion
    (j : Fin 4) :
    ∃ p : F20InvariantModule,
      MvPolynomial.map (algebraMap ℚ FifthCyclotomicField) p.1 =
          coherentAlternateCoordinatePolynomial fifthCyclotomicOmega j ∧
        ∃ c : Fin 6 → SymmetricFiveRing,
          (∑ k : Fin 6, c k • concreteInvariantBasis k) = p := by
  exact ⟨fifthCyclotomicRationalCoordinate j,
    map_fifthCyclotomicRationalCoordinate j,
    fifthCyclotomicConcreteCoordinates j,
    fifthCyclotomicConcreteExpansion j⟩

end ConcreteFifthCyclotomic

end LeanProofs.PolynomialFormulas.LazardQuintic
