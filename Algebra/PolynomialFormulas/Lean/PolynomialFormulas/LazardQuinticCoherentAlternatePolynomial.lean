import PolynomialFormulas.LazardQuinticRootRadicals
import PolynomialFormulas.LazardQuinticSectionFiveCombinedAction
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.FieldTheory.Galois.Basic

/-!
# Polynomial form of the corrected alternate projections

The root-level alternate projections are explicit functions of an ordered
five-tuple.  This file lifts them to actual multivariate polynomials over the
ambient field, proves the evaluation equations by kernel reduction, and proves
the generator-change invariance coefficientwise.  The later descent to the
coefficient field is kept as a separate theorem with an explicit fixed-field
hypothesis.
-/

open scoped BigOperators
open MvPolynomial

namespace LeanProofs.PolynomialFormulas.LazardQuintic

set_option autoImplicit false

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

def coherentRootProjectionValues
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) : Fin 4 → K :=
  coherentAlternateProjections (rootEpsilon omega x) (rootT omega x)
    (rootFormulaU omega x) (rootFourierFifthOrbit omega x)

theorem rootCoherentAlternateProjectionValues_squared
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    coherentRootProjectionValues omega.squared x =
      coherentRootProjectionValues omega x := by
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

abbrev CoherentRootPolynomial (K : Type*) [CommRing K] :=
  MvPolynomial (Fin 5) K

def coherentRootTPrimePolynomial : CoherentRootPolynomial K :=
  (X 0 - X 1) * (X 1 - X 2) * (X 2 - X 3) *
    (X 3 - X 4) * (X 4 - X 0)

def coherentRootUPrimePolynomial : CoherentRootPolynomial K :=
  (X 0 - X 2) * (X 1 - X 3) * (X 2 - X 4) *
    (X 3 - X 0) * (X 4 - X 1)

def coherentRootEpsilonProductPolynomial : CoherentRootPolynomial K :=
  (X 1 - X 2 - X 3 + X 4) *
    (X 2 - X 3 - X 4 + X 0) *
    (X 3 - X 4 - X 0 + X 1) *
    (X 4 - X 0 - X 1 + X 2) *
    (X 0 - X 1 - X 2 + X 3)

def coherentRootEpsilonPolynomial
    (omega : FifthRootOfUnity K) : CoherentRootPolynomial K :=
  C (fifthRootDiscriminantFactor omega) *
    coherentRootEpsilonProductPolynomial

def coherentRootTPolynomial
    (omega : FifthRootOfUnity K) : CoherentRootPolynomial K :=
  C (omega.value - omega.value ^ 4) * coherentRootTPrimePolynomial +
    C (omega.value ^ 2 - omega.value ^ 3) * coherentRootUPrimePolynomial

def coherentRootFormulaUPolynomial
    (omega : FifthRootOfUnity K) : CoherentRootPolynomial K :=
  -(C (omega.value ^ 2 - omega.value ^ 3) *
      coherentRootTPrimePolynomial -
    C (omega.value - omega.value ^ 4) * coherentRootUPrimePolynomial)

def coherentRootFourierP1Polynomial
    (omega : FifthRootOfUnity K) : CoherentRootPolynomial K :=
  X 0 + C omega.value * X 1 + C (omega.value ^ 2) * X 2 +
    C (omega.value ^ 3) * X 3 + C (omega.value ^ 4) * X 4

def coherentRootFourierP2Polynomial
    (omega : FifthRootOfUnity K) : CoherentRootPolynomial K :=
  X 0 + C (omega.value ^ 2) * X 1 + C (omega.value ^ 4) * X 2 +
    C omega.value * X 3 + C (omega.value ^ 3) * X 4

def coherentRootFourierP3Polynomial
    (omega : FifthRootOfUnity K) : CoherentRootPolynomial K :=
  X 0 + C (omega.value ^ 3) * X 1 + C omega.value * X 2 +
    C (omega.value ^ 4) * X 3 + C (omega.value ^ 2) * X 4

def coherentRootFourierP4Polynomial
    (omega : FifthRootOfUnity K) : CoherentRootPolynomial K :=
  X 0 + C (omega.value ^ 4) * X 1 + C (omega.value ^ 3) * X 2 +
    C (omega.value ^ 2) * X 3 + C omega.value * X 4

def coherentRootCoordinatePolynomial
    (omega : FifthRootOfUnity K) : Fin 4 → CoherentRootPolynomial K :=
  let epsilon := coherentRootEpsilonPolynomial omega
  let t := coherentRootTPolynomial omega
  let u := coherentRootFormulaUPolynomial omega
  let s0 := coherentRootFourierP1Polynomial omega ^ 5
  let s1 := coherentRootFourierP2Polynomial omega ^ 5
  let s2 := coherentRootFourierP4Polynomial omega ^ 5
  let s3 := coherentRootFourierP3Polynomial omega ^ 5
  ![s0 + s1 + s2 + s3,
    epsilon * (s0 - s1 + s2 - s3),
    t * s0 - u * s1 - t * s2 + u * s3,
    epsilon * ((-t + 2 * u) * s0 + (-2 * t - u) * s1 +
      (t - 2 * u) * s2 + (2 * t + u) * s3)]

@[simp] theorem eval_coherentRootTPrimePolynomial (x : Fin 5 → K) :
    eval x coherentRootTPrimePolynomial = rootTPrime x := by
  simp [coherentRootTPrimePolynomial, rootTPrime]

@[simp] theorem eval_coherentRootUPrimePolynomial (x : Fin 5 → K) :
    eval x coherentRootUPrimePolynomial = rootUPrime x := by
  simp [coherentRootUPrimePolynomial, rootUPrime]

@[simp] theorem eval_coherentRootEpsilonProductPolynomial
    (x : Fin 5 → K) :
    eval x coherentRootEpsilonProductPolynomial = rootEpsilonProduct x := by
  simp [coherentRootEpsilonProductPolynomial, rootEpsilonProduct]

@[simp] theorem eval_coherentRootEpsilonPolynomial
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    eval x (coherentRootEpsilonPolynomial omega) = rootEpsilon omega x := by
  simp [coherentRootEpsilonPolynomial, rootEpsilon]

@[simp] theorem eval_coherentRootTPolynomial
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    eval x (coherentRootTPolynomial omega) = rootT omega x := by
  simp [coherentRootTPolynomial, rootT]

@[simp] theorem eval_coherentRootFormulaUPolynomial
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    eval x (coherentRootFormulaUPolynomial omega) =
      rootFormulaU omega x := by
  simp [coherentRootFormulaUPolynomial, rootFormulaU, rootU]

@[simp] theorem eval_coherentRootFourierP1Polynomial
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    eval x (coherentRootFourierP1Polynomial omega) = rootFourierP1 omega x := by
  simp [coherentRootFourierP1Polynomial, rootFourierP1]

@[simp] theorem eval_coherentRootFourierP2Polynomial
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    eval x (coherentRootFourierP2Polynomial omega) = rootFourierP2 omega x := by
  simp [coherentRootFourierP2Polynomial, rootFourierP2]

@[simp] theorem eval_coherentRootFourierP3Polynomial
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    eval x (coherentRootFourierP3Polynomial omega) = rootFourierP3 omega x := by
  simp [coherentRootFourierP3Polynomial, rootFourierP3]

@[simp] theorem eval_coherentRootFourierP4Polynomial
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    eval x (coherentRootFourierP4Polynomial omega) = rootFourierP4 omega x := by
  simp [coherentRootFourierP4Polynomial, rootFourierP4]

@[simp] theorem eval_coherentRootCoordinatePolynomial
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) (j : Fin 4) :
    eval x (coherentRootCoordinatePolynomial omega j) =
      coherentRootProjectionValues omega x j := by
  fin_cases j <;>
    simp [coherentRootCoordinatePolynomial,
      coherentRootProjectionValues, coherentAlternateProjections,
      coherentAlternateProjectionMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, rootFourierFifthOrbit] <;> ring

theorem coherentRootCoordinatePolynomial_squared
    (omega : FifthRootOfUnity K) (j : Fin 4) :
    coherentRootCoordinatePolynomial omega.squared j =
      coherentRootCoordinatePolynomial omega j := by
  apply MvPolynomial.funext
  intro x
  rw [eval_coherentRootCoordinatePolynomial,
    eval_coherentRootCoordinatePolynomial]
  exact congrFun (rootCoherentAlternateProjectionValues_squared omega x) j

theorem map_coherentRootCoordinatePolynomial
    {L : Type*} [Field L] [CharZero L]
    (f : K →+* L) (omegaK : FifthRootOfUnity K)
    (omegaL : FifthRootOfUnity L)
    (homega : f omegaK.value = omegaL.value) (j : Fin 4) :
    MvPolynomial.map f (coherentRootCoordinatePolynomial omegaK j) =
      coherentRootCoordinatePolynomial omegaL j := by
  fin_cases j <;>
    simp [coherentRootCoordinatePolynomial,
      coherentRootEpsilonPolynomial,
      coherentRootEpsilonProductPolynomial,
      coherentRootTPolynomial, coherentRootFormulaUPolynomial,
      coherentRootTPrimePolynomial, coherentRootUPrimePolynomial,
      coherentRootFourierP1Polynomial, coherentRootFourierP2Polynomial,
      coherentRootFourierP3Polynomial, coherentRootFourierP4Polynomial,
      fifthRootDiscriminantFactor, homega] <;> ring

theorem map_coherentRootCoordinatePolynomial_eq_self
    {F : Type*} [Field F] [Algebra F K]
    (sigma : K ≃ₐ[F] K) (omega : FifthRootOfUnity K)
    (homega : sigma omega.value = omega.value ^ 2) (j : Fin 4) :
    MvPolynomial.map sigma.toRingHom
        (coherentRootCoordinatePolynomial omega j) =
      coherentRootCoordinatePolynomial omega j := by
  calc
    MvPolynomial.map sigma.toRingHom
        (coherentRootCoordinatePolynomial omega j) =
        coherentRootCoordinatePolynomial omega.squared j :=
      map_coherentRootCoordinatePolynomial sigma.toRingHom omega
        omega.squared homega j
    _ = coherentRootCoordinatePolynomial omega j :=
      coherentRootCoordinatePolynomial_squared omega j

theorem coherentRootCoordinateCoefficient_fixed
    {F : Type*} [Field F] [Algebra F K]
    (sigma : K ≃ₐ[F] K) (omega : FifthRootOfUnity K)
    (homega : sigma omega.value = omega.value ^ 2)
    (j : Fin 4) (d : Fin 5 →₀ ℕ) :
    sigma (MvPolynomial.coeff d (coherentRootCoordinatePolynomial omega j)) =
      MvPolynomial.coeff d (coherentRootCoordinatePolynomial omega j) := by
  have h := congrArg (MvPolynomial.coeff d)
    (map_coherentRootCoordinatePolynomial_eq_self sigma omega homega j)
  simpa [MvPolynomial.coeff_map] using h

section CoefficientwiseDescent

variable {F : Type*} [Field F] [Algebra F K]

/-- A cyclic generator of a finite Galois group identifies its fixed elements
with the coefficient field.  This is the exact fixed-field hypothesis needed
for coefficientwise descent; it does not assume a concrete basis. -/
theorem coherent_fixed_mem_range_of_cyclic_generator
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

/-- Choose a coefficient-field representative for every coefficient known to
lie in the range of the scalar extension map. -/
noncomputable def coherentDescendedCoefficient
    (p : MvPolynomial (Fin 5) K)
    (hcoeff : ∀ d, ∃ a : F, algebraMap F K a = p.coeff d)
    (d : Fin 5 →₀ ℕ) : F :=
  Classical.choose (hcoeff d)

theorem algebraMap_coherentDescendedCoefficient
    (p : MvPolynomial (Fin 5) K)
    (hcoeff : ∀ d, ∃ a : F, algebraMap F K a = p.coeff d)
    (d : Fin 5 →₀ ℕ) :
    algebraMap F K (coherentDescendedCoefficient p hcoeff d) = p.coeff d :=
  Classical.choose_spec (hcoeff d)

/-- Coefficientwise descent of a finite multivariate polynomial. -/
noncomputable def coherentDescendPolynomial
    (p : MvPolynomial (Fin 5) K)
    (hcoeff : ∀ d, ∃ a : F, algebraMap F K a = p.coeff d) :
    MvPolynomial (Fin 5) F :=
  ∑ d ∈ p.support, monomial d (coherentDescendedCoefficient p hcoeff d)

theorem map_coherentDescendPolynomial
    (p : MvPolynomial (Fin 5) K)
    (hcoeff : ∀ d, ∃ a : F, algebraMap F K a = p.coeff d) :
    MvPolynomial.map (algebraMap F K) (coherentDescendPolynomial p hcoeff) = p := by
  classical
  rw [coherentDescendPolynomial]
  simp only [map_sum, map_monomial,
    algebraMap_coherentDescendedCoefficient]
  exact p.support_sum_monomial_coeff

/-- A fixed-coefficient coordinate polynomial has an explicit descent to the
coefficient field.  The theorem is deliberately conditional on the fixed
field range statement, so it can be reused for concrete extensions without
smuggling in a particular presentation of that field. -/
theorem exists_coherentDescendPolynomial_of_fixed_coefficients
    (sigma : K ≃ₐ[F] K) (omega : FifthRootOfUnity K)
    (homega : sigma omega.value = omega.value ^ 2)
    (hfixed : ∀ z : K, sigma z = z → z ∈ Set.range (algebraMap F K))
    (j : Fin 4) :
    ∃ p : MvPolynomial (Fin 5) F,
      MvPolynomial.map (algebraMap F K) p =
        coherentRootCoordinatePolynomial omega j := by
  let q : MvPolynomial (Fin 5) K := coherentRootCoordinatePolynomial omega j
  have hcoeff : ∀ d, ∃ a : F, algebraMap F K a = q.coeff d := by
    intro d
    exact hfixed _
      (coherentRootCoordinateCoefficient_fixed sigma omega homega j d)
  refine ⟨coherentDescendPolynomial q hcoeff, ?_⟩
  exact map_coherentDescendPolynomial q hcoeff

/- The cyclic-generator form is the concrete entry point for the usual
   finite Galois situation.  Its conclusion is still only coefficient
   descent; the later invariant-basis and radical-reconstruction steps remain
   separate obligations. -/
theorem exists_coherentDescendPolynomial_of_cyclic_generator
    [FiniteDimensional F K] [IsGalois F K]
    (sigma : K ≃ₐ[F] K)
    (hgenerator : ∀ tau : K ≃ₐ[F] K, ∃ n : ℕ, tau = sigma ^ n)
    (omega : FifthRootOfUnity K)
    (homega : sigma omega.value = omega.value ^ 2)
    (j : Fin 4) :
    ∃ p : MvPolynomial (Fin 5) F,
      MvPolynomial.map (algebraMap F K) p =
        coherentRootCoordinatePolynomial omega j := by
  exact exists_coherentDescendPolynomial_of_fixed_coefficients
    sigma omega homega
    (fun z hz => coherent_fixed_mem_range_of_cyclic_generator
      sigma hgenerator hz) j

/-- Package the four coordinatewise descent witnesses into one family.  This
form is convenient for the later reconstruction layer, where all corrected
alternate coordinates are consumed together. -/
theorem exists_coherentDescendCoordinateFamily_of_fixed_coefficients
    (sigma : K ≃ₐ[F] K) (omega : FifthRootOfUnity K)
    (homega : sigma omega.value = omega.value ^ 2)
    (hfixed : ∀ z : K, sigma z = z → z ∈ Set.range (algebraMap F K)) :
    ∃ p : Fin 4 → MvPolynomial (Fin 5) F, ∀ j,
      MvPolynomial.map (algebraMap F K) (p j) =
        coherentRootCoordinatePolynomial omega j := by
  classical
  choose p hp using fun j ↦
    exists_coherentDescendPolynomial_of_fixed_coefficients
      sigma omega homega hfixed j
  exact ⟨p, hp⟩

/-- The same family-level interface under the finite-Galois cyclic-generator
hypothesis. -/
theorem exists_coherentDescendCoordinateFamily_of_cyclic_generator
    [FiniteDimensional F K] [IsGalois F K]
    (sigma : K ≃ₐ[F] K)
    (hgenerator : ∀ tau : K ≃ₐ[F] K, ∃ n : ℕ, tau = sigma ^ n)
    (omega : FifthRootOfUnity K)
    (homega : sigma omega.value = omega.value ^ 2) :
    ∃ p : Fin 4 → MvPolynomial (Fin 5) F, ∀ j,
      MvPolynomial.map (algebraMap F K) (p j) =
        coherentRootCoordinatePolynomial omega j := by
  exact exists_coherentDescendCoordinateFamily_of_fixed_coefficients
    sigma omega homega
    (fun z hz => coherent_fixed_mem_range_of_cyclic_generator
      sigma hgenerator hz)

end CoefficientwiseDescent

end

end LeanProofs.PolynomialFormulas.LazardQuintic
