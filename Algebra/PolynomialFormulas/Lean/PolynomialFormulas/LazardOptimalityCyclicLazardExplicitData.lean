import Mathlib.Tactic.LinearCombination
import PolynomialFormulas.LazardOptimalityTheoremThreeCounterexample
import PolynomialFormulas.LazardQuinticDepressionCore
import PolynomialFormulas.LazardQuinticRootInvariantOrbits

/-!
# Lightweight explicit data for the cyclic Lazard roots

This module gives the concrete `C₅`-ordered roots and performs the exact
elementary-symmetric and metacyclic-invariant arithmetic without importing
the generated Dummit-coefficient or root-reconstruction developments.

The tuple is written in the power basis of the real cyclotomic generator
`a = ζ₁₁ + ζ₁₁⁻¹`.  Its order corresponds to the exponent orbit
`1, 2, 4, 3, 5` under multiplication by two modulo eleven (up to sign).
All reductions below are direct consequences of the minimal-polynomial
equation for `a`.
-/

open scoped BigOperators Polynomial

namespace LeanProofs.PolynomialFormulas.LazardOptimalityTheoremThreeFormulaBridge

open IntermediateField
open LeanProofs.PolynomialFormulas.LazardQuintic
open LeanProofs.PolynomialFormulas.FrobeniusDummitResolvent
open LeanProofs.PolynomialFormulas.LazardOptimalityCyclotomicCounterexample
open LeanProofs.PolynomialFormulas.LazardOptimalityCyclicQuinticCounterexample
open LeanProofs.PolynomialFormulas.LazardOptimalityTheoremThreeCounterexample

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

noncomputable section

/-- The original cyclic quintic, as coefficient data for Lazard's general
front end. -/
def cyclicGeneralQuintic : GeneralQuintic ℚ :=
  ⟨1, 1, -4, -3, 3, 1⟩

/-- The coefficient tuple is the cyclotomic cyclic quintic used in the
field-theoretic counterexample. -/
theorem cyclicGeneralQuintic_polynomial :
    cyclicGeneralQuintic.polynomial = cyclicQuinticQ := by
  ext n
  simp [cyclicGeneralQuintic, GeneralQuintic.polynomial,
    cyclicQuinticQ, cyclicQuinticZ, Polynomial.coeff_X_pow] <;>
    ring

/-- The monic depressed form to which Lazard's formula is applied. -/
def cyclicDepressedQuintic : DepressedQuintic ℚ :=
  depress cyclicGeneralQuintic

/-- Its four rational coefficients, exposed for the exact root reductions. -/
theorem cyclicDepressedQuintic_coefficients :
    cyclicDepressedQuintic =
      ⟨-22 / 5, -11 / 25, 462 / 125, 979 / 3125⟩ := by
  norm_num [cyclicDepressedQuintic, cyclicGeneralQuintic, depress]

/-- Irreducibility survives the rational depression translation. -/
theorem cyclicDepressedQuintic_polynomial_irreducible :
    Irreducible cyclicDepressedQuintic.polynomial := by
  apply (irreducible_polynomial_iff_depress_polynomial cyclicGeneralQuintic
    (by norm_num [cyclicGeneralQuintic])).mp
  rw [cyclicGeneralQuintic_polynomial]
  exact cyclicQuinticQ_irreducible

/-- Coordinates of the five depressed roots in the power basis
`1, a, a², a³, a⁴`, where `a = ζ₁₁ + ζ₁₁⁻¹`.

Before the depression shift, the rows represent respectively the conjugates
with exponents `1, 2, 4, 3, 5`.  The last row uses the minimal-polynomial
reduction of `a⁵ - 5a³ + 5a`. -/
def cyclicDepressedRootCoordinates : Fin 5 → Fin 5 → ℚ :=
  ![
    ![1 / 5, 1, 0, 0, 0],
    ![-9 / 5, 0, 1, 0, 0],
    ![11 / 5, 0, -4, 0, 1],
    ![1 / 5, -3, 0, 1, 0],
    ![-4 / 5, 2, 3, -1, -1]
  ]

/-- Evaluate a rational coordinate row at the real cyclotomic generator. -/
def cyclicDepressedRootValue (c : Fin 5 → ℚ) : Ambient :=
  ∑ k : Fin 5,
    algebraMap ℚ Ambient (c k) * cyclicQuinticRootAmbient ^ (k : ℕ)

/-- The explicit `C₅`-ordered depressed roots in the common ambient field. -/
def cyclicDepressedRoots : Fin 5 → Ambient := fun j ↦
  cyclicDepressedRootValue (cyclicDepressedRootCoordinates j)

/-- A simplified display of the five root values.  Keeping this separate from
the coordinate evaluator prevents later polynomial reductions from expanding
nested `Matrix.vecCons` terms. -/
def cyclicDepressedRootValues : Fin 5 → Ambient :=
  ![
    (1 / 5 : Ambient) + cyclicQuinticRootAmbient,
    -(9 / 5 : Ambient) + cyclicQuinticRootAmbient ^ 2,
    (11 / 5 : Ambient) - 4 * cyclicQuinticRootAmbient ^ 2 +
      cyclicQuinticRootAmbient ^ 4,
    (1 / 5 : Ambient) - 3 * cyclicQuinticRootAmbient +
      cyclicQuinticRootAmbient ^ 3,
    -(4 / 5 : Ambient) + 2 * cyclicQuinticRootAmbient +
      3 * cyclicQuinticRootAmbient ^ 2 - cyclicQuinticRootAmbient ^ 3 -
      cyclicQuinticRootAmbient ^ 4
  ]

@[simp] theorem cyclicDepressedRootValues_zero :
    cyclicDepressedRootValues 0 =
      (1 / 5 : Ambient) + cyclicQuinticRootAmbient := rfl

@[simp] theorem cyclicDepressedRootValues_one :
    cyclicDepressedRootValues 1 =
      -(9 / 5 : Ambient) + cyclicQuinticRootAmbient ^ 2 := rfl

@[simp] theorem cyclicDepressedRootValues_two :
    cyclicDepressedRootValues 2 =
      (11 / 5 : Ambient) - 4 * cyclicQuinticRootAmbient ^ 2 +
        cyclicQuinticRootAmbient ^ 4 := rfl

@[simp] theorem cyclicDepressedRootValues_three :
    cyclicDepressedRootValues 3 =
      (1 / 5 : Ambient) - 3 * cyclicQuinticRootAmbient +
        cyclicQuinticRootAmbient ^ 3 := rfl

@[simp] theorem cyclicDepressedRootValues_four :
    cyclicDepressedRootValues 4 =
      -(4 / 5 : Ambient) + 2 * cyclicQuinticRootAmbient +
        3 * cyclicQuinticRootAmbient ^ 2 - cyclicQuinticRootAmbient ^ 3 -
        cyclicQuinticRootAmbient ^ 4 := rfl

@[simp] theorem cyclicDepressedRootValues_mk_two (h : 2 < 5) :
    cyclicDepressedRootValues ⟨2, h⟩ =
      (11 / 5 : Ambient) - 4 * cyclicQuinticRootAmbient ^ 2 +
        cyclicQuinticRootAmbient ^ 4 := rfl

@[simp] theorem cyclicDepressedRootValues_mk_three (h : 3 < 5) :
    cyclicDepressedRootValues ⟨3, h⟩ =
      (1 / 5 : Ambient) - 3 * cyclicQuinticRootAmbient +
        cyclicQuinticRootAmbient ^ 3 := rfl

@[simp] theorem cyclicDepressedRootValues_mk_four (h : 4 < 5) :
    cyclicDepressedRootValues ⟨4, h⟩ =
      -(4 / 5 : Ambient) + 2 * cyclicQuinticRootAmbient +
        3 * cyclicQuinticRootAmbient ^ 2 - cyclicQuinticRootAmbient ^ 3 -
        cyclicQuinticRootAmbient ^ 4 := rfl

/-- The coordinate evaluator reduces once and for all to the five displayed
power-basis expressions. -/
theorem cyclicDepressedRoots_eq_values :
    cyclicDepressedRoots = cyclicDepressedRootValues := by
  funext j
  fin_cases j <;>
    norm_num [cyclicDepressedRoots, cyclicDepressedRootValue,
      cyclicDepressedRootCoordinates, Fin.sum_univ_succ] <;>
    ring

/-- The real cyclotomic generator satisfies its displayed cyclic quintic. -/
theorem cyclicQuinticRootAmbient_polynomial :
    cyclicQuinticRootAmbient ^ 5 + cyclicQuinticRootAmbient ^ 4 -
        4 * cyclicQuinticRootAmbient ^ 3 -
        3 * cyclicQuinticRootAmbient ^ 2 +
        3 * cyclicQuinticRootAmbient + 1 = 0 := by
  have h : Polynomial.aeval cyclicQuinticRootAmbient cyclicQuinticQ = 0 := by
    rw [← cyclicQuinticRootAmbient_minpoly]
    exact minpoly.aeval ℚ cyclicQuinticRootAmbient
  rw [aeval_cyclicQuinticQ] at h
  exact h

/-- The first five powers of the real cyclotomic generator are rationally
linearly independent. -/
theorem cyclicQuinticRootAmbient_powerBasis_linearIndependent :
    LinearIndependent ℚ (fun k : Fin 5 ↦
      cyclicQuinticRootAmbient ^ (k : ℕ)) := by
  have h := linearIndependent_pow (K := ℚ) cyclicQuinticRootAmbient
  rw [cyclicQuinticRootAmbient_minpoly, cyclicQuinticQ_natDegree] at h
  exact h

/-- Evaluation in the five-element power basis is injective. -/
theorem cyclicDepressedRootValue_injective :
    Function.Injective cyclicDepressedRootValue := by
  intro c d h
  apply funext
  intro k
  have hsub :
      cyclicDepressedRootValue c - cyclicDepressedRootValue d = 0 :=
    sub_eq_zero.mpr h
  have hmapSub :
      cyclicDepressedRootValue (fun i ↦ c i - d i) =
        cyclicDepressedRootValue c - cyclicDepressedRootValue d := by
    simp only [cyclicDepressedRootValue, map_sub, sub_mul,
      Finset.sum_sub_distrib]
  have hvalue : cyclicDepressedRootValue (fun i ↦ c i - d i) = 0 := by
    rw [hmapSub, hsub]
  have hlinear :
      ∑ i : Fin 5, (c i - d i) •
          cyclicQuinticRootAmbient ^ (i : ℕ) = 0 := by
    simpa only [cyclicDepressedRootValue, Algebra.smul_def] using hvalue
  have hcoeff := (Fintype.linearIndependent_iff.mp
    cyclicQuinticRootAmbient_powerBasis_linearIndependent
    (fun i ↦ c i - d i) hlinear) k
  exact sub_eq_zero.mp hcoeff

/-- The five rational coordinate rows are distinct. -/
theorem cyclicDepressedRootCoordinates_injective :
    Function.Injective cyclicDepressedRootCoordinates := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals
    first
    | rfl
    | norm_num [cyclicDepressedRootCoordinates] at hij

/-- The displayed ordered root tuple has no repetitions. -/
theorem cyclicDepressedRoots_injective :
    Function.Injective cyclicDepressedRoots :=
  cyclicDepressedRootValue_injective.comp
    cyclicDepressedRootCoordinates_injective

/-- Every displayed root is already in the real cyclic-quintic field. -/
theorem cyclicDepressedRoots_mem_cyclicQuinticField
    (j : Fin 5) : cyclicDepressedRoots j ∈ CyclicQuinticField := by
  have ha : cyclicQuinticRootAmbient ∈ CyclicQuinticField := by
    rw [CyclicQuinticField]
    exact mem_adjoin_simple_self ℚ cyclicQuinticRootAmbient
  rw [cyclicDepressedRoots, cyclicDepressedRootValue]
  apply CyclicQuinticField.sum_mem
  intro k _
  exact mul_mem (CyclicQuinticField.algebraMap_mem _)
    (pow_mem ha (k : ℕ))

/-! ## Lightweight elementary-symmetric certificate

These local definitions deliberately mirror the later generated-code
definitions.  The heavy bridge can identify them by reduction, while this
module stays independent of that generated import graph.
-/

/-- The five elementary symmetric expressions, kept local to the explicit
cyclic calculation. -/
def cyclicExplicitElementaryTuple {R : Type*} [CommRing R]
    (x : Fin 5 → R) : Fin 5 → R :=
  ![x 0 + x 1 + x 2 + x 3 + x 4,
    x 0 * x 1 + x 0 * x 2 + x 0 * x 3 + x 0 * x 4 +
      x 1 * x 2 + x 1 * x 3 + x 1 * x 4 + x 2 * x 3 + x 2 * x 4 + x 3 * x 4,
    x 0 * x 1 * x 2 + x 0 * x 1 * x 3 + x 0 * x 1 * x 4 +
      x 0 * x 2 * x 3 + x 0 * x 2 * x 4 + x 0 * x 3 * x 4 +
      x 1 * x 2 * x 3 + x 1 * x 2 * x 4 + x 1 * x 3 * x 4 + x 2 * x 3 * x 4,
    x 0 * x 1 * x 2 * x 3 + x 0 * x 1 * x 2 * x 4 +
      x 0 * x 1 * x 3 * x 4 + x 0 * x 2 * x 3 * x 4 + x 1 * x 2 * x 3 * x 4,
    x 0 * x 1 * x 2 * x 3 * x 4]

/-- The elementary tuple belonging to a depressed monic quintic. -/
def cyclicExplicitDepressedElementary (c : DepressedQuintic Ambient) :
    Fin 5 → Ambient :=
  ![0, c.p, -c.q, c.r, -c.s]

/-- Direct power-basis reduction of all five elementary symmetric
expressions for the explicit roots. -/
theorem cyclicDepressedRoots_explicitElementaryTuple :
    cyclicExplicitElementaryTuple cyclicDepressedRoots =
      cyclicExplicitDepressedElementary
        (cyclicDepressedQuintic.map (algebraMap ℚ Ambient)) := by
  rw [cyclicDepressedRoots_eq_values]
  have ha := cyclicQuinticRootAmbient_polynomial
  funext k
  fin_cases k
  · norm_num [cyclicExplicitElementaryTuple,
      cyclicExplicitDepressedElementary,
      cyclicDepressedQuintic_coefficients, DepressedQuintic.map]
    ring
  · norm_num [cyclicExplicitElementaryTuple,
      cyclicExplicitDepressedElementary,
      cyclicDepressedQuintic_coefficients, DepressedQuintic.map]
    linear_combination
      (2 * cyclicQuinticRootAmbient - cyclicQuinticRootAmbient ^ 3) * ha
  · norm_num [cyclicExplicitElementaryTuple,
      cyclicExplicitDepressedElementary,
      cyclicDepressedQuintic_coefficients, DepressedQuintic.map]
    linear_combination
      (1 - (9 / 5 : Ambient) * cyclicQuinticRootAmbient -
        7 * cyclicQuinticRootAmbient ^ 2 +
        (17 / 5 : Ambient) * cyclicQuinticRootAmbient ^ 3 +
        5 * cyclicQuinticRootAmbient ^ 4 -
        cyclicQuinticRootAmbient ^ 5 - cyclicQuinticRootAmbient ^ 6) * ha
  · norm_num [cyclicExplicitElementaryTuple,
      cyclicExplicitDepressedElementary,
      cyclicDepressedQuintic_coefficients, DepressedQuintic.map]
    linear_combination
      (-(13 / 5 : Ambient) +
        (1 / 25 : Ambient) * cyclicQuinticRootAmbient +
        (66 / 5 : Ambient) * cyclicQuinticRootAmbient ^ 2 -
        (188 / 25 : Ambient) * cyclicQuinticRootAmbient ^ 3 -
        15 * cyclicQuinticRootAmbient ^ 4 +
        (28 / 5 : Ambient) * cyclicQuinticRootAmbient ^ 5 +
        (33 / 5 : Ambient) * cyclicQuinticRootAmbient ^ 6 -
        cyclicQuinticRootAmbient ^ 7 - cyclicQuinticRootAmbient ^ 8) * ha
  · norm_num [cyclicExplicitElementaryTuple,
      cyclicExplicitDepressedElementary,
      cyclicDepressedQuintic_coefficients, DepressedQuintic.map]
    linear_combination
      ((11 / 25 : Ambient) -
        (363 / 125 : Ambient) * cyclicQuinticRootAmbient +
        (73 / 25 : Ambient) * cyclicQuinticRootAmbient ^ 2 +
        (2169 / 125 : Ambient) * cyclicQuinticRootAmbient ^ 3 -
        (16 / 5 : Ambient) * cyclicQuinticRootAmbient ^ 4 -
        (496 / 25 : Ambient) * cyclicQuinticRootAmbient ^ 5 +
        (34 / 25 : Ambient) * cyclicQuinticRootAmbient ^ 6 +
        (39 / 5 : Ambient) * cyclicQuinticRootAmbient ^ 7 -
        (1 / 5 : Ambient) * cyclicQuinticRootAmbient ^ 8 -
        cyclicQuinticRootAmbient ^ 9) * ha

/-! ## Lightweight metacyclic-invariant arithmetic -/

/-- The rational invariant tuple of the explicit ordering. -/
def cyclicRationalInvariants : Invariants ℚ :=
  ⟨-1991 / 125, -1353 / 625, -4961 / 125,
    73568 / 15625, 5627831 / 78125⟩

/-- The five raw root formulas, before importing the heavier packaged
`rootInvariants` definition. -/
def cyclicExplicitRootInvariants : Invariants Ambient :=
  ⟨thetaFormula cyclicDepressedRoots,
    lazardOrbitFormula 3 1 cyclicDepressedRoots,
    lazardOrbitFormula 4 1 cyclicDepressedRoots,
    lazardOrbitFormula 3 2 cyclicDepressedRoots,
    lazardOrbitFormula 4 2 cyclicDepressedRoots⟩

private theorem cyclicDepressedRoots_explicit_i4 :
    thetaFormula cyclicDepressedRoots =
      algebraMap ℚ Ambient (-1991 / 125) := by
  rw [cyclicDepressedRoots_eq_values]
  have ha := cyclicQuinticRootAmbient_polynomial
  norm_num [thetaFormula]
  linear_combination
    ((59 / 5 : Ambient) +
      (507 / 25 : Ambient) * cyclicQuinticRootAmbient -
      (198 / 5 : Ambient) * cyclicQuinticRootAmbient ^ 2 -
      (241 / 25 : Ambient) * cyclicQuinticRootAmbient ^ 3 +
      27 * cyclicQuinticRootAmbient ^ 4 -
      (14 / 5 : Ambient) * cyclicQuinticRootAmbient ^ 5 -
      (39 / 5 : Ambient) * cyclicQuinticRootAmbient ^ 6 +
      cyclicQuinticRootAmbient ^ 7 + cyclicQuinticRootAmbient ^ 8) * ha

private theorem cyclicDepressedRoots_explicit_i5 :
    lazardOrbitFormula 3 1 cyclicDepressedRoots =
      algebraMap ℚ Ambient (-1353 / 625) := by
  rw [cyclicDepressedRoots_eq_values]
  have ha := cyclicQuinticRootAmbient_polynomial
  norm_num [lazardOrbitFormula]
  linear_combination
    (-3 + (479 / 25 : Ambient) * cyclicQuinticRootAmbient +
      (151 / 5 : Ambient) * cyclicQuinticRootAmbient ^ 2 -
      (1227 / 25 : Ambient) * cyclicQuinticRootAmbient ^ 3 -
      (637 / 5 : Ambient) * cyclicQuinticRootAmbient ^ 4 +
      45 * cyclicQuinticRootAmbient ^ 5 +
      (864 / 5 : Ambient) * cyclicQuinticRootAmbient ^ 6 -
      (7 / 5 : Ambient) * cyclicQuinticRootAmbient ^ 7 -
      (517 / 5 : Ambient) * cyclicQuinticRootAmbient ^ 8 -
      (84 / 5 : Ambient) * cyclicQuinticRootAmbient ^ 9 +
      (143 / 5 : Ambient) * cyclicQuinticRootAmbient ^ 10 +
      (38 / 5 : Ambient) * cyclicQuinticRootAmbient ^ 11 -
      3 * cyclicQuinticRootAmbient ^ 12 -
      cyclicQuinticRootAmbient ^ 13) * ha

private theorem cyclicDepressedRoots_explicit_i6 :
    lazardOrbitFormula 4 1 cyclicDepressedRoots =
      algebraMap ℚ Ambient (-4961 / 125) := by
  rw [cyclicDepressedRoots_eq_values]
  have ha := cyclicQuinticRootAmbient_polynomial
  norm_num [lazardOrbitFormula]
  linear_combination
    ((721 / 25 : Ambient) +
      (2481 / 25 : Ambient) * cyclicQuinticRootAmbient -
      (826 / 5 : Ambient) * cyclicQuinticRootAmbient ^ 2 -
      (8063 / 25 : Ambient) * cyclicQuinticRootAmbient ^ 3 +
      (10421 / 25 : Ambient) * cyclicQuinticRootAmbient ^ 4 +
      (19519 / 25 : Ambient) * cyclicQuinticRootAmbient ^ 5 -
      (17253 / 25 : Ambient) * cyclicQuinticRootAmbient ^ 6 -
      (23634 / 25 : Ambient) * cyclicQuinticRootAmbient ^ 7 +
      (17681 / 25 : Ambient) * cyclicQuinticRootAmbient ^ 8 +
      (15462 / 25 : Ambient) * cyclicQuinticRootAmbient ^ 9 -
      (11184 / 25 : Ambient) * cyclicQuinticRootAmbient ^ 10 -
      (6254 / 25 : Ambient) * cyclicQuinticRootAmbient ^ 11 +
      (848 / 5 : Ambient) * cyclicQuinticRootAmbient ^ 12 +
      (341 / 5 : Ambient) * cyclicQuinticRootAmbient ^ 13 -
      35 * cyclicQuinticRootAmbient ^ 14 -
      12 * cyclicQuinticRootAmbient ^ 15 +
      3 * cyclicQuinticRootAmbient ^ 16 +
      cyclicQuinticRootAmbient ^ 17) * ha

private theorem cyclicDepressedRoots_explicit_i7 :
    lazardOrbitFormula 3 2 cyclicDepressedRoots =
      algebraMap ℚ Ambient (73568 / 15625) := by
  rw [cyclicDepressedRoots_eq_values]
  have ha := cyclicQuinticRootAmbient_polynomial
  norm_num [lazardOrbitFormula]
  linear_combination
    (-(308 / 25 : Ambient) +
      (156142 / 3125 : Ambient) * cyclicQuinticRootAmbient +
      (703 / 25 : Ambient) * cyclicQuinticRootAmbient ^ 2 -
      (1038596 / 3125 : Ambient) * cyclicQuinticRootAmbient ^ 3 +
      (50974 / 125 : Ambient) * cyclicQuinticRootAmbient ^ 4 +
      (81889 / 125 : Ambient) * cyclicQuinticRootAmbient ^ 5 -
      (285938 / 125 : Ambient) * cyclicQuinticRootAmbient ^ 6 -
      (88883 / 125 : Ambient) * cyclicQuinticRootAmbient ^ 7 +
      (559352 / 125 : Ambient) * cyclicQuinticRootAmbient ^ 8 +
      (60986 / 125 : Ambient) * cyclicQuinticRootAmbient ^ 9 -
      (557967 / 125 : Ambient) * cyclicQuinticRootAmbient ^ 10 -
      (25712 / 125 : Ambient) * cyclicQuinticRootAmbient ^ 11 +
      (64327 / 25 : Ambient) * cyclicQuinticRootAmbient ^ 12 +
      (1223 / 25 : Ambient) * cyclicQuinticRootAmbient ^ 13 -
      (22363 / 25 : Ambient) * cyclicQuinticRootAmbient ^ 14 -
      (28 / 5 : Ambient) * cyclicQuinticRootAmbient ^ 15 +
      (926 / 5 : Ambient) * cyclicQuinticRootAmbient ^ 16 +
      (1 / 5 : Ambient) * cyclicQuinticRootAmbient ^ 17 -
      21 * cyclicQuinticRootAmbient ^ 18 +
      cyclicQuinticRootAmbient ^ 20) * ha

private theorem cyclicDepressedRoots_explicit_i8 :
    lazardOrbitFormula 4 2 cyclicDepressedRoots =
      algebraMap ℚ Ambient (5627831 / 78125) := by
  rw [cyclicDepressedRoots_eq_values]
  have ha := cyclicQuinticRootAmbient_polynomial
  norm_num [lazardOrbitFormula]
  linear_combination
    (-(186459 / 3125 : Ambient) +
      (582821 / 15625 : Ambient) * cyclicQuinticRootAmbient +
      (1899748 / 3125 : Ambient) * cyclicQuinticRootAmbient ^ 2 -
      (16726273 / 15625 : Ambient) * cyclicQuinticRootAmbient ^ 3 -
      (1705928 / 625 : Ambient) * cyclicQuinticRootAmbient ^ 4 +
      (11614559 / 3125 : Ambient) * cyclicQuinticRootAmbient ^ 5 +
      (24989524 / 3125 : Ambient) * cyclicQuinticRootAmbient ^ 6 -
      (3461884 / 625 : Ambient) * cyclicQuinticRootAmbient ^ 7 -
      (9799624 / 625 : Ambient) * cyclicQuinticRootAmbient ^ 8 +
      (1589337 / 625 : Ambient) * cyclicQuinticRootAmbient ^ 9 +
      (12289896 / 625 : Ambient) * cyclicQuinticRootAmbient ^ 10 +
      (1744881 / 625 : Ambient) * cyclicQuinticRootAmbient ^ 11 -
      (1980014 / 125 : Ambient) * cyclicQuinticRootAmbient ^ 12 -
      (604568 / 125 : Ambient) * cyclicQuinticRootAmbient ^ 13 +
      (207836 / 25 : Ambient) * cyclicQuinticRootAmbient ^ 14 +
      (82037 / 25 : Ambient) * cyclicQuinticRootAmbient ^ 15 -
      (70909 / 25 : Ambient) * cyclicQuinticRootAmbient ^ 16 -
      (31562 / 25 : Ambient) * cyclicQuinticRootAmbient ^ 17 +
      (15204 / 25 : Ambient) * cyclicQuinticRootAmbient ^ 18 +
      (7207 / 25 : Ambient) * cyclicQuinticRootAmbient ^ 19 -
      (373 / 5 : Ambient) * cyclicQuinticRootAmbient ^ 20 -
      (183 / 5 : Ambient) * cyclicQuinticRootAmbient ^ 21 +
      4 * cyclicQuinticRootAmbient ^ 22 +
      2 * cyclicQuinticRootAmbient ^ 23) * ha

/-- The raw root formulas are exactly the scalar extension of the displayed
rational invariant tuple. -/
theorem cyclicRationalInvariants_map_eq_explicitRootInvariants :
    cyclicRationalInvariants.map (algebraMap ℚ Ambient) =
      cyclicExplicitRootInvariants := by
  unfold cyclicRationalInvariants Invariants.map cyclicExplicitRootInvariants
  rw [cyclicDepressedRoots_explicit_i4,
    cyclicDepressedRoots_explicit_i5,
    cyclicDepressedRoots_explicit_i6,
    cyclicDepressedRoots_explicit_i7,
    cyclicDepressedRoots_explicit_i8]

/-- On the explicit rational coefficient and invariant data Lazard's
invariant `E` is `-242`. -/
theorem cyclicRationalInvariants_invariantE :
    invariantE (cyclicDepressedQuintic.map (algebraMap ℚ Ambient))
        (cyclicRationalInvariants.map (algebraMap ℚ Ambient)) =
      algebraMap ℚ Ambient (-242) := by
  rw [cyclicDepressedQuintic_coefficients]
  norm_num [invariantE, DepressedQuintic.map,
    cyclicRationalInvariants, Invariants.map]

end

end LeanProofs.PolynomialFormulas.LazardOptimalityTheoremThreeFormulaBridge
