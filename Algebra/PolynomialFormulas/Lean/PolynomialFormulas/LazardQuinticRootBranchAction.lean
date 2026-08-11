import PolynomialFormulas.LazardQuinticF20Action
import PolynomialFormulas.LazardQuinticQ1ProjectionBridge
import PolynomialFormulas.LazardQuinticRootFourierCoordinates

/-!
# Lightweight root-branch action

This module records the root and Fourier transformations used by Lazard's
Section 5 combined action.  It deliberately depends only on the explicit
root formulas and finite permutations; the invariant reductions and radical
certificate construction are not needed for these identities.
-/

namespace LeanProofs.PolynomialFormulas.LazardQuintic

open Fin5Solvable FrobeniusDummitResolvent

set_option autoImplicit false

private theorem quadraticTriple_eq_of_fields
    {K : Type*} {a b : QuadraticTriple K}
    (hepsilon : a.epsilon = b.epsilon)
    (ht : a.t = b.t) (hu : a.u = b.u) : a = b := by
  cases a
  cases b
  simp_all

/-- Multiplying by any power of a primitive fifth root disappears after
taking a fifth power. -/
@[simp] theorem FifthRootOfUnity.pow_mul_pow_five
    {K : Type*} [Field K] (omega : FifthRootOfUnity K)
    (n : ℕ) (z : K) :
    (omega.value ^ n * z) ^ 5 = z ^ 5 := by
  rw [mul_pow, ← pow_mul, Nat.mul_comm n 5, pow_mul,
    omega.primitive.pow_eq_one]
  simp

/-- The four positive Fourier components acquire the expected characters
under the five-cycle. -/
theorem rootFourierP1_permute_fiveCycle_f20
    {K : Type*} [Field K] (omega : FifthRootOfUnity K)
    (x : Fin 5 → K) :
    rootFourierP1 omega (permuteRootTuple x fiveCycle) =
      omega.value ^ 4 * rootFourierP1 omega x := by
  simp [rootFourierP1, permuteRootTuple, fiveCycle, finRotate_apply]
  ring_nf
  simp only [omega.pow_eq_pow_mod_five 8,
    omega.pow_eq_pow_mod_five 7, omega.pow_eq_pow_mod_five 6,
    omega.pow_eq_pow_mod_five 5]
  ring

theorem rootFourierP2_permute_fiveCycle_f20
    {K : Type*} [Field K] (omega : FifthRootOfUnity K)
    (x : Fin 5 → K) :
    rootFourierP2 omega (permuteRootTuple x fiveCycle) =
      omega.value ^ 3 * rootFourierP2 omega x := by
  simp [rootFourierP2, permuteRootTuple, fiveCycle, finRotate_apply]
  ring_nf
  simp only [omega.pow_eq_pow_mod_five 7,
    omega.pow_eq_pow_mod_five 6, omega.pow_eq_pow_mod_five 5]
  ring

theorem rootFourierP3_permute_fiveCycle_f20
    {K : Type*} [Field K] (omega : FifthRootOfUnity K)
    (x : Fin 5 → K) :
    rootFourierP3 omega (permuteRootTuple x fiveCycle) =
      omega.value ^ 2 * rootFourierP3 omega x := by
  simp [rootFourierP3, permuteRootTuple, fiveCycle, finRotate_apply]
  ring_nf
  simp only [omega.pow_eq_pow_mod_five 6,
    omega.pow_eq_pow_mod_five 5]
  ring

theorem rootFourierP4_permute_fiveCycle_f20
    {K : Type*} [Field K] (omega : FifthRootOfUnity K)
    (x : Fin 5 → K) :
    rootFourierP4 omega (permuteRootTuple x fiveCycle) =
      omega.value * rootFourierP4 omega x := by
  simp [rootFourierP4, permuteRootTuple, fiveCycle, finRotate_apply]
  ring_nf
  simp only [omega.pow_eq_pow_mod_five 5]
  ring

/-- Therefore the four fifth powers are fixed by the five-cycle. -/
@[simp] theorem rootFourierFifthOrbit_permute_fiveCycle_f20
    {K : Type*} [Field K] (omega : FifthRootOfUnity K)
    (x : Fin 5 → K) :
    rootFourierFifthOrbit omega (permuteRootTuple x fiveCycle) =
      rootFourierFifthOrbit omega x := by
  have hp4 :
      (omega.value * rootFourierP4 omega x) ^ 5 =
        rootFourierP4 omega x ^ 5 := by
    simpa using omega.pow_mul_pow_five 1 (rootFourierP4 omega x)
  funext i
  fin_cases i <;>
    simp [rootFourierFifthOrbit,
      rootFourierP1_permute_fiveCycle_f20,
      rootFourierP2_permute_fiveCycle_f20,
      rootFourierP3_permute_fiveCycle_f20,
      rootFourierP4_permute_fiveCycle_f20, hp4]

/-- The formula-sign quadratic triple is fixed by the five-cycle. -/
@[simp] theorem rootQuadraticTriple_permute_fiveCycle_f20
    {K : Type*} [Field K] (omega : FifthRootOfUnity K)
    (x : Fin 5 → K) :
    rootQuadraticTriple omega (permuteRootTuple x fiveCycle) =
      rootQuadraticTriple omega x := by
  apply quadraticTriple_eq_of_fields
  · simp [rootQuadraticTriple, rootEpsilon, rootEpsilonProduct,
      permuteRootTuple, fiveCycle, finRotate_apply]
    ring_nf
    simp
  · simp [rootQuadraticTriple, rootT]
  · simp [rootQuadraticTriple, rootFormulaU, rootU]

/-- The cyclic epsilon product changes sign under multiplication by two. -/
@[simp] theorem rootEpsilonProduct_permute_multiplierTwo
    {K : Type*} [Field K] (x : Fin 5 → K) :
    rootEpsilonProduct (permuteRootTuple x multiplierTwo) =
      -rootEpsilonProduct x := by
  simp [rootEpsilonProduct, permuteRootTuple, multiplierTwo]
  ring

/-- Root epsilon therefore realizes the epsilon sign of the `rotate`
branch. -/
@[simp] theorem rootEpsilon_permute_multiplierTwo
    {K : Type*} [Field K] (omega : FifthRootOfUnity K)
    (x : Fin 5 → K) :
    rootEpsilon omega (permuteRootTuple x multiplierTwo) =
      -rootEpsilon omega x := by
  simp [rootEpsilon]

/-- The first root-defined quadratic coordinate rotates to formula-sign
`U`. -/
@[simp] theorem rootT_permute_multiplierTwo
    {K : Type*} [Field K] (omega : FifthRootOfUnity K)
    (x : Fin 5 → K) :
    rootT omega (permuteRootTuple x multiplierTwo) =
      rootFormulaU omega x := by
  simp [rootT, rootFormulaU, rootU]
  ring

/-- Formula-sign `U` rotates to `-T`. -/
@[simp] theorem rootFormulaU_permute_multiplierTwo
    {K : Type*} [Field K] (omega : FifthRootOfUnity K)
    (x : Fin 5 → K) :
    rootFormulaU omega (permuteRootTuple x multiplierTwo) =
      -rootT omega x := by
  simp [rootFormulaU, rootU, rootT]
  ring

/-- In the earlier Section-5 sign convention, `U` rotates to `T` rather
than to `-T`.  This is the sign responsible for the anti-invariant alternate
projection recorded in `LazardQuinticQ1ProjectionBridge`. -/
@[simp] theorem rootU_permute_multiplierTwo
    {K : Type*} [Field K] (omega : FifthRootOfUnity K)
    (x : Fin 5 → K) :
    rootU omega (permuteRootTuple x multiplierTwo) =
      rootT omega x := by
  simpa [rootFormulaU] using
    (rootFormulaU_permute_multiplierTwo omega x)

/-- The three transformations above are exactly `branchTriple .rotate`. -/
@[simp] theorem rootQuadraticTriple_permute_multiplierTwo
    {K : Type*} [Field K] (omega : FifthRootOfUnity K)
    (x : Fin 5 → K) :
    rootQuadraticTriple omega (permuteRootTuple x multiplierTwo) =
      branchTriple (rootQuadraticTriple omega x) .rotate := by
  apply quadraticTriple_eq_of_fields
  · exact rootEpsilon_permute_multiplierTwo omega x
  · exact rootT_permute_multiplierTwo omega x
  · exact rootFormulaU_permute_multiplierTwo omega x

/-- Multiplication by two rotates the Fourier orbit in the same coherent
way as the quadratic triple. -/
@[simp] theorem rootFourierOrbit_permute_multiplierTwo
    {K : Type*} [Field K] (omega : FifthRootOfUnity K)
    (x : Fin 5 → K) :
    rootFourierOrbit omega (permuteRootTuple x multiplierTwo) =
      sourceForBranch (rootFourierOrbit omega x) .rotate := by
  funext i
  fin_cases i <;>
    simp [rootFourierOrbit, sourceForBranch, rootFourierP1,
      rootFourierP2, rootFourierP3, rootFourierP4,
      permuteRootTuple, multiplierTwo] <;> ring

/-- The fifth-power Fourier orbit rotates by the same permutation. -/
@[simp] theorem rootFourierFifthOrbit_permute_multiplierTwo
    {K : Type*} [Field K] (omega : FifthRootOfUnity K)
    (x : Fin 5 → K) :
    rootFourierFifthOrbit omega (permuteRootTuple x multiplierTwo) =
      sourceForBranch (rootFourierFifthOrbit omega x) .rotate := by
  have h := rootFourierOrbit_permute_multiplierTwo omega x
  funext i
  have hi := congrFun h i
  fin_cases i <;>
    simpa [rootFourierFifthOrbit, rootFourierOrbit, sourceForBranch] using
      congrArg (fun z : K ↦ z ^ 5) hi

end LeanProofs.PolynomialFormulas.LazardQuintic
