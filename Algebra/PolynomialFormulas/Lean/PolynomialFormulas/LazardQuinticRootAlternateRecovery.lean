import PolynomialFormulas.LazardQuinticRootBranchEquivariance

/-!
# Denominator-safe alternate recovery from ordered roots

Lazard notes that the displayed Section 7 formula using the standard fourth
projection is only proved when `-1` is not a square in the base field.  His
alternate fourth projection removes that restriction, but the paper does not
print the much larger invariant expression for it.

This module closes the root-level linear-algebra part of that alternate path.
For a tuple of distinct roots, the alternate denominator is nonzero, so the
alternate projections recover `P₁⁵` without assuming that `T² + U²` is
nonzero.  Expressing the four alternate projections over the coefficient
field is deliberately a separate invariant-theory step.
-/

namespace LeanProofs.PolynomialFormulas.LazardQuintic

open Fin5Solvable FrobeniusDummitResolvent

set_option autoImplicit false

/-- Lazard's four alternate projections of the root Fourier fifth-power
orbit, using the original Section-5 `U` convention. -/
def rootAlternateProjectionValues
    {K : Type*} [Field K] [CharZero K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) : Fin 4 → K :=
  alternateProjections (rootEpsilon omega x) (rootT omega x)
    (rootU omega x) (rootFourierFifthOrbit omega x)

/-- Convention-safe alternate projection values, using the formula-sign
quadratic coordinate and the corrected coherent fourth row. -/
def rootCoherentAlternateProjectionValues
    {K : Type*} [Field K] [CharZero K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) : Fin 4 → K :=
  coherentAlternateProjections (rootEpsilon omega x) (rootT omega x)
    (rootFormulaU omega x) (rootFourierFifthOrbit omega x)

/-- With the original Section-5 sign, all four projection values are fixed
by the five-cycle.  Combined with the multiplier theorem below, their exact
generator characters are `(+,+)`, `(+,+)`, `(+,-)`, `(+,-)`. -/
@[simp] theorem rootAlternateProjectionValues_permute_fiveCycle
    {K : Type*} [Field K] [CharZero K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootAlternateProjectionValues omega (permuteRootTuple x fiveCycle) =
      rootAlternateProjectionValues omega x := by
  have htriple := rootQuadraticTriple_permute_fiveCycle_f20 omega x
  have hepsilon := congrArg QuadraticTriple.epsilon htriple
  have ht := congrArg QuadraticTriple.t htriple
  have huFormula := congrArg QuadraticTriple.u htriple
  have hu : rootU omega (permuteRootTuple x fiveCycle) = rootU omega x := by
    simpa [rootQuadraticTriple, rootFormulaU] using huFormula
  change
    alternateProjections
        (rootEpsilon omega (permuteRootTuple x fiveCycle))
        (rootT omega (permuteRootTuple x fiveCycle))
        (rootU omega (permuteRootTuple x fiveCycle))
        (rootFourierFifthOrbit omega
          (permuteRootTuple x fiveCycle)) = _
  rw [show rootEpsilon omega (permuteRootTuple x fiveCycle) =
      rootEpsilon omega x by
        simpa [rootQuadraticTriple] using hepsilon,
    show rootT omega (permuteRootTuple x fiveCycle) = rootT omega x by
      simpa [rootQuadraticTriple] using ht,
    hu, rootFourierFifthOrbit_permute_fiveCycle_f20]
  rfl

/-- The corrected formula-sign denominator is the negative of the already
proved nonzero Section-5-sign denominator. -/
theorem root_coherentAlternateDenominator_ne_zero
    {K : Type*} [Field K] [CharZero K]
    (omega : FifthRootOfUnity K) {x : Fin 5 → K}
    (hinjective : Function.Injective x) :
    coherentAlternateDenominator (rootT omega x)
        (rootFormulaU omega x) ≠ 0 := by
  rw [coherentAlternateDenominator_eq_neg_alternateDenominator]
  simpa [rootFormulaU] using
    neg_ne_zero.mpr (root_alternateDenominator_ne_zero omega hinjective)

/-- Multiplication by two fixes all four corrected alternate projection
values.  This is the generator-level invariance missing from the printed-row
path with the Section-5 sign for `U`. -/
@[simp] theorem rootCoherentAlternateProjectionValues_permute_multiplierTwo
    {K : Type*} [Field K] [CharZero K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootCoherentAlternateProjectionValues omega
        (permuteRootTuple x multiplierTwo) =
      rootCoherentAlternateProjectionValues omega x := by
  change
    coherentAlternateProjections
        (rootQuadraticTriple omega
          (permuteRootTuple x multiplierTwo)).epsilon
        (rootQuadraticTriple omega
          (permuteRootTuple x multiplierTwo)).t
        (rootQuadraticTriple omega
          (permuteRootTuple x multiplierTwo)).u
        (rootFourierFifthOrbit omega
          (permuteRootTuple x multiplierTwo)) = _
  rw [rootQuadraticTriple_permute_multiplierTwo,
    rootFourierFifthOrbit_permute_multiplierTwo]
  exact coherentAlternateProjections_branchTriple_sourceForBranch
    (rootQuadraticTriple omega x) (rootFourierFifthOrbit omega x) .rotate

/-- The corrected projection values are also fixed by the five-cycle. -/
@[simp] theorem rootCoherentAlternateProjectionValues_permute_fiveCycle
    {K : Type*} [Field K] [CharZero K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootCoherentAlternateProjectionValues omega
        (permuteRootTuple x fiveCycle) =
      rootCoherentAlternateProjectionValues omega x := by
  change
    coherentAlternateProjections
        (rootQuadraticTriple omega
          (permuteRootTuple x fiveCycle)).epsilon
        (rootQuadraticTriple omega
          (permuteRootTuple x fiveCycle)).t
        (rootQuadraticTriple omega
          (permuteRootTuple x fiveCycle)).u
        (rootFourierFifthOrbit omega
          (permuteRootTuple x fiveCycle)) = _
  rw [rootQuadraticTriple_permute_fiveCycle_f20,
    rootFourierFifthOrbit_permute_fiveCycle_f20]
  rfl

theorem rootCoherentAlternateProjectionValues_permute_fiveCycle_pow
    {K : Type*} [Field K] [CharZero K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) (n : ℕ) :
    rootCoherentAlternateProjectionValues omega
        (permuteRootTuple x (fiveCycle ^ n)) =
      rootCoherentAlternateProjectionValues omega x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, permuteRootTuple_mul,
        rootCoherentAlternateProjectionValues_permute_fiveCycle, ih]

theorem rootCoherentAlternateProjectionValues_permute_multiplierTwo_pow
    {K : Type*} [Field K] [CharZero K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) (n : ℕ) :
    rootCoherentAlternateProjectionValues omega
        (permuteRootTuple x (multiplierTwo ^ n)) =
      rootCoherentAlternateProjectionValues omega x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, permuteRootTuple_mul,
        rootCoherentAlternateProjectionValues_permute_multiplierTwo, ih]

/-- Full invariance under the explicit affine normal form of `F20`. -/
theorem rootCoherentAlternateProjectionValues_permute_affineElement
    {K : Type*} [Field K] [CharZero K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K)
    (ab : Fin 5 × Fin 4) :
    rootCoherentAlternateProjectionValues omega
        (permuteRootTuple x (affineElement ab)) =
      rootCoherentAlternateProjectionValues omega x := by
  rw [affineElement, permuteRootTuple_mul,
    rootCoherentAlternateProjectionValues_permute_multiplierTwo_pow,
    rootCoherentAlternateProjectionValues_permute_fiveCycle_pow]

/-- The corrected four-vector is fixed by every element of the standard
metacyclic subgroup.  This is a root-value equivariance theorem; by itself it
does not yet construct a polynomial over the coefficient field. -/
theorem rootCoherentAlternateProjectionValues_permute_of_mem_standardF20
    {K : Type*} [Field K] [CharZero K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K)
    (g : Fin5Solvable.S5) (hg : g ∈ standardF20) :
    rootCoherentAlternateProjectionValues omega
        (permuteRootTuple x g) =
      rootCoherentAlternateProjectionValues omega x := by
  have hg' : g ∈ affineF20 := by
    rw [affineF20_eq_standardF20]
    exact hg
  obtain ⟨ab, hab⟩ := affineElementSubtype_surjective ⟨g, hg'⟩
  have hgeq : g = affineElement ab := congrArg Subtype.val hab.symm
  rw [hgeq]
  exact rootCoherentAlternateProjectionValues_permute_affineElement
    omega x ab

/-- The corrected denominator-safe system recovers the actual fifth power
of the first Fourier component while staying coherent with the formula-sign
branch action. -/
theorem root_coherentAlternateRecover_fourierP1_pow_five
    {K : Type*} [Field K] [CharZero K]
    (omega : FifthRootOfUnity K) {x : Fin 5 → K}
    (hinjective : Function.Injective x)
    (hepsilon : rootEpsilon omega x ≠ 0) :
    coherentAlternateRecover (rootEpsilon omega x) (rootT omega x)
        (rootFormulaU omega x)
        (rootCoherentAlternateProjectionValues omega x) =
      rootFourierP1 omega x ^ 5 := by
  simpa [rootCoherentAlternateProjectionValues, rootFourierFifthOrbit] using
    coherentAlternateRecover_coherentAlternateProjections
      (rootEpsilon omega x) (rootT omega x) (rootFormulaU omega x)
      (rootFourierFifthOrbit omega x) hepsilon
      (root_coherentAlternateDenominator_ne_zero omega hinjective)

/-- With the original Section-5 sign for `U`, multiplication by two fixes
the first two alternate projections and negates the last two.  Thus the
fourth value used by the denominator-safe recovery path is an
anti-invariant, not an element of the ordinary `F20` invariant ring. -/
@[simp] theorem rootAlternateProjectionValues_permute_multiplierTwo
    {K : Type*} [Field K] [CharZero K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootAlternateProjectionValues omega
        (permuteRootTuple x multiplierTwo) =
      ![rootAlternateProjectionValues omega x 0,
        rootAlternateProjectionValues omega x 1,
        -rootAlternateProjectionValues omega x 2,
        -rootAlternateProjectionValues omega x 3] := by
  change
    alternateProjections
        (rootEpsilon omega (permuteRootTuple x multiplierTwo))
        (rootT omega (permuteRootTuple x multiplierTwo))
        (rootU omega (permuteRootTuple x multiplierTwo))
        (rootFourierFifthOrbit omega
          (permuteRootTuple x multiplierTwo)) = _
  rw [rootEpsilon_permute_multiplierTwo,
    rootT_permute_multiplierTwo, rootU_permute_multiplierTwo,
    rootFourierFifthOrbit_permute_multiplierTwo]
  simpa [rootFormulaU, rootAlternateProjectionValues] using
    (alternateProjections_sectionFiveU_multiplierTwo
      (rootEpsilon omega x) (rootT omega x) (rootU omega x)
      (rootFourierFifthOrbit omega x))

/-- The product `epsilon * I4'` has trivial multiplier-by-two character,
even though `I4'` itself has the sign character. -/
@[simp] theorem rootEpsilon_mul_rootAlternateProjection_fourth_permute_multiplierTwo
    {K : Type*} [Field K] [CharZero K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootEpsilon omega (permuteRootTuple x multiplierTwo) *
        rootAlternateProjectionValues omega
          (permuteRootTuple x multiplierTwo) 3 =
      rootEpsilon omega x * rootAlternateProjectionValues omega x 3 := by
  rw [rootEpsilon_permute_multiplierTwo]
  have h := congrFun
    (rootAlternateProjectionValues_permute_multiplierTwo omega x) 3
  simpa using congrArg (fun z : K ↦ (-rootEpsilon omega x) * z) h

/-- The alternate projection system recovers the actual fifth power of the
first Fourier component for every ordered tuple of distinct roots.  In
particular, this theorem has no `T² + U² ≠ 0` hypothesis. -/
theorem root_alternateRecover_fourierP1_pow_five
    {K : Type*} [Field K] [CharZero K]
    (omega : FifthRootOfUnity K) {x : Fin 5 → K}
    (hinjective : Function.Injective x)
    (hepsilon : rootEpsilon omega x ≠ 0) :
    alternateRecover (rootEpsilon omega x) (rootT omega x) (rootU omega x)
        (rootAlternateProjectionValues omega x) =
      rootFourierP1 omega x ^ 5 := by
  simpa [rootAlternateProjectionValues, rootFourierFifthOrbit] using
    alternateRecover_alternateProjections
      (rootEpsilon omega x) (rootT omega x) (rootU omega x)
      (rootFourierFifthOrbit omega x) hepsilon
      (root_alternateDenominator_ne_zero omega hinjective)

end LeanProofs.PolynomialFormulas.LazardQuintic
