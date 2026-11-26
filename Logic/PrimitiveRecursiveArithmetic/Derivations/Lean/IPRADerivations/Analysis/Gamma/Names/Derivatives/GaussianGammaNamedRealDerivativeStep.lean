import IPRADerivations.Analysis.Gamma.Names.Derivatives.GaussianGammaNamedRealDerivativeDemand
import IPRADerivations.Analysis.Gamma.EulerProducts.Derivatives.GaussianGammaUnitEulerDifference
import IPRADerivations.Analysis.Gamma.EulerProducts.Derivatives.GaussianGammaUnitInverseSamples
import IPRADerivations.Analysis.RationalArithmetic.Fibers.GaussianRationalCurveFibers

/-!
# An explicit nonzero increment for the real Gamma derivative

The constant increment is the reciprocal of a dyadic integer. Its
denominator pays the common chart demand and the requested precision.
The same exponent certifies apartness from zero.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNamedRealDerivativeStep

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (oneCode normSq normSq_one scale)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialSmallPerturbation (smallSamples)
open GaussianFastValueCut (exponent query_budget)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaNamedRealDerivativeDemand (modulus modulus_positive)
open GaussianRationalHorner (ofGaussian ofGaussian_represents qmul qzero)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalSyntheticDivision (qone qmul_congr qmul_zero_right)
open GaussianRealNameExponentialInjectivity (axisSamples)
open RationalGaussianEmbedding (axis axis_congr)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def stepAnchor (f : PR 2) (p x E : PTm n) : PTm n :=
  exponent (modulus f p x E) p

def stepDenominator (f : PR 2) (p x E : PTm n) : PTm n := unit (stepAnchor f p x E)

def stepData (f : PR 2) (p x E : PTm n) : PTm n := ofGaussian oneCode (stepDenominator f p x E)

@[simp] theorem subst_stepAnchor {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (p x E : PTm n) :
    Syn.subst σ (stepAnchor f p x E) = stepAnchor f (Syn.subst σ p) (Syn.subst σ x) (Syn.subst σ E) := by
  simp [stepAnchor]

@[simp] theorem subst_stepDenominator {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (p x E : PTm n) :
    Syn.subst σ (stepDenominator f p x E) = stepDenominator f (Syn.subst σ p) (Syn.subst σ x) (Syn.subst σ E) := by
  simp [stepDenominator]

@[simp] theorem subst_stepData {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (p x E : PTm n) :
    Syn.subst σ (stepData f p x E) = stepData f (Syn.subst σ p) (Syn.subst σ x) (Syn.subst σ E) := by
  simp [stepData]

theorem denominator_positive (f : PR 2) (p x E : PTm n) :
    Γ ⊢[PRAAx] le one (stepDenominator f p x E) :=
  unit_positive (stepAnchor f p x E)

theorem denominator_budget (f : PR 2) (p x E : PTm n) :
    Γ ⊢[PRAAx] le (modulus f p x E*unit p) (stepDenominator f p x E) :=
  query_budget (modulus f p x E) p

theorem step_at (f : PR 2) (p x E k : PTm n) :
    Γ ⊢[PRAAx] ap2 constantF k (stepData f p x E) ≐ stepData f p x E :=
  constant_at k (stepData f p x E)

theorem reciprocal_input (f : PR 2) (p x E : PTm n) :
    Γ ⊢[PRAAx] GaussianNameReciprocal.input constantF (stepAnchor f p x E) (stepData f p x E) := by
  let a := stepAnchor f p x E
  let D := stepDenominator f p x E
  let q := stepData f p x E
  have hD := denominator_positive (Γ := Γ) f p x E
  have square : Γ ⊢[PRAAx] (D*D)*normSq oneCode ≐ D*D :=
    (congrMul (.eqRefl _) normSq_one).eqTrans (by ipra_ring)
  have lower : Γ ⊢[PRAAx] GaussianNameReciprocal.lower q D :=
    GaussianRationalLowerBounds.lower_from_representation q oneCode D one D hD hD
      (ofGaussian_represents _ _ hD) (le_congr (by ipra_ring) square.eqSymm (le_refl (D*D)))
  exact .andI (constant_regular q)
    (GaussianNameReciprocal.lower_congr (step_at f p x E (GaussianNameReciprocal.anchor a)).eqSymm (.eqRefl _) lower)

theorem step_nonzero (f : PR 2) (p x E : PTm n) :
    Γ ⊢[PRAAx] neg (stepData f p x E ≐ qzero) := by
  let D := stepDenominator f p x E
  let q := stepData f p x E
  let r := GaussianNamedDifferenceQuotient.inverse oneCode D
  have separated := GaussianGammaUnitInverseSamples.actual_step_separated D (denominator_positive (Γ := Γ) f p x E)
  have inverse : Γ ⊢[PRAAx] qmul r q ≐ qone := GaussianNamedDifferenceQuotient.actual_inverse oneCode D separated
  refine .impI ?_
  have equalsZero := (qmul_congr (.eqRefl r) (Prf.hyp0 : (q ≐ qzero) :: Γ ⊢[PRAAx] q ≐ qzero)).eqTrans (qmul_zero_right r)
  exact .impE GaussianRationalCurveFibers.gaussian_one_nonzero (inverse.wk.eqSymm.eqTrans equalsZero)

theorem step_axis (f : PR 2) (p x E : PTm n) : Γ ⊢[PRAAx] axis (stepData f p x E) := by
  let D := stepDenominator f p x E
  have hD := denominator_positive (Γ := Γ) f p x E
  have scalar : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (scale one oneCode) oneCode := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale] <;> ipra_simps <;> ring
  have same := GaussianGammaFiniteValueProperness.fraction_equal (scale one oneCode) oneCode D hD scalar
  exact axis_congr same (GaussianStirlingNames.fraction_axis one D hD)

theorem axis_samples (f : PR 2) (p x E : PTm n) :
    Γ ⊢[PRAAx] axisSamples constantF (stepData f p x E) := by
  let sh (t : PTm n) := Syn.shift t
  let Δ := Γ.map Fm.shift
  refine .allI ?_
  have real := step_axis (Γ := Δ) f (sh p) (sh x) (sh E)
  have read := step_at (Γ := Δ) f (sh p) (sh x) (sh E) (var 0)
  simpa only [axisSamples,Syn.shift,subst_stepData,sh,Δ] using axis_congr read.eqSymm real

theorem small_samples (f : PR 2) (p x E : PTm n) :
    Γ ⊢[PRAAx] smallSamples constantF (stepData f p x E) one (modulus f p x E) := by
  let sh (t : PTm n) := Syn.shift t
  let Δ := Γ.map Fm.shift
  let M := modulus f (sh p) (sh x) (sh E)
  let D := stepDenominator f (sh p) (sh x) (sh E)
  have hM : Δ ⊢[PRAAx] le one M := modulus_positive f (sh p) (sh x) (sh E)
  have paid : Δ ⊢[PRAAx] le (M*unit (sh p)) D := denominator_budget f (sh p) (sh x) (sh E)
  have left : Δ ⊢[PRAAx] le M (M*unit (sh p)) :=
    le_congr (one_mul M) (mul_comm _ _) (mul_le_mul_right M (unit_positive (sh p)))
  have bound := GaussianGammaUnitEulerDifference.increment_bound M D hM (le_trans left paid)
  have read := step_at (Γ := Δ) f (sh p) (sh x) (sh E) (var 0)
  refine .allI ?_
  simpa only [smallSamples,Syn.shift,subst_stepData,GaussianGammaNamedRealDerivativeDemand.subst_modulus,
    sh,Δ,M,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    bound_congr read.eqSymm (.eqRefl _) (.eqRefl _) bound

theorem step_source (f : PR 2) (p x E : PTm n) :
    Γ ⊢[PRAAx] axisSamples constantF (stepData f p x E) ⋏
      (GaussianNameReciprocal.input constantF (stepAnchor f p x E) (stepData f p x E) ⋏
        smallSamples constantF (stepData f p x E) one (modulus f p x E)) :=
  .andI (axis_samples f p x E) (.andI (reciprocal_input f p x E) (small_samples f p x E))

theorem actual_Gamma_named_real_derivative_step_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (neg (stepData f (var 0) (var 1) (var 2) ≐ qzero) ⋏
        (axisSamples constantF (stepData f (var 0) (var 1) (var 2)) ⋏
          (GaussianNameReciprocal.input constantF (stepAnchor f (var 0) (var 1) (var 2))
            (stepData f (var 0) (var 1) (var 2)) ⋏
           smallSamples constantF (stepData f (var 0) (var 1) (var 2)) one (modulus f (var 0) (var 1) (var 2))))) :=
  closeUniv 3 (.andI (step_nonzero f _ _ _) (step_source f _ _ _))

end LeanProofs.IPRA.Analysis.GaussianGammaNamedRealDerivativeStep
