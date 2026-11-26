import IPRADerivations.Analysis.Integration.GaussianOddSymmetricQuadrature
import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerUnitNormalization

/-!
# Original quadratic kernels at positive integer Gamma arguments

At the original trajectory N+1 the quadratic kernel is the literal
positive-time odd Gaussian monomial times the unchanged original decay.
The named observation uses the product's computed decay precision.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianOddMomentIntegrand

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIntegrandName (powerF powerData decayF decayData)
open GaussianEulerSquareKernel (doubled kernelF)
open GaussianEulerIntegerMomentIntegrand (monomial)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_at)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalHorner (ofGaussian canonical_unique ofGaussian_represents represents_congr qmul)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit)
open ComplexLogarithmRemainder (oneCode scale re im)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def argument (N : PTm n) : PTm n := GaussianGammaShiftTrajectory.point oneCode one N
abbrev radius := @GaussianGammaHalfIntegerDomain.radius
def degree (N : PTm n) : PTm n := succ (two*N)

@[simp] theorem subst_argument {m : ℕ} (σ : Fin n → PTm m) (N : PTm n) :
    Syn.subst σ (argument N) = argument (Syn.subst σ N) := by simp [argument]
@[simp] theorem subst_degree {m : ℕ} (σ : Fin n → PTm m) (N : PTm n) :
    Syn.subst σ (degree N) = degree (Syn.subst σ N) := by simp [degree]

theorem base_source : Γ ⊢[PRAAx] GaussianEulerIntegralGammaIdentification.source (oneCode : PTm n) one one one := by
  have h := GaussianEulerUnitNormalization.unit_lower_source (Γ := Γ) (n := n)
  exact .andI (.andI h.andE₁ (.andI h.andE₂.andE₁ h.andE₂.andE₂)) (le_refl one)

theorem quadratic_source (N c d : PTm n) (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    GaussianEulerQuadraticGamma.source (argument N) (radius N) one one c d :=
  .andI (GaussianGammaDensityDomain.shifted_source oneCode one one one N base_source) (.andI hc hd)

theorem doubled_coefficient (N : PTm n) : Γ ⊢[PRAAx]
    GaussianEulerIntegrandName.coefficient (doubled (argument N) one) one ≐
      GaussianRationalNaturalScale.naturalPoint (degree N) := by
  have hp : Γ ⊢[PRAAx] le one (one : PTm n) := le_refl one
  have lhs := GaussianRationalMetric.qsub_represents _ _ _ _ one hp
    (ofGaussian_represents (doubled (argument N) one) one hp)
    (GaussianRationalReciprocal.qone_represents_scaled one)
  apply canonical_unique _ _ _ _ (GaussianRationalMetric.qsub_canonical _ _)
    (GaussianRationalHorner.ofGaussian_canonical _ _ hp) hp ?_
    (GaussianRationalNaturalScale.natural_point_represents (degree N))
  apply represents_congr (.eqRefl _) ?_ (.eqRefl _) lhs
  have pt := GaussianGammaShiftTrajectory.point_native (Γ := Γ) oneCode one N
  have dt := GaussianEulerSquareKernel.doubled_parameter_equal (Γ := Γ) (argument N) one
  apply GaussianRootAlgebra.equal_of_values
  · simp only [GaussianRootAlgebra.re_sub,GaussianRootAlgebra.re_scale]
    rw [GaussianRootAlgebra.equal_re dt]
    simp only [GaussianRootAlgebra.re_add]
    change ZT.toZ Γ (re (GaussianGammaShiftTrajectory.point oneCode one N)) +
      ZT.toZ Γ (re (GaussianGammaShiftTrajectory.point oneCode one N)) - _ = _
    rw [GaussianRootAlgebra.equal_re pt]
    simp only [GaussianGammaEulerHeadLower.translated,GaussianRootAlgebra.re_add,GaussianRootAlgebra.re_scale,
      GaussianRootAlgebra.re_one,degree]
    ipra_simps
    ring
  · simp only [GaussianRootAlgebra.im_sub,GaussianRootAlgebra.im_scale]
    rw [GaussianRootAlgebra.equal_im dt]
    simp only [GaussianRootAlgebra.im_add]
    change ZT.toZ Γ (im (GaussianGammaShiftTrajectory.point oneCode one N)) +
      ZT.toZ Γ (im (GaussianGammaShiftTrajectory.point oneCode one N)) - _ = _
    rw [GaussianRootAlgebra.equal_im pt]
    simp only [GaussianGammaEulerHeadLower.translated,GaussianRootAlgebra.im_add,GaussianRootAlgebra.im_scale,
      GaussianRootAlgebra.im_one]
    ipra_simps
    ring

abbrev source := @GaussianEvenMomentIntegrand.source
def originalData (N a b c d : PTm n) : PTm n :=
  GaussianEulerSquareKernel.kernelData (doubled (argument N) one) one a b c d
abbrev nameF : PR 2 := multiplyF constantF decayF
def data (N a b c d : PTm n) : PTm n := multiplyData constantF decayF
  (monomial (degree N) a b) (decayData (c*(a*a)) (d*(b*b)))
def clock (p N a b c d : PTm n) : PTm n := GaussianFastValueCut.exponent
  (GaussianNameArithmetic.multiplyModulus constantF decayF (monomial (degree N) a b) (decayData (c*(a*a)) (d*(b*b)))) p
@[simp] theorem subst_clock {m : ℕ} (σ : Fin n → PTm m) (p N a b c d : PTm n) :
    Syn.subst σ (clock p N a b c d) = clock (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ a) (Syn.subst σ b)
      (Syn.subst σ c) (Syn.subst σ d) := by simp [clock]

theorem original_kernel (N a b E T c d : PTm n) (h : Γ ⊢[PRAAx] source a b E T c d) : Γ ⊢[PRAAx]
    crossEquivalent kernelF nameF (originalData N a b c d) (data N a b c d) := by
  let Z := doubled (argument N) one
  let D := decayData (c*(a*a)) (d*(b*b))
  have ht : Γ ⊢[PRAAx] GaussianEulerIntegrandName.source Z one a b := .andI (le_refl one) h.andE₁.andE₂.andE₁
  have hd := GaussianEulerPositiveScalingIntegrand.decay_regular (Γ := Γ) (c*(a*a)) (d*(b*b))
  exact GaussianGammaAdjacentCutoff.multiply_cross powerF constantF decayF decayF (powerData Z one a b)
    (monomial (degree N) a b) D D (GaussianEulerIntegrandName.power_regular _ _ _ _ ht)
    (constant_regular _) hd hd
    (GaussianEulerNaturalPower.original_power Z one (degree N) a b E T (le_refl one) h.andE₁
      (doubled_coefficient N)) (cross_refl _ _ hd)

theorem sample_at (p N a b c d : PTm n) : Γ ⊢[PRAAx]
    ap2 nameF p (data N a b c d) ≐ GaussianMomentReflection.row (clock p N a b c d) (degree N)
      (GaussianPositiveRationalLogarithm.fraction a b) a b c d :=
  (GaussianNameArithmetic.multiply_at constantF decayF _ _ p).eqTrans
    ((GaussianNameArithmetic.recode_congr (GaussianRationalSyntheticDivision.qmul_congr
      (GaussianGammaCanonicalExponent.constant_at _ _) (.eqRefl _))).eqTrans
      (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qmul_canonical _ _)))

theorem original_observations (p q N a b E T c d : PTm n) (h : Γ ⊢[PRAAx] source a b E T c d) : Γ ⊢[PRAAx]
    distanceBounded (ap2 kernelF p (originalData N a b c d)) (ap2 nameF q (data N a b c d))
      (unit p+unit q) (unit p*unit q) := cross_at _ _ _ _ p q (original_kernel N a b E T c d h)

theorem actual_original_odd_Gaussian_moment_row_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶ crossEquivalent kernelF nameF
      (originalData (var 0) (var 1) (var 2) (var 5) (var 6)) (data (var 0) (var 1) (var 2) (var 5) (var 6))) :=
  closeUniv 7 (.impI (original_kernel _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianOddMomentIntegrand
