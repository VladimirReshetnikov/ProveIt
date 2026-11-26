import IPRADerivations.Analysis.Gamma.HalfInteger.GaussianGammaHalfIntegerDomain
import IPRADerivations.Analysis.Euler.GaussianEulerNaturalPower

/-!
# Original quadratic kernels are literal even Gaussian moment rows

At the actual half-integer trajectory N+1/2 the ORIGINAL quadratic
kernel is the normalized product of the rational monomial u^(2N)
and the unchanged original decay at (c/d)u². All native coefficient
and time sources are derived; no Gaussian or half-integer value
formula is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEvenMomentIntegrand

open_ipra
open GaussianGammaHalfIntegerDomain (argument radius)
open GaussianEulerIntegrandName (powerF powerData decayF decayData)
open GaussianEulerSquareKernel (doubled kernelF)
open GaussianEulerIntegerMomentIntegrand (monomial)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_at)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalHorner (qmul)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (a b E T c d : PTm n) : Fm PTm n :=
  GaussianHarmonicIntegerExponential.source a b E T ⋏ (le one c ⋏ le one d)
def originalData (N a b c d : PTm n) : PTm n :=
  GaussianEulerSquareKernel.kernelData (doubled (argument N) two) two a b c d
def nameF : PR 2 := multiplyF constantF decayF
def data (N a b c d : PTm n) : PTm n := multiplyData constantF decayF
  (monomial (two*N) a b) (decayData (c*(a*a)) (d*(b*b)))
def clock (p N a b c d : PTm n) : PTm n := GaussianFastValueCut.exponent
  (GaussianNameArithmetic.multiplyModulus constantF decayF (monomial (two*N) a b) (decayData (c*(a*a)) (d*(b*b)))) p
ipra_subst source
ipra_subst originalData
ipra_subst data
ipra_subst clock

theorem old_source (a b E T c d : PTm n) (h : Γ ⊢[PRAAx] source a b E T c d) : Γ ⊢[PRAAx]
    GaussianEulerPositiveScalingIntegrand.source two a b c d :=
  .andI (zero_lt_succ one) (.andI h.andE₂ h.andE₁.andE₂.andE₁)

theorem name_regular (N a b c d : PTm n) : Γ ⊢[PRAAx] pointCN nameF (data N a b c d) :=
  multiply_fast _ _ _ _ (constant_regular _) (GaussianEulerPositiveScalingIntegrand.decay_regular _ _)

theorem original_kernel (N a b E T c d : PTm n) (h : Γ ⊢[PRAAx] source a b E T c d) : Γ ⊢[PRAAx]
    crossEquivalent kernelF nameF (originalData N a b c d) (data N a b c d) := by
  let Z := doubled (argument N) two
  let D := decayData (c*(a*a)) (d*(b*b))
  have timeSource : Γ ⊢[PRAAx] GaussianEulerIntegrandName.source Z two a b :=
    .andI (zero_lt_succ one) h.andE₁.andE₂.andE₁
  have hd := GaussianEulerPositiveScalingIntegrand.decay_regular (Γ := Γ) (c*(a*a)) (d*(b*b))
  exact GaussianGammaAdjacentCutoff.multiply_cross powerF constantF decayF decayF (powerData Z two a b)
    (monomial (two*N) a b) D D (GaussianEulerIntegrandName.power_regular _ _ _ _ timeSource)
    (constant_regular _) hd hd
    (GaussianEulerNaturalPower.original_power Z two (two*N) a b E T (zero_lt_succ one) h.andE₁
      (GaussianGammaHalfIntegerDomain.doubled_coefficient N)) (cross_refl _ _ hd)

theorem sample_at (p N a b c d : PTm n) : Γ ⊢[PRAAx]
    ap2 nameF p (data N a b c d) ≐ qmul (monomial (two*N) a b)
      (ap2 decayF (clock p N a b c d) (decayData (c*(a*a)) (d*(b*b)))) :=
  (GaussianNameArithmetic.multiply_at constantF decayF _ _ p).eqTrans
    ((GaussianNameArithmetic.recode_congr (GaussianRationalSyntheticDivision.qmul_congr
      (GaussianGammaCanonicalExponent.constant_at _ _) (.eqRefl _))).eqTrans
      (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qmul_canonical _ _)))

theorem original_observations (p q N a b E T c d : PTm n) (h : Γ ⊢[PRAAx] source a b E T c d) : Γ ⊢[PRAAx]
    distanceBounded (ap2 kernelF p (originalData N a b c d)) (ap2 nameF q (data N a b c d))
      (unit p+unit q) (unit p*unit q) := cross_at _ _ _ _ p q (original_kernel N a b E T c d h)

theorem actual_original_even_Gaussian_moment_row_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶ crossEquivalent kernelF nameF
      (originalData (var 0) (var 1) (var 2) (var 5) (var 6)) (data (var 0) (var 1) (var 2) (var 5) (var 6))) :=
  closeUniv 7 (.impI (original_kernel _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_original_even_Gaussian_moment_sample_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (ap2 nameF (var 0) (data (var 1) (var 2) (var 3) (var 4) (var 5)) ≐ qmul (monomial (two*(var 1)) (var 2) (var 3))
      (ap2 decayF (clock (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
        (decayData ((var 4)*((var 2)*(var 2))) ((var 5)*((var 3)*(var 3)))))) :=
  closeUniv 6 (sample_at _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianEvenMomentIntegrand
