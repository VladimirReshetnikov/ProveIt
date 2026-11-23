import IPRADerivations.Analysis.GaussianEulerSquareKernel
import IPRADerivations.Analysis.GaussianEulerSquareTimeGeometry

/-!
# Source-only rates for the genuine quadratic Euler kernel

The original power at u and the original decay at (c/d)u^2 retain
their actual normalized multiplication and observation clocks. Their
verified compact rates give the ordinary independent observation
errors for the kernel itself. No factored Jacobian representation or
kernel variation/bound premise is used.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerQuadraticKernelTimeRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerSquareKernel (kernelF kernelData doubled)
open GaussianEulerIntegrandName (powerF powerData decayF decayData)
open GaussianEulerSquareTimeGeometry (source)
open GaussianCompactLogarithmBounds (domain)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def decayBound (T c : PTm n) : PTm n := GaussianEulerDampedTimeRate.decayBound (T*T) c
def lipschitz (R E T c _d : PTm n) : PTm n :=
  decayBound T c*GaussianEulerCompactPowerVariation.lipschitz R E T+
    GaussianEulerCompactPowerMajorant.majorant R E T*GaussianEulerDampedTimeRate.decayLipschitz (T*T) c*(two*T)
def majorant (R E T c : PTm n) : PTm n := GaussianEulerCompactPowerMajorant.majorant R E T*decayBound T c
def clock (p z B a b c d : PTm n) : PTm n := GaussianFastValueCut.exponent
  (GaussianNameArithmetic.multiplyModulus powerF decayF (powerData z B a b) (decayData (c*(a*a)) (d*(b*b)))) p

@[simp] theorem subst_decayBound {m : ℕ} (σ : Fin n → PTm m) (T c : PTm n) :
    Syn.subst σ (decayBound T c) = decayBound (Syn.subst σ T) (Syn.subst σ c) := by simp [decayBound]
@[simp] theorem subst_lipschitz {m : ℕ} (σ : Fin n → PTm m) (R E T c d : PTm n) :
    Syn.subst σ (lipschitz R E T c d) = lipschitz (Syn.subst σ R) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ c) (Syn.subst σ d) := by
  simp [lipschitz,GaussianEulerCompactPowerMajorant.majorant,GaussianEulerCompactPowerMajorant.exponentRadius]
@[simp] theorem subst_majorant {m : ℕ} (σ : Fin n → PTm m) (R E T c : PTm n) :
    Syn.subst σ (majorant R E T c) = majorant (Syn.subst σ R) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ c) := by
  simp [majorant,GaussianEulerCompactPowerMajorant.majorant,GaussianEulerCompactPowerMajorant.exponentRadius]
@[simp] theorem subst_clock {m : ℕ} (σ : Fin n → PTm m) (p z B a b c d : PTm n) :
    Syn.subst σ (clock p z B a b c d) = clock (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ B)
      (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ c) (Syn.subst σ d) := by simp [clock]

theorem doubled_source (z R B E c d : PTm n) (h : Γ ⊢[PRAAx] source z R B E c d) : Γ ⊢[PRAAx]
    source (doubled z B) (two*R) B E c d := by
  have sum := ComplexLogarithmRemainder.bounded_add h.andE₁.andE₂.andE₂ h.andE₁.andE₂.andE₂
  have disk : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (doubled z B) ((two*R)*B) :=
    le_congr (GaussianRootAlgebra.normSq_equal (GaussianEulerSquareKernel.doubled_parameter_equal z B)).eqSymm (by ipra_ring) sum
  exact .andI (.andI h.andE₁.andE₁ (.andI h.andE₁.andE₂.andE₁ disk)) h.andE₂

theorem square_domain (a b E T : PTm n) (h : Γ ⊢[PRAAx] domain a b E T) : Γ ⊢[PRAAx]
    domain (a*a) (b*b) (E*E) (T*T) :=
  .andI (.andI (positive_product _ _ h.andE₁.andE₁ h.andE₁.andE₁) (positive_product _ _ h.andE₁.andE₂ h.andE₁.andE₂))
    (.andI (le_congr (.eqRefl _) (by ipra_ring) (LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono h.andE₂.andE₁ h.andE₂.andE₁))
      (le_congr (.eqRefl _) (by ipra_ring) (LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono h.andE₂.andE₂ h.andE₂.andE₂)))

theorem square_distance (a b u v E T A D : PTm n) (ha : Γ ⊢[PRAAx] domain a b E T) (hu : Γ ⊢[PRAAx] domain u v E T)
    (hD : Γ ⊢[PRAAx] le one D) (near : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction u v) A D) : Γ ⊢[PRAAx]
    distanceBounded (fraction (a*a) (b*b)) (fraction (u*u) (v*v)) (two*T*A) D :=
  distance_congr (GaussianCompactRiemannName.fraction_congr _ _ _ _ (by ipra_ring) (by ipra_ring))
    (GaussianCompactRiemannName.fraction_congr _ _ _ _ (by ipra_ring) (by ipra_ring)) (by ipra_ring) (.eqRefl _)
    (GaussianEulerSquareTimeGeometry.mapped_distance a b u v E T one one A D (le_refl one) ha hu hD near)

private theorem cancel_denominator (F G : PR 2) (x y K D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] independentRate F G x y (K*D) (D*D)) : Γ ⊢[PRAAx] independentRate F G x y K D := by
  let sh := fun t : PTm n => Syn.shift (Syn.shift t)
  have ds : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (sh D) := by simpa [Fm.shift,Syn.shift,sh] using hD.shift.shift
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] independentRate F G (sh x) (sh y) (sh K*sh D) (sh D*sh D) := by simpa [Fm.shift,Syn.shift,sh] using h.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate,Syn.shift,sh] using distance_radius_mono _ _ _ _ (rateNumerator (sh K) (sh D) (var 1) (var 0))
    (rateDenominator (sh D) (var 1) (var 0))
    (GaussianNamedInverseRate.denominator_positive _ _ _ (positive_product _ _ ds ds))
    (GaussianNamedInverseRate.denominator_positive _ _ _ ds) (le_of_eq_add (d := zero) (by unfold rateNumerator rateDenominator; ipra_ring))
    (GaussianNamedInverseRate.rate_at _ _ _ _ _ _ (var 1) (var 0) hs)

theorem original_rate (z R B E T c d a b u v A D : PTm n) (h : Γ ⊢[PRAAx] source z R B E c d)
    (ha : Γ ⊢[PRAAx] domain a b E T) (hu : Γ ⊢[PRAAx] domain u v E T)
    (hD : Γ ⊢[PRAAx] le one D) (near : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction u v) A D) : Γ ⊢[PRAAx]
    independentRate kernelF kernelF (kernelData z B a b c d) (kernelData z B u v c d) (lipschitz R E T c d*A) D := by
  have ha' := square_domain a b E T ha
  have hu' := square_domain u v E T hu
  have decay := GaussianEulerDampedTimeRate.original_decay_rate (T*T) c d (a*a) (b*b) (u*u) (v*v) (E*E) (two*T*A) D
    h.andE₂.andE₂ ha' hu' hD (square_distance a b u v E T A D ha hu hD near)
  have power := GaussianEulerCompactPowerVariation.original_power_rate z R B E T a b u v A D
    (.andI h.andE₁ (.andI ha (.andI hu (.andI hD near))))
  have raw := GaussianNamedMultiplyRate.independent_rate powerF decayF powerF decayF
    (powerData z B a b) (decayData (c*(a*a)) (d*(b*b))) (powerData z B u v) (decayData (c*(u*u)) (d*(v*v)))
    (GaussianEulerCompactPowerVariation.lipschitz R E T*A) D (GaussianEulerDampedTimeRate.decayLipschitz (T*T) c*(two*T*A)) D
    (decayBound T c) (GaussianEulerCompactPowerMajorant.majorant R E T) hD hD
    (GaussianEulerIntegrandName.power_regular z B a b (.andI h.andE₁.andE₁ ha.andE₁)) (GaussianEulerPositiveScalingIntegrand.decay_regular _ _)
    (GaussianEulerIntegrandName.power_regular z B u v (.andI h.andE₁.andE₁ hu.andE₁)) (GaussianEulerPositiveScalingIntegrand.decay_regular _ _)
    (GaussianEulerDampedTimeRate.decay_sample_bound (T*T) c d (a*a) (b*b) (E*E) h.andE₂.andE₂ ha')
    (GaussianEulerDampedTimeRate.power_sample_bound z R B E T u v h.andE₁ hu) power decay
  have combined : Γ ⊢[PRAAx] independentRate kernelF kernelF (kernelData z B a b c d) (kernelData z B u v c d)
      ((lipschitz R E T c d*A)*D) (D*D) :=
    GaussianEulerCompactModulus.rate_congr _ _ _ _ _ _ _ (by unfold GaussianNamedMultiplyRate.leadingNumerator lipschitz; ipra_ring) raw
  exact cancel_denominator _ _ _ _ _ _ hD combined

theorem kernel_at (p z B a b c d : PTm n) : Γ ⊢[PRAAx]
    ap2 kernelF p (kernelData z B a b c d) ≐
      qmul (ap2 powerF (clock p z B a b c d) (powerData z B a b))
        (ap2 decayF (clock p z B a b c d) (decayData (c*(a*a)) (d*(b*b)))) :=
  (GaussianNameArithmetic.multiply_at powerF decayF _ _ p).eqTrans
    (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qmul_canonical _ _))

theorem original_observation_bound (p z R B E T c d a b : PTm n) (h : Γ ⊢[PRAAx] source z R B E c d)
    (ht : Γ ⊢[PRAAx] domain a b E T) : Γ ⊢[PRAAx]
    bounded (ap2 kernelF p (kernelData z B a b c d)) (majorant R E T c) one := by
  have power := GaussianEulerCompactPowerMajorant.original_power_observation (clock p z B a b c d) z R B E T a b h.andE₁ ht
  have decay := GaussianEulerDampedTimeRate.decay_observation_bound (clock p z B a b c d) (T*T) c d (a*a) (b*b) (E*E)
    h.andE₂.andE₂ (square_domain a b E T ht)
  exact GaussianRationalReciprocal.bound_congr (kernel_at p z B a b c d).eqSymm (.eqRefl _) (by ipra_ring)
    (GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one) power decay)

theorem actual_original_quadratic_kernel_compact_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (source (var 1) (var 2) (var 3) (var 4) (var 6) (var 7) ⟶ domain (var 8) (var 9) (var 4) (var 5) ⟶
      bounded (ap2 kernelF (var 0) (kernelData (var 1) (var 3) (var 8) (var 9) (var 6) (var 7)))
        (majorant (var 2) (var 4) (var 5) (var 6)) one) :=
  closeUniv 10 (.impI (.impI (original_observation_bound _ _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEulerQuadraticKernelTimeRate
