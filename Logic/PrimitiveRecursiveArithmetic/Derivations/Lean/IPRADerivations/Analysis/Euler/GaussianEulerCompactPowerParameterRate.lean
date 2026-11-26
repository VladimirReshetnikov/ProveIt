import IPRADerivations.Analysis.Euler.GaussianEulerCompactPowerVariation
import IPRADerivations.Analysis.Euler.Integration.GaussianEulerIntegrandParameterContinuity
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedAddRate
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedMultiplyRate

/-!
# Parameter continuity of the original Euler power

At a common positive rational time, only the complex coefficient of the
original logarithm varies. A fixed time window controls the logarithm and
the exponential disk uniformly across different native parameter encodings.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianEulerCompactPowerParameterRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCompactLogarithmBounds (domain)
open GaussianEulerExponentCompactBounds (source)
open GaussianEulerIntegrandName (coefficient powerF powerData powerExponentF powerExponentData powerRadius)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedMultiplyRate (sampleBound leadingNumerator leadingDenominator)
open GaussianRationalHorner (ofGaussian)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianNamedDifferenceRate (rate_parameters_congr)
open GaussianNameEquivalence (cross_refl)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "L" => GaussianPositiveRationalLogarithm.logF
local notation "logData" => GaussianPositiveRationalLogarithm.data
local notation "logRadius" => GaussianCompactLogarithmBounds.radius
local notation "disk" => GaussianEulerCompactPowerVariation.radius
local notation "expFactor" => GaussianRadiusExponentialLipschitzRate.factor

def gain (R E T : PTm n) : PTm n := expFactor (disk R E T)*logRadius E T

def input (z w R B D E T a b H N : PTm n) : Fm PTm n :=
  source z R B E ⋏ (source w R D E ⋏
    (domain a b E T ⋏ (le one N ⋏ distanceBounded (ofGaussian z B) (ofGaussian w D) H N)))

@[simp] theorem subst_gain {m : ℕ} (σ : Fin n → PTm m) (R E T : PTm n) :
    Syn.subst σ (gain R E T) = gain (Syn.subst σ R) (Syn.subst σ E) (Syn.subst σ T) := by
  simp [gain]

@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (z w R B D E T a b H N : PTm n) :
    (input z w R B D E T a b H N).subst σ =
      input (Syn.subst σ z) (Syn.subst σ w) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ D)
        (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ H) (Syn.subst σ N) := by
  simp [input]

private theorem logarithm_samples (a b E T : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (ht : Γ ⊢[PRAAx] domain a b E T) : Γ ⊢[PRAAx] sampleBound L (logData a b) (logRadius E T) := by
  let sh (v : PTm n) := Syn.shift v
  have he : Γ.map Fm.shift ⊢[PRAAx] le one (sh E) := by
    simpa only [Fm.shift,Syn.shift,sh,subst_le,one,PTm.subst_succ,PTm.subst_zero] using hE.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] domain (sh a) (sh b) (sh E) (sh T) := by
    simpa [Fm.shift,Syn.shift,sh] using ht.shift
  refine .allI ?_
  simpa only [sampleBound,Syn.shift,sh,GaussianPositiveRationalLogarithm.subst_data,
    GaussianCompactLogarithmBounds.subst_radius,GaussianPositiveRationalLogarithm.sample] using
    GaussianCompactLogarithmBounds.sample_bound (var 0) (sh a) (sh b) (sh E) (sh T) he hs

private theorem coefficient_samples (z R B E : PTm n) (hz : Γ ⊢[PRAAx] source z R B E) :
    Γ ⊢[PRAAx] sampleBound constantF (coefficient z B) (R+one) := by
  let sh (v : PTm n) := Syn.shift v
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh E) := by
    simpa [Fm.shift,Syn.shift,sh] using hz.shift
  refine .allI ?_
  have k := GaussianEulerIntegrandName.coefficient_bound (sh z) (sh R) (sh B) hs.andE₁ hs.andE₂.andE₂
  simpa only [sampleBound,Syn.shift,sh,GaussianEulerIntegrandName.subst_coefficient,
    PTm.subst_add,one,PTm.subst_succ,PTm.subst_zero] using
    GaussianRationalReciprocal.bound_congr (constant_at (var 0) (coefficient (sh z) (sh B))).eqSymm
      (.eqRefl _) (.eqRefl _) k

theorem exponent_rate (z w R B D E T a b H N : PTm n) (h : Γ ⊢[PRAAx] input z w R B D E T a b H N) :
    Γ ⊢[PRAAx] independentRate powerExponentF powerExponentF (powerExponentData z B a b) (powerExponentData w D a b)
      (logRadius E T*H) N := by
  let x := coefficient z B
  let y := coefficient w D
  let t := logData a b
  let M := logRadius E T
  have hN := h.andE₂.andE₂.andE₂.andE₁
  have ht := h.andE₂.andE₂.andE₁
  have hr := GaussianPositiveRationalLogarithm.name_regular a b ht.andE₁
  have cd := GaussianEulerIntegrandParameterContinuity.coefficient_distance z w B D H N hN h.andE₂.andE₂.andE₂.andE₂
  have rate := GaussianNamedMultiplyRate.independent_rate constantF L constantF L x t y t H N zero one M (R+one)
    hN (le_refl one) (constant_regular x) hr (constant_regular y) hr
    (logarithm_samples a b E T h.andE₁.andE₂.andE₁ ht) (coefficient_samples w R D E h.andE₂.andE₁)
    (GaussianNamedAddRate.constant_rate x y H N hN cd) (GaussianNamedDifferenceRate.self_rate L t hr)
  exact rate_parameters_congr powerExponentF powerExponentF (powerExponentData z B a b) (powerExponentData w D a b)
    (leadingNumerator H N zero one M (R+one)) (leadingDenominator N one) (M*H) N
    (by unfold leadingNumerator; ipra_ring) (by unfold leadingDenominator; ipra_ring) rate

theorem original_power_rate (z w R B D E T a b H N : PTm n) (h : Γ ⊢[PRAAx] input z w R B D E T a b H N) :
    Γ ⊢[PRAAx] independentRate powerF powerF (powerData z B a b) (powerData w D a b) (gain R E T*H) N := by
  let r := disk R E T
  let x := powerExponentData z B a b
  let y := powerExponentData w D a b
  let P := GaussianRadiusExponentialName.nameF powerExponentF
  let hN := h.andE₂.andE₂.andE₂.andE₁
  have ht := h.andE₂.andE₂.andE₁
  have ca := GaussianEulerCompactPowerVariation.common_input z R B E T a b h.andE₁ ht
  have cb := GaussianEulerCompactPowerVariation.common_input w R D E T a b h.andE₂.andE₁ ht
  have oa := GaussianEulerIntegrandName.power_input z B a b (.andI h.andE₁.andE₁ ht.andE₁)
  have ob := GaussianEulerIntegrandName.power_input w D a b (.andI h.andE₂.andE₁.andE₁ ht.andE₁)
  have parallel := GaussianRadiusExponentialLipschitzRate.independent_rate powerExponentF powerExponentF r x y
    (logRadius E T*H) N (.andI hN (.andI ca (.andI cb (exponent_rate z w R B D E T a b H N h))))
  have pa := GaussianExponentialRadiusIndependence.independent_radii_proper powerExponentF powerExponentF
    (powerRadius z B a b) r x x oa ca (cross_refl _ _ oa.andE₁)
  have pb := GaussianExponentialRadiusIndependence.independent_radii_proper powerExponentF powerExponentF
    (powerRadius w D a b) r y y ob cb (cross_refl _ _ ob.andE₁)
  have moved := GaussianNamedRateTransport.transport P P powerF powerF (GaussianRadiusExponentialName.data r x)
    (GaussianRadiusExponentialName.data r y) (powerData z B a b) (powerData w D a b)
    (expFactor r*(logRadius E T*H)) N hN parallel pa pb
  exact rate_parameters_congr powerF powerF (powerData z B a b) (powerData w D a b)
    (expFactor r*(logRadius E T*H)) N (gain R E T*H) N
    (by unfold gain r; ipra_ring) (.eqRefl N) moved

theorem actual_original_compact_power_parameter_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
      (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) ⟶
        independentRate powerF powerF (powerData (var 0) (var 3) (var 7) (var 8))
          (powerData (var 1) (var 4) (var 7) (var 8)) (gain (var 2) (var 5) (var 6)*var 9) (var 10)) :=
  closeUniv 11 (.impI (original_power_rate _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerCompactPowerParameterRate
