import IPRADerivations.Analysis.Euler.PowerScaling.GaussianEulerNamedPowerScalingFormula
import IPRADerivations.Analysis.Euler.PowerScaling.GaussianEulerNamedPowerScalingParameterFrozen
import IPRADerivations.Analysis.Euler.PowerScaling.GaussianEulerPowerScalingFrozenIntegrand
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateRadius
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedMultiplyRate

/-!
# The named inverse scale power at frozen parameters

Compare the original named exponential of -(z/r) log(c) to the original
rational inverse scale power at the literal decoded samples of c and r.
The common exponential disk and the sufficient late index depend on the
given names and compact bounds.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianEulerNamedPowerScalingPowerFrozen

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerNamedPowerScalingFormula (source exponentF exponentData powerF powerData)
open GaussianEulerPowerScalingKernel (scaleF scaleData scaleExpF scaleExpData)
open GaussianEulerNamedPowerScalingParameterFrozen (frozenPoint original_frozen_source original_frozen_rate)
open GaussianNamedPositiveLogarithm (numerator denominator)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameRingLaws (negativeF negativeData negative_fast)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianNameBounds (U all_samples_bounded)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalHorner (positive_product)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_radius_mono)
open GaussianRationalReciprocal (bound_congr)
open GaussianFastValueCut (exponent query_budget)
open GaussianExponentialReference (unit_monotone)
open GaussianPositiveRationalLogarithm (logF)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem unit_rate_after (F G : PR 2) (x y K k s : PTm n)
    (hk : Γ ⊢[PRAAx] le (exponent K s) k) (hr : Γ ⊢[PRAAx] independentRate F G x y K (unit k)) :
    Γ ⊢[PRAAx] independentRate F G x y one (unit s) :=
  GaussianNamedRateRadius.weaken F G x y K (unit k) one (unit s) (unit_positive k) (unit_positive s)
    (le_congr (.eqRefl _) (one_mul (unit k)).eqSymm (le_trans (query_budget K s) (unit_monotone hk))) hr

theorem multiply_same_denominator (F G H K : PR 2) (x y u v A C D M R : PTm n)
    (hD : Γ ⊢[PRAAx] le one D)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hg : Γ ⊢[PRAAx] pointCN G y)
    (hh : Γ ⊢[PRAAx] pointCN H u) (hk : Γ ⊢[PRAAx] pointCN K v)
    (hM : Γ ⊢[PRAAx] sampleBound G y M) (hR : Γ ⊢[PRAAx] sampleBound H u R)
    (hA : Γ ⊢[PRAAx] independentRate F H x u A D) (hC : Γ ⊢[PRAAx] independentRate G K y v C D) :
    Γ ⊢[PRAAx] independentRate (multiplyF F G) (multiplyF H K) (multiplyData F G x y) (multiplyData H K u v)
      (M*A+R*C) D := by
  have h := GaussianNamedMultiplyRate.independent_rate F G H K x y u v A D C D M R
    hD hD hf hg hh hk hM hR hA hC
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ (positive_product _ _ hD hD) hD
    (le_of_eq_add (d := zero) (by unfold GaussianNamedMultiplyRate.leadingNumerator; ipra_ring)) h

theorem constant_bound (w M : PTm n) (hw : Γ ⊢[PRAAx] bounded w M one) :
    Γ ⊢[PRAAx] sampleBound constantF w M := by
  refine .allI ?_
  have h : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift w) (Syn.shift M) one := by
    simpa [Fm.shift,Syn.shift] using hw.shift
  simpa only [sampleBound,Syn.shift] using
    bound_congr (constant_at (var 0) (Syn.shift w)).eqSymm (.eqRefl _) (.eqRefl _) h

private theorem frozen_observation_bound (F G : PR 2) (x y s q : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hr : Γ ⊢[PRAAx] independentRate F G x y one (unit s)) :
    Γ ⊢[PRAAx] bounded (ap2 G q y) (U F x+num 3) one := by
  have den := GaussianNamedInverseRate.denominator_positive (unit s) zero q (unit_positive (Γ := Γ) s)
  have h := distance_symmetric _ _ _ _ den (rate_at F G x y one (unit s) zero q hr)
  have uz := pw_zero (Γ := Γ) two
  have rn := congrAdd (congrMul (congrMul (.eqRefl one) uz) (.eqRefl (unit q)))
    (congrMul (.eqRefl (unit s)) (congrAdd uz (.eqRefl (unit q))))
  have rd := congrMul (congrMul (.eqRefl (unit s)) uz) (.eqRefl (unit q))
  have hpos := positive_product _ _ (positive_product _ _ (unit_positive (Γ := Γ) s) (le_refl one)) (unit_positive q)
  have raw := distance_congr (.eqRefl _) (.eqRefl _) rn rd h
  have close := distance_radius_mono _ _ _ _ (num 3) one hpos (le_refl one)
    (by ipra_le 𝔞(unit q)*sl (unit_positive (Γ := Γ) s)+𝔞(unit s)*sl (unit_positive (Γ := Γ) q)) raw
  have bound := GaussianReconstructionRoots.norm_from_distance _ _ (num 3) one (U F x) one
    (le_refl _) (le_refl _) close (GaussianNameBounds.sample_bound F x zero hf)
  exact bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring) bound

theorem frozen_sample_bound (F G : PR 2) (x y s : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hr : Γ ⊢[PRAAx] independentRate F G x y one (unit s)) :
    Γ ⊢[PRAAx] sampleBound G y (U F x+num 3) := by
  refine .allI ?_
  have fs : Γ.map Fm.shift ⊢[PRAAx] pointCN F (Syn.shift x) := by
    simpa [Fm.shift,Syn.shift] using hf.shift
  have rs : Γ.map Fm.shift ⊢[PRAAx] independentRate F G (Syn.shift x) (Syn.shift y) one (unit (Syn.shift s)) := by
    simpa [Fm.shift,Syn.shift] using hr.shift
  simpa only [sampleBound,Syn.shift,GaussianNameBounds.subst_U,PTm.subst_add,PTm.subst_num] using
    frozen_observation_bound F G (Syn.shift x) (Syn.shift y) (Syn.shift s) (var 0) fs rs

def frozenExponentData (F G : PR 2) (k z B x y : PTm n) : PTm n :=
  scaleData z B (numerator G k y) (denominator G k y) (numerator F k x) (denominator F k x)

def frozenPowerData (F G : PR 2) (k z B x y : PTm n) : PTm n :=
  scaleExpData z B (numerator G k y) (denominator G k y) (numerator F k x) (denominator F k x)

def exponentGain (F : PR 2) (R x E H : PTm n) : PTm n :=
  U (GaussianNamedPositiveLogarithm.nameF F) (GaussianNamedPositiveLogarithm.data x E)*(R*(H*H))+(H*R)*E

def exponentialRadius (F G : PR 2) (z R B x E y H : PTm n) : PTm n :=
  U (exponentF F G) (exponentData F G z R B x E y H)+num 3

def powerClock (F G : PR 2) (s z R B x E y H : PTm n) : PTm n :=
  exponent (exponentGain F R x E H)
    (exponent (GaussianRadiusExponentialLipschitzRate.factor (exponentialRadius F G z R B x E y H)) s)

@[simp] theorem subst_powerClock {m : ℕ} (σ : Fin n → PTm m) (F G : PR 2) (s z R B x E y H : PTm n) :
    Syn.subst σ (powerClock F G s z R B x E y H) = powerClock F G (Syn.subst σ s) (Syn.subst σ z)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ x) (Syn.subst σ E) (Syn.subst σ y) (Syn.subst σ H) := by
  simp [powerClock,exponentGain,exponentialRadius,exponentData]

theorem exponent_rate (F G : PR 2) (k z R B A x E T y H J : PTm n)
    (hs : Γ ⊢[PRAAx] source F G z R B A x E T y H J) : Γ ⊢[PRAAx]
    independentRate (exponentF F G) scaleF (exponentData F G z R B x E y H)
      (frozenExponentData F G k z B x y) (exponentGain F R x E H) (unit k) := by
  let P := GaussianEulerNamedPowerScalingParameter.nameF G
  let L := GaussianNamedPositiveLogarithm.nameF F
  let a := GaussianEulerNamedPowerScalingParameter.data z R B y H
  let b := GaussianNamedPositiveLogarithm.data x E
  let w := frozenPoint G k z B y
  let v := GaussianNamedPositiveLogarithm.rationalData F k x
  have p := GaussianEulerNamedPowerScalingParameter.regular G z R B A y H J hs.andE₁
  have l := GaussianNamedPositiveLogarithm.name_regular F x E T hs.andE₂
  have hp := original_frozen_rate G k z R B A y H J hs.andE₁
  have hl := GaussianNamedPositiveLogarithm.original_frozen_rate F k x E T hs.andE₂
  have decoder := GaussianNamedPositiveLogarithm.decoded_domain F k x E T hs.andE₂
  have l' : Γ ⊢[PRAAx] pointCN logF v :=
    GaussianPositiveRationalLogarithm.name_regular _ _ decoder.andE₁
  have ws := original_frozen_source G k z R B A y H J hs.andE₁
  have native := ws.andE₁.andE₂.andE₁
  have hRep := GaussianRationalHorner.ofGaussian_represents
    (GaussianEulerPowerScalingParameter.scaled z (denominator G k y)) (B*numerator G k y) native.andE₁
  have wb : Γ ⊢[PRAAx] bounded w (H*R) one :=
    GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ native.andE₁ (le_refl one) hRep
      (le_congr (by ipra_ring) (by ipra_ring) native.andE₂)
  have product := multiply_same_denominator P L constantF logF a b w v (R*(H*H)) E (unit k)
    (U L b) (H*R) (unit_positive _) p l (constant_regular _) l' (all_samples_bounded L b l)
    (constant_bound w (H*R) wb) hp hl
  exact GaussianEulerPowerScalingCompactRate.negative_rate _ _ _ _ _ _
    (multiply_fast P L a b p l) (multiply_fast constantF logF w v (constant_regular _) l')
    (unit_positive _) product

/-- Both exponential names run on their original radii and their own schedules. -/
theorem original_independent_rate (F G : PR 2) (s k z R B A x E T y H J : PTm n)
    (hs : Γ ⊢[PRAAx] source F G z R B A x E T y H J)
    (hk : Γ ⊢[PRAAx] le (powerClock F G s z R B x E y H) k) : Γ ⊢[PRAAx]
    independentRate (powerF F G) scaleExpF (powerData F G z R B x E y H) (frozenPowerData F G k z B x y)
      one (unit s) := by
  let D := exponentF F G
  let u := exponentData F G z R B x E y H
  let v := frozenExponentData F G k z B x y
  let S := exponentialRadius F G z R B x E y H
  let K := GaussianRadiusExponentialLipschitzRate.factor S
  let t := exponent K s
  have lin := GaussianEulerNamedPowerScalingParameter.regular G z R B A y H J hs.andE₁
  have log := GaussianNamedPositiveLogarithm.name_regular F x E T hs.andE₂
  have hu : Γ ⊢[PRAAx] pointCN D u := negative_fast _ _ (multiply_fast _ _ _ _ lin log)
  have d := GaussianNamedPositiveLogarithm.decoded_domain F k x E T hs.andE₂
  have hv : Γ ⊢[PRAAx] pointCN scaleF v := negative_fast _ _
    (GaussianEulerExponentialSubstitutionNamedKernel.linear_regular logF _ _ _
      (GaussianPositiveRationalLogarithm.name_regular _ _ d.andE₁))
  have h := unit_rate_after D scaleF u v (exponentGain F R x E H) k t hk (exponent_rate F G k z R B A x E T y H J hs)
  have u₀ := GaussianGammaFiniteApproximantName.exponential_input D u hu
  have v₀ := GaussianGammaFiniteApproximantName.exponential_input scaleF v hv
  have u₁ := GaussianExponentialRadiusIndependence.input_widen D (U D u) S u u₀ (le_add_right _ _)
  have v₁ : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input scaleF S v := .andI hv (frozen_sample_bound D scaleF u v t hu h)
  have common := GaussianRadiusExponentialLipschitzRate.independent_rate D scaleF S u v one (unit t)
    (.andI (unit_positive _) (.andI u₁ (.andI v₁ h)))
  have l := GaussianExponentialRadiusIndependence.same_input_cross D (U D u) S u u₀ u₁
  have r := GaussianExponentialRadiusIndependence.same_input_cross scaleF (U scaleF v) S v v₀ v₁
  have moved := GaussianNamedRateTransport.transport _ _ _ _ _ _ (powerData F G z R B x E y H)
    (frozenPowerData F G k z B x y) (K*one) (unit t) (unit_positive _) common l r
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ (unit_positive t) (unit_positive s)
    (le_congr (by ipra_ring) (by ipra_ring) (query_budget K s)) moved

theorem actual_named_inverse_scale_power_frozen_rate_closed (F G : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 12
      ((source F G (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) ⋏
        le (powerClock F G (var 0) (var 2) (var 3) (var 4) (var 6) (var 7) (var 9) (var 10)) (var 1)) ⟶
        independentRate (powerF F G) scaleExpF (powerData F G (var 2) (var 3) (var 4) (var 6) (var 7) (var 9) (var 10))
          (frozenPowerData F G (var 1) (var 2) (var 4) (var 6) (var 9)) one (unit (var 0))) :=
  closeUniv 12 (.impI (original_independent_rate F G _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerNamedPowerScalingPowerFrozen
