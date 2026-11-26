import IPRADerivations.Analysis.Euler.PowerScaling.Named.GaussianEulerNamedPowerScalingPowerFrozen
import IPRADerivations.Analysis.Gamma.Integrals.GaussianEulerNamedPowerScalingGammaFrozen
import IPRADerivations.Analysis.Euler.PowerScaling.GaussianEulerPowerScalingImproper

/-!
# The original named Gamma-side formula at frozen parameters

Freeze both scales at the same literal sample index. Their actual
rational Gamma-side product approximates the original named product at
independent observation times. The freeze clock uses only the requested
precision, the named data, and the supplied compact guards.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianEulerNamedPowerScalingFormulaFrozen

open_ipra
open GaussianEulerNamedPowerScalingFormula (source nameF data powerF powerData gammaF gammaData)
open GaussianEulerNamedPowerScalingPowerFrozen (powerClock frozenPowerData frozen_sample_bound
  multiply_same_denominator constant_bound unit_rate_after)
open GaussianEulerPowerScalingImproper (formulaF formulaData)
open GaussianEulerPowerScalingKernel (scaleExpF)
open GaussianNamedPositiveLogarithm (numerator denominator)
open GaussianNamedPositiveReciprocalFrozen (frozen)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U all_samples_bounded)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at denominator_positive)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalMetric (distanceBounded)
open GaussianFastValueCut (exponent query_budget)
open GaussianExponentialReference (unit_monotone)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def frozenData (F G : PR 2) (k z R B A x y H J : PTm n) : PTm n :=
  formulaData z R B A (numerator G k y) (denominator G k y) (numerator F k x) (denominator F k x) H J

def innerGain (F G : PR 2) (z R B A x E y H J : PTm n) : PTm n :=
  U (gammaF G) (gammaData z R B A y H J)+(U (powerF F G) (powerData F G z R B x E y H)+num 3)

def formulaGain (F G : PR 2) (z R B A x E y H J : PTm n) : PTm n :=
  U (multiplyF (powerF F G) (gammaF G))
      (multiplyData (powerF F G) (gammaF G) (powerData F G z R B x E y H) (gammaData z R B A y H J))+
    H*innerGain F G z R B A x E y H J

def freezeClock (F G : PR 2) (s z R B A x E y H J : PTm n) : PTm n :=
  let t := exponent (formulaGain F G z R B A x E y H J) s
  powerClock F G t z R B x E y H+GaussianEulerNamedPowerScalingGammaFrozen.frozenClock G t z R B A y H J+
    exponent (H*H) t

def observationClock (s : PTm n) : PTm n := exponent (num 3) s

ipra_subst freezeClock [formulaGain, innerGain, powerData, gammaData, GaussianEulerNamedPowerScalingFormula.exponentData, GaussianGammaFiniteApproximantName.exponentialInputData]

ipra_subst observationClock

@[simp] theorem subst_named_source {m : ℕ} (σ : Fin n → PTm m) (F G : PR 2) (z R B A x E T y H J : PTm n) :
    (source F G z R B A x E T y H J).subst σ = source F G (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ A) (Syn.subst σ x) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ y) (Syn.subst σ H) (Syn.subst σ J) := by
  simp [source,GaussianEulerNamedPowerScalingParameter.source,one]

@[simp] theorem subst_named_data {m : ℕ} (σ : Fin n → PTm m) (F G : PR 2) (z R B A x E y H J : PTm n) :
    Syn.subst σ (data F G z R B A x E y H J) = data F G (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ A) (Syn.subst σ x) (Syn.subst σ E) (Syn.subst σ y) (Syn.subst σ H) (Syn.subst σ J) := by
  simp [data,powerData,gammaData,GaussianEulerNamedPowerScalingFormula.exponentData,
    GaussianGammaFiniteApproximantName.exponentialInputData]

ipra_subst frozenData [formulaData, GaussianEulerCompactExhaustionScaled.referenceData, numerator, denominator, GaussianGammaReciprocalInverse.gammaData, GaussianGammaReciprocalInverse.gammaHeight, GaussianEulerPowerScalingParameter.scaled]

/-- The certificate uses the actual rational chart parameters on the original cofinal sampler. -/
theorem original_frozen_source (F G : PR 2) (k z R B A x E T y H J : PTm n)
    (hs : Γ ⊢[PRAAx] source F G z R B A x E T y H J) : Γ ⊢[PRAAx]
    GaussianEulerPowerChartCofinalSchedule.source z R B A
      (numerator G k y) (denominator G k y) (numerator F k x) (denominator F k x) H J T := by
  have rr := GaussianNamedPositiveLogarithm.decoded_domain G k y H J hs.andE₁.andE₂.andE₂
  have cc := GaussianNamedPositiveLogarithm.decoded_domain F k x E T hs.andE₂
  have hT := GaussianDominantScalarOrder.factor_positive_left T (denominator F k x)
    (le_trans cc.andE₁.andE₁ cc.andE₂.andE₂)
  exact .andI (.andI hs.andE₁.andE₁ (.andI rr.andE₁.andE₁ (.andI rr.andE₁.andE₂
    (.andI hs.andE₁.andE₂.andE₂.andE₂.andE₁ (.andI hs.andE₁.andE₂.andE₁ rr.andE₂)))))
    (.andI rr.andE₁ (.andI cc.andE₁
      (.andI (.andI hs.andE₁.andE₂.andE₁ hT)
        (.andI rr.andE₂.andE₂ cc.andE₂.andE₂))))

theorem frozen_regular (F G : PR 2) (k z R B A x E T y H J : PTm n)
    (hs : Γ ⊢[PRAAx] source F G z R B A x E T y H J) :
    Γ ⊢[PRAAx] pointCN formulaF (frozenData F G k z R B A x y H J) := by
  let e := numerator G k y
  let f := denominator G k y
  let c := numerator F k x
  let d := denominator F k x
  have dec := GaussianNamedPositiveLogarithm.decoded_domain F k x E T hs.andE₂
  have power := GaussianEulerPowerScalingFrozenIntegrand.scale_regular z B e f c d dec.andE₁
  have gamma := GaussianEulerIntegralGammaIdentification.original_gamma_regular
    (GaussianEulerPowerScalingParameter.scaled z f) (H*R) (B*e) (J*A)
    (GaussianEulerNamedPowerScalingParameterFrozen.original_frozen_source G k z R B A y H J hs.andE₁)
  exact multiply_fast _ _ _ _ (constant_regular (frozen G k y)) (multiply_fast _ _ _ _ power gamma)

theorem original_independent_rate (F G : PR 2) (s k z R B A x E T y H J : PTm n)
    (hs : Γ ⊢[PRAAx] source F G z R B A x E T y H J)
    (hk : Γ ⊢[PRAAx] le (freezeClock F G s z R B A x E y H J) k) : Γ ⊢[PRAAx]
    independentRate (nameF F G) formulaF (data F G z R B A x E y H J)
      (frozenData F G k z R B A x y H J) one (unit s) := by
  let P := powerF F G
  let G₀ := gammaF G
  let I := GaussianNamedPositiveReciprocal.nameF G
  let p := powerData F G z R B x E y H
  let g := gammaData z R B A y H J
  let i := GaussianNamedPositiveReciprocal.data y H
  let P' := scaleExpF
  let G' := GaussianGammaReciprocalInverse.gammaF
  let p' := frozenPowerData F G k z B x y
  let g' := GaussianEulerNamedPowerScalingGammaFrozen.frozenData G k z R B A y H J
  let i' := frozen G k y
  let t := exponent (formulaGain F G z R B A x E y H J) s
  let K₁ := powerClock F G t z R B x E y H
  let K₂ := GaussianEulerNamedPowerScalingGammaFrozen.frozenClock G t z R B A y H J
  let K₃ := exponent (H*H) t
  have k₁ : Γ ⊢[PRAAx] le K₁ k := le_trans (le_add_right K₁ K₂) (le_trans (le_add_right (K₁+K₂) K₃) hk)
  have k₂ : Γ ⊢[PRAAx] le K₂ k := le_trans (le_add_left K₂ K₁) (le_trans (le_add_right (K₁+K₂) K₃) hk)
  have k₃ : Γ ⊢[PRAAx] le K₃ k := le_trans (le_add_left K₃ (K₁+K₂)) hk
  have a := GaussianEulerNamedPowerScalingPowerFrozen.original_independent_rate F G t k z R B A x E T y H J hs k₁
  have b := GaussianEulerNamedPowerScalingGammaFrozen.original_independent_rate G t k z R B A y H J hs.andE₁ k₂
  have c := unit_rate_after I constantF i i' (H*H) k t k₃
    (GaussianNamedPositiveReciprocalFrozen.original_rate G k y H J hs.andE₁.andE₂.andE₂)
  have hparam := GaussianEulerNamedPowerScalingParameter.named_half_plane G z R B A y H J hs.andE₁
  have hg : Γ ⊢[PRAAx] pointCN G₀ g := GaussianNamedGamma.name_regular _ _ _ hparam
  have hi : Γ ⊢[PRAAx] pointCN I i := GaussianNamedPositiveReciprocal.name_regular G y H J hs.andE₁.andE₂.andE₂
  have hlog := GaussianNamedPositiveLogarithm.name_regular F x E T hs.andE₂
  have hexp : Γ ⊢[PRAAx] pointCN (GaussianEulerNamedPowerScalingFormula.exponentF F G)
      (GaussianEulerNamedPowerScalingFormula.exponentData F G z R B x E y H) :=
    GaussianNameRingLaws.negative_fast _ _ (multiply_fast _ _ _ _ hparam.andE₁ hlog)
  have hp : Γ ⊢[PRAAx] pointCN P p :=
    GaussianRadiusExponentialName.name_regular _ _ _
      (GaussianGammaFiniteApproximantName.exponential_input _ _ hexp)
  have hc := GaussianNamedPositiveLogarithm.decoded_domain F k x E T hs.andE₂
  have hr := GaussianNamedPositiveLogarithm.decoded_domain G k y H J hs.andE₁.andE₂.andE₂
  have hp' : Γ ⊢[PRAAx] pointCN P' p' :=
    GaussianEulerPowerScalingFrozenIntegrand.scale_regular z B (numerator G k y) (denominator G k y)
      (numerator F k x) (denominator F k x) hc.andE₁
  have hg' : Γ ⊢[PRAAx] pointCN G' g' := GaussianEulerIntegralGammaIdentification.original_gamma_regular
    (GaussianEulerPowerScalingParameter.scaled z (denominator G k y)) (H*R) (B*numerator G k y) (J*A)
    (GaussianEulerNamedPowerScalingParameterFrozen.original_frozen_source G k z R B A y H J hs.andE₁)
  have hb := GaussianEulerCompactExhaustionNormalization.inverse_bound (numerator G k y) (denominator G k y) H
    hr.andE₁.andE₁ hr.andE₂.andE₁
  have inner := multiply_same_denominator P G₀ P' G' p g p' g' one one (unit t) (U G₀ g) (U P p+num 3)
    (unit_positive t) hp hg hp' hg' (all_samples_bounded G₀ g hg) (frozen_sample_bound P P' p p' t hp a) a b
  let N := multiplyF P G₀
  let N' := multiplyF P' G'
  let u := multiplyData P G₀ p g
  let u' := multiplyData P' G' p' g'
  have reg := multiply_fast P G₀ p g hp hg
  have reg' := multiply_fast P' G' p' g' hp' hg'
  have inner' : Γ ⊢[PRAAx] independentRate N N' u u' (innerGain F G z R B A x E y H J) (unit t) :=
    GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ (unit_positive t) (unit_positive t)
      (le_of_eq_add (d := zero) (by unfold innerGain; ipra_ring)) inner
  have whole := multiply_same_denominator I N constantF N' i u i' u' one (innerGain F G z R B A x E y H J)
    (unit t) (U N u) H (unit_positive t) hi reg (constant_regular _) reg'
    (all_samples_bounded N u reg) (constant_bound i' H hb) c inner'
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ (unit_positive t) (unit_positive s)
    (le_congr (by dsimp only [formulaGain,N,u]; ipra_ring) (one_mul (unit t)).eqSymm
      (query_budget (formulaGain F G z R B A x E y H J) s)) whole

/-- The observation times may be chosen independently once they reach the displayed clock. -/
theorem original_scheduled_observations (F G : PR 2) (s p q k z R B A x E T y H J : PTm n)
    (hs : Γ ⊢[PRAAx] source F G z R B A x E T y H J)
    (hk : Γ ⊢[PRAAx] le (freezeClock F G (observationClock s) z R B A x E y H J) k)
    (hp : Γ ⊢[PRAAx] le (observationClock s) p) (hq : Γ ⊢[PRAAx] le (observationClock s) q) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF F G) p (data F G z R B A x E y H J))
      (ap2 formulaF q (frozenData F G k z R B A x y H J)) one (unit s) := by
  let t := observationClock s
  have h := rate_at _ _ _ _ one (unit t) p q
    (original_independent_rate F G t k z R B A x E T y H J hs hk)
  have den := denominator_positive (unit t) p q (unit_positive (Γ := Γ) t)
  have growp := unit_monotone hp
  have growq := unit_monotone hq
  have bound := distance_radius_mono _ _ _ _ (num 3) (unit t) den (unit_positive t)
    (by
      unfold rateNumerator rateDenominator
      ipra_le 𝔞(unit t*unit q)*sl growp+𝔞(unit t*unit p)*sl growq) h
  exact distance_radius_mono _ _ _ _ one (unit s) (unit_positive t) (unit_positive s)
    (le_congr (.eqRefl _) (one_mul (unit t)).eqSymm (query_budget (num 3) s)) bound

theorem actual_named_Gamma_power_scaling_formula_frozen_rate_closed (F G : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 12
      ((source F G (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) ⋏
        le (freezeClock F G (var 0) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 9) (var 10) (var 11)) (var 1)) ⟶
        independentRate (nameF F G) formulaF (data F G (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 9) (var 10) (var 11))
          (frozenData F G (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 9) (var 10) (var 11)) one (unit (var 0))) :=
  closeUniv 12 (.impI (original_independent_rate F G _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_named_Gamma_power_scaling_formula_frozen_observations_closed (F G : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 14
      ((source F G (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13) ⋏
        (le (freezeClock F G (observationClock (var 0)) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9)
          (var 11) (var 12) (var 13)) (var 3) ⋏ (le (observationClock (var 0)) (var 1) ⋏ le (observationClock (var 0)) (var 2)))) ⟶
        distanceBounded (ap2 (nameF F G) (var 1) (data F G (var 4) (var 5) (var 6) (var 7) (var 8) (var 9)
          (var 11) (var 12) (var 13))) (ap2 formulaF (var 2) (frozenData F G (var 3) (var 4) (var 5) (var 6) (var 7)
            (var 8) (var 11) (var 12) (var 13))) one (unit (var 0))) :=
  closeUniv 14 (.impI (original_scheduled_observations F G _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerNamedPowerScalingFormulaFrozen
