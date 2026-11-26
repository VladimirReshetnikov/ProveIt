import IPRADerivations.Analysis.Beta.GaussianBetaAllDegreeEulerInverse
import IPRADerivations.Analysis.Euler.GaussianEulerCompactPowerMajorant

/-!
# A numerical bound for every original finite beta endpoint sample

On the original positive-half-plane source, every observation of the
N-scaled upper beta primitive is bounded by
N*(A^(N+1)*N!)*3^((R+1)*radius(1,N)). The observation clock remains the
literal named product clock. There is no observation error in this bound,
and every positive finite degree is allowed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaUniformEndpointBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBetaAllDegreeEulerInverse (source endpointF endpointData)
open GaussianBetaUpperEndpointName (upperSample endpointConstant)
open GaussianEulerIntegrandName (powerF powerData)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianExponentialSmallPerturbation (smallSamples)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def endpointBound (R A N : PTm n) : PTm n := N*GaussianEulerBetaProductValue.denominator A N*
  GaussianEulerCompactPowerMajorant.majorant R one N
@[simp] theorem subst_endpointBound {m : ℕ} (σ : Fin n → PTm m) (R A N : PTm n) :
    Syn.subst σ (endpointBound R A N) = endpointBound (Syn.subst σ R) (Syn.subst σ A) (Syn.subst σ N) := by
  simp [endpointBound,GaussianEulerCompactPowerMajorant.majorant,GaussianEulerCompactPowerMajorant.exponentRadius,
    GaussianCompactLogarithmBounds.radius,one]

theorem endpoint_bound_positive (R A N : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    le one (endpointBound R A N) := by
  have hp : Γ ⊢[PRAAx] le one (GaussianEulerCompactPowerMajorant.majorant R one N) :=
    le_congr (GaussianPolynomialPerturbation.one_power _) (.eqRefl _)
      (pw_le_pw _ (le_of_eq_add (d := two) (by ipra_ring : Γ ⊢[PRAAx] (num 3 : PTm n) ≐ one+two)))
  exact positive_product _ _ (positive_product _ _ hN (GaussianEulerBetaProductValue.denominator_positive A N hA)) hp

theorem original_power_bound (p z R B A b N : PTm n) (h : Γ ⊢[PRAAx] source z R B A N)
    (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    bounded (ap2 powerF p (powerData z B (b*N) b)) (GaussianEulerCompactPowerMajorant.majorant R one N) one := by
  have hz : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.source z R B one :=
    .andI h.andE₁.andE₂.andE₁.andE₁ (.andI (le_refl one) h.andE₁.andE₂.andE₁.andE₂)
  have ht : Γ ⊢[PRAAx] GaussianCompactLogarithmBounds.domain (b*N) b one N :=
    .andI (.andI (positive_product _ _ hb h.andE₂) hb)
      (.andI (le_congr (one_mul b) (by ipra_ring) (mul_le_mul_right b h.andE₂))
        (le_congr (.eqRefl _) (mul_comm b N) (le_refl (b*N))))
  exact GaussianEulerCompactPowerMajorant.original_power_observation p z R B one N (b*N) b hz ht

theorem original_constant_bound (z R B A b N : PTm n) (h : Γ ⊢[PRAAx] source z R B A N)
    (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    bounded (endpointConstant z B b N) (N*GaussianEulerBetaProductValue.denominator A N) one := by
  have hz := (GaussianEulerBetaPoleGuard.original_integral_source z R B A N h.andE₁).andE₁
  exact bound_congr (GaussianBetaUpperEndpointName.original_constant_is_scaled_inverse z B A b N hz hb h.andE₂).eqSymm
    (.eqRefl _) (.eqRefl _) (GaussianNamedNaturalScale.scaled_bound N _ _ (GaussianEulerBetaProductValue.value_bound z B A N hz))

theorem original_sample_product (p z B b N : PTm n) : Γ ⊢[PRAAx]
    upperSample p z B b N ≐ qmul
      (ap2 powerF (GaussianBetaUpperEndpointName.clock p z B b N) (powerData z B (b*N) b)) (endpointConstant z B b N) :=
  (GaussianNameArithmetic.multiply_at powerF constantF _ _ p).eqTrans
    ((GaussianNameArithmetic.recode_congr (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) (constant_at _ _))).eqTrans
      (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qmul_canonical _ _)))

theorem original_sample_bound (p z R B A b N : PTm n) (h : Γ ⊢[PRAAx] source z R B A N)
    (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    bounded (upperSample p z B b N) (endpointBound R A N) one := by
  have hp := original_power_bound (GaussianBetaUpperEndpointName.clock p z B b N) z R B A b N h hb
  have hc := original_constant_bound z R B A b N h hb
  exact bound_congr (original_sample_product p z B b N).eqSymm (by unfold endpointBound; ipra_ring) (by ipra_ring)
    (bounded_product _ _ _ one _ one (le_refl one) (le_refl one) hp hc)

theorem original_all_samples_bound (z R B A b N : PTm n) (h : Γ ⊢[PRAAx] source z R B A N)
    (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    smallSamples GaussianBetaUpperEndpointName.nameF (GaussianBetaUpperEndpointName.data z B b N) (endpointBound R A N) one := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have hbs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift b) := by simpa [Fm.shift,Syn.shift] using hb.shift
  refine .allI ?_
  simpa only [smallSamples,upperSample,subst_endpointBound,GaussianBetaUpperEndpointName.subst_data,Syn.shift,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,one] using
      original_sample_bound (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A) (Syn.shift b) (Syn.shift N) hs hbs

theorem original_endpoint_disk (z R B A N : PTm n) (h : Γ ⊢[PRAAx] source z R B A N) : Γ ⊢[PRAAx]
    smallSamples endpointF (endpointData z B N) (endpointBound R A N) one :=
  original_all_samples_bound z R B A one N h (le_refl one)

theorem original_all_degree_endpoint_numerical_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((source (var 0) (var 1) (var 2) (var 3) (var 5) ⋏ le one (var 4)) ⟶
      smallSamples GaussianBetaUpperEndpointName.nameF
        (GaussianBetaUpperEndpointName.data (var 0) (var 2) (var 4) (var 5)) (endpointBound (var 1) (var 3) (var 5)) one) :=
  closeUniv 6 (.impI (original_all_samples_bound _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBetaUniformEndpointBound
