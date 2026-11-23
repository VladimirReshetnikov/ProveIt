import IPRADerivations.Analysis.GaussianBetaUpperEndpointName
import IPRADerivations.Analysis.GaussianGammaEulerReciprocalInverse
import IPRADerivations.Analysis.GaussianGammaEulerShiftLimit
import IPRADerivations.Analysis.GaussianBetaUpperPowerCancellation

/-!
# The actual upper beta endpoint is the original finite Euler inverse

Original named product exchange preserves all multiplication clocks.
The original polynomial endpoint supplies head times endpoint constant
equal to N; the original positive-time power and finite Euler exponent
supply 1/N. Their actual named product is one. The existing pole-safe
Q_N reciprocal therefore equals the actual N-scaled beta endpoint by
the checked reciprocal uniqueness theorem.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaUpperEndpointInverse

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qmul ofGaussian_represents canonical_unique)
open GaussianRationalSyntheticDivision (qone qone_canonical)
open GaussianRationalNaturalScale (natScale naturalPoint natScale_as_product natScale_represents)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaFiniteApproximantName (logExponentF logExponentData exponentialInputData qF qData q_regular)
open GaussianEulerIntegrandName (powerF powerData power_regular)
open GaussianBetaUpperEndpointName (nameF data endpointConstant)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans cross_symm)
open GaussianNameRingLaws (oneF multiply_commutative)
open GaussianGammaWeierstrassApproximant (constant_product_cross constant_data_cross)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaEulerShiftLimit (reciprocalPoint)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def expF : PR 2 := GaussianRadiusExponentialName.nameF logExponentF
def expData (z B N : PTm n) : PTm n := exponentialInputData logExponentF (logExponentData z B N)
def powerCancellation (z B b N : PTm n) : Fm PTm n :=
  crossEquivalent (multiplyF powerF expF) constantF
    (multiplyData powerF expF (powerData z B (b*N) b) (expData z B N)) (reciprocalPoint N)

theorem exponential_regular (z B N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN expF (expData z B N) :=
  GaussianRadiusExponentialName.name_regular _ _ _
    (GaussianGammaFiniteApproximantName.exponential_input _ _
      (GaussianGammaFiniteApproximantName.log_exponent_regular z B N hN))

theorem natural_reciprocal_one (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    qmul (naturalPoint N) (reciprocalPoint N) ≐ qone := by
  have scaled : Γ ⊢[PRAAx] natScale N (reciprocalPoint N) ≐ qone :=
    canonical_unique _ _ _ N (GaussianRationalNaturalScale.natScale_canonical _ _) qone_canonical hN
      (natScale_represents _ _ _ _ hN (ofGaussian_represents _ _ hN))
      (GaussianRationalReciprocal.qone_represents_scaled N)
  exact (natScale_as_product _ _).eqSymm.eqTrans scaled

theorem original_endpoint_inverse_product (z B A b N : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianEulerBetaPoleGuard.source z B A)
    (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N)
    (hCancellation : Γ ⊢[PRAAx] powerCancellation z B b N) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF qF nameF) oneF
      (multiplyData qF nameF (qData z B N) (data z B b N)) (qData z B N) := by
  let H := GaussianGammaEulerHead.run z B N
  let E := expData z B N
  let P := powerData z B (b*N) b
  let C := endpointConstant z B b N
  have hP := power_regular z B (b*N) b (GaussianBetaUpperEndpointName.power_source z B b N hz.andE₁ hb hN)
  have hE := exponential_regular z B N hN
  have hH := constant_regular (Γ := Γ) H
  have hC := constant_regular (Γ := Γ) C
  have hQ := q_regular z B N hN
  have hU := GaussianBetaUpperEndpointName.name_regular z B b N hz.andE₁ hb hN
  have hSwap := multiply_fast constantF powerF C P hC hP
  have swapEndpoint := multiply_cross qF qF nameF (multiplyF constantF powerF)
    (qData z B N) (qData z B N) (data z B b N) (multiplyData constantF powerF C P)
      hQ hQ hU hSwap (cross_refl _ _ hQ) (multiply_commutative powerF constantF P C hP hC)
  have exchange := GaussianGammaReciprocalInverse.named_product_exchange constantF expF constantF powerF H E C P hH hE hC hP
  have headPair : Γ ⊢[PRAAx] crossEquivalent (multiplyF constantF constantF) constantF
      (multiplyData constantF constantF H C) (naturalPoint N) :=
    cross_trans _ _ _ _ _ _ (constant_product_cross H C)
      (constant_data_cross _ _ (GaussianBetaUpperEndpointName.original_head_endpoint_constant z B A b N hz hb hN))
  have expPair : Γ ⊢[PRAAx] crossEquivalent (multiplyF expF powerF) constantF
      (multiplyData expF powerF E P) (reciprocalPoint N) :=
    cross_trans _ _ _ _ _ _ (multiply_commutative expF powerF E P hE hP) hCancellation
  have pairs := multiply_cross (multiplyF constantF constantF) constantF (multiplyF expF powerF) constantF
    (multiplyData constantF constantF H C) (naturalPoint N) (multiplyData expF powerF E P) (reciprocalPoint N)
      (multiply_fast _ _ _ _ hH hC) (constant_regular _) (multiply_fast _ _ _ _ hE hP) (constant_regular _)
        headPair expPair
  exact cross_trans _ _ _ _ _ _ swapEndpoint (cross_trans _ _ _ _ _ _ exchange
    (cross_trans _ _ _ _ _ _ pairs
      (GaussianGammaReciprocalInverse.constant_inverse _ _ _ (natural_reciprocal_one N hN))))

theorem original_endpoint_matches_euler (z R B A a d b N : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianEulerBetaPoleGuard.source z B A)
    (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N)
    (hEuler : Γ ⊢[PRAAx] GaussianGammaEulerReciprocalInverse.source z R B a d N)
    (hCancellation : Γ ⊢[PRAAx] powerCancellation z B b N) : Γ ⊢[PRAAx]
    crossEquivalent GaussianGammaEulerReciprocalInverse.eulerF nameF
      (GaussianGammaEulerReciprocalInverse.eulerData z R B d N) (data z B b N) := by
  have input := (GaussianGammaEulerReciprocalInverse.original_euler_inverse z R B a d N hEuler).andE₁
  exact GaussianBoundedInverseApartness.reciprocal_matches_inverse qF nameF _ _ _
    (q_regular z B N hN) (GaussianBetaUpperEndpointName.name_regular z B b N hz.andE₁ hb hN) input.andE₂
      (original_endpoint_inverse_product z B A b N hz hb hN hCancellation)

theorem original_euler_source (z R B A N : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A)
    (hR : Γ ⊢[PRAAx] le one R) (hCut : Γ ⊢[PRAAx] le (two*R) N) : Γ ⊢[PRAAx]
    GaussianGammaEulerReciprocalInverse.source z R B one A N :=
  .andI (.andI (.andI hR hz.andE₂.andE₁)
    (.andI (le_refl one) (.andI hz.andE₁
      (GaussianEulerBetaPoleGuard.all_finite_guards z B A (two*R) hz.andE₂.andE₂)))) hCut

theorem original_upper_product (z R B A b N : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A)
    (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF qF nameF) oneF
      (multiplyData qF nameF (qData z B N) (data z B b N)) (qData z B N) :=
  original_endpoint_inverse_product z B A b N
    (GaussianEulerBetaPoleGuard.original_integral_source z R B A N hz).andE₁ hb hN
    (GaussianBetaUpperPowerCancellation.original_product z B b N hz.andE₂.andE₁.andE₁ hb hN)

theorem original_upper_inverse (z R B A b N : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A)
    (hR : Γ ⊢[PRAAx] le one R) (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N)
    (hCut : Γ ⊢[PRAAx] le (two*R) N) : Γ ⊢[PRAAx]
    crossEquivalent nameF GaussianGammaEulerReciprocalInverse.eulerF
      (data z B b N) (GaussianGammaEulerReciprocalInverse.eulerData z R B A N) :=
  cross_symm _ _ _ _ (original_endpoint_matches_euler z R B A one A b N
    (GaussianEulerBetaPoleGuard.original_integral_source z R B A N hz).andE₁ hb hN
    (original_euler_source z R B A N hz hR hCut)
    (GaussianBetaUpperPowerCancellation.original_product z B b N hz.andE₂.andE₁.andE₁ hb hN))

def source (z R B A b N : PTm n) : Fm PTm n :=
  GaussianEulerLowerPowerCoefficients.source z R B A ⋏
    (le one R ⋏ (le one b ⋏ (le one N ⋏ le (two*R) N)))

theorem original_upper_name_binding (z R B A b N : PTm n) (h : Γ ⊢[PRAAx] source z R B A b N) : Γ ⊢[PRAAx]
    GaussianNameReciprocal.input qF (GaussianGammaEulerReciprocalInverse.eulerHeight z R B A N) (qData z B N) ⋏
      (GaussianEuclideanDistanceName.pointCN nameF (data z B b N) ⋏
        crossEquivalent nameF GaussianGammaEulerReciprocalInverse.eulerF
          (data z B b N) (GaussianGammaEulerReciprocalInverse.eulerData z R B A N)) :=
  .andI (GaussianGammaEulerReciprocalInverse.original_euler_inverse z R B one A N
    (original_euler_source z R B A N h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₂)).andE₁
      (.andI (GaussianBetaUpperEndpointName.name_regular z B b N h.andE₁.andE₂.andE₁.andE₁
        h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₁)
          (original_upper_inverse z R B A b N h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂.andE₁
            h.andE₂.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₂))

theorem original_upper_Beta_endpoint_is_finite_Euler_inverse_product_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      ((GaussianEulerLowerPowerCoefficients.source (var 0) (var 1) (var 2) (var 3) ⋏ le one (var 4) ⋏ le one (var 5)) ⟶
        crossEquivalent (multiplyF qF nameF) oneF
          (multiplyData qF nameF (qData (var 0) (var 2) (var 5)) (data (var 0) (var 2) (var 4) (var 5)))
          (qData (var 0) (var 2) (var 5))) :=
  closeUniv 6 (.impI (original_upper_product _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

theorem original_N_scaled_Beta_primitive_endpoint_is_actual_Euler_reciprocal_name_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
        GaussianNameReciprocal.input qF
          (GaussianGammaEulerReciprocalInverse.eulerHeight (var 0) (var 1) (var 2) (var 3) (var 5))
          (qData (var 0) (var 2) (var 5)) ⋏
          (GaussianEuclideanDistanceName.pointCN nameF (data (var 0) (var 2) (var 4) (var 5)) ⋏
            crossEquivalent nameF GaussianGammaEulerReciprocalInverse.eulerF
              (data (var 0) (var 2) (var 4) (var 5))
              (GaussianGammaEulerReciprocalInverse.eulerData (var 0) (var 1) (var 2) (var 3) (var 5)))) :=
  closeUniv 6 (.impI (original_upper_name_binding _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBetaUpperEndpointInverse
