import IPRADerivations.Analysis.Beta.Primitives.GaussianBetaPrimitiveLinearStep
import IPRADerivations.Analysis.Beta.EulerProducts.GaussianEulerBetaEndpoint
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaWeierstrassApproximant

/-!
# Actual N-scaled upper endpoint of the original beta primitive

The actual named product retains the original positive-time power at
the encoded time (bN)/b and N times the unchanged stored beta primitive
factor. Every output is literally N times the original primitive sample
at the product program's actual clock. The argument is exactly one and
the checked original polynomial endpoint is the reciprocal Euler head.
The exact head times endpoint-constant identity is the natural point N.
No endpoint value, regularity or inverse identity is an input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaUpperEndpointName

open_ipra
open GaussianRationalHorner (qmul canonical_unique ofGaussian_canonical ofGaussian_represents positive_product)
open GaussianRationalSyntheticDivision (qone qone_canonical qmul_congr)
open GaussianRationalNaturalScale (natScale naturalPoint natScale_congr natScale_product)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianEulerIntegrandName (powerF powerData power_regular)
open GaussianBetaPrimitiveLinearStep (argument sample)
open GaussianTimeWeightedPolynomialIncrement (value)
open GaussianEulerBetaPolynomialPrimitive (primitive)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def endpointConstant (z B b N : PTm n) : PTm n := natScale N (value (primitive z B N) (argument (b*N) b N))
def nameF : PR 2 := multiplyF powerF constantF
def data (z B b N : PTm n) : PTm n := multiplyData powerF constantF (powerData z B (b*N) b) (endpointConstant z B b N)
def clock (p z B b N : PTm n) : PTm n := GaussianFastValueCut.exponent
  (GaussianNameArithmetic.multiplyModulus powerF constantF (powerData z B (b*N) b) (endpointConstant z B b N)) p
def upperSample (p z B b N : PTm n) : PTm n := ap2 nameF p (data z B b N)
ipra_subst endpointConstant [GaussianBetaPrimitiveLinearStep.argument, GaussianTimeWeightedPolynomialIncrement.value]
ipra_subst data
ipra_subst clock
ipra_subst upperSample

theorem power_source (z B b N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    GaussianEulerIntegrandName.source z B (b*N) b :=
  .andI hB (.andI (positive_product b N hb hN) hb)

theorem name_regular (z B b N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] pointCN nameF (data z B b N) :=
  multiply_fast _ _ _ _ (power_regular _ _ _ _ (power_source z B b N hB hb hN)) (constant_regular _)

theorem original_sample_at (p z B b N : PTm n) : Γ ⊢[PRAAx]
    upperSample p z B b N ≐ natScale N (sample (clock p z B b N) z B (b*N) b N) :=
  (GaussianNameArithmetic.multiply_at powerF constantF _ _ p).eqTrans
    ((GaussianNameArithmetic.recode_congr (qmul_congr (.eqRefl _) (constant_at _ _))).eqTrans
      ((GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qmul_canonical _ _)).eqTrans (natScale_product _ _ _)))

theorem argument_one (b N : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] argument (b*N) b N ≐ qone :=
  canonical_unique _ _ _ (b*N) (ofGaussian_canonical _ _ (positive_product b N hb hN))
    qone_canonical (positive_product b N hb hN)
    (ofGaussian_represents _ _ (positive_product b N hb hN)) (GaussianRationalReciprocal.qone_represents_scaled (b*N))

theorem original_factor_is_head_inverse (z B A b N : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianEulerBetaPoleGuard.source z B A)
    (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    value (primitive z B N) (argument (b*N) b N) ≐ GaussianEulerBetaProductValue.value z B N := by
  have atOne : Γ ⊢[PRAAx] GaussianRationalHorner.evaluate (primitive z B N) (argument (b*N) b N) ≐
      GaussianEulerBetaProductValue.value z B N :=
    (congrAp3 GaussianRationalHorner.hornerF (.eqRefl _) (.eqRefl _) (argument_one b N hb hN)).eqTrans
      (GaussianEulerBetaEndpoint.primitive_endpoint z B A N hz)
  exact (qmul_congr atOne (argument_one b N hb hN)).eqTrans
    (GaussianReciprocalHorner.qmul_one_right _ (GaussianEulerBetaProductValue.value_canonical _ _ _))

theorem original_constant_is_scaled_inverse (z B A b N : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianEulerBetaPoleGuard.source z B A)
    (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    endpointConstant z B b N ≐ natScale N (GaussianEulerBetaProductValue.value z B N) :=
  natScale_congr (.eqRefl _) (original_factor_is_head_inverse z B A b N hz hb hN)

theorem original_head_endpoint_constant (z B A b N : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianEulerBetaPoleGuard.source z B A)
    (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    qmul (GaussianGammaEulerHead.run z B N) (endpointConstant z B b N) ≐ naturalPoint N :=
  (qmul_congr (GaussianGammaEulerHead.program_at _ _ _) (original_constant_is_scaled_inverse z B A b N hz hb hN)).eqTrans
    ((natScale_product _ _ _).eqTrans
      ((natScale_congr (.eqRefl _) (GaussianEulerBetaProductValue.value_inverse z B A N hz)).eqTrans
        (GaussianEulerBetaProductValue.natural_scale_one N)))

theorem actual_upper_Beta_name_is_N_scaled_original_primitive_sample_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (upperSample (var 0) (var 1) (var 2) (var 3) (var 4) ≐
        natScale (var 4) (sample (clock (var 0) (var 1) (var 2) (var 3) (var 4)) (var 1) (var 2) (var 3*var 4) (var 3) (var 4))) :=
  closeUniv 5 (original_sample_at _ _ _ _ _)

theorem original_upper_Beta_endpoint_head_constant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((GaussianEulerBetaPoleGuard.source (var 0) (var 1) (var 2) ⋏ le one (var 3) ⋏ le one (var 4)) ⟶
      qmul (GaussianGammaEulerHead.run (var 0) (var 1) (var 4)) (endpointConstant (var 0) (var 1) (var 3) (var 4)) ≐ naturalPoint (var 4)) :=
  closeUniv 5 (.impI (original_head_endpoint_constant _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBetaUpperEndpointName
