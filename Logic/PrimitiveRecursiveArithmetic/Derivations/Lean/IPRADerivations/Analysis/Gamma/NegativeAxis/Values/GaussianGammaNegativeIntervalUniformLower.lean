import IPRADerivations.Analysis.Gamma.NegativeAxis.Values.GaussianGammaNegativeIntervalGammaSign
import IPRADerivations.Analysis.Gamma.NegativeAxis.Derivatives.Products.GaussianGammaNegativeProductDerivativeRate
import IPRADerivations.Analysis.Stirling.Bounds.GaussianStirlingMultiplicativeBoundsLog

/-!
# Uniform positive floor for the signed original negative Gamma

The literal shift product has a finite bound depending only on the
interval index. The positive terminal Gamma floor and the inverse
recurrence then give a floor independent of the rational encoding.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalUniformLower

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianFactorBudget (power_positive)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeIntervalGammaSign (signedF signedData inversePoint productNumerator productDenominator)
open GaussianGammaNegativeIntervalProductSign (signUnit signedProduct fraction_readback)
open GaussianGammaNegativeProductDerivative (rising_product)
open GaussianGammaNegativeProductDerivativeRate (productCap prefix_bounds)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameArithmetic (multiplyF)
open GaussianNameEquivalence (cross_symm)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNamedRightHalfPlane (source marginPoint)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (ofGaussian_represents positive_product qmul)
open GaussianRationalMetric (bounded bounded_iff)
open GaussianRationalPowerAlgebra (unit_bounded unit_power norm_one)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalSyntheticDivision (qone)
open GaussianStirlingGammaLogarithm (arg gammaMargin gammaData gamma_regular gammaRealF gamma_real_cross gamma_real_positive)
open GaussianStirlingMultiplicativeBoundsLog (constant_order fractions_order)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def productBound (N : PTm n) : PTm n := productCap (succ N) (succ N)
def lowerDenominator (N : PTm n) : PTm n := gammaMargin*productBound N

private theorem unit_fraction (a b : PTm n) (ha : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] bounded (fraction a b) one one := by
  have hb := le_trans ha.andE₁ (le_of_lt ha.andE₂)
  have square := LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono (le_of_lt ha.andE₂) (le_of_lt ha.andE₂)
  apply (bounded_iff _ (arg a) b one one hb (le_refl one) (ofGaussian_represents _ _ hb)).iffMpr
  have e : Γ ⊢[PRAAx] ComplexLogarithmRemainder.normSq (arg a) ≐ a*a :=
    GaussianGammaGaussReference.scaled_one_norm a
  exact le_congr (e.eqSymm.eqTrans (by ipra_ring)) (by ipra_ring) square

theorem shift_product_bound (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] bounded (signedProduct a b N) (productBound N) one := by
  let j := succ N
  let P := GaussianGammaNegativeIntervalNative.product a b N
  let I := fraction a b
  let f := GaussianGammaPoleFiniteFactors.differenceProduct (arg a) b j
  let sign := signUnit j
  have hb := le_trans h.andE₁ (le_of_lt h.andE₂)
  have prefixBound := (prefix_bounds a a b j zero one j h h (le_refl one)
    (GaussianRationalPowerDifference.distance_refl_zero _ _ (le_refl one)) (le_refl j)).andE₁
  have prod : Γ ⊢[PRAAx] bounded P (productBound N) one :=
    bound_congr (rising_product (arg a) b j hb).eqSymm (by ipra_ring) (by ipra_ring)
      (bounded_product f I (productBound N) one one one (le_refl one) (le_refl one) prefixBound (unit_fraction a b h))
  have sb : Γ ⊢[PRAAx] bounded sign one one :=
    unit_bounded _ (unit_power _ j ((GaussianRationalRelativeTwoTerm.norm_negative qone).eqTrans norm_one))
  exact bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (bounded_product sign P one one (productBound N) one (le_refl one) (le_refl one) sb prod)

theorem numerator_bound (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) : Γ ⊢[PRAAx]
    le (productNumerator a b N) (productBound N*productDenominator b N) := by
  let c := productNumerator a b N
  let d := productDenominator b N
  let R := productBound N
  have hb := le_trans h.andE₁ (le_of_lt h.andE₂)
  have hd := positive_product (Γ := Γ) _ _ (power_positive b (succ N) hb) hb
  have all := bound_congr (fraction_readback a b N h.andE₁ h.andE₂) (.eqRefl _) (.eqRefl _)
    (shift_product_bound a b N h)
  have rep := ofGaussian_represents (arg c) d hd
  have cleared := (bounded_iff (fraction c d) (arg c) d R one hd (le_refl one) rep).iffMp all
  exact LeanProofs.IPRA.DiophantineNumberTheory.Coprime.le_of_sq_le
    (le_congr ((by ipra_ring : Γ ⊢[PRAAx] (one*one)*ComplexLogarithmRemainder.normSq (arg c) ≐
      ComplexLogarithmRemainder.normSq (arg c)).eqTrans (GaussianGammaGaussReference.scaled_one_norm c))
      (by ipra_ring) cleared)

theorem signed_gamma_source (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] source signedF (signedData a b N) (lowerDenominator N) := by
  let c := productNumerator a b N
  let d := productDenominator b N
  let I := inversePoint a b N
  let L := lowerDenominator N
  let t := fraction (one : PTm n) gammaMargin
  let y := gammaData (b+a) b
  have old := GaussianGammaNegativeIntervalGammaSign.signed_gamma_source a b N h
  have hc : Γ ⊢[PRAAx] le one c :=
    GaussianDominantScalarOrder.factor_positive_left _ _
      (le_congr (.eqRefl _) (mul_comm _ _) old.andE₂.andE₁)
  have hm : Γ ⊢[PRAAx] le one gammaMargin := by unfold gammaMargin; ipra_le 17
  have hR := power_positive (Γ := Γ) (succ (succ N)) (succ N) (zero_lt_succ _)
  have hL : Γ ⊢[PRAAx] le one L := positive_product _ _ hm hR
  have hb := le_trans h.andE₁ (le_of_lt h.andE₂)
  have hs : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source (b+a) b :=
    .andI (le_trans hb (le_add_right b a)) hb
  have hy := gamma_regular (b+a) b hs
  have code := GaussianGammaDigammaStep.unit_step_value gammaMargin hm
  have floor : Γ ⊢[PRAAx] realOrder constantF gammaF t y :=
    GaussianNamedRealOrderTransport.transport constantF constantF gammaRealF gammaF _ _ _ _
      (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ code)
      (cross_symm _ _ _ _ (gamma_real_cross (b+a) b hs)) (gamma_real_positive (b+a) b hs).andE₂.andE₂
  have lifted := GaussianNamedRealOrderLinear.fractional_order constantF gammaF d c t y hc (constant_regular t) hy floor
  have scaled := GaussianNamedRealOrderTransport.transport constantF (multiplyF constantF constantF) signedF signedF _ _ _ _
    (cross_symm _ _ _ _ (GaussianGammaWeierstrassApproximant.constant_product_cross I t))
    (cross_symm _ _ _ _ (GaussianGammaNegativeIntervalGammaSign.signed_gamma_identity a b N h)) lifted
  have eq : Γ ⊢[PRAAx] qmul I t ≐ fraction d (gammaMargin*c) :=
    (GaussianStirlingOddCoefficients.fraction_product d c one gammaMargin hc hm).eqTrans
      (GaussianCompactRiemannName.fraction_congr _ _ _ _ (by ipra_ring) (mul_comm _ _))
  have hcL := positive_product (Γ := Γ) _ _ hm hc
  have cmp : Γ ⊢[PRAAx] le ((gammaMargin*c)*one) (d*L) :=
    le_congr (by ipra_ring) (by unfold L lowerDenominator; ipra_ring) (mul_le_mul_right gammaMargin (numerator_bound a b N h))
  have rational := fractions_order one L d (gammaMargin*c) hL hcL cmp
  have lower := constant_order (marginPoint L) (qmul I t)
    (RationalArgmin.rationalLE_congr (congrFst (GaussianGammaDigammaStep.unit_step_value L hL)) (congrFst eq).eqSymm rational)
  exact .andI old.andE₁ (.andI hL (GaussianEulerPowerChartTimeOrder.order_trans _ _ _ _ _ _ lower scaled))

theorem actual_original_negative_Gamma_uniform_signed_floor_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (guard (var 0) (var 1) ⟶ source signedF (signedData (var 0) (var 1) (var 2)) (lowerDenominator (var 2))) :=
  closeUniv 3 (.impI (signed_gamma_source _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalUniformLower
