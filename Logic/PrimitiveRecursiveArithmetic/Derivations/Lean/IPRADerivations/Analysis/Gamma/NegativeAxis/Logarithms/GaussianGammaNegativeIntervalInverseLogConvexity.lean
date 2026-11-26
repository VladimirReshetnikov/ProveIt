import IPRADerivations.Analysis.Gamma.EulerProducts.Convexity.GaussianGammaEulerRationalLogHead
import IPRADerivations.Analysis.Gamma.NegativeAxis.Logarithms.GaussianGammaNegativeIntervalLogAbsolute
import IPRADerivations.Analysis.Gamma.NegativeAxis.Logarithms.GaussianGammaNegativeIntervalProductConvexity

/-!
# Weighted convexity of the logarithm of the inverse signed product

The powered signed product inequality reverses on reciprocation. The
original logarithm preserves the reversed rational order, and its exact
product and power laws give the corresponding named weighted comparison.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalInverseLogConvexity

open_ipra
open GaussianDominantPairAlgebra (radius_power)
open GaussianEulerDampedTimeRate (fraction_product)
open GaussianEulerDecayFactorBounds (fraction_is_radius_point)
open GaussianFactorBudget (power_positive)
open GaussianGammaEulerRationalHeadConvexity (barycenter weight)
open GaussianGammaEulerRationalLogHead (logarithm_power scaled_regular)
open GaussianGammaHalfSqrtBrackets (fraction_first_represents)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeIntervalGammaSign (productNumerator productDenominator)
open GaussianGammaNegativeIntervalLogAbsolute (inverseLogData inverse_source)
open GaussianGammaNegativeIntervalProductConvexity (center_guard powered_order)
open GaussianGammaNegativeIntervalProductSign (signedProduct fraction_readback)
open GaussianHarmonicLogarithmPower (power_source)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNaturalScaleProductName (productF productData)
open GaussianPositiveRationalLogarithm (fraction logF data name_regular)
open GaussianRationalHorner (qmul)
open GaussianRationalReciprocal (power powerF)
open GaussianRationalSyntheticDivision (qmul_congr)
open RationalArgmin (rationalLE_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => productF logF

private theorem signed_power_readback (a b N k : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] power (signedProduct a b N) k ≐
      fraction (pw (productNumerator a b N) k) (pw (productDenominator b N) k) := by
  let x := productNumerator a b N
  let d := productDenominator b N
  have hd := (inverse_source a b N h).andE₁
  have e := (fraction_readback a b N h.andE₁ h.andE₂).eqTrans (fraction_is_radius_point x d hd)
  exact (congrAp2 powerF (.eqRefl k) e).eqTrans
    ((radius_power x d k hd).eqTrans (fraction_is_radius_point _ _ (power_positive d k hd)).eqSymm)

theorem inverse_powered_comparison (a b c N r s : PTm n) (ha : Γ ⊢[PRAAx] guard a b)
    (hc : Γ ⊢[PRAAx] guard c b) : Γ ⊢[PRAAx]
    le (pw (productDenominator (weight r s*b) N) (weight r s)*
        (pw (productNumerator a b N) (succ r)*pw (productNumerator c b N) s))
      (pw (productNumerator (barycenter a c r s) (weight r s*b) N) (weight r s)*
        (pw (productDenominator b N) (succ r)*pw (productDenominator b N) s)) := by
  let x := barycenter a c r s
  let d := weight r s*b
  let w := weight r s
  have hx : Γ ⊢[PRAAx] guard x d := center_guard a b c r s ha.andE₁ hc.andE₁ ha.andE₂ hc.andE₂
  have hd := (inverse_source a b N ha).andE₁
  have hl := power_positive (productDenominator b N) (succ r) hd
  have hr := power_positive (productDenominator b N) s hd
  have hm := power_positive (productDenominator d N) w (inverse_source x d N hx).andE₁
  have product := (qmul_congr (signed_power_readback a b N (succ r) ha) (signed_power_readback c b N s hc)).eqTrans
    (fraction_product _ _ _ _ hl hr)
  have order := rationalLE_congr (congrFst product) (congrFst (signed_power_readback x d N w hx))
    (powered_order a b c N r s ha.andE₁ hc.andE₁ ha.andE₂ hc.andE₂)
  exact GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (fraction_first_represents _ _ (GaussianRationalHorner.positive_product _ _ hl hr))
    (fraction_first_represents _ _ hm) order

theorem weighted_order (a b c N r s : PTm n) (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c b) :
    Γ ⊢[PRAAx] realOrder L (addF L L)
      (productData logF (weight r s) (inverseLogData (barycenter a c r s) (weight r s*b) N))
      (addData (productData logF (succ r) (inverseLogData a b N)) (productData logF s (inverseLogData c b N))) := by
  let w := weight r s
  let x := barycenter a c r s
  let d := w*b
  let U := productDenominator b N
  let V := productDenominator d N
  let X := productNumerator a b N
  let Y := productNumerator c b N
  let W := productNumerator x d N
  have hx : Γ ⊢[PRAAx] guard x d := center_guard a b c r s ha.andE₁ hc.andE₁ ha.andE₂ hc.andE₂
  have sx := inverse_source a b N ha
  have sy := inverse_source c b N hc
  have sz := inverse_source x d N hx
  have px := power_source U X (succ r) sx
  have py := power_source U Y s sy
  have pz := power_source V W w sz
  have comb := GaussianHarmonicLogarithmProduct.product_source
    (pw U (succ r)) (pw X (succ r)) (pw U s) (pw Y s) (.andI px py)
  have h := GaussianPositiveRationalLogarithmOrder.logarithm_order
    (pw V w) (pw W w) (pw U (succ r)*pw U s) (pw X (succ r)*pw Y s) pz comb
    (inverse_powered_comparison a b c N r s ha hc)
  let x₀ := data (pw U (succ r)) (pw X (succ r))
  let y₀ := data (pw U s) (pw Y s)
  let x₁ := productData logF (succ r) (data U X)
  let y₁ := productData logF s (data U Y)
  have lift : Γ ⊢[PRAAx] crossEquivalent (addF logF logF) (addF L L) (addData x₀ y₀) (addData x₁ y₁) :=
    GaussianNamedGammaHalfShift.add_cross logF L logF L x₀ x₁ y₀ y₁
      (name_regular _ _ px) (scaled_regular _ _ _ sx)
      (name_regular _ _ py) (scaled_regular _ _ _ sy)
      (logarithm_power _ _ _ sx) (logarithm_power _ _ _ sy)
  let z₀ := data (pw V w) (pw W w)
  let z₁ := productData logF w (data V W)
  let paired := data (pw U (succ r)*pw U s) (pw X (succ r)*pw Y s)
  have summed := GaussianEulerPositiveTimePowerProduct.logarithm_product
    (pw U (succ r)) (pw X (succ r)) (pw U s) (pw Y s) (.andI px py)
  exact GaussianNamedRealOrderTransport.transport L logF logF (addF L L) z₁ z₀ paired (addData x₁ y₁)
    (cross_symm logF L z₀ z₁ (logarithm_power w V W sz))
    (cross_trans logF (addF logF logF) (addF L L) paired (addData x₀ y₀) (addData x₁ y₁) summed lift) h

theorem actual_signed_negative_interval_inverse_log_weighted_order_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      ((guard (var 0) (var 1) ⋏ guard (var 2) (var 1)) ⟶
        realOrder L (addF L L)
          (productData logF (weight (var 4) (var 5))
            (inverseLogData (barycenter (var 0) (var 2) (var 4) (var 5)) (weight (var 4) (var 5)*var 1) (var 3)))
          (addData (productData logF (succ (var 4)) (inverseLogData (var 0) (var 1) (var 3)))
            (productData logF (var 5) (inverseLogData (var 2) (var 1) (var 3))))) :=
  closeUniv 6 (.impI (weighted_order _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalInverseLogConvexity
