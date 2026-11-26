import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaEulerRationalLog
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaEulerRationalHeadConvexity
import IPRADerivations.Analysis.Euler.GaussianHarmonicLogarithmPower
import IPRADerivations.Analysis.Names.GaussianNaturalScaleProductName
import IPRADerivations.Analysis.Logarithm.GaussianPositiveRationalLogarithmOrder
import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianNamedGammaHalfShift

/-!
# Weighted logarithmic comparison of the original inverse heads

Apply monotonicity of the original logarithm to the cleared
Euler-head power inequality with both sides inverted. The power
and product laws read the resulting order as the required weighted
comparison of the actual finite inverse head logarithms.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerRationalLogHead

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaEulerRationalHead (numerator denominator)
open GaussianGammaEulerRationalHeadConvexity (weight barycenter)
open GaussianGammaEulerRationalLog (headLogData head_log_source)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianNameArithmetic (addF addData multiply_fast multiply_equivalent)
open GaussianNameEquivalence (crossEquivalent cross_to_diagonal cross_refl cross_symm cross_trans)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNaturalScaleProductName (productF productData scale_product_cross)
open GaussianPositiveRationalLogarithm (logF data source name_regular)
open GaussianRationalHorner (positive_product)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => productF logF

theorem scaled_regular (m a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] pointCN L (productData logF m (data a b)) :=
  multiply_fast constantF logF _ _ (constant_regular (naturalPoint m)) (name_regular a b h)

theorem logarithm_power (m a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent logF L (data (pw a m) (pw b m)) (productData logF m (data a b)) := by
  let H := GaussianHarmonicLogarithmName.nameF
  let X := GaussianHarmonicLogarithmName.data a b
  let Z := data a b
  let T := naturalPoint m
  have hc := constant_regular (Γ := Γ) T
  have Hreg := GaussianHarmonicLogarithmName.name_regular a b h
  have Lreg := name_regular a b h
  have eq := cross_symm logF H Z X (GaussianHarmonicLogarithmName.cross_original a b h)
  have scale := scale_product_cross H m m (GaussianHarmonicLogarithmPower.radius a b) X
    (GaussianHarmonicLogarithmPower.original_input a b h) (le_refl m)
  have ret : Γ ⊢[PRAAx] crossEquivalent (productF H) L (productData H m X) (productData logF m Z) :=
    multiply_equivalent constantF constantF H logF T T X Z hc hc Hreg Lreg
      (cross_to_diagonal _ _ _ _ (cross_refl constantF T hc)) (cross_to_diagonal H logF X Z eq)
  exact cross_trans logF GaussianHarmonicLogarithmPower.scaledF L _ _ _
    (GaussianHarmonicLogarithmPower.original_logarithm_power a b m h)
    (cross_trans GaussianHarmonicLogarithmPower.scaledF (productF H) L _ _ _ scale ret)

theorem weighted_head_log_order (N a d b r s : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hd : Γ ⊢[PRAAx] le one d) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] realOrder L (addF L L)
      (productData logF (weight r s) (headLogData N (barycenter a d r s) (weight r s*b)))
      (addData (productData logF (succ r) (headLogData N a b)) (productData logF s (headLogData N d b))) := by
  let P := weight r s
  let A := barycenter a d r s
  let B := P*b
  let U := denominator N b
  let V := denominator N B
  let X := numerator (succ N) a b
  let Y := numerator (succ N) d b
  let W := numerator (succ N) A B
  have hc : Γ ⊢[PRAAx] le one A :=
    le_trans (positive_product _ _ (zero_lt_succ r) ha) (le_add_right _ _)
  have hB : Γ ⊢[PRAAx] le one B := positive_product _ _ (zero_lt_succ (r+s)) hb
  have sx : Γ ⊢[PRAAx] source U X := head_log_source N a b ha hb
  have sy : Γ ⊢[PRAAx] source U Y := head_log_source N d b hd hb
  have sz : Γ ⊢[PRAAx] source V W := head_log_source N A B hc hB
  have px := GaussianHarmonicLogarithmPower.power_source U X (succ r) sx
  have py := GaussianHarmonicLogarithmPower.power_source U Y s sy
  have pz := GaussianHarmonicLogarithmPower.power_source V W P sz
  have comb := GaussianHarmonicLogarithmProduct.product_source
    (pw U (succ r)) (pw X (succ r)) (pw U s) (pw Y s) (.andI px py)
  have powerOrder := GaussianGammaEulerRationalHeadConvexity.weighted_head_comparison (Γ := Γ) N a d b r s
  have order : Γ ⊢[PRAAx] le (pw V P*(pw X (succ r)*pw Y s))
      (pw W P*(pw U (succ r)*pw U s)) :=
    le_congr (mul_comm _ _) (.eqRefl _) powerOrder
  have h := GaussianPositiveRationalLogarithmOrder.logarithm_order
    (pw V P) (pw W P) (pw U (succ r)*pw U s) (pw X (succ r)*pw Y s) pz comb order
  let x₀ := data (pw U (succ r)) (pw X (succ r))
  let y₀ := data (pw U s) (pw Y s)
  let x₁ := productData logF (succ r) (data U X)
  let y₁ := productData logF s (data U Y)
  have lift : Γ ⊢[PRAAx] crossEquivalent (addF logF logF) (addF L L) (addData x₀ y₀) (addData x₁ y₁) :=
    GaussianNamedGammaHalfShift.add_cross logF L logF L x₀ x₁ y₀ y₁
      (name_regular _ _ px) (scaled_regular _ _ _ sx)
      (name_regular _ _ py) (scaled_regular _ _ _ sy)
      (logarithm_power _ _ _ sx) (logarithm_power _ _ _ sy)
  let z₀ := data (pw V P) (pw W P)
  let z₁ := productData logF P (data V W)
  let paired := data (pw U (succ r)*pw U s) (pw X (succ r)*pw Y s)
  have summed := GaussianEulerPositiveTimePowerProduct.logarithm_product
    (pw U (succ r)) (pw X (succ r)) (pw U s) (pw Y s) (.andI px py)
  exact GaussianNamedRealOrderTransport.transport L logF logF (addF L L) z₁ z₀ paired (addData x₁ y₁)
    (cross_symm logF L z₀ z₁ (logarithm_power P V W sz))
    (cross_trans logF (addF logF logF) (addF L L) paired (addData x₀ y₀) (addData x₁ y₁) summed lift) h

end LeanProofs.IPRA.Analysis.GaussianGammaEulerRationalLogHead
