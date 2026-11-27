import IPRADerivations.Analysis.Gamma.EulerProducts.Convexity.GaussianGammaEulerMidpointHeadGap
import IPRADerivations.Analysis.Gamma.EulerProducts.Convexity.GaussianGammaEulerRationalLogConvexity
import IPRADerivations.Analysis.Stirling.Bounds.Multiplicative.GaussianStirlingMultiplicativeBoundsLog
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.Endpoints.Order.GaussianEulerPowerChartTimeOrder

/-!
# A rational logarithmic midpoint margin in finite Euler heads

The head-ratio comparison is transported by monotonicity and the exact
product and square laws for the original positive logarithm. Its
positive relative difference gives a rational lower bound on the margin.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerMidpointLogHeadGap

open_ipra
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaEulerMidpointHeadGap (large small gap gap_split head_gap square_power)
open GaussianGammaEulerRationalHead (numerator denominator)
open GaussianGammaEulerRationalLog (headLogData head_log_source)
open GaussianGammaEulerRationalLogHead (scaled_regular logarithm_power)
open GaussianGammaEulerRationalLogOrder (add_order order_refl)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNaturalScaleProductName (productF productData)
open GaussianPositiveRationalLogarithm (logF data source fraction name_regular)
open GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => productF logF

def margin (a d : PTm n) : PTm n := fraction (gap a d) (large a d)
def centerData (N a d b : PTm n) : PTm n := productData logF two (headLogData N (a+d) (two*b))
def weightedData (N a d b : PTm n) : PTm n := addData (headLogData N a b) (headLogData N d b)

ipra_subst margin

theorem data_congr {a b c d : PTm n} (ha : Γ ⊢[PRAAx] a ≐ c) (hb : Γ ⊢[PRAAx] b ≐ d) :
    Γ ⊢[PRAAx] data a b ≐ data c d := by
  simpa only [GaussianPositiveRationalLogarithm.subst_data,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (data (var 0) (var 1) : PTm 2)
      (σ := ![a,b]) (σ' := ![c,d]) (fun i => by fin_cases i; exact ha; exact hb)

theorem fraction_congr {a b c d : PTm n} (ha : Γ ⊢[PRAAx] a ≐ c) (hb : Γ ⊢[PRAAx] b ≐ d) :
    Γ ⊢[PRAAx] fraction a b ≐ fraction c d := by
  simpa only [GaussianPositiveRationalLogarithm.subst_fraction,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (fraction (var 0) (var 1) : PTm 2)
      (σ := ![a,b]) (σ' := ![c,d]) (fun i => by fin_cases i; exact ha; exact hb)

theorem margin_source (a d : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hd : Γ ⊢[PRAAx] le one d) :
    Γ ⊢[PRAAx] source (large a d) (small a d) := by
  have hp := le_trans ha (le_add_right a d)
  exact .andI (positive_product _ _ hp hp)
    (positive_product _ _ (positive_product _ _ (positive_product _ _ RationalAlgebra.two_positive
      RationalAlgebra.two_positive) ha) hd)

theorem margin_order (a d : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hd : Γ ⊢[PRAAx] le one d) :
    Γ ⊢[PRAAx] realOrder constantF logF (margin a d) (data (large a d) (small a d)) := by
  let A := small a d
  let C := gap a d
  let U := large a d
  have h := (GaussianStirlingMultiplicativeBoundsLog.logarithm_rectangles A C (margin_source a d ha hd).andE₂).andE₁
  have e := gap_split (Γ := Γ) a d
  have left := GaussianGammaWeierstrassApproximant.constant_data_cross (margin a d) (fraction C (A+C))
    (fraction_congr (.eqRefl C) e)
  have hx : Γ ⊢[PRAAx] source (A+C) A :=
    .andI (le_trans (margin_source a d ha hd).andE₂ (le_add_right _ _)) (margin_source a d ha hd).andE₂
  have right := GaussianGammaCompactCutoffAlignment.cross_data_congr logF logF _ _ _ _
    (.eqRefl (data (A+C) A)) (data_congr e.eqSymm (.eqRefl A))
    (cross_refl _ _ (name_regular _ _ hx))
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ left right h

theorem head_log_order (N a d b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hd : Γ ⊢[PRAAx] le one d)
    (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] realOrder (addF constantF L) (addF logF logF)
      (addData (margin a d) (centerData N a d b)) (weightedData N a d b) := by
  let U := denominator N b
  let V := denominator N (two*b)
  let X := numerator (succ N) a b
  let Y := numerator (succ N) d b
  let Z := numerator (succ N) (a+d) (two*b)
  let M := large a d
  let m := small a d
  let T := data M m
  let C := centerData N a d b
  have hx := head_log_source N a b ha hb
  have hy := head_log_source N d b hd hb
  have hz := head_log_source N (a+d) (two*b) (le_trans ha (le_add_right a d))
    (positive_product _ _ RationalAlgebra.two_positive hb)
  have hz2 := GaussianHarmonicLogarithmPower.power_source V Z two hz
  have hT := margin_source a d ha hd
  have left := GaussianHarmonicLogarithmProduct.product_source M m (pw V two) (pw Z two) (.andI hT hz2)
  have right := GaussianHarmonicLogarithmProduct.product_source U X U Y (.andI hx hy)
  have power : Γ ⊢[PRAAx] le ((M*pw V two)*(X*Y)) ((m*pw Z two)*(U*U)) :=
    le_congr (by ipra_ring) (by ipra_ring) (head_gap N a d b)
  have compared := GaussianPositiveRationalLogarithmOrder.logarithm_order
    (M*pw V two) (m*pw Z two) (U*U) (X*Y) left right power
  have eq1 := GaussianEulerPositiveTimePowerProduct.logarithm_product M m (pw V two) (pw Z two) (.andI hT hz2)
  have eq2 := GaussianEulerPositiveTimePowerProduct.logarithm_product U X U Y (.andI hx hy)
  have eq3 := add_cross logF logF logF L T T (data (pw V two) (pw Z two)) C
    (name_regular _ _ hT) (name_regular _ _ hT) (name_regular _ _ hz2) (scaled_regular _ _ _ hz)
    (cross_refl _ _ (name_regular _ _ hT)) (logarithm_power two V Z hz)
  have ord := GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _
    (cross_symm _ _ _ _ (cross_trans _ _ _ _ _ _ eq1 eq3)) eq2 compared
  have lower := add_order constantF logF L L (margin a d) T C C (margin_order a d ha hd)
    (order_refl _ _ (scaled_regular two V Z hz))
  exact GaussianEulerPowerChartTimeOrder.order_trans _ _ _ _ _ _ lower ord

end LeanProofs.IPRA.Analysis.GaussianGammaEulerMidpointLogHeadGap
