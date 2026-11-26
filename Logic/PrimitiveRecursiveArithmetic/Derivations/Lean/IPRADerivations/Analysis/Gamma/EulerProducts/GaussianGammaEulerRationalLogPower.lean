import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaEulerRationalLog
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaEulerRationalHeadConvexity
import IPRADerivations.Analysis.LinearAlgebra.GaussianDeterminantSignTransport

/-!
# Exact affine power term of the finite Euler logarithm

The positive scale of the original logarithm of N is affine in
the rational argument. This cancels the power contribution in a
weighted convexity comparison of the original Euler logarithms.
-/

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerRationalLogPower

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN subst_pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaEulerRationalHeadConvexity (weight barycenter)
open GaussianGammaEulerRationalLog (powerF powerData power_regular)
open GaussianGammaFiniteApproximantName (logF log_regular logExponentF logExponentData log_exponent_regular)
open GaussianGammaWeierstrassApproximant (constant_product_cross constant_data_cross)
open GaussianNameArithmetic (addF addData multiplyF multiplyData multiplyModulus multiplyRawF multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (negativeF negativeData negativeRawF multiply_associative multiply_commutative)
open GaussianNamedGammaHalfShift (add_cross constant_sum)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qadd qmul qzero ofGaussian_canonical positive_product)
open GaussianRationalMatrixFiniteSums (minusOne negative_as_minusOne)
open GaussianRationalMetric (qnegative qnegative_canonical)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalSyntheticDivision (qmul_congr qzero_add)
open GaussianStirlingGammaLogarithm (arg)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "C" => constantF
local notation "L" => logF
local notation "scaledF" => GaussianNaturalScaleProductName.productF
local notation "scaledData" => GaussianNaturalScaleProductName.productData

private theorem negative_product_raw (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx]
    ap2 (multiplyRawF f C) p (GaussianNameArithmetic.data x minusOne) ≐ ap2 (negativeRawF f) p x := by
  let q := ap2 f p x
  have read := GaussianNameArithmetic.multiply_raw_at (Γ := Γ) f C p x (minusOne : PTm n)
  exact read.eqTrans ((qmul_congr (.eqRefl _) (constant_at p minusOne)).eqTrans
    ((GaussianRationalPowerAlgebra.qmul_commutative q minusOne).eqTrans
      ((negative_as_minusOne q).eqSymm.eqTrans
        ((qzero_add _ (qnegative_canonical q)).eqSymm.eqTrans
          (GaussianNameRingLaws.negative_raw_at f x p).eqSymm))))

private theorem negative_product_cross (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] crossEquivalent (negativeF f) (multiplyF f C) (negativeData x) (multiplyData f C x minusOne) := by
  apply cross_symm
  refine GaussianValueNormalizerExtensionality.normalized_names_equivalent
    (multiplyRawF f C) (negativeRawF f) (multiplyModulus f C x minusOne) (one+one)
    (GaussianNameArithmetic.data x minusOne) x zero
    (GaussianNameArithmetic.multiply_regular _ _ _ _ hf (constant_regular minusOne))
    (GaussianNameRingLaws.negative_regular f x hf) (.allI ?_)
  let m := Syn.shift x
  let p : PTm (n+1) := var 0
  have e := negative_product_raw (Γ := Γ.map Fm.shift) f p m
  have d := GaussianRationalPowerDifference.distance_refl_zero (Γ := Γ.map Fm.shift)
    (ap2 (negativeRawF f) p m) (unit p) (unit_positive p)
  simpa only [Syn.shift,GaussianNameArithmetic.subst_data,GaussianRationalMatrixFiniteSums.subst_minusOne,
    ConciseIPRA.PTm.subst_zero,m,p] using
    GaussianRationalDistanceOrder.distance_congr e.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) d

def positivePowerF : PR 2 := multiplyF C L
def positivePowerData (N a b : PTm n) : PTm n := multiplyData C L (fraction a b) N

theorem positive_power_regular (N a b : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] pointCN positivePowerF (positivePowerData N a b) :=
  multiply_fast C L _ _ (constant_regular _) (log_regular N hN)

theorem positive_power_cross (N a b : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] crossEquivalent powerF positivePowerF (powerData N a b) (positivePowerData N a b) := by
  let u := fraction a b
  let v := qnegative u
  let p := logExponentData (arg a) b N
  let k : PTm n := minusOne
  have hn := log_exponent_regular (arg a) b N hN
  have hl := log_regular N hN
  have hk := constant_regular (Γ := Γ) k
  have hv := constant_regular (Γ := Γ) v
  have hu := constant_regular (Γ := Γ) u
  have hq : Γ ⊢[PRAAx] qmul v k ≐ u :=
    (GaussianRationalPowerAlgebra.qmul_commutative v k).eqTrans
      ((negative_as_minusOne v).eqSymm.eqTrans
        (GaussianDeterminantSignTransport.negative_involution u (ofGaussian_canonical _ _ hb)))
  have hc := cross_trans _ _ _ _ _ _ (constant_product_cross v k) (constant_data_cross _ _ hq)
  have e₁ := negative_product_cross logExponentF p hn
  have e₂ := multiply_associative L C C N v k hl hv hk
  have e₃ := multiply_cross L L (multiplyF C C) C N N (multiplyData C C v k) u hl hl
    (multiply_fast C C _ _ hv hk) hu (cross_refl _ _ hl) hc
  have e₄ := multiply_commutative L C N u hl hu
  exact cross_trans _ _ _ _ _ _ e₁
    (cross_trans _ _ _ _ _ _ e₂ (cross_trans _ _ _ _ _ _ e₃ e₄))

private theorem scaled_fraction_code (m a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] qmul (naturalPoint m) (fraction a b) ≐ fraction (m*a) b :=
  (GaussianEulerDampedTimeRate.fraction_product m one a b (le_refl one) hb).eqTrans
    (GaussianEulerPositivePowerChartJacobian.fraction_congr (.eqRefl _) (one_mul b))

theorem scaled_power_cross (N a b m : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] crossEquivalent (scaledF powerF) positivePowerF
      (scaledData powerF m (powerData N a b)) (positivePowerData N (m*a) b) := by
  let P := positivePowerF
  let t := naturalPoint m
  let u := fraction a b
  let v := fraction (m*a) b
  have ht := constant_regular (Γ := Γ) t
  have hu := constant_regular (Γ := Γ) u
  have hv := constant_regular (Γ := Γ) v
  have ha := log_regular N hN
  have first := multiply_cross C C powerF P t t (powerData N a b) (positivePowerData N a b) ht ht
    (power_regular N a b hN) (positive_power_regular N a b hN) (cross_refl _ _ ht) (positive_power_cross N a b hN hb)
  have second := cross_symm _ _ _ _ (multiply_associative C C L t u N ht hu ha)
  have coef := cross_trans _ _ _ _ _ _ (constant_product_cross t u) (constant_data_cross _ _ (scaled_fraction_code m a b hb))
  have last := multiply_cross (multiplyF C C) C L L (multiplyData C C t u) v N N
    (multiply_fast C C _ _ ht hu) hv ha ha coef (cross_refl _ _ ha)
  exact cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ second last)

private theorem sum_positive_power (N a d b : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] crossEquivalent (addF positivePowerF positivePowerF) positivePowerF
      (addData (positivePowerData N a b) (positivePowerData N d b)) (positivePowerData N (a+d) b) := by
  let x := fraction a b
  let y := fraction d b
  let z := fraction (a+d) b
  have hx := constant_regular (Γ := Γ) x
  have hy := constant_regular (Γ := Γ) y
  have hz := constant_regular (Γ := Γ) z
  have hL := log_regular N hN
  have combine := GaussianNameRingLaws.right_distributive C C L x y N hx hy hL
  have coef := constant_sum x y z (GaussianRationalQuadratureSquareCells.fraction_add_same a d b hb)
  have last := multiply_cross (addF C C) C L L (addData x y) z N N
    (GaussianNameArithmetic.add_fast C C x y hx hy) hz hL hL coef (cross_refl _ _ hL)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ combine) last

theorem weighted_power_balance (N a d b r s : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] crossEquivalent (addF (scaledF powerF) (scaledF powerF)) (scaledF powerF)
      (addData (scaledData powerF (succ r) (powerData N a b)) (scaledData powerF s (powerData N d b)))
      (scaledData powerF (weight r s) (powerData N (barycenter a d r s) (weight r s*b))) := by
  let P := weight r s
  let A := barycenter a d r s
  let x := powerData N a b
  let y := powerData N d b
  let F := scaledF powerF
  let G := positivePowerF
  let u := positivePowerData N (succ r*a) b
  let v := positivePowerData N (s*d) b
  have hP : Γ ⊢[PRAAx] le one P := zero_lt_succ (r+s)
  have hl := log_regular N hN
  have hx : Γ ⊢[PRAAx] pointCN F (scaledData powerF (succ r) x) :=
    multiply_fast C powerF _ _ (constant_regular _) (power_regular N a b hN)
  have hy : Γ ⊢[PRAAx] pointCN F (scaledData powerF s y) :=
    multiply_fast C powerF _ _ (constant_regular _) (power_regular N d b hN)
  have left := add_cross F G F G (scaledData powerF (succ r) x) u (scaledData powerF s y) v
    hx (positive_power_regular N (succ r*a) b hN) hy (positive_power_regular N (s*d) b hN)
    (scaled_power_cross N a b (succ r) hN hb) (scaled_power_cross N d b s hN hb)
  have center := sum_positive_power N (succ r*a) (s*d) b hN hb
  have right := scaled_power_cross N A (P*b) P hN (positive_product _ _ hP hb)
  have eq := constant_data_cross _ _ (GaussianCompactRiemannSplit.fraction_cancel P A b hP hb)
  have cancel := multiply_cross C C L L (fraction (P*A) (P*b)) (fraction A b) N N
    (constant_regular _) (constant_regular _) hl hl eq (cross_refl _ _ hl)
  exact cross_trans _ _ _ _ _ _ left (cross_trans _ _ _ _ _ _ center
    (cross_symm _ _ _ _ (cross_trans _ _ _ _ _ _ right cancel)))

theorem actual_weighted_Euler_log_power_balance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le one (var 0) ⋏ le one (var 3)) ⟶
      crossEquivalent (addF (scaledF powerF) (scaledF powerF)) (scaledF powerF)
        (addData (scaledData powerF (succ (var 4)) (powerData (var 0) (var 1) (var 3)))
          (scaledData powerF (var 5) (powerData (var 0) (var 2) (var 3))))
        (scaledData powerF (weight (var 4) (var 5))
          (powerData (var 0) (barycenter (var 1) (var 2) (var 4) (var 5)) (weight (var 4) (var 5)*var 3)))) :=
  closeUniv 6 (.impI (weighted_power_balance _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaEulerRationalLogPower
