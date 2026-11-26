import IPRADerivations.Analysis.Names.Rates.Scaling.GaussianBoundedConstantProductRate
import IPRADerivations.Analysis.Names.Differences.GaussianNamedDifferenceAlgebra
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateRadius
import IPRADerivations.Analysis.Trigonometry.Pi.GaussianPiRationalScaleFactors
import IPRADerivations.Analysis.Trigonometry.Hyperbolic.GaussianSineProductImaginaryExponentialShift

/-!
# A uniform first-order rate for the original hyperbolic sine name

The original signed exponential rates combine at the common step
`1/(kB)`. The unweighted first-order term is built at the original base
representation `A/B` and is independent of the internal step scale `k`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianSineProductImaginaryHyperbolicDerivative

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBoundedConstantProductName (constantF constant_regular)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (multiply_associative multiply_commutative)
open GaussianNamedDifference (name_regular)
open GaussianNamedDifferenceQuotientProperness (difference_proper)
open GaussianNamedDifferenceRate (leadingNumerator leadingDenominator rate_parameters_congr)
open GaussianNamedInverseRate (independentRate)
open GaussianPiRationalScaleFactors (signedF signedData signed_regular)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded)
open GaussianSineProductImaginaryExponentialShift (source errorCoefficient)
open GaussianSineProductImaginaryHyperbolic (expF expData sinhF sinhData)
open GaussianSineProductImaginaryLogDerivative (rationalReal)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Diff" => GaussianNamedDifference.nameF
local notation "difference" => GaussianNamedDifference.data
local notation "Scale" => GaussianPiRationalScale.nameF
local notation "I" => GaussianSineProductImaginaryExponentialShift.incrementF
local notation "W" => GaussianSineProductImaginaryExponentialShift.weightedF
local notation "iData" => GaussianSineProductImaginaryExponentialShift.incrementData
local notation "wData" => GaussianSineProductImaginaryExponentialShift.weightedData

def negativeHalf : PTm n := GaussianPiRationalScale.point true one two
def branchF : PR 2 := multiplyF expF signedF
def branchData (s : Bool) (A B R x : PTm n) : PTm n :=
  multiplyData expF signedF (expData s A B R x) (signedData s x)
def derivativeF : PR 2 := multiplyF constantF (Diff branchF branchF)
def derivativeData (A B R x : PTm n) : PTm n :=
  multiplyData constantF (Diff branchF branchF) negativeHalf (difference (branchData true A B R x) (branchData false A B R x))
def incrementF : PR 2 := Diff sinhF sinhF
def incrementData (A B k R x : PTm n) : PTm n :=
  difference (sinhData (k*A+one) (k*B) R x) (sinhData A B R x)
def weightedF : PR 2 := multiplyF constantF derivativeF
def weightedData (A B k R x : PTm n) : PTm n :=
  multiplyData constantF derivativeF (rationalReal one (k*B)) (derivativeData A B R x)
def error (A B R x : PTm n) : PTm n := errorCoefficient true A B R x+errorCoefficient false A B R x

private theorem exp_regular (s : Bool) (A B R x : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hA : Γ ⊢[PRAAx] le A (R*B)) : Γ ⊢[PRAAx] pointCN expF (expData s A B R x) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (GaussianPiRationalScale.exponential_input s A B R x hB hA)

theorem derivative_regular (A B R x : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hA : Γ ⊢[PRAAx] le A (R*B)) : Γ ⊢[PRAAx] pointCN derivativeF (derivativeData A B R x) :=
  multiply_fast _ _ _ _ (constant_regular _)
    (name_regular _ _ _ _ (multiply_fast _ _ _ _ (exp_regular true A B R x hB hA) (signed_regular true x))
      (multiply_fast _ _ _ _ (exp_regular false A B R x hB hA) (signed_regular false x)))

private theorem pull_scalar (f g : PR 2) (a x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF f (multiplyF constantF g)) (multiplyF constantF (multiplyF f g))
      (multiplyData f (multiplyF constantF g) x (multiplyData constantF g a y))
      (multiplyData constantF (multiplyF f g) a (multiplyData f g x y)) := by
  have ha := constant_regular (Γ := Γ) a
  have flip := multiply_cross f f _ _ x x _ _ hf hf (multiply_fast _ _ _ _ ha hg) (multiply_fast _ _ _ _ hg ha)
    (cross_refl _ _ hf) (multiply_commutative constantF g a y ha hg)
  have regroup := cross_symm _ _ _ _ (multiply_associative f g constantF x y a hf hg ha)
  have swap := multiply_commutative (multiplyF f g) constantF (multiplyData f g x y) a
    (multiply_fast _ _ _ _ hf hg) ha
  exact cross_trans _ _ _ _ _ _ flip (cross_trans _ _ _ _ _ _ regroup swap)

private theorem weighted_branch (s : Bool) (A B k R x : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hA : Γ ⊢[PRAAx] le A (R*B)) (hE : Γ ⊢[PRAAx] le one (k*B)) (hRE : Γ ⊢[PRAAx] le one (R*(k*B))) :
    Γ ⊢[PRAAx] crossEquivalent W (multiplyF constantF branchF) (wData s A B k R x)
      (multiplyData constantF branchF (rationalReal one (k*B)) (branchData s A B R x)) := by
  let v := expData s A B R x
  let a := rationalReal one (k*B)
  let b := signedData s x
  have hv := exp_regular s A B R x hB hA
  have hb := signed_regular (Γ := Γ) s x
  have step := GaussianPiRationalScaleFactors.split_step s (k*B) R x hE hRE
  have lift := multiply_cross expF expF Scale (multiplyF constantF signedF) v v _ _ hv hv
    (GaussianPiRationalScale.regular s one (k*B) R x hE hRE) (multiply_fast _ _ _ _ (constant_regular a) hb)
    (cross_refl _ _ hv) step
  exact cross_trans _ _ _ _ _ _ lift (pull_scalar expF signedF a v b hv hb)

private theorem weight_rearrange (A B k R x : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A (R*B))
    (hE : Γ ⊢[PRAAx] le one (k*B)) (hRE : Γ ⊢[PRAAx] le one (R*(k*B))) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF constantF (Diff W W)) weightedF
      (multiplyData constantF (Diff W W) negativeHalf (difference (wData true A B k R x) (wData false A B k R x)))
      (weightedData A B k R x) := by
  let a := rationalReal one (k*B)
  let m := (negativeHalf : PTm n)
  let z := branchData true A B R x
  let w := branchData false A B R x
  let F := multiplyF constantF branchF
  let v := multiplyData constantF branchF a z
  let u := multiplyData constantF branchF a w
  let y := difference z w
  have ha := constant_regular (Γ := Γ) a
  have hm := constant_regular (Γ := Γ) m
  have hz := multiply_fast expF signedF (expData true A B R x) (signedData true x)
    (exp_regular true A B R x hB hA) (signed_regular true x)
  have hw := multiply_fast expF signedF (expData false A B R x) (signedData false x)
    (exp_regular false A B R x hB hA) (signed_regular false x)
  have stepReg (s : Bool) := multiply_fast expF Scale (expData s A B R x) (GaussianPiRationalScale.data s one (k*B) R x)
    (exp_regular s A B R x hB hA) (GaussianPiRationalScale.regular s one (k*B) R x hE hRE)
  have hv : Γ ⊢[PRAAx] pointCN F v := multiply_fast _ _ _ _ ha hz
  have hu : Γ ⊢[PRAAx] pointCN F u := multiply_fast _ _ _ _ ha hw
  have hy := name_regular branchF branchF z w hz hw
  have df := difference_proper W F W F _ v _ u (stepReg true) hv (stepReg false) hu
    (weighted_branch true A B k R x hB hA hE hRE) (weighted_branch false A B k R x hB hA hE hRE)
  have distribute := GaussianNamedDifferenceAlgebra.distribute constantF branchF branchF a z w ha hz hw
  have lift := multiply_cross constantF constantF (Diff W W) (multiplyF constantF (Diff branchF branchF)) m m _ _
    hm hm (name_regular _ _ _ _ (stepReg true) (stepReg false)) (multiply_fast _ _ _ _ ha hy)
    (cross_refl _ _ hm) (cross_trans _ _ _ _ _ _ df (cross_symm _ _ _ _ distribute))
  exact cross_trans _ _ _ _ _ _ lift (pull_scalar constantF (Diff branchF branchF) a m y hm hy)

private theorem increment_rearrange (A B k R x : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A (R*B))
    (hE : Γ ⊢[PRAAx] le one (k*B)) (hL : Γ ⊢[PRAAx] le (k*A+one) (R*(k*B))) :
    Γ ⊢[PRAAx] crossEquivalent incrementF (multiplyF constantF (Diff I I)) (incrementData A B k R x)
      (multiplyData constantF (Diff I I) negativeHalf (difference (iData true A B k R x) (iData false A B k R x))) := by
  let a := expData true (k*A+one) (k*B) R x
  let b := expData false (k*A+one) (k*B) R x
  let c := expData true A B R x
  let d := expData false A B R x
  let m := (negativeHalf : PTm n)
  let E := Diff expF expF
  have ha := exp_regular true (k*A+one) (k*B) R x hE hL
  have hb := exp_regular false (k*A+one) (k*B) R x hE hL
  have hc := exp_regular true A B R x hB hA
  have hd := exp_regular false A B R x hB hA
  have hm := constant_regular (Γ := Γ) m
  have shuffle := GaussianNamedDifferenceAlgebra.shuffle expF expF expF expF a b c d ha hb hc hd
  have move := GaussianNamedDifferenceAlgebra.distribute constantF E E m (difference a b) (difference c d) hm
    (name_regular _ _ _ _ ha hb) (name_regular _ _ _ _ hc hd)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ move)
    (multiply_cross constantF constantF (Diff E E) (Diff I I) m m _ _ hm hm
      (name_regular _ _ _ _ (name_regular _ _ _ _ ha hb) (name_regular _ _ _ _ hc hd))
      (name_regular _ _ _ _ (name_regular _ _ _ _ ha hc) (name_regular _ _ _ _ hb hd))
      (cross_refl _ _ hm) shuffle)

theorem independent_rate (A B k R x : PTm n) (h : Γ ⊢[PRAAx] source A B k R x) : Γ ⊢[PRAAx]
    independentRate incrementF weightedF (incrementData A B k R x) (weightedData A B k R x) (error A B R x) ((k*B)*(k*B)) := by
  let E := k*B
  let D := E*E
  let m := (negativeHalf : PTm n)
  let S := Diff I I
  let T := Diff W W
  let y := difference (iData true A B k R x) (iData false A B k R x)
  let z := difference (wData true A B k R x) (wData false A B k R x)
  have hR := h.andE₁
  have hB := h.andE₂.andE₁
  have hk := h.andE₂.andE₂.andE₁
  have hA := h.andE₂.andE₂.andE₂.andE₁
  have hL := h.andE₂.andE₂.andE₂.andE₂.andE₁
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ hk hB
  have hRE : Γ ⊢[PRAAx] le one (R*E) := positive_product _ _ hR hE
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hE hE
  have inc (s : Bool) := name_regular expF expF _ _ (exp_regular s (k*A+one) E R x hE hL) (exp_regular s A B R x hB hA)
  have wgt (s : Bool) := multiply_fast expF Scale _ _ (exp_regular s A B R x hB hA)
    (GaussianPiRationalScale.regular s one E R x hE hRE)
  have raw := GaussianNamedDifferenceRate.original_rate I I W W _ _ _ _
    (errorCoefficient true A B R x) D (errorCoefficient false A B R x) D
    (.andI (.andI hD hD) (.andI (.andI (inc true) (inc false)) (.andI (.andI (wgt true) (wgt false))
      (.andI (GaussianSineProductImaginaryExponentialShift.increment_rate true A B k R x h)
        (GaussianSineProductImaginaryExponentialShift.increment_rate false A B k R x h)))))
  have rate : Γ ⊢[PRAAx] independentRate S T y z (error A B R x) D :=
    GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ (positive_product _ _ hD hD) hD
      (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by dsimp only [leadingNumerator,leadingDenominator,error]; ipra_ring)) raw
  have b : Γ ⊢[PRAAx] bounded m one one :=
    GaussianPiRationalScale.point_bound true one two one one (le_succ_self one) (le_refl one) (le_mul_mono (le_refl one) (le_succ_self one))
  have scaled := GaussianBoundedConstantProductRate.original_rate S T one m y z (error A B R x) D hD b rate
  have moveL := GaussianBoundedConstantProductName.ordinary_product_identity S one m y
    (.andI (name_regular _ _ _ _ (inc true) (inc false)) b)
  have moveR := GaussianBoundedConstantProductName.ordinary_product_identity T one m z
    (.andI (name_regular _ _ _ _ (wgt true) (wgt false)) b)
  have left := cross_trans _ _ _ _ _ _ (increment_rearrange A B k R x hB hA hE hL) (cross_symm _ _ _ _ moveL)
  have right := cross_symm _ _ _ _ (cross_trans _ _ _ _ _ _ moveR (weight_rearrange A B k R x hB hA hE hRE))
  exact rate_parameters_congr _ _ _ _ _ _ _ _ (one_mul _) (.eqRefl _)
    (GaussianNamedRateTransport.transport _ _ incrementF weightedF _ _ _ _ (one*error A B R x) D hD scaled left right)

theorem actual_original_hyperbolic_sine_first_order_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      independentRate incrementF weightedF (incrementData (var 0) (var 1) (var 2) (var 3) (var 4))
        (weightedData (var 0) (var 1) (var 2) (var 3) (var 4)) (error (var 0) (var 1) (var 3) (var 4))
        ((var 2*var 1)*(var 2*var 1))) :=
  closeUniv 5 (.impI (independent_rate _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianSineProductImaginaryHyperbolicDerivative
