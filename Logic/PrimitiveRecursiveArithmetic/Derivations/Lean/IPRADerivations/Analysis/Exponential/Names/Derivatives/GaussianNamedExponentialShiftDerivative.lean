import IPRADerivations.Analysis.Exponential.Names.Identities.GaussianExponentialAddition
import IPRADerivations.Analysis.Exponential.Names.Evaluators.GaussianExponentialRadiusIndependence
import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameConjugation
import IPRADerivations.Analysis.Exponential.Names.LocalEstimates.GaussianNamedExponentialLinearRate
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedDifferenceQuotientProperness
import IPRADerivations.Analysis.Names.Rates.Perturbations.GaussianNamedDifferenceRate
import IPRADerivations.Analysis.Names.FiniteOperations.Products.Bounds.GaussianNamedMultiplyRate
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateTransport

/-!
# First-order exponential increment at a regular complex name

The original addition law transports the exact small-argument
quadratic estimate to the exponential difference at a named base.
The linear term is the product of the actual base exponential and
the original increment name.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianNamedExponentialShiftDerivative

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianExponentialAddition (sumData productF productData exponential_add_cross)
open GaussianExponentialRadiusIndependence (independent_radii_proper input_widen)
open GaussianNameArithmetic (addF addData add_fast add_equivalent multiplyF multiplyData multiply_fast multiply_equivalent)
open GaussianNameBounds (U all_samples_bounded)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_to_diagonal cross_trans)
open GaussianNameRingLaws
  (add_associative add_commutative add_negative distributive multiply_one negative_fast negativeF negativeData
    oneF one_at one_fast zeroF zero_at zero_fast)
open GaussianNamedDifferenceQuotientProperness (difference_proper)
open GaussianNamedDifferenceRate (rate_parameters_congr same_right_rate self_rate)
open GaussianNamedInverseRate (independentRate)
open GaussianRadiusExponentialName (nameF name_regular data input)
open GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "diffF" => GaussianNamedDifference.nameF
local notation "diffData" => GaussianNamedDifference.data
local notation "sumExpF" => GaussianExponentialAddition.sumF
local notation "linearF" => GaussianNamedExponentialLinearRate.linearF
local notation "linearData" => GaussianNamedExponentialLinearRate.linearData
local notation "small" => GaussianNamedExponentialLinearRate.source

def incrementF (f g : PR 2) : PR 2 := diffF (sumExpF f g) (nameF f)
def incrementData (R x y : PTm n) : PTm n := diffData (sumData R x y) (data R x)
def weightedF (f g : PR 2) : PR 2 := multiplyF (nameF f) g
def weightedData (f g : PR 2) (R x y : PTm n) : PTm n := multiplyData (nameF f) g (data R x) y
def coefficient (f : PR 2) (R x A : PTm n) : PTm n := U (nameF f) (data R x)*(A*A)

private theorem add_cross (f g h k : PR 2) (x y u v : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hh : Γ ⊢[PRAAx] pointCN h u) (hk : Γ ⊢[PRAAx] pointCN k v)
    (a : Γ ⊢[PRAAx] crossEquivalent f g x y) (b : Γ ⊢[PRAAx] crossEquivalent h k u v) :
    Γ ⊢[PRAAx] crossEquivalent (addF f h) (addF g k) (addData x u) (addData y v) :=
  add_equivalent f g h k x y u v hf hg hh hk (cross_to_diagonal _ _ _ _ a) (cross_to_diagonal _ _ _ _ b)

private theorem cancel_left (F G : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hg : Γ ⊢[PRAAx] pointCN G y) :
    Γ ⊢[PRAAx] crossEquivalent (diffF (addF F G) F) G (diffData (addData x y) x) y := by
  let N := negativeF F
  let n := negativeData x
  have hn := negative_fast F x hf
  have p := add_cross (addF F G) (addF G F) N N (addData x y) (addData y x) n n
    (add_fast _ _ _ _ hf hg) (add_fast _ _ _ _ hg hf) hn hn
    (add_commutative F G x y hf hg) (cross_refl _ _ hn)
  have q := add_associative G F N y x n hg hf hn
  have r := add_cross G G (addF F N) zeroF y y (addData x n) y hg hg
    (add_fast _ _ _ _ hf hn) (zero_fast y) (cross_refl _ _ hg)
    (cross_trans _ _ _ _ _ _ (add_negative F x hf) (GaussianNameRingLaws.zero_name_cross x y))
  exact cross_trans _ _ _ _ _ _ p
    (cross_trans _ _ _ _ _ _ q (cross_trans _ _ _ _ _ _ r (GaussianNameRingLaws.add_zero G y hg)))

private theorem weighted_cancel (E g : PR 2) (d y : PTm n)
    (he : Γ ⊢[PRAAx] pointCN E d) (hg : Γ ⊢[PRAAx] pointCN g y) :
    Γ ⊢[PRAAx] crossEquivalent
      (diffF (multiplyF E (linearF g)) E) (multiplyF E g)
      (diffData (multiplyData E (linearF g) d (linearData y)) d) (multiplyData E g d y) := by
  let W := multiplyF E g
  let z := multiplyData E g d y
  let H := multiplyF E (linearF g)
  let u := multiplyData E (linearF g) d (linearData y)
  let Q := multiplyF E oneF
  let q := multiplyData E oneF d zero
  have hq := multiply_fast E oneF d zero he (one_fast zero)
  have hw := multiply_fast E g d y he hg
  have hh := multiply_fast E (linearF g) d (linearData y) he (add_fast _ _ _ _ (one_fast zero) hg)
  have distribute := distributive E oneF g d zero y he (one_fast zero) hg
  have same_one := multiply_equivalent E E oneF oneF d d zero d he he (one_fast zero) (one_fast d)
    (cross_to_diagonal _ _ _ _ (cross_refl _ _ he)) (cross_to_diagonal _ _ _ _ (GaussianNameRingLaws.one_name_cross zero d))
  have one := add_cross Q E W W q d z z hq he hw hw
    (cross_trans _ _ _ _ _ _ same_one (multiply_one E d he)) (cross_refl _ _ hw)
  have change := difference_proper H (addF E W) E E u (addData d z) d d hh
    (add_fast _ _ _ _ he hw) he he (cross_trans _ _ _ _ _ _ distribute one) (cross_refl _ _ he)
  exact cross_trans _ _ _ _ _ _ change (cancel_left E W d z he hw)

theorem independent_rate (f g : PR 2) (R x y A B : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hf : Γ ⊢[PRAAx] input f R x)
    (hg : Γ ⊢[PRAAx] small g y A B) : Γ ⊢[PRAAx]
    independentRate (incrementF f g) (weightedF f g) (incrementData R x y) (weightedData f g R x y)
      (coefficient f R x A) (B*B) := by
  let E := nameF f
  let G := nameF g
  let L := linearF g
  let d := data R x
  let yR := data R y
  let v := linearData y
  let D := B*B
  let U₀ := U E d
  let U₁ := U G yR
  let W := weightedF f g
  let w := weightedData f g R x y
  let P := productF f g
  let p := productData f g R x y
  let H := multiplyF E L
  let u := multiplyData E L d v
  let S := sumExpF f g
  let z := sumData R x y
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hg.andE₁ hg.andE₁
  have unitG := GaussianNamedExponentialLinearRate.unit_input g y A B hg
  have wideG := input_widen g one R y unitG hR
  have he := name_regular f R x hf
  have hgr := name_regular g R y wideG
  have hl := add_fast oneF g zero y (one_fast zero) unitG.andE₁
  have lin := GaussianNamedExponentialLinearRate.independent_rate g y A B hg
  have toUnit := independent_radii_proper g g R one y y wideG unitG (cross_refl g y unitG.andE₁)
  have efold := GaussianNamedRateTransport.transport G L G L (data one y) v yR v (A*A) D hD lin
    toUnit (cross_refl _ _ hl)
  have raw := GaussianNamedMultiplyRate.independent_rate E G E L d yR d v zero one (A*A) D U₁ U₀
    (le_refl one) hD he hgr he hl (all_samples_bounded G yR hgr) (all_samples_bounded E d he)
    (self_rate E d he) efold
  have productRate : Γ ⊢[PRAAx] independentRate P H p u (coefficient f R x A) D :=
    rate_parameters_congr _ _ _ _ _ _ _ _
      (by unfold GaussianNamedMultiplyRate.leadingNumerator coefficient U₀; ipra_ring)
      (by unfold GaussianNamedMultiplyRate.leadingDenominator; ipra_ring) raw
  have moved := same_right_rate P H E p u d (coefficient f R x A) D hD
    (multiply_fast E G d yR he hgr) (multiply_fast E L d v he hl) he productRate
  have left := difference_proper S P E E z p d d
    (name_regular (addF f g) (R+R) (addData x y) (GaussianExponentialReference.add_input f g R x y hf wideG))
    (multiply_fast E G d yR he hgr) he he
    (cross_symm _ _ _ _ (exponential_add_cross f g R x y hR hf wideG)) (cross_refl _ _ he)
  have right : Γ ⊢[PRAAx] crossEquivalent W (diffF H E) w (diffData u d) :=
    cross_symm _ _ _ _ (weighted_cancel E g d y he unitG.andE₁)
  exact GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ (coefficient f R x A) D hD moved left right

theorem actual_named_exponential_shift_derivative_rate_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (let R := var 0
       let x := var 1
       let y := var 2
       let A := var 3
       let B := var 4
       (le one R ⋏ (input f R x ⋏ small g y A B)) ⟶
        independentRate (incrementF f g) (weightedF f g) (incrementData R x y) (weightedData f g R x y)
          (coefficient f R x A) (B*B)) :=
  closeUniv 5 (.impI (independent_rate f g _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedExponentialShiftDerivative
