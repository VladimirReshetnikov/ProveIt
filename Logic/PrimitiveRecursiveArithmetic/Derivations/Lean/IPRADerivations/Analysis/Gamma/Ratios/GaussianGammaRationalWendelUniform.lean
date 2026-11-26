import IPRADerivations.Analysis.Exponential.Estimates.GaussianRationalExponentialTangent

/-!
# The explicit uniform relative Wendel estimate on the original quotient

For `x=a/b` and `u=r/b` with `r+s=b`, the original Wendel relative
name has deficit between zero and `r*s/(b*a) ≤ b/(4*a)`. No cutoff,
precision-dependent input restriction, or limit premise is required.
-/

set_option autoImplicit false
set_option maxHeartbeats 1650000

namespace LeanProofs.IPRA.Analysis.GaussianGammaRationalWendelUniform

open_ipra
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaEulerRationalLogOrder (add_order order_refl)
open GaussianGammaFiniteApproximantName (exponentialInputData)
open GaussianGammaRationalLogGautschi (ratioExponentData)
open GaussianGammaRationalLogWendel (relativeExponentF relativeExponentData relative_exponent_regular relative_exponent_real)
open GaussianGammaRationalWendelGautschi (relativeF relativeData)
open GaussianGammaRationalWendelBoundary (weak_order)
open GaussianGammaRationalWendelUniformLog (error negativeError log_estimate quarter_error)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (negativeF negativeData negative_fast add_negative oneF one_at one_fast zeroF zero_at zero_fast)
open GaussianNamedDifference (nameF data name_regular)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qzero positive_product)
open GaussianRationalSyntheticDivision (qone)
open GaussianStirlingLogDuplication (exponential_regular)
open GaussianStirlingMultiplicativeBoundsOrder (exponential_order)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "C" => constantF
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => exponentialInputData
local notation "Q" => relativeF

def deficitF : PR 2 := nameF C Q
def deficitData (a b r s : PTm n) : PTm n := data qone (relativeData a b r s)

theorem zero_constant (x : PTm n) : Γ ⊢[PRAAx] crossEquivalent zeroF C x qzero := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (zero_fast _) (constant_regular _)
  refine .allI ?_
  simpa [Syn.shift] using (zero_at (Γ := Γ.map Fm.shift) (var 0) (Syn.shift x)).eqTrans (constant_at (var 0) qzero).eqSymm

theorem one_constant (x : PTm n) : Γ ⊢[PRAAx] crossEquivalent oneF C x qone := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (one_fast _) (constant_regular _)
  refine .allI ?_
  simpa [Syn.shift] using (one_at (Γ := Γ.map Fm.shift) (var 0) (Syn.shift x)).eqTrans (constant_at (var 0) qone).eqSymm

theorem one_le_relative_plus_error (a b r s : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hb : Γ ⊢[PRAAx] le one b) (h : Γ ⊢[PRAAx] b ≐ r+s) :
    Γ ⊢[PRAAx] realOrder C (addF C Q) qone (addData (error a b r s) (relativeData a b r s)) := by
  let t := error a b r s
  let c := negativeError a b r s
  let z := relativeExponentData a b r s
  let q := relativeData a b r s
  have hP := positive_product _ _ hb ha
  have ord := exponential_order C relativeExponentF c z (constant_regular _) (relative_exponent_regular a b r s ha hb)
    (GaussianRationalExponentialTangent.negative_fraction_real (s*r) (b*a) hP)
    (relative_exponent_real a b r s hb) (log_estimate a b r s ha hb h).andE₁
  have leSum := add_order C C (E C) Q t t (ed C c) q (order_refl _ _ (constant_regular _)) ord
  exact GaussianEulerPowerChartTimeOrder.order_trans _ _ _ _ _ _
    (GaussianRationalExponentialTangent.tangent (s*r) (b*a) hP) leSum

def estimate (a b r s : PTm n) : Fm PTm n :=
  realOrder C deficitF qzero (deficitData a b r s) ⋏
  realOrder deficitF C (deficitData a b r s) (error a b r s) ⋏
  realOrder deficitF C (deficitData a b r s) (fraction b (num 4*a))

theorem uniform_estimate (a b r s : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hb : Γ ⊢[PRAAx] le one b) (h : Γ ⊢[PRAAx] b ≐ r+s) :
    Γ ⊢[PRAAx] estimate a b r s := by
  let q := relativeData a b r s
  let t := error a b r s
  let y := ratioExponentData a b r
  let N := negativeF Q
  let v := negativeData q
  have hq := exponential_regular relativeExponentF _ (relative_exponent_regular a b r s ha hb)
  have hv := negative_fast Q q hq
  have hf := name_regular C Q qone q (constant_regular _) hq
  have opp := order_refl N v hv
  have up := GaussianNamedRealOrderTransport.transport Q Q oneF C q q y qone
    (cross_refl _ _ hq) (one_constant y) (weak_order a b r s ha hb h).andE₂
  have low' := add_order Q C N N q qone v v up opp
  have low := GaussianNamedRealOrderTransport.transport C (addF Q N) deficitF deficitF qzero (addData q v)
    (deficitData a b r s) (deficitData a b r s)
    (cross_symm _ _ _ _ (cross_trans _ _ _ _ _ _ (add_negative Q q hq) (zero_constant q)))
    (cross_refl _ _ hf) low'
  have sum := one_le_relative_plus_error a b r s ha hb h
  have high' := add_order C (addF C Q) N N qone (addData t q) v v sum opp
  have high := GaussianNamedRealOrderTransport.transport deficitF deficitF (addF (addF C Q) N) C
    (deficitData a b r s) (deficitData a b r s) (addData (addData t q) v) t
    (cross_refl _ _ hf) (GaussianNamedStrictOrderDifference.sum_sub_right C Q t q (constant_regular _) hq) high'
  exact .andI low (.andI high (GaussianEulerPowerChartTimeOrder.order_trans _ _ _ _ _ _
    high (quarter_error a b r s ha hb h)))

theorem actual_positive_rational_Wendel_uniform_relative_estimate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((le one (var 0) ⋏ (le one (var 1) ⋏ var 1 ≐ var 2+var 3)) ⟶
      estimate (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (uniform_estimate _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaRationalWendelUniform
