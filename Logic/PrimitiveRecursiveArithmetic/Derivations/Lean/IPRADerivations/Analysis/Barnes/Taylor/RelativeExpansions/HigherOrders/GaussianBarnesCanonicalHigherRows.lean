import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.Cofinal.GaussianBarnesCanonicalDerivativeRow
import IPRADerivations.Analysis.Euler.Integration.Incomplete.IntegerValues.GaussianEulerIncompleteFactorialDenominator

/-!
# Higher rational Barnes logarithmic coefficients

The variable j represents Taylor degree j+3. The signed reciprocal
power uses the original Barnes base and the alternating Mercator sign.
The coefficient and its factorial-scaled form have both their sharp
denominator bounds and uniform inverse-square bounds.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHigherRows

open_ipra
open GaussianBarnesCanonicalFactor (base)
open GaussianBarnesCanonicalLogRow (source)
open GaussianBarnesCanonicalDerivativeRow (inverse_base_bound)
open GaussianDominantPairAlgebra (radiusPoint radius_multiply radius_congr radius_bounded)
open GaussianEulerIncompleteFactorialDenominator (radius_rescale)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded qnegative)
open GaussianRationalReciprocal (power reciprocal bounded_power bounded_negative bounded_product bound_congr)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReciprocalHorner (qmul_associative)
open GaussianCoefficientNameBounds (bounded_radius_mono)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def previous (j : PTm n) : PTm n := succ (succ j)
def degree (j : PTm n) : PTm n := succ (previous j)

def signedPower (z B k j : PTm n) : PTm n :=
  qnegative (power (qnegative (reciprocal (base z B k))) (degree j))

def coefficientGain (j : PTm n) : PTm n := pw two (degree j)
def derivativeGain (j : PTm n) : PTm n := coefficientGain j*fact (previous j)
def powerDenominator (k j : PTm n) : PTm n := pw k (previous j)
def coefficientDenominator (k j : PTm n) : PTm n := degree j*powerDenominator k j

def coefficient (z B k j : PTm n) : PTm n :=
  qmul (signedPower z B k j) (radiusPoint one (coefficientDenominator k j))

def derivative (z B k j : PTm n) : PTm n :=
  qmul (signedPower z B k j) (radiusPoint (fact (previous j)) (powerDenominator k j))

@[simp] theorem subst_previous {m : ℕ} (σ : Fin n → PTm m) (j : PTm n) :
    Syn.subst σ (previous j) = previous (Syn.subst σ j) := by simp [previous]

@[simp] theorem subst_degree {m : ℕ} (σ : Fin n → PTm m) (j : PTm n) :
    Syn.subst σ (degree j) = degree (Syn.subst σ j) := by simp [degree]

@[simp] theorem subst_signedPower {m : ℕ} (σ : Fin n → PTm m) (z B k j : PTm n) :
    Syn.subst σ (signedPower z B k j) = signedPower (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ k) (Syn.subst σ j) :=
  by simp [signedPower,base]

@[simp] theorem subst_coefficientGain {m : ℕ} (σ : Fin n → PTm m) (j : PTm n) :
    Syn.subst σ (coefficientGain j) = coefficientGain (Syn.subst σ j) := by simp [coefficientGain,two]

@[simp] theorem subst_derivativeGain {m : ℕ} (σ : Fin n → PTm m) (j : PTm n) :
    Syn.subst σ (derivativeGain j) = derivativeGain (Syn.subst σ j) := by simp [derivativeGain]

@[simp] theorem subst_powerDenominator {m : ℕ} (σ : Fin n → PTm m) (k j : PTm n) :
    Syn.subst σ (powerDenominator k j) = powerDenominator (Syn.subst σ k) (Syn.subst σ j) := by simp [powerDenominator]

@[simp] theorem subst_coefficientDenominator {m : ℕ} (σ : Fin n → PTm m) (k j : PTm n) :
    Syn.subst σ (coefficientDenominator k j) = coefficientDenominator (Syn.subst σ k) (Syn.subst σ j) :=
  by simp [coefficientDenominator]

@[simp] theorem subst_coefficient {m : ℕ} (σ : Fin n → PTm m) (z B k j : PTm n) :
    Syn.subst σ (coefficient z B k j) = coefficient (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ k) (Syn.subst σ j) :=
  by simp [coefficient,one]

@[simp] theorem subst_derivative {m : ℕ} (σ : Fin n → PTm m) (z B k j : PTm n) :
    Syn.subst σ (derivative z B k j) = derivative (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ k) (Syn.subst σ j) :=
  by simp [derivative]

theorem degree_positive (j : PTm n) : Γ ⊢[PRAAx] le one (degree j) := zero_lt_succ _

theorem power_denominator_positive (k j : PTm n) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] le one (powerDenominator k j) :=
  GaussianFactorBudget.power_positive k (previous j) hk

theorem coefficient_denominator_positive (k j : PTm n) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] le one (coefficientDenominator k j) :=
  positive_product _ _ (degree_positive j) (power_denominator_positive k j hk)

theorem signed_power_bound (z R B k j : PTm n) (h : Γ ⊢[PRAAx] source z R B k) :
    Γ ⊢[PRAAx] bounded (signedPower z B k j) (coefficientGain j) one := by
  let q := reciprocal (base z B k)
  have neg := bounded_negative q two one (le_refl one) (inverse_base_bound z R B k h)
  have raw := bounded_power (qnegative q) two one (degree j) (le_refl one) neg
  exact bounded_negative _ _ _ (le_refl one)
    (bound_congr (.eqRefl _) (.eqRefl _) (GaussianPolynomialPerturbation.one_power (degree j)) raw)

theorem coefficient_bound (z R B k j : PTm n) (h : Γ ⊢[PRAAx] source z R B k) :
    Γ ⊢[PRAAx] bounded (coefficient z B k j) (coefficientGain j) (coefficientDenominator k j) := by
  let P := coefficientDenominator k j
  have hp := coefficient_denominator_positive k j h.andE₂.andE₁
  exact bound_congr (.eqRefl _) (by ipra_ring) (one_mul P)
    (bounded_product _ _ _ one one P (le_refl one) hp (signed_power_bound z R B k j h) (radius_bounded one P hp))

theorem derivative_bound (z R B k j : PTm n) (h : Γ ⊢[PRAAx] source z R B k) :
    Γ ⊢[PRAAx] bounded (derivative z B k j) (derivativeGain j) (powerDenominator k j) := by
  let P := powerDenominator k j
  let A := fact (previous j)
  have hp := power_denominator_positive k j h.andE₂.andE₁
  exact bound_congr (.eqRefl _) (.eqRefl _) (one_mul P)
    (bounded_product _ _ _ one A P (le_refl one) hp (signed_power_bound z R B k j h) (radius_bounded A P hp))

private theorem square_le (k j : PTm n) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] le (k*k) (powerDenominator k j) := by
  have order : Γ ⊢[PRAAx] le two (previous j) :=
    le_congr (.eqRefl _) (by unfold previous; ipra_ring) (le_add_left two j)
  have square : Γ ⊢[PRAAx] pw k two ≐ k*k :=
    (pw_succ k one).eqTrans (congrMul (pw_one k) (.eqRefl k))
  exact le_congr square (.eqRefl _) (GaussianFactorBudget.power_monotone_length k two (previous j) hk order)

theorem coefficient_square_bound (z R B k j : PTm n) (h : Γ ⊢[PRAAx] source z R B k) :
    Γ ⊢[PRAAx] bounded (coefficient z B k j) (coefficientGain j) (k*k) := by
  let hk := h.andE₂.andE₁
  let P := powerDenominator k j
  have fit : Γ ⊢[PRAAx] le (k*k) (coefficientDenominator k j) :=
    le_trans (square_le k j hk)
      (le_congr (one_mul P) (.eqRefl _) (mul_le_mul_right P (degree_positive j)))
  exact bounded_radius_mono _ _ _ _ _ (coefficient_denominator_positive k j hk) (positive_product _ _ hk hk)
    (mul_le_mul_left (coefficientGain j) fit) (coefficient_bound z R B k j h)

theorem derivative_square_bound (z R B k j : PTm n) (h : Γ ⊢[PRAAx] source z R B k) :
    Γ ⊢[PRAAx] bounded (derivative z B k j) (derivativeGain j) (k*k) := by
  let hk := h.andE₂.andE₁
  exact bounded_radius_mono _ _ _ _ _ (power_denominator_positive k j hk) (positive_product _ _ hk hk)
    (mul_le_mul_left (derivativeGain j) (square_le k j hk))
    (derivative_bound z R B k j h)

theorem factorial_binding (z B k j : PTm n) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] qmul (coefficient z B k j) (radiusPoint (fact (degree j)) one) ≐ derivative z B k j := by
  let P := powerDenominator k j
  let E := coefficientDenominator k j
  let A := fact (previous j)
  let r := degree j
  have hp := power_denominator_positive k j hk
  have hE := coefficient_denominator_positive k j hk
  have factor : Γ ⊢[PRAAx] qmul (radiusPoint one E) (radiusPoint (fact r) one) ≐ radiusPoint A P := by
    refine (radius_multiply one E (fact r) one hE (le_refl one)).eqTrans ?_
    exact (radius_congr ((one_mul (fact r)).eqTrans (fact_succ (previous j) zero))
      (by change Γ ⊢[PRAAx] (r*P)*one ≐ P*r; ipra_ring)).eqTrans
        (radius_rescale A P r hp (degree_positive j))
  exact (qmul_associative _ _ _).eqTrans (qmul_congr (.eqRefl _) factor)

theorem actual_Barnes_higher_row_bounds_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let z := var 0
     let R := var 1
     let B := var 2
     let k := var 3
     let j := var 4
     source z R B k ⟶
       (bounded (coefficient z B k j) (coefficientGain j) (coefficientDenominator k j) ⋏
        (bounded (derivative z B k j) (derivativeGain j) (powerDenominator k j) ⋏
        (qmul (coefficient z B k j) (radiusPoint (fact (degree j)) one) ≐ derivative z B k j)))) :=
  closeUniv 5 (.impI (.andI (coefficient_bound _ _ _ _ _ Prf.hyp0)
    (.andI (derivative_bound _ _ _ _ _ Prf.hyp0) (factorial_binding _ _ _ _ Prf.hyp0.andE₂.andE₁))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHigherRows
