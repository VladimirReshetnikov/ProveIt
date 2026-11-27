import IPRADerivations.Analysis.Barnes.HeadProducts.BasePowers.GaussianBarnesCanonicalHeadPolynomial
import IPRADerivations.Analysis.Polynomials.Taylor.GaussianRational.GaussianRationalUniformFirstOrderPolynomial

/-!
# First-order bound for the actual finite Barnes base-power product

The numerical coefficient-buffer degree is determined by the kept
cutoff alone. Its synthetic quotient gives the slope at the original
rational input. The linear comparison has a uniform quadratic error
and continues to hold at a zero of the kept product.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadPolynomialDerivative

open_ipra
open ComplexLogarithmRemainder (add normSq)
open GaussianBarnesCanonicalBaseProductShift (powerProduct)
open GaussianBarnesCanonicalHeadPolynomial (degree polynomial polynomial_length original_evaluation)
open GaussianRationalFirstOrderPolynomial (slope remainder)
open GaussianRationalHorner (qadd qmul ofGaussian ofGaussian_represents ofGaussian_canonical canonical_unique
  qadd_canonical qadd_represents)
open GaussianRationalMetric (bounded bounded_of_cleared distanceBounded qsub)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalSyntheticDivision (qsub_congr)
open GaussianRationalUniformFirstOrderPolynomial (mass constant slopeConstant)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def input (z h R B H : PTm n) : Fm PTm n :=
  le one B ⋏ (ComplexLogarithmRemainder.bounded z (R*B) ⋏
    (ComplexLogarithmRemainder.bounded (add z h) (R*B) ⋏ ComplexLogarithmRemainder.bounded h H))

def valueCap (R N : PTm n) : PTm n := mass (polynomial N) (succ R)
def slopeCap (R N : PTm n) : PTm n := slopeConstant (polynomial N) (degree N) (succ R)
def errorGain (R N : PTm n) : PTm n := constant (polynomial N) (degree N) (succ R)

def powerSlope (z B N : PTm n) : PTm n :=
  slope (polynomial N) (ofGaussian z B) (degree N)

def increment (z h B N : PTm n) : PTm n := qsub (powerProduct (add z h) B N) (powerProduct z B N)
def linear (z h B N : PTm n) : PTm n := qmul (ofGaussian h B) (powerSlope z B N)

@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (z h R B H : PTm n) :
    (input z h R B H).subst σ =
      input (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ H) := by
  simp [input,one]

@[simp] theorem subst_valueCap {m : ℕ} (σ : Fin n → PTm m) (R N : PTm n) :
    Syn.subst σ (valueCap R N) = valueCap (Syn.subst σ R) (Syn.subst σ N) := by simp [valueCap]

@[simp] theorem subst_slopeCap {m : ℕ} (σ : Fin n → PTm m) (R N : PTm n) :
    Syn.subst σ (slopeCap R N) = slopeCap (Syn.subst σ R) (Syn.subst σ N) := by simp [slopeCap]

@[simp] theorem subst_errorGain {m : ℕ} (σ : Fin n → PTm m) (R N : PTm n) :
    Syn.subst σ (errorGain R N) = errorGain (Syn.subst σ R) (Syn.subst σ N) := by simp [errorGain]

@[simp] theorem subst_powerSlope {m : ℕ} (σ : Fin n → PTm m) (z B N : PTm n) :
    Syn.subst σ (powerSlope z B N) = powerSlope (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by
  simp [powerSlope]

@[simp] theorem subst_increment {m : ℕ} (σ : Fin n → PTm m) (z h B N : PTm n) :
    Syn.subst σ (increment z h B N) = increment (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ N) := by
  simp [increment]

@[simp] theorem subst_linear {m : ℕ} (σ : Fin n → PTm m) (z h B N : PTm n) :
    Syn.subst σ (linear z h B N) = linear (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ N) := by
  simp [linear]

theorem argument_add (z h B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qadd (ofGaussian z B) (ofGaussian h B) ≐ ofGaussian (add z h) B :=
  canonical_unique _ _ (add z h) B (qadd_canonical _ _) (ofGaussian_canonical _ _ hB) hB
    (qadd_represents _ _ _ _ _ hB (ofGaussian_represents z B hB) (ofGaussian_represents h B hB))
    (ofGaussian_represents _ _ hB)

theorem argument_bound (z R B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) : Γ ⊢[PRAAx]
    bounded (ofGaussian z B) (succ R) one := by
  have larger := ComplexLogarithmRemainder.bounded_mono hz (mul_le_mul_right B (le_succ_self R))
  exact bounded_of_cleared _ _ _ _ _ hB (le_refl one) (ofGaussian_represents z B hB)
    (le_congr (by ipra_ring) (by ipra_ring) larger)

theorem step_bound (h B H : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hh : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded h H) :
    Γ ⊢[PRAAx] bounded (ofGaussian h B) H B :=
  bounded_of_cleared _ _ _ _ _ hB hB (ofGaussian_represents h B hB)
    (le_congr (mul_comm _ _) (.eqRefl _) (mul_le_mul_right (B*B) hh))

theorem value_bound (z R B N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] bounded (powerProduct z B N) (valueCap R N) one :=
  bound_congr (original_evaluation z B N hB) (.eqRefl _) (.eqRefl _)
    (GaussianRationalUniformFirstOrderPolynomial.value_bound (polynomial N) (ofGaussian z B) (succ R)
      (zero_lt_succ R) (argument_bound z R B hB hz))

theorem slope_bound (z R B N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] bounded (powerSlope z B N) (slopeCap R N) one :=
  GaussianRationalUniformFirstOrderPolynomial.slope_bound (polynomial N) (ofGaussian z B) (degree N)
    (succ R) (polynomial_length N) (zero_lt_succ R) (argument_bound z R B hB hz)

theorem quadratic_bound (z h R B H N : PTm n) (hs : Γ ⊢[PRAAx] input z h R B H) :
    Γ ⊢[PRAAx] distanceBounded (increment z h B N) (linear z h B N) (errorGain R N*H*H) (B*B) := by
  let C := polynomial N
  let t := ofGaussian z B
  let d := ofGaussian h B
  let U := succ R
  have hB := hs.andE₁
  have cap := argument_bound z R B hB hs.andE₂.andE₁
  have cap' := argument_bound (add z h) R B hB hs.andE₂.andE₂.andE₁
  have e := argument_add z h B hB
  have actual : Γ ⊢[PRAAx] remainder C t d (degree N) ≐ qsub (increment z h B N) (linear z h B N) :=
    qsub_congr (qsub_congr ((GaussianRationalMonicReduction.evaluate_congr (.eqRefl C) e).eqTrans
      (original_evaluation (add z h) B N hB)) (original_evaluation z B N hB)) (.eqRefl _)
  exact bound_congr actual (.eqRefl _) (.eqRefl _)
    (GaussianRationalUniformFirstOrderPolynomial.first_order_bound C t d (degree N) U H B
      (polynomial_length N) (zero_lt_succ R) cap
      (bound_congr e.eqSymm (.eqRefl _) (.eqRefl _) cap') hB (step_bound h B H hB hs.andE₂.andE₂.andE₂))

theorem actual_Barnes_finite_base_power_quadratic_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     let H := var 4
     let N := var 5
     input z h R B H ⟶ distanceBounded (increment z h B N) (linear z h B N) (errorGain R N*H*H) (B*B)) :=
  closeUniv 6 (.impI (quadratic_bound _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadPolynomialDerivative
