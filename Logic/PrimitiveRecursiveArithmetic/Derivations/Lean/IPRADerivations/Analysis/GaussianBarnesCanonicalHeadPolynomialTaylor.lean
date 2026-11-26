/-
A second-order expansion of the literal kept Barnes base powers.
The head product is evaluated by its existing exact finite polynomial.
-/
import IPRADerivations.Analysis.GaussianBarnesCanonicalHeadPolynomialDerivative
import IPRADerivations.Analysis.GaussianRationalUniformSecondOrderPolynomial

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadPolynomialTaylor

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalHeadPolynomial (polynomial degree polynomial_length original_evaluation)
open GaussianBarnesCanonicalHeadPolynomialDerivative (input increment linear argument_bound argument_add step_bound)
open GaussianRationalHorner (qmul qadd ofGaussian)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalSyntheticDivision (qsub_congr)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def coefficient (z B N : PTm n) : PTm n :=
  GaussianRationalUniformSecondOrderPolynomial.coefficient (polynomial N) (ofGaussian z B) (degree N)

def quadratic (z h B N : PTm n) : PTm n :=
  qadd (linear z h B N) (qmul (qmul (ofGaussian h B) (ofGaussian h B)) (coefficient z B N))

def errorGain (R N : PTm n) : PTm n :=
  GaussianRationalUniformSecondOrderPolynomial.errorGain (polynomial N) (degree N) (succ R)

@[simp] theorem subst_coefficient {m : ℕ} (σ : Fin n → PTm m) (z B N : PTm n) :
    Syn.subst σ (coefficient z B N) = coefficient (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by
  simp [coefficient]

@[simp] theorem subst_quadratic {m : ℕ} (σ : Fin n → PTm m) (z h B N : PTm n) :
    Syn.subst σ (quadratic z h B N) = quadratic (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ N) := by
  simp [quadratic]

@[simp] theorem subst_errorGain {m : ℕ} (σ : Fin n → PTm m) (R N : PTm n) :
    Syn.subst σ (errorGain R N) = errorGain (Syn.subst σ R) (Syn.subst σ N) := by
  simp [errorGain]

theorem cubic_bound (z h R B H N : PTm n) (hs : Γ ⊢[PRAAx] input z h R B H) : Γ ⊢[PRAAx]
    distanceBounded (increment z h B N) (quadratic z h B N) (errorGain R N*H*H*H) (B*B*B) := by
  let C := polynomial N
  let t := ofGaussian z B
  let d := ofGaussian h B
  let U := succ R
  have hB := hs.andE₁
  have cap := argument_bound z R B hB hs.andE₂.andE₁
  have cap' := argument_bound (add z h) R B hB hs.andE₂.andE₂.andE₁
  have e := argument_add z h B hB
  have actual : Γ ⊢[PRAAx] GaussianRationalUniformSecondOrderPolynomial.error C t d (degree N) ≐
      GaussianRationalMetric.qsub (increment z h B N) (quadratic z h B N) :=
    qsub_congr (qsub_congr ((GaussianRationalMonicReduction.evaluate_congr (.eqRefl C) e).eqTrans
      (original_evaluation (add z h) B N hB)) (original_evaluation z B N hB)) (.eqRefl _)
  exact bound_congr actual (.eqRefl _) (.eqRefl _)
    (GaussianRationalUniformSecondOrderPolynomial.cubic_bound C t d (degree N) U H B
      (polynomial_length N) (zero_lt_succ R) cap
      (bound_congr e.eqSymm (.eqRefl _) (.eqRefl _) cap') hB (step_bound h B H hB hs.andE₂.andE₂.andE₂))

theorem actual_Barnes_finite_base_power_cubic_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      distanceBounded (increment (var 0) (var 1) (var 3) (var 5)) (quadratic (var 0) (var 1) (var 3) (var 5))
        (errorGain (var 2) (var 5)*var 4*var 4*var 4) (var 3*var 3*var 3)) :=
  closeUniv 6 (.impI (cubic_bound _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadPolynomialTaylor
