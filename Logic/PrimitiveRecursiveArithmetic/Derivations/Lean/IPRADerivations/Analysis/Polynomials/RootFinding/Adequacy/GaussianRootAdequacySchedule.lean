import IPRADerivations.Analysis.Polynomials.RootFinding.Adequacy.GaussianRootSchedule
import IPRADerivations.Foundations.DemandClosure

/-!
# Actual finite precision selectors for root-support adequacy

Source04 (FE) uses t=k+1+ell(2C) and
s=max(k+1,N(k+3)+ell(C+T)). Here ell is the actual bounded binary-length
search and max is the actual primitive recursive natural maximum. The
computed powers give the exact denominator-cleared residual budget at
radius 2^(-k-1), without a supplied precision or successful-search premise.
All numerical degrees, constants, radii and indices remain internal.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRootAdequacySchedule

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRootSchedule (binaryLength toleranceDenominator)
open LeanProofs.IPRA.Foundations.DemandClosure (maximum maximum_left maximum_right)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def three : PTm n := succ two
def stage (C k : PTm n) : PTm n := k+one+binaryLength (two*C)
def exponent (N k : PTm n) : PTm n := N*(k+three)
def sample (N C T k : PTm n) : PTm n := maximum (k+one) (exponent N k+binaryLength (C+T))
def evaluationDenominator (N R C k : PTm n) : PTm n := toleranceDenominator N R (stage C k)
def sampleDenominator (N C T k : PTm n) : PTm n := pw two (sample N C T k)
def targetPower (N k : PTm n) : PTm n := pw (pw two (k+one)) N

@[simp] theorem subst_three {m : ℕ} (σ : Fin n → PTm m) : Syn.subst σ (three : PTm n) = (three : PTm m) := by
  simp only [three,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]
@[simp] theorem subst_stage {m : ℕ} (σ : Fin n → PTm m) (C k : PTm n) :
    Syn.subst σ (stage C k) = stage (Syn.subst σ C) (Syn.subst σ k) := by
  simp only [stage,PTm.subst_add,PTm.subst_mul,GaussianRootSchedule.subst_binaryLength,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]
@[simp] theorem subst_exponent {m : ℕ} (σ : Fin n → PTm m) (N k : PTm n) :
    Syn.subst σ (exponent N k) = exponent (Syn.subst σ N) (Syn.subst σ k) := by simp only [exponent,PTm.subst_mul,PTm.subst_add,subst_three]
@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (N C T k : PTm n) :
    Syn.subst σ (sample N C T k) = sample (Syn.subst σ N) (Syn.subst σ C) (Syn.subst σ T) (Syn.subst σ k) := by
  simp only [sample,Foundations.DemandClosure.subst_maximum,PTm.subst_add,subst_exponent,GaussianRootSchedule.subst_binaryLength,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]
@[simp] theorem subst_evaluationDenominator {m : ℕ} (σ : Fin n → PTm m) (N R C k : PTm n) :
    Syn.subst σ (evaluationDenominator N R C k) = evaluationDenominator (Syn.subst σ N) (Syn.subst σ R) (Syn.subst σ C) (Syn.subst σ k) := by
  simp only [evaluationDenominator,GaussianRootSchedule.subst_toleranceDenominator,subst_stage]
@[simp] theorem subst_sampleDenominator {m : ℕ} (σ : Fin n → PTm m) (N C T k : PTm n) :
    Syn.subst σ (sampleDenominator N C T k) = sampleDenominator (Syn.subst σ N) (Syn.subst σ C) (Syn.subst σ T) (Syn.subst σ k) := by
  simp only [sampleDenominator,subst_ap2,subst_sample,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]
@[simp] theorem subst_targetPower {m : ℕ} (σ : Fin n → PTm m) (N k : PTm n) :
    Syn.subst σ (targetPower N k) = targetPower (Syn.subst σ N) (Syn.subst σ k) := by
  simp only [targetPower,subst_ap2,PTm.subst_add,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]

theorem stage_ge_succ (C k : PTm n) : Γ ⊢[PRAAx] le (k+one) (stage C k) := le_add_right _ _
theorem stage_ge_index (C k : PTm n) : Γ ⊢[PRAAx] le k (stage C k) := le_trans (le_add_right k one) (stage_ge_succ C k)
theorem sample_ge_succ (N C T k : PTm n) : Γ ⊢[PRAAx] le (k+one) (sample N C T k) := maximum_left _ _
theorem sample_ge_exponent (N C T k : PTm n) : Γ ⊢[PRAAx] le (exponent N k+binaryLength (C+T)) (sample N C T k) := maximum_right _ _

/-- The actual source E at the computed t contains the full binary-length
shift, because the positive degree multiplies it by at least one. -/
theorem precision_lower (N R C k : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    le (exponent N k+binaryLength (two*C)) (GaussianRootSchedule.precision N R (stage C k)) := by
  have scale : Γ ⊢[PRAAx] le (binaryLength (two*C)) (N*binaryLength (two*C)) :=
    le_congr (one_mul _) (.eqRefl _) (le_mul_mono hN (le_refl _))
  have add := add_le_add₂ (le_refl (exponent N k)) scale
  have shape : Γ ⊢[PRAAx] exponent N k+N*binaryLength (two*C) ≐ N*(stage C k+two) := by unfold exponent stage three; ipra_ring
  exact le_trans (le_congr (.eqRefl _) shape add) (GaussianRootSchedule.precision_lower _ _ _)

/-- The bounded binary-length search gives the exact multiplicative power
budget at a sum of exponents, for every natural constant including zero. -/
theorem binary_power_budget (v e : PTm n) : Γ ⊢[PRAAx] le (v*pw two e) (pw two (e+binaryLength v)) :=
  le_congr (mul_comm _ _) (pw_add two e (binaryLength v)).eqSymm
    (le_mul_mono (le_refl (pw two e)) (Prf.andE₁ (GaussianRootSchedule.binary_length_correct v)))

theorem denominator_budget (N R C k : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    le ((two*C)*pw two (exponent N k)) (evaluationDenominator N R C k) :=
  le_trans (binary_power_budget _ _) (GaussianFactorBudget.power_monotone_length _ _ _ (le_succ_self one) (precision_lower N R C k hN))

theorem sample_budget (N C T k : PTm n) : Γ ⊢[PRAAx]
    le ((C+T)*pw two (exponent N k)) (sampleDenominator N C T k) :=
  le_trans (binary_power_budget _ _) (GaussianFactorBudget.power_monotone_length _ _ _ (le_succ_self one) (sample_ge_exponent N C T k))

theorem evaluation_denominator_positive (N R C k : PTm n) : Γ ⊢[PRAAx] le one (evaluationDenominator N R C k) :=
  GaussianRootSchedule.tolerance_positive _ _ _
theorem sample_denominator_positive (N C T k : PTm n) : Γ ⊢[PRAAx] le one (sampleDenominator N C T k) :=
  GaussianFactorBudget.power_positive _ _ (le_succ_self one)

theorem target_power_value (N k : PTm n) : Γ ⊢[PRAAx] targetPower N k ≐ pw two (N*(k+one)) :=
  (GaussianDescentClockArithmetic.power_composition two (k+one) N).eqTrans
    (congrAp2 powF (mul_comm _ _) (.eqRefl _))

/-- The source's two precision units give at least a factor-two margin
for adding the two FE error terms, uniformly in positive runtime degree. -/
theorem target_power_margin (N k : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    le (two*targetPower N k) (pw two (exponent N k)) := by
  have positive : Γ ⊢[PRAAx] le one (two*N) := le_congr (by ipra_ring) (.eqRefl _)
    (le_mul_mono (le_succ_self one) hN)
  have index : Γ ⊢[PRAAx] le (succ (N*(k+one))) (exponent N k) :=
    le_congr (by ipra_ring) (by unfold exponent three; ipra_ring)
      (add_le_add₂ (le_refl (N*(k+one))) positive)
  have first : Γ ⊢[PRAAx] pw two (succ (N*(k+one))) ≐ two*targetPower N k :=
    (pw_succ _ _).eqTrans ((congrMul (target_power_value N k).eqSymm (.eqRefl _)).eqTrans (mul_comm _ _))
  exact le_congr first (.eqRefl _) (GaussianFactorBudget.power_monotone_length _ _ _ (le_succ_self one) index)

/-- Exact natural cross-denominator form of the source FE residual budget:
the two actual chosen precisions make the sum no larger than
(2^(-k-1))^N. No analytic residual or precision-correctness premise is used. -/
theorem finite_evaluation_budget (N R C T k : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    le (targetPower N k*((two*C)*sampleDenominator N C T k+(C+T)*evaluationDenominator N R C k))
      (evaluationDenominator N R C k*sampleDenominator N C T k) := by
  have first := le_mul_mono (denominator_budget N R C k hN) (le_refl (sampleDenominator N C T k))
  have second := le_mul_mono (sample_budget (Γ := Γ) N C T k) (le_refl (evaluationDenominator N R C k))
  have combined : Γ ⊢[PRAAx] le
      (pw two (exponent N k)*((two*C)*sampleDenominator N C T k+(C+T)*evaluationDenominator N R C k))
      (two*(evaluationDenominator N R C k*sampleDenominator N C T k)) :=
    le_congr (by ipra_ring) (by ipra_ring) (add_le_add₂ first second)
  have scaled := le_trans (le_mul_mono (target_power_margin N k hN)
    (le_refl ((two*C)*sampleDenominator N C T k+(C+T)*evaluationDenominator N R C k))) combined
  exact RationalValueBounds.positive_cancel (le_succ_self one)
    (le_congr (by ipra_ring) (.eqRefl _) scaled)

/-! Actual precision-selector program and universally closed budgets. -/
def output (N R C T k : PTm n) : PTm n := pairT (stage C k) (pairT (sample N C T k)
  (pairT (evaluationDenominator N R C k) (sampleDenominator N C T k)))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (N R C T k : PTm n) :
    Syn.subst σ (output N R C T k) = output (Syn.subst σ N) (Syn.subst σ R) (Syn.subst σ C) (Syn.subst σ T) (Syn.subst σ k) := by
  simp only [output,subst_pairT,subst_stage,subst_sample,subst_evaluationDenominator,subst_sampleDenominator]
theorem output_at (N R C T k : PTm n) : Γ ⊢[PRAAx] PTm.app outputF ![N,R,C,T,k] ≐ output N R C T k := by
  simpa only [outputF,subst_output,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![N,R,C,T,k]

theorem adequacy_indices_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 0) ⟶
      (le (var 4) (stage (var 2) (var 4)) ⋏
        (le (var 4+one) (sample (var 0) (var 2) (var 3) (var 4)) ⋏
          le (exponent (var 0) (var 4)+binaryLength (two*var 2))
            (GaussianRootSchedule.precision (var 0) (var 1) (stage (var 2) (var 4)))))) :=
  closeUniv 5 (.impI (.andI (stage_ge_index _ _) (.andI (sample_ge_succ _ _ _ _) (precision_lower _ _ _ _ Prf.hyp0))))

theorem adequacy_denominator_bounds_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 0) ⟶
      (le ((two*var 2)*pw two (exponent (var 0) (var 4))) (evaluationDenominator (var 0) (var 1) (var 2) (var 4)) ⋏
        le ((var 2+var 3)*pw two (exponent (var 0) (var 4))) (sampleDenominator (var 0) (var 2) (var 3) (var 4)))) :=
  closeUniv 5 (.impI (.andI (denominator_budget _ _ _ _ Prf.hyp0) (sample_budget _ _ _ _)))

theorem finite_root_evaluation_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 0) ⟶
      le (targetPower (var 0) (var 4)*
          ((two*var 2)*sampleDenominator (var 0) (var 2) (var 3) (var 4)+
            (var 2+var 3)*evaluationDenominator (var 0) (var 1) (var 2) (var 4)))
        (evaluationDenominator (var 0) (var 1) (var 2) (var 4)*sampleDenominator (var 0) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (finite_evaluation_budget _ _ _ _ _ Prf.hyp0))

theorem adequacy_schedule_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((PTm.app outputF ![var 0,var 1,var 2,var 3,var 4] ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
      (le one (evaluationDenominator (var 0) (var 1) (var 2) (var 4)) ⋏
        le one (sampleDenominator (var 0) (var 2) (var 3) (var 4)))) :=
  closeUniv 5 (.andI (output_at _ _ _ _ _) (.andI (evaluation_denominator_positive _ _ _ _) (sample_denominator_positive _ _ _ _)))

end LeanProofs.IPRA.Analysis.GaussianRootAdequacySchedule
