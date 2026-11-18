import IPRADerivations.Analysis.GaussianRationalReciprocal
import IPRADerivations.Analysis.RationalClosure

/-!
# Removing dyadic slack from original rational Euclidean bounds

One explicitly computed finite precision already removes the slack in
|z| <= A/B + C*2^(-m). Its proof clears the actual independent component
denominators, expands the squared inequality and reduces it to the checked
natural rational-closure integer-gap argument. The global statement merely
queries its forall-m input at that actual PR precision. No Archimedean or
limit premise, or induction on a quantified formula, is used.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalSlackRemoval

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded bounded_to_cleared bounded_of_cleared)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (normSq)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def squaredNorm (z B : PTm n) : PTm n := (B*B)*normSq (rawGaussian z)
def squaredRadius (z A : PTm n) : PTm n := (A*A)*(rawDen z*rawDen z)
def linearCost (z A B C : PTm n) : PTm n := two*A*C*B*(rawDen z*rawDen z)
def quadraticCost (z B C : PTm n) : PTm n := (C*C)*(B*B)*(rawDen z*rawDen z)
def precision (z A B C : PTm n) : PTm n := linearCost z A B C+quadraticCost z B C
def slack (z A B C m : PTm n) : Fm PTm n := bounded z (A*pw two m+C*B) (B*pw two m)
def allSlack (z A B C : PTm n) : Fm PTm n :=
  .all (slack (Syn.shift z) (Syn.shift A) (Syn.shift B) (Syn.shift C) (var 0))

@[simp] theorem subst_squaredNorm {m : ℕ} (σ : Fin n → PTm m) (z B : PTm n) :
    Syn.subst σ (squaredNorm z B) = squaredNorm (Syn.subst σ z) (Syn.subst σ B) := by
  simp only [squaredNorm,PTm.subst_mul,ComplexLogarithmRemainder.subst_normSq,GaussianRationalL1.subst_rawGaussian]
@[simp] theorem subst_squaredRadius {m : ℕ} (σ : Fin n → PTm m) (z A : PTm n) :
    Syn.subst σ (squaredRadius z A) = squaredRadius (Syn.subst σ z) (Syn.subst σ A) := by
  simp only [squaredRadius,PTm.subst_mul,GaussianRationalL1.subst_rawDen]
@[simp] theorem subst_linearCost {m : ℕ} (σ : Fin n → PTm m) (z A B C : PTm n) :
    Syn.subst σ (linearCost z A B C) = linearCost (Syn.subst σ z) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ C) := by
  simp only [linearCost,PTm.subst_mul,GaussianRationalL1.subst_rawDen,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]
@[simp] theorem subst_quadraticCost {m : ℕ} (σ : Fin n → PTm m) (z B C : PTm n) :
    Syn.subst σ (quadraticCost z B C) = quadraticCost (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ C) := by
  simp only [quadraticCost,PTm.subst_mul,GaussianRationalL1.subst_rawDen]
@[simp] theorem subst_precision {m : ℕ} (σ : Fin n → PTm m) (z A B C : PTm n) :
    Syn.subst σ (precision z A B C) = precision (Syn.subst σ z) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ C) := by
  simp only [precision,PTm.subst_add,subst_linearCost,subst_quadraticCost]
@[simp] theorem subst_slack {m : ℕ} (σ : Fin n → PTm m) (z A B C k : PTm n) :
    (slack z A B C k).subst σ = slack (Syn.subst σ z) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ C) (Syn.subst σ k) := by
  simp only [slack,GaussianRationalMetric.subst_bounded,PTm.subst_add,PTm.subst_mul,subst_ap2,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]
@[simp] theorem subst_allSlack {m : ℕ} (σ : Fin n → PTm m) (z A B C : PTm n) :
    (allSlack z A B C).subst σ = allSlack (Syn.subst σ z) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ C) := by
  simp only [allSlack,Fm.subst_all,subst_slack,Syn.subst_var,Syn.up_zero,Syn.up_succ,Syn.subst_shift,Syn.shift_subst]

theorem power_positive (m : PTm n) : Γ ⊢[PRAAx] le one (pw two m) :=
  le_trans (zero_lt_succ m) (RationalClosure.succ_le_two_pow m)

/-- The square expansion is linearized using only 1<=2^m. The positive
power is canceled in natural arithmetic, not in a host ordered field. -/
theorem squared_to_linear (U V W X m : PTm n)
    (h : Γ ⊢[PRAAx] le ((pw two m*pw two m)*U)
      ((pw two m*pw two m)*V+pw two m*W+X)) : Γ ⊢[PRAAx]
    le (pw two m*U) (pw two m*V+(W+X)) := by
  have grow : Γ ⊢[PRAAx] le X (pw two m*X) :=
    le_congr (one_mul X) (.eqRefl _) (le_mul_mono (power_positive m) (le_refl X))
  have lifted := le_trans h (add_le_add₂ (le_refl ((pw two m*pw two m)*V+pw two m*W)) grow)
  exact RationalValueBounds.positive_cancel (power_positive m)
    (le_congr (by ipra_ring) (by ipra_ring) lifted)

/-- The actual original-rational Euclidean comparison gives its genuine
cleared square expansion, retaining the computed raw point denominator. -/
theorem slack_linear (z A B C m : PTm n) (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] slack z A B C m) : Γ ⊢[PRAAx]
    le (pw two m*squaredNorm z B) (pw two m*squaredRadius z A+precision z A B C) := by
  have den : Γ ⊢[PRAAx] le one (B*pw two m) :=
    le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono hB (power_positive m))
  have actual := bounded_to_cleared z (rawGaussian z) (rawDen z) (A*pw two m+C*B) (B*pw two m)
    (raw_den_positive z) den (raw_represents z) h
  have expansion : Γ ⊢[PRAAx] le ((pw two m*pw two m)*squaredNorm z B)
      ((pw two m*pw two m)*squaredRadius z A+pw two m*linearCost z A B C+quadraticCost z B C) :=
    le_congr (by unfold squaredNorm; ipra_ring) (by unfold squaredRadius linearCost quadraticCost; ipra_ring) actual
  exact squared_to_linear _ _ _ _ m expansion

/-- A single actual finite query suffices: every strict integer gap would
contradict 2^precision>=precision+1. Both zero radius and zero slack work. -/
theorem slack_removal_at (z A B C : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] slack z A B C (precision z A B C)) : Γ ⊢[PRAAx] bounded z A B := by
  have linear := slack_linear z A B C (precision z A B C) hB h
  have target : Γ ⊢[PRAAx] le (squaredNorm z B) (squaredRadius z A) := by
    refine .orE (lt_or_le (squaredRadius z A) (squaredNorm z B)) ?_ Prf.hyp0
    exact RationalClosure.closure_aux _ Prf.hyp0 linear.wk
  exact bounded_of_cleared z (rawGaussian z) (rawDen z) A B (raw_den_positive z) hB (raw_represents z) target

/-- Original rational Euclidean slack removal. The forall-m hypothesis is
instantiated at the explicit PR integer-gap precision, with no selector,
Archimedean premise or quantified induction. -/
theorem slack_removal (z A B C : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] allSlack z A B C) : Γ ⊢[PRAAx] bounded z A B := by
  apply slack_removal_at z A B C hB
  simpa only [allSlack,subst_slack,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE (precision z A B C)

def dyadicVanishing (z C : PTm n) : Fm PTm n := .all (bounded (Syn.shift z) (Syn.shift C) (pw two (var 0)))
@[simp] theorem subst_dyadicVanishing {m : ℕ} (σ : Fin n → PTm m) (z C : PTm n) :
    (dyadicVanishing z C).subst σ = dyadicVanishing (Syn.subst σ z) (Syn.subst σ C) := by
  simp only [dyadicVanishing,Fm.subst_all,GaussianRationalMetric.subst_bounded,subst_ap2,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.subst_var,Syn.up_zero,Syn.up_succ,Syn.subst_shift,Syn.shift_subst]

/-- A fixed original rational Gaussian point bounded by C*2^(-m) at every
precision has exact zero Euclidean norm, without a canonical-code premise. -/
theorem dyadic_vanishing (z C : PTm n) (h : Γ ⊢[PRAAx] dyadicVanishing z C) : Γ ⊢[PRAAx] bounded z zero one := by
  have actual : Γ ⊢[PRAAx] bounded z C (pw two (precision z zero one C)) := by
    simpa only [dyadicVanishing,GaussianRationalMetric.subst_bounded,subst_ap2,ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE (precision z zero one C)
  exact slack_removal_at z zero one C (le_refl _)
    (GaussianRationalReciprocal.bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring) actual)

theorem vanishing_raw_norm_zero (z C : PTm n) (h : Γ ⊢[PRAAx] dyadicVanishing z C) : Γ ⊢[PRAAx]
    normSq (rawGaussian z) ≐ zero :=
  GaussianRationalMetric.bounded_zero_norm z (rawGaussian z) (rawDen z) one (raw_den_positive z) (le_refl _)
    (raw_represents z) (dyadic_vanishing z C h)

/-! Actual query program and universally closed original-rational results. -/
def precisionF : PR 4 := PTm.toPR (precision (var 0) (var 1) (var 2) (var 3))
theorem precision_at (z A B C : PTm n) : Γ ⊢[PRAAx] PTm.app precisionF ![z,A,B,C] ≐ precision z A B C := by
  simpa only [precisionF,subst_precision,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (precision (var 0) (var 1) (var 2) (var 3) : PTm 4) ![z,A,B,C]

theorem finite_euclidean_slack_removal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ slack (var 0) (var 1) (var 2) (var 3) (precision (var 0) (var 1) (var 2) (var 3)) ⟶
      bounded (var 0) (var 1) (var 2)) :=
  closeUniv 4 (.impI (.impI (slack_removal_at _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem euclidean_slack_removal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ allSlack (var 0) (var 1) (var 2) (var 3) ⟶ bounded (var 0) (var 1) (var 2)) :=
  closeUniv 4 (.impI (.impI (slack_removal _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem dyadic_vanishing_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (dyadicVanishing (var 0) (var 1) ⟶
      (bounded (var 0) zero one ⋏ normSq (rawGaussian (var 0)) ≐ zero)) :=
  closeUniv 2 (.impI (.andI (dyadic_vanishing _ _ Prf.hyp0) (vanishing_raw_norm_zero _ _ Prf.hyp0)))

theorem slack_query_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (PTm.app precisionF ![var 0,var 1,var 2,var 3] ≐ precision (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (precision_at _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianRationalSlackRemoval
