import IPRADerivations.Analysis.GaussianDominantScalarOrder
import IPRADerivations.Core.LinearCombination

/-!
# Exact natural weights for residual decrease

The three integer weights are derived from the represented alpha=P/Q.
The original lower bound 64Q<=65DP supplies the contraction budget;
no successful weighted sum or target decrease is assumed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianResidualDecreaseWeights

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (positive_product)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def mainWeight (P Q : PTm n) : PTm n := num 6144*monus Q P
def errorWeight (P : PTm n) : PTm n := num 195*P
def otherWeight (P : PTm n) : PTm n := num 4160*P
def sumWeight (P Q : PTm n) : PTm n := mainWeight P Q+errorWeight P+otherWeight P
def scale (Q : PTm n) : PTm n := num 6144*Q
def gain (P : PTm n) : PTm n := num 1789*P
def rateDen (D : PTm n) : PTm n := (two*two)*D
def rateNum (D : PTm n) : PTm n := monus (rateDen D) one
def lowerBound (D P Q : PTm n) : Fm PTm n := le ((num 64)*Q) ((num 65)*D*P)
def input (D P Q : PTm n) : Fm PTm n := le one D ⋏ (le one Q ⋏ (le P Q ⋏ lowerBound D P Q))

@[simp] theorem subst_mainWeight {m : ℕ} (σ : Fin n → PTm m) (P Q : PTm n) :
    Syn.subst σ (mainWeight P Q) = mainWeight (Syn.subst σ P) (Syn.subst σ Q) := by simp [mainWeight]
@[simp] theorem subst_errorWeight {m : ℕ} (σ : Fin n → PTm m) (P : PTm n) :
    Syn.subst σ (errorWeight P) = errorWeight (Syn.subst σ P) := by simp [errorWeight]
@[simp] theorem subst_otherWeight {m : ℕ} (σ : Fin n → PTm m) (P : PTm n) :
    Syn.subst σ (otherWeight P) = otherWeight (Syn.subst σ P) := by simp [otherWeight]
@[simp] theorem subst_sumWeight {m : ℕ} (σ : Fin n → PTm m) (P Q : PTm n) :
    Syn.subst σ (sumWeight P Q) = sumWeight (Syn.subst σ P) (Syn.subst σ Q) := by simp [sumWeight]
@[simp] theorem subst_scale {m : ℕ} (σ : Fin n → PTm m) (Q : PTm n) :
    Syn.subst σ (scale Q) = scale (Syn.subst σ Q) := by simp [scale]
@[simp] theorem subst_gain {m : ℕ} (σ : Fin n → PTm m) (P : PTm n) :
    Syn.subst σ (gain P) = gain (Syn.subst σ P) := by simp [gain]
@[simp] theorem subst_rateDen {m : ℕ} (σ : Fin n → PTm m) (D : PTm n) :
    Syn.subst σ (rateDen D) = rateDen (Syn.subst σ D) := by simp [rateDen]
@[simp] theorem subst_rateNum {m : ℕ} (σ : Fin n → PTm m) (D : PTm n) :
    Syn.subst σ (rateNum D) = rateNum (Syn.subst σ D) := by simp [rateNum]
@[simp] theorem subst_lowerBound {m : ℕ} (σ : Fin n → PTm m) (D P Q : PTm n) :
    (lowerBound D P Q).subst σ = lowerBound (Syn.subst σ D) (Syn.subst σ P) (Syn.subst σ Q) := by simp [lowerBound]
@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (D P Q : PTm n) :
    (input D P Q).subst σ = input (Syn.subst σ D) (Syn.subst σ P) (Syn.subst σ Q) := by simp [input]

theorem scale_positive (Q : PTm n) (hQ : Γ ⊢[PRAAx] le one Q) : Γ ⊢[PRAAx] le one (scale Q) :=
  positive_product _ _ (le_of_eq_add (d := num 6143) (by ipra_ring)) hQ

theorem rate_den_positive (D : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx] le one (rateDen D) :=
  positive_product _ _ (positive_product two two (le_succ_self one) (le_succ_self one)) hD

theorem rate_identity (D : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    rateDen D ≐ one+rateNum D := eq_add_of_le (rate_den_positive D hD)

theorem total_gain_identity (P Q : PTm n) (hPQ : Γ ⊢[PRAAx] le P Q) : Γ ⊢[PRAAx]
    scale Q ≐ sumWeight P Q+gain P := by
  have e := natEq (eq_add_of_le hPQ)
  apply deriveNat
  unfold scale sumWeight mainWeight errorWeight otherWeight gain
  ipra_simps
  linear_combination 6144*e

theorem numerator_positive (D P Q : PTm n) (hQ : Γ ⊢[PRAAx] le one Q)
    (hLower : Γ ⊢[PRAAx] lowerBound D P Q) : Γ ⊢[PRAAx] le one P := by
  have positive : Γ ⊢[PRAAx] le one ((num 65)*D*P) :=
    le_trans (positive_product _ _ (le_of_eq_add (d := num 63) (by ipra_ring)) hQ) hLower
  exact GaussianDominantScalarOrder.factor_positive_left P ((num 65)*D)
    (le_congr (.eqRefl _) (by ipra_ring) positive)

/-- 65*6144<=64*4*1789 is the exact spare numerical gain. -/
theorem gain_budget (D P Q : PTm n) (hLower : Γ ⊢[PRAAx] lowerBound D P Q) : Γ ⊢[PRAAx]
    le (scale Q) (rateDen D*gain P) := by
  have constant : Γ ⊢[PRAAx] le ((num 65)*(num 6144) : PTm n) ((num 64)*(two*two)*(num 1789)) :=
    le_of_eq_add (d := num 58624) (by ipra_ring)
  have first : Γ ⊢[PRAAx] le ((num 64)*scale Q) (((num 65)*(num 6144))*D*P) :=
    le_congr (by unfold scale; ipra_ring) (by ipra_ring) (mul_le_mul_right (num 6144) hLower)
  have second : Γ ⊢[PRAAx] le (((num 65)*(num 6144))*D*P) ((num 64)*(rateDen D*gain P)) :=
    le_congr (by ipra_ring) (by unfold rateDen gain; ipra_ring) (mul_le_mul_right (D*P) constant)
  exact RationalValueBounds.positive_cancel
    (le_of_eq_add (d := num 63) (by ipra_ring)) (le_trans first second)

theorem contraction_budget (D P Q : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hPQ : Γ ⊢[PRAAx] le P Q) (hLower : Γ ⊢[PRAAx] lowerBound D P Q) : Γ ⊢[PRAAx]
    le (rateDen D*sumWeight P Q) (rateNum D*scale Q) := by
  refine le_of_eq_add (d := monus (rateDen D*gain P) (scale Q)) ?_
  ipra_lc 𝔞(rateDen D)*natEq (total_gain_identity P Q hPQ)-𝔞(scale Q)*natEq (rate_identity D hD)+
    natEq (eq_add_of_le (gain_budget D P Q hLower))

theorem weights_correct (D P Q : PTm n) (h : Γ ⊢[PRAAx] input D P Q) : Γ ⊢[PRAAx]
    le one P ⋏ (le one (scale Q) ⋏ le (rateDen D*sumWeight P Q) (rateNum D*scale Q)) :=
  .andI (numerator_positive D P Q (Prf.andE₁ (Prf.andE₂ h)) (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h))))
    (.andI (scale_positive Q (Prf.andE₁ (Prf.andE₂ h)))
      (contraction_budget D P Q (Prf.andE₁ h) (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h)))
        (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))))

theorem numerator_nonzero (D P Q : PTm n) (hQ : Γ ⊢[PRAAx] le one Q)
    (hLower : Γ ⊢[PRAAx] lowerBound D P Q) : Γ ⊢[PRAAx] neg (P ≐ zero) := by
  refine .impI ?_
  exact not_succ_le_self zero _ (le_congr (.eqRefl _) Prf.hyp0 (numerator_positive D P Q hQ hLower).wk)

theorem rate_positive (D : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx] le one (rateNum D) := by
  have fourDen : Γ ⊢[PRAAx] le (two*two) (rateDen D) :=
    le_congr (one_mul _) (mul_comm D (two*two)) (mul_le_mul_right (two*two) hD)
  have twoDen : Γ ⊢[PRAAx] le two (rateDen D) :=
    le_trans (le_of_eq_add (d := two) (by ipra_ring)) fourDen
  apply le_of_add_le_add_right (c := one)
  exact le_congr (by ipra_ring) ((rate_identity D hD).eqTrans (add_comm _ _)) twoDen

theorem rate_strict (D : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx] lt (rateNum D) (rateDen D) :=
  le_congr (.eqRefl _) (((succ_eq_add_one (rateNum D)).eqTrans (add_comm _ _)).eqTrans (rate_identity D hD).eqSymm)
    (le_refl _)

def output (D P Q : PTm n) : PTm n := pairT (mainWeight P Q)
  (pairT (errorWeight P) (pairT (otherWeight P) (pairT (scale Q) (pairT (rateNum D) (rateDen D)))))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (D P Q : PTm n) : PTm n := ap3 outputF D P Q

@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (D P Q : PTm n) :
    Syn.subst σ (output D P Q) = output (Syn.subst σ D) (Syn.subst σ P) (Syn.subst σ Q) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (D P Q : PTm n) :
    Syn.subst σ (run D P Q) = run (Syn.subst σ D) (Syn.subst σ P) (Syn.subst σ Q) := by simp [run]

theorem program_at (D P Q : PTm n) : Γ ⊢[PRAAx] run D P Q ≐ output D P Q := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![D,P,Q]

theorem returned_main (D P Q : PTm n) : Γ ⊢[PRAAx] fstT (run D P Q) ≐ mainWeight P Q :=
  (congrFst (program_at D P Q)).eqTrans (fst_pair _ _)
theorem returned_error (D P Q : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run D P Q)) ≐ errorWeight P :=
  (congrFst ((congrSnd (program_at D P Q)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_other (D P Q : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run D P Q))) ≐ otherWeight P :=
  (congrFst ((congrSnd ((congrSnd (program_at D P Q)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_scale (D P Q : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run D P Q)))) ≐ scale Q :=
  (congrFst ((congrSnd ((congrSnd ((congrSnd (program_at D P Q)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_rate_num (D P Q : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (sndT (run D P Q))))) ≐ rateNum D :=
  (congrFst ((congrSnd ((congrSnd ((congrSnd ((congrSnd (program_at D P Q)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_rate_den (D P Q : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (sndT (run D P Q))))) ≐ rateDen D :=
  (congrSnd ((congrSnd ((congrSnd ((congrSnd ((congrSnd (program_at D P Q)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)

theorem exact_residual_weights_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (input (var 0) (var 1) (var 2) ⟶
      (le one (var 1) ⋏ (le one (scale (var 2)) ⋏
        le (rateDen (var 0)*sumWeight (var 1) (var 2)) (rateNum (var 0)*scale (var 2))))) :=
  closeUniv 3 (.impI (weights_correct _ _ _ Prf.hyp0))

theorem derived_contraction_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ le (var 1) (var 2) ⟶ lowerBound (var 0) (var 1) (var 2) ⟶
      le (rateDen (var 0)*sumWeight (var 1) (var 2)) (rateNum (var 0)*scale (var 2))) :=
  closeUniv 3 (.impI (.impI (.impI (contraction_budget _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem actual_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (var 0) ⟶ le one (rateNum (var 0)) ⋏ lt (rateNum (var 0)) (rateDen (var 0))) :=
  closeUniv 1 (.impI (.andI (rate_positive _ Prf.hyp0) (rate_strict _ Prf.hyp0)))

theorem actual_weight_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)

end LeanProofs.IPRA.Analysis.GaussianResidualDecreaseWeights
