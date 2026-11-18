import IPRADerivations.Analysis.GaussianDominantPairAlgebra
import IPRADerivations.Analysis.GaussianRationalTranslation
import IPRADerivations.Analysis.GaussianDominantScalarOrder

/-!
# Actual largest radius-weighted translated coefficient

An inclusive rational argmin on negative squared norms selects an actual
positive-degree translated coefficient. Its value is computed by the
original synthetic-quotient stages and multiplied by the actual rational
radius power. Every degree, list, point, radius numerator/denominator and
candidate index is numerical. Ties retain the earlier value. No maximum,
positive coefficient, canonical original input or common denominator is
assumed. The positive numerical degree is the sole range guard.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianTranslationCoefficientMaximum

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qmul evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (power)
open LeanProofs.IPRA.Analysis.GaussianDominantPairAlgebra (radiusPoint)
open LeanProofs.IPRA.Analysis.GaussianRationalTranslationStages (stage)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qnormSq)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE selected)
open LeanProofs.IPRA.Analysis.RationalValueBounds (negate)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def term (C N z A B i : PTm n) : PTm n :=
  qmul (power (radiusPoint A B) i) (evaluate (stage C N z i) z)
def data (C N z A B : PTm n) : PTm n := pairT C (pairT N (pairT z (pairT A B)))
def negativeScore (C N z A B r : PTm n) : PTm n := negate (qnormSq (term C N z A B (succ r)))
def negativeBody : PTm 2 := negativeScore (fstT (var 1)) (fstT (sndT (var 1)))
  (fstT (sndT (sndT (var 1)))) (fstT (sndT (sndT (sndT (var 1)))))
  (sndT (sndT (sndT (sndT (var 1))))) (var 0)
def negativeScoreF : PR 2 := PTm.toPR negativeBody
def winner (C N z A B : PTm n) : PTm n := succ (selected negativeScoreF (pred N) (data C N z A B))
def base (C N z A B : PTm n) : PTm n := term C N z A B (winner C N z A B)

@[simp] theorem subst_term {m : ℕ} (σ : Fin n → PTm m) (C N z A B i : PTm n) :
    Syn.subst σ (term C N z A B i) = term (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z)
      (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ i) := by simp [term]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (C N z A B : PTm n) :
    Syn.subst σ (data C N z A B) = data (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z)
      (Syn.subst σ A) (Syn.subst σ B) := by simp [data]
@[simp] theorem subst_negativeScore {m : ℕ} (σ : Fin n → PTm m) (C N z A B r : PTm n) :
    Syn.subst σ (negativeScore C N z A B r) = negativeScore (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ z) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ r) := by simp [negativeScore]
@[simp] theorem subst_winner {m : ℕ} (σ : Fin n → PTm m) (C N z A B : PTm n) :
    Syn.subst σ (winner C N z A B) = winner (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z)
      (Syn.subst σ A) (Syn.subst σ B) := by simp [winner]
@[simp] theorem subst_base {m : ℕ} (σ : Fin n → PTm m) (C N z A B : PTm n) :
    Syn.subst σ (base C N z A B) = base (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z)
      (Syn.subst σ A) (Syn.subst σ B) := by simp [base]

theorem term_congr {C C' N N' z z' A A' B B' i i' : PTm n}
    (hC : Γ ⊢[PRAAx] C ≐ C') (hN : Γ ⊢[PRAAx] N ≐ N') (hz : Γ ⊢[PRAAx] z ≐ z')
    (hA : Γ ⊢[PRAAx] A ≐ A') (hB : Γ ⊢[PRAAx] B ≐ B') (hi : Γ ⊢[PRAAx] i ≐ i') : Γ ⊢[PRAAx]
    term C N z A B i ≐ term C' N' z' A' B' i' := by
  simpa only [subst_term,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,
    (show (![C,N,z,A,B,i] : Fin 6 → PTm n) 5 = i from rfl),
    (show (![C',N',z',A',B',i'] : Fin 6 → PTm n) 5 = i' from rfl)] using
    Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (term (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6)
      (σ := ![C,N,z,A,B,i]) (σ' := ![C',N',z',A',B',i'])
      (fun j => by fin_cases j; exact hC; exact hN; exact hz; exact hA; exact hB; exact hi)

theorem term_canonical (C N z A B i : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (term C N z A B i) := GaussianRationalHorner.qmul_canonical _ _

theorem negative_score_at (C N z A B r : PTm n) : Γ ⊢[PRAAx]
    ap2 negativeScoreF r (data C N z A B) ≐ negate (qnormSq (term C N z A B (succ r))) := by
  have t1 : Γ ⊢[PRAAx] sndT (data C N z A B) ≐ pairT N (pairT z (pairT A B)) := snd_pair _ _
  have t2 := (congrSnd t1).eqTrans (snd_pair _ _)
  have t3 := (congrSnd t2).eqTrans (snd_pair _ _)
  have fields := RationalValueBounds.negate_congr (GaussianRationalProductWitness.qnormSq_congr
    (term_congr (fst_pair C (pairT N (pairT z (pairT A B))))
      ((congrFst t1).eqTrans (fst_pair _ _)) ((congrFst t2).eqTrans (fst_pair _ _))
      ((congrFst t3).eqTrans (fst_pair _ _)) ((congrSnd t3).eqTrans (snd_pair _ _)) (.eqRefl (succ r))))
  have program := toPR_eq (Γ := Γ) negativeBody ![r,data C N z A B]
  have shape : Syn.subst ![r,data C N z A B] negativeBody =
      negativeScore (fstT (data C N z A B)) (fstT (sndT (data C N z A B)))
        (fstT (sndT (sndT (data C N z A B)))) (fstT (sndT (sndT (sndT (data C N z A B)))))
        (sndT (sndT (sndT (sndT (data C N z A B))))) r := by
    simp only [negativeBody,subst_negativeScore,subst_fstT,subst_sndT,Syn.subst_var,
      Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [shape] at program
  exact program.eqTrans (by simpa only [negativeScore,data] using fields)

theorem negative_score_at_degree (C N z A B i : PTm n) (hi : Γ ⊢[PRAAx] le one i) : Γ ⊢[PRAAx]
    ap2 negativeScoreF (pred i) (data C N z A B) ≐ negate (qnormSq (term C N z A B i)) :=
  (negative_score_at C N z A B (pred i)).eqTrans (RationalValueBounds.negate_congr
    (GaussianRationalProductWitness.qnormSq_congr (term_congr (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (.eqRefl _) (.eqRefl _) (RationalIntegerNormalization.positive_form hi).eqSymm)))

theorem winner_bounds (C N z A B : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    le one (winner C N z A B) ⋏ le (winner C N z A B) N :=
  .andI (zero_lt_succ _) (le_congr (.eqRefl _) (RationalIntegerNormalization.positive_form hN).eqSymm
    ((succ_monus_succ _ _).eqTrans (RationalArgmin.selected_spec negativeScoreF (pred N) (data C N z A B))))

theorem winner_maximal (C N z A B i : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hi : Γ ⊢[PRAAx] le one i) (hiN : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    rationalLE (qnormSq (term C N z A B i)) (qnormSq (base C N z A B)) := by
  have range : Γ ⊢[PRAAx] le (pred i) (pred N) := (succ_monus_succ _ _).eqSymm.eqTrans
    (le_congr (RationalIntegerNormalization.positive_form hi) (RationalIntegerNormalization.positive_form hN) hiN)
  have least := RationalArgmin.selected_minimal negativeScoreF (pred N) (pred i) (data C N z A B) range
  have negative := RationalArgmin.rationalLE_congr (negative_score_at C N z A B _)
    (negative_score_at_degree C N z A B i hi) least
  exact GaussianDominantScalarOrder.unnegate_le _ _ negative

def output (C N z A B : PTm n) : PTm n := pairT (winner C N z A B) (base C N z A B)
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (C N z A B : PTm n) : PTm n := PTm.app outputF ![C,N,z,A,B]

@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (C N z A B : PTm n) :
    Syn.subst σ (output C N z A B) = output (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z)
      (Syn.subst σ A) (Syn.subst σ B) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (C N z A B : PTm n) :
    Syn.subst σ (run C N z A B) = run (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z)
      (Syn.subst σ A) (Syn.subst σ B) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (C N z A B : PTm n) : Γ ⊢[PRAAx] run C N z A B ≐ output C N z A B := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![C,N,z,A,B]
theorem returned_index (C N z A B : PTm n) : Γ ⊢[PRAAx] fstT (run C N z A B) ≐ winner C N z A B :=
  (congrFst (program_at C N z A B)).eqTrans (fst_pair _ _)
theorem returned_value (C N z A B : PTm n) : Γ ⊢[PRAAx] sndT (run C N z A B) ≐ base C N z A B :=
  (congrSnd (program_at C N z A B)).eqTrans (snd_pair _ _)

theorem translated_coefficient_maximum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 1) ⟶ le one (var 5) ⟶ le (var 5) (var 1) ⟶
      rationalLE (qnormSq (term (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))
        (qnormSq (base (var 0) (var 1) (var 2) (var 3) (var 4)))) :=
  closeUniv 6 (.impI (.impI (.impI (winner_maximal _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem translated_coefficient_winner_bounds_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ (le one (winner (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
      le (winner (var 0) (var 1) (var 2) (var 3) (var 4)) (var 1))) :=
  closeUniv 5 (.impI (winner_bounds _ _ _ _ _ Prf.hyp0))

theorem translated_coefficient_maximum_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianTranslationCoefficientMaximum
