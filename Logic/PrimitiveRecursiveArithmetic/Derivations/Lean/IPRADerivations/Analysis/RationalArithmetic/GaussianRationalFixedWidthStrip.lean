import IPRADerivations.Analysis.Polynomials.GaussianPolynomialMonicCompanion
import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianRationalMonicReduction
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual repeated synthetic stripping at a fixed original width

Every step is the actual synthetic quotient followed by one leading zero.
It therefore writes D+1 canonical coefficients, even at D=0 and without
successful division. An actual numerical recursor iterates this same step.
Original raw coefficients are retained literally at stage zero; every
positive stage is canonical independently of the original data. Original
shape and an actual current evaluation-zero condition derive a local factor
equation. No predicted degree/count bound, root preservation, cancellation
through another polynomial or global factor accumulation is assumed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalFixedWidthStrip

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qadd qmul evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision
  (quotient quotient_length quotient_canonical canonicalCoefficients qadd_congr qmul_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialBuffers
  (leftPad pad_length pad_evaluation pad_leading pad_tail)
open LeanProofs.IPRA.Analysis.GaussianRationalMonicReduction
  (evaluate_congr canonical_coefficients_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def stripStep (Q D x : PTm n) : PTm n := leftPad (quotient Q x D) one
def data (Q D x : PTm n) : PTm n := pairT Q (pairT D x)
def initial : PTm 1 := fstT (var 0)
def stepBody : PTm 3 := stripStep (var 1) (fstT (sndT (var 2))) (sndT (sndT (var 2)))
def blockF : PR 2 := rec2 initial stepBody
def block (Q D x r : PTm n) : PTm n := ap2 blockF r (data Q D x)
@[simp] theorem subst_stripStep {l : ℕ} (σ : Fin n → PTm l) (Q D x : PTm n) :
    Syn.subst σ (stripStep Q D x) = stripStep (Syn.subst σ Q) (Syn.subst σ D) (Syn.subst σ x) := by simp [stripStep]
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (Q D x : PTm n) :
    Syn.subst σ (data Q D x) = data (Syn.subst σ Q) (Syn.subst σ D) (Syn.subst σ x) := by simp [data]
@[simp] theorem subst_block {l : ℕ} (σ : Fin n → PTm l) (Q D x r : PTm n) :
    Syn.subst σ (block Q D x r) = block (Syn.subst σ Q) (Syn.subst σ D) (Syn.subst σ x) (Syn.subst σ r) := by simp [block]

theorem strip_congr {Q Q' D D' x x' : PTm n} (hQ : Γ ⊢[PRAAx] Q ≐ Q')
    (hD : Γ ⊢[PRAAx] D ≐ D') (hx : Γ ⊢[PRAAx] x ≐ x') : Γ ⊢[PRAAx]
    stripStep Q D x ≐ stripStep Q' D' x' := by
  ipra_congr (stripStep (var 0) (var 1) (var 2) : PTm 3) with [hQ, hD, hx]
theorem block_congr {Q Q' D D' x x' r r' : PTm n} (hQ : Γ ⊢[PRAAx] Q ≐ Q')
    (hD : Γ ⊢[PRAAx] D ≐ D') (hx : Γ ⊢[PRAAx] x ≐ x') (hr : Γ ⊢[PRAAx] r ≐ r') : Γ ⊢[PRAAx]
    block Q D x r ≐ block Q' D' x' r' := congrAp2 blockF hr (congrPairT hQ (congrPairT hD hx))
theorem block_index_congr (Q D x : PTm n) {r s : PTm n} (h : Γ ⊢[PRAAx] r ≐ s) : Γ ⊢[PRAAx]
    block Q D x r ≐ block Q D x s := block_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) h

theorem strip_length (Q D x : PTm n) : Γ ⊢[PRAAx] length (stripStep Q D x) ≐ succ D :=
  (pad_length _ _).eqTrans ((congrAdd (.eqRefl _) (quotient_length _ _ _)).eqTrans (by ipra_ring))
theorem strip_canonical (Q D x : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (stripStep Q D x) :=
  GaussianPolynomialMonicCompanion.pad_canonical _ _ (quotient_canonical _ _ _)
theorem strip_head (Q D x : PTm n) : Γ ⊢[PRAAx] entry (stripStep Q D x) zero ≐ qzero :=
  pad_leading _ _ _ (le_refl one)
theorem strip_tail (Q D x i : PTm n) (hi : Γ ⊢[PRAAx] lt i D) : Γ ⊢[PRAAx]
    entry (stripStep Q D x) (succ i) ≐ entry (quotient Q x D) i :=
  (entry_congr (.eqRefl _) (by ipra_ring : Γ ⊢[PRAAx] succ i ≐ one+i)).eqTrans
    (pad_tail _ _ _ (lt_congr (.eqRefl _) (quotient_length _ _ _).eqSymm hi))
theorem strip_division_evaluation (Q D x z : PTm n) (hQ : Γ ⊢[PRAAx] length Q ≐ succ D) : Γ ⊢[PRAAx]
    evaluate Q z ≐ qadd (qmul (qsub z x) (evaluate (stripStep Q D x) z)) (evaluate Q x) :=
  (GaussianRationalSyntheticDivision.division_evaluation _ _ _ _ hQ).eqTrans
    (qadd_congr (qmul_congr (.eqRefl _) (pad_evaluation _ _ _).eqSymm) (.eqRefl _))
theorem strip_factor (Q D x z : PTm n) (hQ : Γ ⊢[PRAAx] length Q ≐ succ D)
    (hRoot : Γ ⊢[PRAAx] evaluate Q x ≐ qzero) : Γ ⊢[PRAAx]
    evaluate Q z ≐ qmul (qsub z x) (evaluate (stripStep Q D x) z) :=
  (strip_division_evaluation _ _ _ _ hQ).eqTrans
    ((qadd_congr (.eqRefl _) hRoot).eqTrans
      (GaussianReciprocalHorner.qadd_zero_right _ (GaussianRationalHorner.qmul_canonical _ _)))
theorem zero_width_evaluation (Q x z : PTm n) : Γ ⊢[PRAAx] evaluate (stripStep Q zero x) z ≐ qzero :=
  (pad_evaluation _ _ _).eqTrans
    ((congrAp3 GaussianRationalHorner.hornerF (quotient_length Q x zero) (.eqRefl _) (.eqRefl _)).eqTrans
      (GaussianRationalHorner.horner_zero _ _))

theorem block_zero (Q D x : PTm n) : Γ ⊢[PRAAx] block Q D x zero ≐ Q := by
  have e := rec2_zero (Γ := Γ) initial stepBody (data Q D x)
  simp only [initial,subst_fstT,Syn.subst_var,Matrix.cons_val_zero] at e
  exact e.eqTrans (fst_pair _ _)
theorem block_succ (Q D x r : PTm n) : Γ ⊢[PRAAx]
    block Q D x (succ r) ≐ stripStep (block Q D x r) D x := by
  have e := rec2_succ (Γ := Γ) initial stepBody r (data Q D x)
  simp only [stepBody,subst_stripStep,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at e
  exact e.eqTrans (strip_congr (.eqRefl _)
    ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
    ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)))

/-- No bound on the number of stripping steps occurs in this shape proof. -/
theorem block_length (Q D x r : PTm n) (hQ : Γ ⊢[PRAAx] length Q ≐ succ D) : Γ ⊢[PRAAx]
    length (block Q D x r) ≐ succ D := by
  refine .orE (zero_or_succ r) ?_ ?_
  · exact (congrFst (block_index_congr _ _ _ Prf.hyp0)).eqTrans
      ((congrFst (block_zero _ _ _)).eqTrans hQ.wk)
  · exact (congrFst (block_index_congr _ _ _ Prf.hyp0)).eqTrans
      ((congrFst (block_succ _ _ _ _)).eqTrans (strip_length _ _ _))
theorem block_positive_canonical (Q D x r : PTm n) (hr : Γ ⊢[PRAAx] le one r) : Γ ⊢[PRAAx]
    canonicalCoefficients (block Q D x r) := by
  refine .orE (zero_or_succ r) ?_ ?_
  · exact not_succ_le_self zero _ (le_congr (.eqRefl _) Prf.hyp0 hr.wk)
  · exact canonical_coefficients_congr
      ((block_index_congr _ _ _ Prf.hyp0).eqTrans (block_succ _ _ _ _)) (strip_canonical _ _ _)
theorem block_canonical (Q D x r : PTm n) (hQ : Γ ⊢[PRAAx] canonicalCoefficients Q) : Γ ⊢[PRAAx]
    canonicalCoefficients (block Q D x r) := by
  refine .orE (zero_or_succ r) ?_ ?_
  · exact canonical_coefficients_congr
      ((block_index_congr _ _ _ Prf.hyp0).eqTrans (block_zero _ _ _)) hQ.wk
  · exact canonical_coefficients_congr
      ((block_index_congr _ _ _ Prf.hyp0).eqTrans (block_succ _ _ _ _)) (strip_canonical _ _ _)
theorem block_division_evaluation (Q D x r z : PTm n) (hQ : Γ ⊢[PRAAx] length Q ≐ succ D) : Γ ⊢[PRAAx]
    evaluate (block Q D x r) z ≐
      qadd (qmul (qsub z x) (evaluate (block Q D x (succ r)) z)) (evaluate (block Q D x r) x) :=
  (strip_division_evaluation _ _ _ _ (block_length _ _ _ _ hQ)).eqTrans
    (qadd_congr (qmul_congr (.eqRefl _) (evaluate_congr (block_succ _ _ _ _).eqSymm (.eqRefl _))) (.eqRefl _))
theorem block_factor (Q D x r z : PTm n) (hQ : Γ ⊢[PRAAx] length Q ≐ succ D)
    (hRoot : Γ ⊢[PRAAx] evaluate (block Q D x r) x ≐ qzero) : Γ ⊢[PRAAx]
    evaluate (block Q D x r) z ≐ qmul (qsub z x) (evaluate (block Q D x (succ r)) z) :=
  (strip_factor _ _ _ _ (block_length _ _ _ _ hQ) hRoot).eqTrans
    (qmul_congr (.eqRefl _) (evaluate_congr (block_succ _ _ _ _).eqSymm (.eqRefl _)))

/-- All original inputs and the number of stripping steps are runtime data. -/
def blockProgramF : PR 4 := PTm.toPR (block (var 0) (var 1) (var 2) (var 3))
def output (Q D x r : PTm n) : PTm n := pairT (block Q D x r)
  (pairT (block Q D x (succ r)) (stripStep (block Q D x r) D x))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (Q D x r : PTm n) : PTm n := app outputF ![Q,D,x,r]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (Q D x r : PTm n) :
    Syn.subst σ (output Q D x r) = output (Syn.subst σ Q) (Syn.subst σ D) (Syn.subst σ x) (Syn.subst σ r) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (Q D x r : PTm n) :
    Syn.subst σ (run Q D x r) = run (Syn.subst σ Q) (Syn.subst σ D) (Syn.subst σ x) (Syn.subst σ r) := by
  simp [run]
  funext i
  fin_cases i <;> rfl
theorem block_program_at (Q D x r : PTm n) : Γ ⊢[PRAAx] app blockProgramF ![Q,D,x,r] ≐ block Q D x r := by
  simpa [blockProgramF] using toPR_eq (Γ := Γ) (block (var 0) (var 1) (var 2) (var 3) : PTm 4) ![Q,D,x,r]
theorem program_at (Q D x r : PTm n) : Γ ⊢[PRAAx] run Q D x r ≐ output Q D x r := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![Q,D,x,r]
theorem returned_current (Q D x r : PTm n) : Γ ⊢[PRAAx] fstT (run Q D x r) ≐ block Q D x r :=
  (congrFst (program_at _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_next (Q D x r : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run Q D x r)) ≐ block Q D x (succ r) :=
  (congrFst ((congrSnd (program_at _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_strip (Q D x r : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run Q D x r)) ≐ stripStep (block Q D x r) D x :=
  (congrSnd ((congrSnd (program_at _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_successor_code (Q D x r : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run Q D x r)) ≐ sndT (sndT (run Q D x r)) :=
  (returned_next _ _ _ _).eqTrans ((block_succ _ _ _ _).eqTrans (returned_strip _ _ _ _).eqSymm)
theorem returned_current_length (Q D x r : PTm n) (hQ : Γ ⊢[PRAAx] length Q ≐ succ D) : Γ ⊢[PRAAx]
    length (fstT (run Q D x r)) ≐ succ D := (congrFst (returned_current _ _ _ _)).eqTrans (block_length _ _ _ _ hQ)
theorem returned_next_length (Q D x r : PTm n) : Γ ⊢[PRAAx]
    length (fstT (sndT (run Q D x r))) ≐ succ D :=
  (congrFst (returned_next _ _ _ _)).eqTrans ((congrFst (block_succ _ _ _ _)).eqTrans (strip_length _ _ _))
theorem returned_next_canonical (Q D x r : PTm n) : Γ ⊢[PRAAx]
    canonicalCoefficients (fstT (sndT (run Q D x r))) := canonical_coefficients_congr
      ((returned_next _ _ _ _).eqTrans (block_succ _ _ _ _)) (strip_canonical _ _ _)
theorem returned_factor (Q D x r z : PTm n) (hQ : Γ ⊢[PRAAx] length Q ≐ succ D)
    (hRoot : Γ ⊢[PRAAx] evaluate (fstT (run Q D x r)) x ≐ qzero) : Γ ⊢[PRAAx]
    evaluate (fstT (run Q D x r)) z ≐ qmul (qsub z x) (evaluate (fstT (sndT (run Q D x r))) z) :=
  (evaluate_congr (returned_current _ _ _ _) (.eqRefl _)).eqTrans
    ((block_factor _ _ _ _ _ hQ ((evaluate_congr (returned_current _ _ _ _).eqSymm (.eqRefl _)).eqTrans hRoot)).eqTrans
      (qmul_congr (.eqRefl _) (evaluate_congr (returned_next _ _ _ _).eqSymm (.eqRefl _))))

theorem actual_strip_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((length (stripStep (var 0) (var 1) (var 2)) ≐ succ (var 1)) ⋏
      (canonicalCoefficients (stripStep (var 0) (var 1) (var 2)) ⋏ entry (stripStep (var 0) (var 1) (var 2)) zero ≐ qzero)) :=
  closeUniv 3 (.andI (strip_length _ _ _) (.andI (strip_canonical _ _ _) (strip_head _ _ _)))
theorem actual_strip_tail_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (var 1) ⟶ entry (stripStep (var 0) (var 1) (var 2)) (succ (var 3)) ≐
      entry (quotient (var 0) (var 2) (var 1)) (var 3)) := closeUniv 4 (.impI (strip_tail _ _ _ _ Prf.hyp0))
theorem actual_strip_division_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶ evaluate (var 0) (var 3) ≐
      qadd (qmul (qsub (var 3) (var 2)) (evaluate (stripStep (var 0) (var 1) (var 2)) (var 3))) (evaluate (var 0) (var 2))) :=
  closeUniv 4 (.impI (strip_division_evaluation _ _ _ _ Prf.hyp0))
theorem actual_strip_factor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶ evaluate (var 0) (var 2) ≐ qzero ⟶ evaluate (var 0) (var 3) ≐
      qmul (qsub (var 3) (var 2)) (evaluate (stripStep (var 0) (var 1) (var 2)) (var 3))) :=
  closeUniv 4 (.impI (.impI (strip_factor _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_block_recursion_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((block (var 0) (var 1) (var 2) zero ≐ var 0) ⋏ block (var 0) (var 1) (var 2) (succ (var 3)) ≐
      stripStep (block (var 0) (var 1) (var 2) (var 3)) (var 1) (var 2)) :=
  closeUniv 4 (.andI (block_zero _ _ _) (block_succ _ _ _ _))
theorem actual_block_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶ length (block (var 0) (var 1) (var 2) (var 3)) ≐ succ (var 1)) :=
  closeUniv 4 (.impI (block_length _ _ _ _ Prf.hyp0))
theorem actual_positive_block_canonical_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶ canonicalCoefficients (block (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (block_positive_canonical _ _ _ _ Prf.hyp0))
theorem actual_original_canonical_block_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (canonicalCoefficients (var 0) ⟶ canonicalCoefficients (block (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (block_canonical _ _ _ _ Prf.hyp0))
theorem actual_block_factor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (length (var 0) ≐ succ (var 1) ⟶ evaluate (block (var 0) (var 1) (var 2) (var 3)) (var 2) ≐ qzero ⟶
      evaluate (block (var 0) (var 1) (var 2) (var 3)) (var 4) ≐ qmul (qsub (var 4) (var 2))
        (evaluate (block (var 0) (var 1) (var 2) (succ (var 3))) (var 4))) :=
  closeUniv 5 (.impI (.impI (block_factor _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_zero_width_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (evaluate (stripStep (var 0) zero (var 1)) (var 2) ≐ qzero) := closeUniv 3 (zero_width_evaluation _ _ _)
theorem actual_block_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((app blockProgramF ![var 0,var 1,var 2,var 3] ≐ block (var 0) (var 1) (var 2) (var 3)) ⋏
      ((run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) ⋏
        fstT (sndT (run (var 0) (var 1) (var 2) (var 3))) ≐ sndT (sndT (run (var 0) (var 1) (var 2) (var 3))))) :=
  closeUniv 4 (.andI (block_program_at _ _ _ _) (.andI (program_at _ _ _ _) (returned_successor_code _ _ _ _)))
theorem actual_returned_block_factor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (length (var 0) ≐ succ (var 1) ⟶ evaluate (fstT (run (var 0) (var 1) (var 2) (var 3))) (var 2) ≐ qzero ⟶
      evaluate (fstT (run (var 0) (var 1) (var 2) (var 3))) (var 4) ≐ qmul (qsub (var 4) (var 2))
        (evaluate (fstT (sndT (run (var 0) (var 1) (var 2) (var 3)))) (var 4))) :=
  closeUniv 5 (.impI (.impI (returned_factor _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRationalFixedWidthStrip
