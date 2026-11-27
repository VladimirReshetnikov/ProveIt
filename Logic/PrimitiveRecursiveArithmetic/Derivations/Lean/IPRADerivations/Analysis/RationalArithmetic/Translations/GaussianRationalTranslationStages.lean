import IPRADerivations.Analysis.Polynomials.Division.GaussianRationalSyntheticDivision

/-!
# Actual successive synthetic quotients for rational translation

Q_0=C and Q_(j+1) is the actual synthetic quotient of Q_j at the fixed
original Gaussian-rational point z, with numerical remaining degree N-j.
No monicity is needed for the length or terminal-constant evaluation law.
Actual monic heads are preserved by QF induction. Input coefficients and
query points may be noncanonical; every constructed quotient is canonical.
All degrees, stages, input lists and points are internal numerical inputs.
This module does not assume a translation or evaluation identity.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalTranslationStages

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (quotient qone canonicalCoefficients)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate qadd qmul)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def remaining (N j : PTm n) : PTm n := monus N j
def stageStep : PTm 5 := quotient (var 1) (var 4) (remaining (var 3) (var 0))
def stageF : PR 4 := recDef (var 0 : PTm 3) stageStep
def stage (C N z j : PTm n) : PTm n := PTm.app stageF ![j,C,N,z]

ipra_subst remaining
ipra_subst stage

theorem stage_zero (C N z : PTm n) : Γ ⊢[PRAAx] stage C N z zero ≐ C := by
  have h := rec_zero_vecCons (Γ := Γ) (var 0 : PTm 3) stageStep ![C,N,z]
  simpa only [stage,stageF,Syn.subst_var,Matrix.cons_val_zero] using h

theorem stage_succ (C N z j : PTm n) : Γ ⊢[PRAAx]
    stage C N z (succ j) ≐ quotient (stage C N z j) z (remaining N j) := by
  have h := rec_succ_vecCons (Γ := Γ) (var 0 : PTm 3) stageStep j ![C,N,z]
  simpa only [stage,stageF,stageStep,GaussianRationalSyntheticDivision.subst_quotient,subst_remaining,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using h

theorem stage_index_congr (C N z : PTm n) {j k : PTm n} (h : Γ ⊢[PRAAx] j ≐ k) : Γ ⊢[PRAAx]
    stage C N z j ≐ stage C N z k := by
  apply congrApp
  intro i
  fin_cases i
  · exact h
  · exact .eqRefl _
  · exact .eqRefl _
  · exact .eqRefl _

theorem remaining_step (N j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    remaining N j ≐ succ (remaining N (succ j)) := by
  have h : Γ ⊢[PRAAx] N ≐ j+succ (monus N (succ j)) := (eq_add_of_le hj).eqTrans (by ipra_ring)
  exact (congrMonus h (.eqRefl _)).eqTrans (add_monus' _ _)

theorem remaining_positive (N j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx] le one (remaining N j) :=
  le_of_eq_add (d := remaining N (succ j)) ((remaining_step N j hj).eqTrans (by ipra_ring))

/-- The actual quotient producer always writes the requested number of
coefficients. This proves the active-stage length without a monicity guard. -/
theorem stage_length (C N z j : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx] length (stage C N z j) ≐ succ (remaining N j) := by
  refine .orE (zero_or_succ j) ?_ ?_
  · have atZero := (congrFst (stage_index_congr C N z (Prf.hyp0 : (j ≐ zero)::Γ ⊢[PRAAx] j ≐ zero))).eqTrans
      ((congrFst (stage_zero C N z)).eqTrans hLen.wk)
    have rem : (j ≐ zero)::Γ ⊢[PRAAx] remaining N j ≐ N :=
      (congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_zero N)
    exact atZero.eqTrans (congrSucc rem).eqSymm
  · have shape : (j ≐ succ (pred j))::Γ ⊢[PRAAx] j ≐ succ (pred j) := Prf.hyp0
    have active : (j ≐ succ (pred j))::Γ ⊢[PRAAx] lt (pred j) N :=
      le_congr shape (.eqRefl _) hj.wk
    exact (congrFst (stage_index_congr C N z shape)).eqTrans
      ((congrFst (stage_succ C N z (pred j))).eqTrans
        ((GaussianRationalSyntheticDivision.quotient_length _ _ _).eqTrans
          ((remaining_step N (pred j) active).eqTrans (congrSucc (congrMonus (.eqRefl _) shape.eqSymm)))))

def headLaw (C N z j : PTm n) : Fm PTm n := le j N ⟶ entry (stage C N z j) zero ≐ qone
ipra_subst headLaw

/-- Genuine QF induction preserves a literal monic head. It does not need
canonical input coefficients or a supplied quotient/head invariant. -/
theorem stage_head (C N z j : PTm n) (hm : Γ ⊢[PRAAx] entry C zero ≐ qone)
    (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx] entry (stage C N z j) zero ≐ qone := by
  have all : Γ ⊢[PRAAx] .all (headLaw (Syn.shift C) (Syn.shift N) (Syn.shift z) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,trivial⟩) [subst_headLaw]
    · exact .impI (((entry_congr (stage_zero C N z) (.eqRefl _)).eqTrans hm).wk)
    · refine .impI ?_
      let I := headLaw (Syn.shift C) (Syn.shift N) (Syn.shift z) (var 0)
      let Δ := le (succ (var 0)) (Syn.shift N) :: I :: Γ.map Fm.shift
      have prev : Δ ⊢[PRAAx] entry (stage (Syn.shift C) (Syn.shift N) (Syn.shift z) (var 0)) zero ≐ qone :=
        .impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)
      have head := Prf.andE₂ (GaussianRationalSyntheticDivision.quotient_monic
        (stage (Syn.shift C) (Syn.shift N) (Syn.shift z) (var 0)) (Syn.shift z)
        (remaining (Syn.shift N) (var 0)) (remaining_positive _ _ Prf.hyp0) prev)
      exact (entry_congr (stage_succ _ _ _ _) (.eqRefl _)).eqTrans head
  have rule : Γ ⊢[PRAAx] headLaw C N z j := by
    simpa only [subst_headLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact .impE rule hj

theorem stage_monic (C N z j : PTm n) (_hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hm : Γ ⊢[PRAAx] entry C zero ≐ qone) (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx]
    entry (stage C N z j) zero ≐ qone := stage_head C N z j hm hj

theorem stage_canonical (C N z j : PTm n) (hj : Γ ⊢[PRAAx] le one j) : Γ ⊢[PRAAx]
    canonicalCoefficients (stage C N z j) := by
  have actual : Γ ⊢[PRAAx] stage C N z j ≐ quotient (stage C N z (pred j)) z (remaining N (pred j)) :=
    (stage_index_congr C N z (RationalIntegerNormalization.positive_form hj)).eqTrans (stage_succ C N z (pred j))
  have p := Prf.eqSubst (Ax := PRAAx) (Γ := Γ) (canonicalCoefficients (var 0) : Fm PTm 1)
    ![quotient (stage C N z (pred j)) z (remaining N (pred j))] ![stage C N z j]
    (fun i => by fin_cases i; exact actual.eqSymm)
    (by simpa using GaussianRationalSyntheticDivision.quotient_canonical (stage C N z (pred j)) z (remaining N (pred j)))
  simpa using p

/-- The true one-step division identity concerns this actual next stage. -/
theorem stage_division (C N z y j : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    evaluate (stage C N z j) y ≐
      qadd (qmul (qsub y z) (evaluate (stage C N z (succ j)) y)) (evaluate (stage C N z j) z) := by
  have h := GaussianRationalSyntheticDivision.division_evaluation (stage C N z j) z y (remaining N j)
    (stage_length C N z j hLen (le_trans (le_succ_self _) hj))
  exact h.eqTrans (GaussianRationalSyntheticDivision.qadd_congr
    (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _)
      (congrAp3 GaussianRationalHorner.hornerF (congrFst (stage_succ C N z j)).eqSymm
        (stage_succ C N z j).eqSymm (.eqRefl _))) (.eqRefl _))

theorem terminal_length (C N z : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    length (stage C N z N) ≐ one :=
  (stage_length C N z N hLen (le_refl _)).eqTrans (congrSucc (monus_self N))

/-- A singleton polynomial's actual canonical evaluation is independent
of its argument even when the stored singleton coefficient is raw. -/
theorem constant_evaluation (C y w : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ one) : Γ ⊢[PRAAx]
    evaluate C y ≐ evaluate C w :=
  (congrAp3 GaussianRationalHorner.hornerF hLen (.eqRefl _) (.eqRefl _)).eqTrans
    ((GaussianRationalSyntheticDivision.first_prefix C y).eqTrans
      ((GaussianRationalSyntheticDivision.first_prefix C w).eqSymm.eqTrans
        (congrAp3 GaussianRationalHorner.hornerF hLen.eqSymm (.eqRefl _) (.eqRefl _))))

theorem terminal_evaluation (C N z y w : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    evaluate (stage C N z N) y ≐ evaluate (stage C N z N) w :=
  constant_evaluation _ _ _ (terminal_length C N z hLen)

theorem terminal_monic_evaluation (C N z y : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hm : Γ ⊢[PRAAx] entry C zero ≐ qone) : Γ ⊢[PRAAx] evaluate (stage C N z N) y ≐ qone :=
  (congrAp3 GaussianRationalHorner.hornerF (terminal_length C N z hLen) (.eqRefl _) (.eqRefl _)).eqTrans
    ((GaussianRationalSyntheticDivision.first_prefix _ _).eqTrans
      ((GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) (stage_head C N z N hm (le_refl _))).eqTrans
        (GaussianRationalSyntheticDivision.qzero_add qone GaussianRationalSyntheticDivision.qone_canonical)))

/-! Actual PR4 metadata exposes the quotient, remaining degree and
computed stored length as literal returned fields. -/
def output (C N z j : PTm n) : PTm n := pairT (stage C N z j) (pairT (remaining N j) (length (stage C N z j)))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
ipra_subst output

theorem program_at (C N z j : PTm n) : Γ ⊢[PRAAx] PTm.app outputF ![C,N,z,j] ≐ output C N z j := by
  simpa [outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![C,N,z,j]

theorem returned_stage (C N z j : PTm n) : Γ ⊢[PRAAx] fstT (PTm.app outputF ![C,N,z,j]) ≐ stage C N z j :=
  (program_at C N z j).fstE
theorem returned_remaining (C N z j : PTm n) : Γ ⊢[PRAAx] fstT (sndT (PTm.app outputF ![C,N,z,j])) ≐ remaining N j :=
  (program_at C N z j).sndE.fstE
theorem returned_length (C N z j : PTm n) : Γ ⊢[PRAAx] sndT (sndT (PTm.app outputF ![C,N,z,j])) ≐ length (stage C N z j) :=
  (program_at C N z j).sndE.sndE

theorem quotient_stages_recursion_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((stage (var 0) (var 1) (var 2) zero ≐ var 0) ⋏
      stage (var 0) (var 1) (var 2) (succ (var 3)) ≐
        quotient (stage (var 0) (var 1) (var 2) (var 3)) (var 2) (remaining (var 1) (var 3))) :=
  closeUniv 4 (.andI (stage_zero _ _ _) (stage_succ _ _ _ _))

theorem quotient_stages_length_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶ le (var 3) (var 1) ⟶
      length (stage (var 0) (var 1) (var 2) (var 3)) ≐ succ (remaining (var 1) (var 3))) :=
  closeUniv 4 (.impI (.impI (stage_length _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem quotient_stages_monic_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶ entry (var 0) zero ≐ qone ⟶ le (var 3) (var 1) ⟶
      (length (stage (var 0) (var 1) (var 2) (var 3)) ≐ succ (remaining (var 1) (var 3)) ⋏
       entry (stage (var 0) (var 1) (var 2) (var 3)) zero ≐ qone)) :=
  closeUniv 4 (.impI (.impI (.impI (.andI (stage_length _ _ _ _ Prf.hyp0.wk.wk Prf.hyp0)
    (stage_monic _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

theorem quotient_stages_canonical_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶ canonicalCoefficients (stage (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (stage_canonical _ _ _ _ Prf.hyp0))

theorem quotient_stages_division_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (length (var 0) ≐ succ (var 1) ⟶ lt (var 4) (var 1) ⟶
      evaluate (stage (var 0) (var 1) (var 2) (var 4)) (var 3) ≐
        qadd (qmul (qsub (var 3) (var 2)) (evaluate (stage (var 0) (var 1) (var 2) (succ (var 4))) (var 3)))
          (evaluate (stage (var 0) (var 1) (var 2) (var 4)) (var 2))) :=
  closeUniv 5 (.impI (.impI (stage_division _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem terminal_constant_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (length (var 0) ≐ succ (var 1) ⟶
      (length (stage (var 0) (var 1) (var 2) (var 1)) ≐ one ⋏
       evaluate (stage (var 0) (var 1) (var 2) (var 1)) (var 3) ≐ evaluate (stage (var 0) (var 1) (var 2) (var 1)) (var 4))) :=
  closeUniv 5 (.impI (.andI (terminal_length _ _ _ Prf.hyp0) (terminal_evaluation _ _ _ _ _ Prf.hyp0)))

theorem terminal_monic_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶ entry (var 0) zero ≐ qone ⟶
      evaluate (stage (var 0) (var 1) (var 2) (var 1)) (var 3) ≐ qone) :=
  closeUniv 4 (.impI (.impI (terminal_monic_evaluation _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem quotient_stages_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((PTm.app outputF ![var 0,var 1,var 2,var 3] ≐ output (var 0) (var 1) (var 2) (var 3)) ⋏
      ((fstT (PTm.app outputF ![var 0,var 1,var 2,var 3]) ≐ stage (var 0) (var 1) (var 2) (var 3)) ⋏
       ((fstT (sndT (PTm.app outputF ![var 0,var 1,var 2,var 3])) ≐ remaining (var 1) (var 3)) ⋏
        (sndT (sndT (PTm.app outputF ![var 0,var 1,var 2,var 3])) ≐ length (stage (var 0) (var 1) (var 2) (var 3)))))) :=
  closeUniv 4 (.andI (program_at _ _ _ _) (.andI (returned_stage _ _ _ _)
    (.andI (returned_remaining _ _ _ _) (returned_length _ _ _ _))))

end LeanProofs.IPRA.Analysis.GaussianRationalTranslationStages
