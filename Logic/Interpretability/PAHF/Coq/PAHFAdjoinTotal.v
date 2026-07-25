(* ===================================================================== *)
(*  PAHFAdjoinTotal.v                                                    *)
(*                                                                       *)
(*  PA-internal totality of one-point Ackermann-code adjunction.         *)
(*                                                                       *)
(*  The only genuinely new arithmetic ingredient is a short beta-prefix  *)
(*  construction which prepends one value to a finite halving trace.      *)
(*  Everything else is assembled from the existing CRT extension and     *)
(*  shifted-tail developments.                                           *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF PAHFProofCalculus PAHFOrdinalCode PAHFOrdinalCodeTotal
  PAHFOrdinalCodeTotalCapacity PAHFOrdinalCodeTotalInduction
  PAHFBetaShiftPrefix PAHFMembershipBound PAHFMembershipTail.

Import ListNotations.
Import PA PA.Term PA.Formula.

(** Slot-indexed specialization of the term-parametric adjoin graph. *)
Definition hfAdjoinGraphAt
    (newCode oldCode elemCode : nat) : formula :=
  hfAdjoinGraphTermAt
    (tVar newCode) (tVar oldCode) (tVar elemCode).

Lemma hfAdjoinGraphAt_unfold : forall newCode oldCode elemCode,
  hfAdjoinGraphAt newCode oldCode elemCode =
    pAll
      (iffForm
        (hfMemAt 0 (S newCode))
        (pOr
          (hfMemAt 0 (S oldCode))
          (pEq (tVar 0) (tVar (S elemCode))))).
Proof.
  intros newCode oldCode elemCode.
  unfold hfAdjoinGraphAt, hfAdjoinGraphTermAt.
  simpl.
  reflexivity.
Qed.

(** Open the two code witnesses of an unsubstituted membership formula. *)
Lemma BProv_Ax_s_hfMemTermAt_elim_opened_code_step :
  forall G target elem setCode,
  BProv Ax_s G (hfMemTermAt elem setCode) ->
  (let bitBody :=
      pAnd (oneAt 0) (betaDiv2BitAt 0 2 1 (elem + 3)) in
   let tail :=
      pAnd (betaDiv2StepsThroughAt 1 0 (elem + 2)) (pEx bitBody) in
   let body := pAnd
      (betaTermAtConstIdx
        (Term.rename (fun n => n + 2) setCode) 1 0 0)
      tail in
   BProv Ax_s
     (body :: map (rename S) (pEx body :: map (rename S) G))
     (rename S (rename S target))) ->
  BProv Ax_s G target.
Proof.
  intros G target elem setCode hmem hopened.
  set (bitBody :=
    pAnd (oneAt 0) (betaDiv2BitAt 0 2 1 (elem + 3))).
  set (tail :=
    pAnd (betaDiv2StepsThroughAt 1 0 (elem + 2)) (pEx bitBody)).
  set (body := pAnd
    (betaTermAtConstIdx
      (Term.rename (fun n => n + 2) setCode) 1 0 0)
    tail).
  assert (hmem' : BProv Ax_s G (pEx (pEx body))).
  {
    unfold hfMemTermAt in hmem.
    unfold body, tail, bitBody.
    replace (elem + 2) with (S (S elem)) by lia.
    replace (elem + 3) with (S (S (S elem))) by lia.
    replace (Term.rename (fun n => n + 2) setCode)
      with (Term.rename S (Term.rename S setCode))
      by (rewrite Term.rename_comp;
          apply Term.rename_ext; intro n; lia).
    exact hmem.
  }
  exact (BProv_two_exE_of_sentences
    Ax_s sentence_ax_s G body target hmem' hopened).
Qed.

Lemma BProv_Ax_s_betaTermTermAt_of_betaTermTermAtConstIdx_eq_term :
  forall G out code step idxTerm idxValue,
  BProv Ax_s G
    (betaTermTermAtConstIdx out code step idxValue) ->
  BProv Ax_s G (pEq (Term.numeral idxValue) idxTerm) ->
  BProv Ax_s G (betaTermTermAt out code step idxTerm).
Proof.
  intros G out code step idxTerm idxValue hbeta hidx.
  set (body := pAnd (eqConstAt 0 idxValue)
    (betaTermTermAt (Term.rename S out)
      (Term.rename S code) (Term.rename S step) (tVar 0))).
  assert (hopened : BProv Ax_s (body :: map (rename S) G)
      (rename S (betaTermTermAt out code step idxTerm))).
  {
    set (C := body :: map (rename S) G).
    assert (hbody : BProv Ax_s C body).
    { apply BProv_ass. unfold C. simpl. left. reflexivity. }
    pose proof (BProv_andE1 Ax_s C _ _ hbody) as hsourceIdx.
    pose proof (BProv_andE2 Ax_s C _ _ hbody) as hraw.
    pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
      hidx S) as hidxRen.
    assert (hidxC : BProv Ax_s C
        (pEq (Term.numeral idxValue) (Term.rename S idxTerm))).
    {
      pose proof (BProv_context_cons Ax_s (map (rename S) G)
        body _ hidxRen) as h.
      simpl in h.
      repeat rewrite Term.rename_numeral in h.
      exact h.
    }
    assert (hidxEq : BProv Ax_s C
        (pEq (tVar 0) (Term.rename S idxTerm))).
    {
      unfold eqConstAt in hsourceIdx.
      exact (BProv_eqTrans Ax_s C _ _ _ hsourceIdx hidxC).
    }
    pose proof (BProv_Ax_s_betaTermTermAt_of_eq_index C
      (Term.rename S out) (Term.rename S code) (Term.rename S step)
      (tVar 0) (Term.rename S idxTerm) hidxEq hraw) as htarget.
    rewrite rename_betaTermTermAt.
    exact htarget.
  }
  unfold betaTermTermAtConstIdx in hbeta.
  unfold body in hopened.
  exact (BProv_exE_of_sentences Ax_s G _
    (betaTermTermAt out code step idxTerm)
    sentence_ax_s hbeta hopened).
Qed.

Lemma BProv_Ax_s_betaDiv2StepsThroughTermTermAt_vars_of_legacy :
  forall G code step last,
  BProv Ax_s G (betaDiv2StepsThroughAt code step last) ->
  BProv Ax_s G
    (betaDiv2StepsThroughTermTermAt
      (tVar code) (tVar step) (tVar last)).
Proof.
  intros G code step last hsteps.
  set (leHyp := leAt 0 (S last)).
  set (body := pImp leHyp
    (betaDiv2StepWitnessTermAt
      (tVar (S code)) (tVar (S step)) (tVar 0))).
  assert (hbody : BProv Ax_s (map (rename S) G) body).
  {
    set (C := leHyp :: map (rename S) G).
    assert (hle : BProv Ax_s C (leAt 0 (S last))).
    { apply BProv_ass. unfold C, leHyp. simpl. left. reflexivity. }
    pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
      hsteps S) as hstepsRen.
    assert (hstepsC : BProv Ax_s C
        (betaDiv2StepsThroughAt (S code) (S step) (S last))).
    {
      pose proof (BProv_context_cons Ax_s (map (rename S) G)
        leHyp _ hstepsRen) as h.
      replace
        (betaDiv2StepsThroughAt (S code) (S step) (S last))
        with (rename S (betaDiv2StepsThroughAt code step last)).
      - exact h.
      - unfold betaDiv2StepsThroughAt, betaDiv2StepWitnessAt,
          betaAtSuccIdx, betaAt, remAt, div2StepAt, boolAt,
          ltAt, leAt, betaModTerm, zeroAt, oneAt, eqConstAt.
        simpl.
        repeat rewrite term_rename_up_succ_rename_succ.
        repeat rewrite Term.rename_comp.
        reflexivity.
    }
    pose proof (BProv_Ax_s_betaDiv2StepsThroughAt_step_of_le
      C (S code) (S step) (S last) 0 hstepsC hle) as hlegacy.
    pose proof (BProv_eqRefl Ax_s C (tVar 0)) as hidx.
    pose proof (BProv_Ax_s_betaDiv2StepWitnessAt_to_termAt_of_idxEq
      C (S code) (S step) 0 (tVar 0) hlegacy hidx) as hterm.
    unfold body.
    exact (BProv_impI Ax_s (map (rename S) G) leHyp _ hterm).
  }
  pose proof (BProv_allI_of_sentences Ax_s G body
    sentence_ax_s hbody) as hall.
  replace
    (betaDiv2StepsThroughTermTermAt
      (tVar code) (tVar step) (tVar last))
    with (pAll body).
  - exact hall.
  - unfold betaDiv2StepsThroughTermTermAt, body, leHyp,
      leTermAt.
    simpl.
    reflexivity.
Qed.

Lemma rename_S_hfAdjoinGraphAt : forall newCode oldCode elemCode,
  rename S (hfAdjoinGraphAt newCode oldCode elemCode) =
    hfAdjoinGraphAt (S newCode) (S oldCode) (S elemCode).
Proof.
  intros newCode oldCode elemCode.
  unfold hfAdjoinGraphAt.
  rewrite rename_hfAdjoinGraphTermAt.
  simpl.
  reflexivity.
Qed.

Lemma BProv_hfAdjoinGraphAt_point :
  forall B G query newCode oldCode elemCode,
  BProv B G (hfAdjoinGraphAt newCode oldCode elemCode) ->
  BProv B G
    (iffForm
      (hfMemAt query newCode)
      (pOr
        (hfMemAt query oldCode)
        (pEq (tVar query) (tVar elemCode)))).
Proof.
  intros B G query newCode oldCode elemCode hgraph.
  rewrite hfAdjoinGraphAt_unfold in hgraph.
  pose proof (BProv_allE B G _ (tVar query) hgraph) as hpoint.
  change (BProv B G
    (iffForm
      (subst (instTerm (tVar query)) (hfMemAt 0 (S newCode)))
      (pOr
        (subst (instTerm (tVar query)) (hfMemAt 0 (S oldCode)))
        (pEq
          (Term.subst (instTerm (tVar query)) (tVar 0))
          (Term.subst (instTerm (tVar query))
            (tVar (S elemCode))))))) in hpoint.
  rewrite !subst_instTerm_var_hfMemAt_zero_succ in hpoint.
  simpl in hpoint.
  exact hpoint.
Qed.

Lemma BProv_hfAdjoinGraphTermAt_point :
  forall B G query newCode oldCode elemCode,
  BProv B G (hfAdjoinGraphTermAt newCode oldCode elemCode) ->
  BProv B G
    (iffForm
      (hfMemTermAt query newCode)
      (pOr
        (hfMemTermAt query oldCode)
        (pEq (tVar query) elemCode))).
Proof.
  intros B G query newCode oldCode elemCode hgraph.
  unfold hfAdjoinGraphTermAt in hgraph.
  pose proof (BProv_allE B G _ (tVar query) hgraph) as hpoint.
  change (BProv B G
    (iffForm
      (subst (instTerm (tVar query))
        (hfMemTermAt 0 (Term.rename S newCode)))
      (pOr
        (subst (instTerm (tVar query))
          (hfMemTermAt 0 (Term.rename S oldCode)))
        (pEq
          (Term.subst (instTerm (tVar query)) (tVar 0))
          (Term.subst (instTerm (tVar query))
            (Term.rename S elemCode)))))) in hpoint.
  rewrite !subst_instTerm_var_hfMemTermAt_zero_rename_succ in hpoint.
  repeat rewrite term_subst_instTerm_rename_succ in hpoint.
  simpl in hpoint.
  exact hpoint.
Qed.

Lemma substSuccVar_hfMemAt_zero_succ : forall set,
  subst substSuccVar (hfMemAt 0 (S set)) =
    subst (instTerm (tSucc (tVar 0))) (hfMemAt 0 (S (S set))).
Proof.
  intro set.
  unfold hfMemAt, hfMemTermAt, betaTermAtConstIdx, betaTermAt,
    remTermAt, ltTermAt, betaAt, remAt, ltAt, leAt,
    betaDiv2StepsThroughAt, betaDiv2StepWitnessAt,
    betaDiv2BitAt, betaAtSuccIdx, div2StepAt, boolAt,
    zeroAt, oneAt, eqConstAt, betaModTerm.
  simpl.
  repeat rewrite Term.subst_rename_succ_up.
  repeat rewrite term_subst_instTerm_rename_succ.
  reflexivity.
Qed.

(** If a queried slot is zero and the set code is explicitly doubled,
    membership is contradictory.  This is the open-term counterpart of the
    closed trace fact already in [PAHF.v]. *)
Lemma BProv_Ax_s_hfMemAt_bot_of_eqConst_zero_elem_low_double :
  forall G elem low lowHalf,
  BProv Ax_s G (eqConstAt elem 0) ->
  BProv Ax_s G (doubleEqAt low lowHalf) ->
  BProv Ax_s G (hfMemAt elem low) ->
  BProv Ax_s G pBot.
Proof.
  intros G elem low lowHalf helem hdouble hmem.
  set (modEq := eqConstAt 0 2).
  pose proof (BProv_exists_eqConstAt Ax_s G 2) as hex.
  apply (BProv_exE_of_sentences Ax_s G modEq pBot
    sentence_ax_s hex).
  set (C := modEq :: map (rename S) G).
  assert (hmod : BProv Ax_s C (eqConstAt 0 2)).
  { apply BProv_ass. unfold C, modEq. simpl. left. reflexivity. }
  pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
    helem S) as helemRen.
  pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
    hdouble S) as hdoubleRen.
  pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
    hmem S) as hmemRen.
  assert (helemC : BProv Ax_s C (eqConstAt (S elem) 0)).
  {
    exact (BProv_context_cons Ax_s (map (rename S) G)
      modEq _ helemRen).
  }
  assert (hdoubleC : BProv Ax_s C
      (doubleEqAt (S low) (S lowHalf))).
  {
    exact (BProv_context_cons Ax_s (map (rename S) G)
      modEq _ hdoubleRen).
  }
  assert (hmemC : BProv Ax_s C (hfMemAt (S elem) (S low))).
  {
    pose proof (BProv_context_cons Ax_s (map (rename S) G)
      modEq _ hmemRen) as h.
    rewrite rename_hfMemAt in h.
    exact h.
  }
  pose proof (BProv_Ax_s_dvdAt_of_doubleEqAt_two
    C 0 (S low) (S lowHalf) hmod hdoubleC) as hdvd.
  exact (BProv_Ax_s_hfMemAt_bot_of_eqConst_zero_elem_dvd_set
    C (S elem) (S low) 0 helemC hmod hdvd hmemC).
Qed.

Lemma BProv_Ax_s_div2StepAt_of_oddDoubleEqAt_bit_one :
  forall G value half bit,
  BProv Ax_s G (oddDoubleEqAt value half) ->
  BProv Ax_s G (eqConstAt bit 1) ->
  BProv Ax_s G (div2StepAt value half bit).
Proof.
  intros G value half bit hodd hbit.
  set (d := tAdd (tVar half) (tVar half)).
  assert (hbool : BProv Ax_s G (boolAt bit)).
  {
    unfold boolAt, zeroAt, oneAt.
    exact (BProv_orI2 Ax_s G (eqConstAt bit 0)
      (eqConstAt bit 1) hbit).
  }
  assert (hvalue : BProv Ax_s G (pEq (tVar value) (tSucc d))).
  { unfold oddDoubleEqAt, d in *. exact hodd. }
  assert (hbit' : BProv Ax_s G (pEq (tVar bit) (tSucc tZero))).
  { unfold eqConstAt in hbit. simpl in hbit. exact hbit. }
  pose proof (BProv_eq_congr_add_right Ax_s G d
    (tVar bit) (tSucc tZero) hbit') as hreplace.
  pose proof (BProv_Ax_s_addSucc_terms G d tZero) as haddSucc.
  pose proof (BProv_eq_congr_succ Ax_s G _ _
    (BProv_Ax_s_addZero_term G d)) as haddZero.
  pose proof (BProv_eqTrans Ax_s G _ _ _ hreplace
    (BProv_eqTrans Ax_s G _ _ _ haddSucc haddZero)) as hsum.
  pose proof (BProv_eqTrans Ax_s G _ _ _ hvalue
    (BProv_eqSym Ax_s G _ _ hsum)) as heq.
  unfold div2StepAt, d.
  exact (BProv_andI Ax_s G _ _ hbool heq).
Qed.

(* Compatibility aliases: the canonical definitions now live in [PA.Formula]. *)
Definition betaUnshiftPrefixTermAt :=
  PA.Formula.betaUnshiftPrefixTermAt.

Definition betaPrependPrefixTermAt :=
  PA.Formula.betaPrependPrefixTermAt.

Definition betaPrependPrefixCodeExistsTermAt :=
  PA.Formula.betaPrependPrefixCodeExistsTermAt.

Definition betaPrependPrefixCodeExistsTermAtBody :=
  PA.Formula.betaPrependPrefixCodeExistsTermAtBody.

Definition betaPrependExistsTermAt :=
  PA.Formula.betaPrependExistsTermAt.

Definition betaPrependExistsTermAtBody :=
  PA.Formula.betaPrependExistsTermAtBody.

Definition betaPrependCodingStepTermAt :=
  PA.Formula.betaPrependCodingStepTermAt.

Definition betaPrependCodingStepExistsTermAt :=
  PA.Formula.betaPrependCodingStepExistsTermAt.

Definition betaPrependCodingStepExistsTermAtBody :=
  PA.Formula.betaPrependCodingStepExistsTermAtBody.

Lemma subst_betaUnshiftPrefixTermAt :
  forall sigma sourceCode sourceStep targetCode targetStep bound,
  subst sigma
      (betaUnshiftPrefixTermAt
        sourceCode sourceStep targetCode targetStep bound) =
    betaUnshiftPrefixTermAt
      (Term.subst sigma sourceCode)
      (Term.subst sigma sourceStep)
      (Term.subst sigma targetCode)
      (Term.subst sigma targetStep)
      (Term.subst sigma bound).
Proof.
  intros sigma sourceCode sourceStep targetCode targetStep bound.
  exact (PA.Formula.subst_betaUnshiftPrefixTermAt
    sigma sourceCode sourceStep targetCode targetStep bound).
Qed.

Lemma rename_betaUnshiftPrefixTermAt :
  forall r sourceCode sourceStep targetCode targetStep bound,
  rename r
      (betaUnshiftPrefixTermAt
        sourceCode sourceStep targetCode targetStep bound) =
    betaUnshiftPrefixTermAt
      (Term.rename r sourceCode)
      (Term.rename r sourceStep)
      (Term.rename r targetCode)
      (Term.rename r targetStep)
      (Term.rename r bound).
Proof.
  intros r sourceCode sourceStep targetCode targetStep bound.
  exact (PA.Formula.rename_betaUnshiftPrefixTermAt
    r sourceCode sourceStep targetCode targetStep bound).
Qed.

Lemma subst_betaPrependPrefixTermAt :
  forall sigma sourceCode sourceStep head targetCode targetStep bound,
  subst sigma
      (betaPrependPrefixTermAt
        sourceCode sourceStep head targetCode targetStep bound) =
    betaPrependPrefixTermAt
      (Term.subst sigma sourceCode)
      (Term.subst sigma sourceStep)
      (Term.subst sigma head)
      (Term.subst sigma targetCode)
      (Term.subst sigma targetStep)
      (Term.subst sigma bound).
Proof.
  intros sigma sourceCode sourceStep head targetCode targetStep bound.
  exact (PA.Formula.subst_betaPrependPrefixTermAt
    sigma sourceCode sourceStep head targetCode targetStep bound).
Qed.

Lemma rename_betaPrependPrefixTermAt :
  forall r sourceCode sourceStep head targetCode targetStep bound,
  rename r
      (betaPrependPrefixTermAt
        sourceCode sourceStep head targetCode targetStep bound) =
    betaPrependPrefixTermAt
      (Term.rename r sourceCode)
      (Term.rename r sourceStep)
      (Term.rename r head)
      (Term.rename r targetCode)
      (Term.rename r targetStep)
      (Term.rename r bound).
Proof.
  intros r sourceCode sourceStep head targetCode targetStep bound.
  exact (PA.Formula.rename_betaPrependPrefixTermAt
    r sourceCode sourceStep head targetCode targetStep bound).
Qed.

Lemma subst_betaPrependPrefixCodeExistsTermAt :
  forall sigma sourceCode sourceStep head targetStep bound,
  subst sigma
      (betaPrependPrefixCodeExistsTermAt
        sourceCode sourceStep head targetStep bound) =
    betaPrependPrefixCodeExistsTermAt
      (Term.subst sigma sourceCode)
      (Term.subst sigma sourceStep)
      (Term.subst sigma head)
      (Term.subst sigma targetStep)
      (Term.subst sigma bound).
Proof.
  intros sigma sourceCode sourceStep head targetStep bound.
  exact (PA.Formula.subst_betaPrependPrefixCodeExistsTermAt
    sigma sourceCode sourceStep head targetStep bound).
Qed.

Lemma rename_betaPrependPrefixCodeExistsTermAt :
  forall r sourceCode sourceStep head targetStep bound,
  rename r
      (betaPrependPrefixCodeExistsTermAt
        sourceCode sourceStep head targetStep bound) =
    betaPrependPrefixCodeExistsTermAt
      (Term.rename r sourceCode)
      (Term.rename r sourceStep)
      (Term.rename r head)
      (Term.rename r targetStep)
      (Term.rename r bound).
Proof.
  intros r sourceCode sourceStep head targetStep bound.
  exact (PA.Formula.rename_betaPrependPrefixCodeExistsTermAt
    r sourceCode sourceStep head targetStep bound).
Qed.

Lemma subst_betaPrependExistsTermAt :
  forall sigma sourceCode sourceStep head bound,
  subst sigma
      (betaPrependExistsTermAt sourceCode sourceStep head bound) =
    betaPrependExistsTermAt
      (Term.subst sigma sourceCode)
      (Term.subst sigma sourceStep)
      (Term.subst sigma head)
      (Term.subst sigma bound).
Proof.
  intros sigma sourceCode sourceStep head bound.
  exact (PA.Formula.subst_betaPrependExistsTermAt
    sigma sourceCode sourceStep head bound).
Qed.

Lemma rename_betaPrependExistsTermAt :
  forall r sourceCode sourceStep head bound,
  rename r
      (betaPrependExistsTermAt sourceCode sourceStep head bound) =
    betaPrependExistsTermAt
      (Term.rename r sourceCode)
      (Term.rename r sourceStep)
      (Term.rename r head)
      (Term.rename r bound).
Proof.
  intros r sourceCode sourceStep head bound.
  exact (PA.Formula.rename_betaPrependExistsTermAt
    r sourceCode sourceStep head bound).
Qed.

Lemma subst_betaPrependCodingStepTermAt :
  forall sigma bound sourceCode head step,
  subst sigma
      (betaPrependCodingStepTermAt bound sourceCode head step) =
    betaPrependCodingStepTermAt
      (Term.subst sigma bound)
      (Term.subst sigma sourceCode)
      (Term.subst sigma head)
      (Term.subst sigma step).
Proof.
  intros sigma bound sourceCode head step.
  exact (PA.Formula.subst_betaPrependCodingStepTermAt
    sigma bound sourceCode head step).
Qed.

Lemma rename_betaPrependCodingStepTermAt :
  forall r bound sourceCode head step,
  rename r
      (betaPrependCodingStepTermAt bound sourceCode head step) =
    betaPrependCodingStepTermAt
      (Term.rename r bound)
      (Term.rename r sourceCode)
      (Term.rename r head)
      (Term.rename r step).
Proof.
  intros r bound sourceCode head step.
  exact (PA.Formula.rename_betaPrependCodingStepTermAt
    r bound sourceCode head step).
Qed.

Lemma subst_betaPrependCodingStepExistsTermAt :
  forall sigma bound sourceCode head,
  subst sigma
      (betaPrependCodingStepExistsTermAt bound sourceCode head) =
    betaPrependCodingStepExistsTermAt
      (Term.subst sigma bound)
      (Term.subst sigma sourceCode)
      (Term.subst sigma head).
Proof.
  intros sigma bound sourceCode head.
  exact (PA.Formula.subst_betaPrependCodingStepExistsTermAt
    sigma bound sourceCode head).
Qed.

Lemma rename_betaPrependCodingStepExistsTermAt :
  forall r bound sourceCode head,
  rename r
      (betaPrependCodingStepExistsTermAt bound sourceCode head) =
    betaPrependCodingStepExistsTermAt
      (Term.rename r bound)
      (Term.rename r sourceCode)
      (Term.rename r head).
Proof.
  intros r bound sourceCode head.
  exact (PA.Formula.rename_betaPrependCodingStepExistsTermAt
    r bound sourceCode head).
Qed.

Lemma BProv_Ax_s_betaUnshiftPrefixTermAt_zero :
  forall G sourceCode sourceStep targetCode targetStep,
  BProv Ax_s G
    (betaUnshiftPrefixTermAt
      sourceCode sourceStep targetCode targetStep tZero).
Proof.
  intros G sourceCode sourceStep targetCode targetStep.
  set (antecedent := ltTermAt (tVar 0) tZero).
  set (innerBody := pImp
    (betaTermTermAt (tVar 0)
      (Term.rename (fun n => n + 2) sourceCode)
      (Term.rename (fun n => n + 2) sourceStep)
      (tVar 1))
    (betaTermTermAt (tVar 0)
      (Term.rename (fun n => n + 2) targetCode)
      (Term.rename (fun n => n + 2) targetStep)
      (tSucc (tVar 1)))).
  set (body := pImp antecedent (pAll innerBody)).
  set (C := antecedent :: map (rename S) G).
  assert (hlt : BProv Ax_s C (ltTermAt (tVar 0) tZero)).
  { apply BProv_ass. unfold C, antecedent. simpl. left. reflexivity. }
  pose proof (BProv_Ax_s_leTermAt_zero_left C (tVar 0)) as hle.
  pose proof (BProv_Ax_s_ltTermAt_leTermAt_bot
    C (tVar 0) tZero hlt hle) as hbot.
  assert (hinner : BProv Ax_s C (pAll innerBody)).
  { exact (BProv_botE Ax_s C _ hbot). }
  assert (himp : BProv Ax_s (map (rename S) G) body).
  {
    unfold C in hinner.
    exact (BProv_impI Ax_s (map (rename S) G)
      antecedent (pAll innerBody) hinner).
  }
  pose proof (BProv_allI_of_sentences Ax_s G body
    sentence_ax_s himp) as hall.
  unfold betaUnshiftPrefixTermAt, body, antecedent, innerBody in *.
  simpl in hall |- *.
  exact hall.
Qed.

Lemma BProv_Ax_s_betaTermTermAt_self_zero_of_succ_le_step :
  forall G out step,
  BProv Ax_s G (leTermAt (tSucc out) step) ->
  BProv Ax_s G (betaTermTermAt out out step tZero).
Proof.
  intros G out step hlarge.
  set (modulus := betaModTermTerm step tZero).
  pose proof (BProv_Ax_s_leTermAt_step_betaModTermTerm
    G step tZero) as hstepMod.
  assert (hlt : BProv Ax_s G (ltTermAt out modulus)).
  {
    apply (BProv_Ax_s_ltTermAt_of_succ_leTermAt G out modulus).
    exact (BProv_Ax_s_leTermAt_trans G (tSucc out) step modulus
      hlarge hstepMod).
  }
  pose proof (BProv_Ax_s_zero_mul_term G modulus) as hzeroMul.
  pose proof (BProv_eq_congr_add_left Ax_s G
    (tMul tZero modulus) tZero out hzeroMul) as haddCong.
  pose proof (BProv_Ax_s_zero_add_term G out) as hzeroAdd.
  pose proof (BProv_eqSym Ax_s G _ _
    (BProv_eqTrans Ax_s G _ _ _ haddCong hzeroAdd)) as hdecomp.
  pose proof (BProv_Ax_s_remTermTermAt_of_eq_add_mul_terms
    G out out modulus tZero hlt hdecomp) as hrem.
  exact (BProv_Ax_s_betaTermTermAt_of_rem
    G out out step tZero modulus
    (BProv_eqRefl Ax_s G modulus) hrem).
Qed.

Lemma BProv_Ax_s_betaPrependPrefixTermAt_of_components :
  forall G sourceCode sourceStep head targetCode targetStep bound,
  BProv Ax_s G (betaTermTermAt head targetCode targetStep tZero) ->
  BProv Ax_s G
    (betaUnshiftPrefixTermAt
      sourceCode sourceStep targetCode targetStep bound) ->
  BProv Ax_s G
    (betaPrependPrefixTermAt
      sourceCode sourceStep head targetCode targetStep bound).
Proof.
  intros G sourceCode sourceStep head targetCode targetStep bound
    hhead hunshift.
  unfold betaPrependPrefixTermAt.
  exact (BProv_andI Ax_s G _ _ hhead hunshift).
Qed.

Lemma BProv_Ax_s_betaPrependPrefixCodeExistsTermAt_of_term :
  forall G sourceCode sourceStep head targetCode targetStep bound,
  BProv Ax_s G
    (betaPrependPrefixTermAt
      sourceCode sourceStep head targetCode targetStep bound) ->
  BProv Ax_s G
    (betaPrependPrefixCodeExistsTermAt
      sourceCode sourceStep head targetStep bound).
Proof.
  intros G sourceCode sourceStep head targetCode targetStep bound hprefix.
  unfold betaPrependPrefixCodeExistsTermAt.
  apply (BProv_exI Ax_s G _ targetCode).
  rewrite subst_betaPrependPrefixTermAt.
  simpl.
  repeat rewrite term_subst_instTerm_rename_succ.
  exact hprefix.
Qed.

Lemma BProv_Ax_s_betaPrependPrefixCodeExistsTermAt_elim_opened :
  forall G sourceCode sourceStep head targetStep bound target,
  BProv Ax_s
    (betaPrependPrefixCodeExistsTermAtBody
        sourceCode sourceStep head targetStep bound ::
      map (rename S) G)
    (rename S target) ->
  BProv Ax_s G
    (betaPrependPrefixCodeExistsTermAt
      sourceCode sourceStep head targetStep bound) ->
  BProv Ax_s G target.
Proof.
  intros G sourceCode sourceStep head targetStep bound target
    hopened hex.
  unfold betaPrependPrefixCodeExistsTermAt in hex.
  unfold betaPrependPrefixCodeExistsTermAtBody in hopened.
  exact (BProv_exE_of_sentences Ax_s G _ target
    sentence_ax_s hex hopened).
Qed.

Lemma BProv_Ax_s_betaPrependPrefixCodeExistsTermAt_zero :
  forall G sourceCode sourceStep head targetStep,
  BProv Ax_s G (leTermAt (tSucc head) targetStep) ->
  BProv Ax_s G
    (betaPrependPrefixCodeExistsTermAt
      sourceCode sourceStep head targetStep tZero).
Proof.
  intros G sourceCode sourceStep head targetStep hlarge.
  apply (BProv_Ax_s_betaPrependPrefixCodeExistsTermAt_of_term
    G sourceCode sourceStep head head targetStep tZero).
  apply BProv_Ax_s_betaPrependPrefixTermAt_of_components.
  - exact (BProv_Ax_s_betaTermTermAt_self_zero_of_succ_le_step
      G head targetStep hlarge).
  - apply BProv_Ax_s_betaUnshiftPrefixTermAt_zero.
Qed.

Lemma BProv_Ax_s_betaPrependCodingStepTermAt_of_positiveCommon :
  forall G bound sourceCode head multiple,
  BProv Ax_s G
    (positiveCommonMultipleThroughTermAt bound multiple) ->
  BProv Ax_s G
    (betaPrependCodingStepTermAt bound sourceCode head
      (tMul multiple (tSucc (tAdd sourceCode head)))).
Proof.
  intros G bound sourceCode head multiple hpositive.
  set (sum := tAdd sourceCode head).
  set (step := tMul multiple (tSucc sum)).
  unfold positiveCommonMultipleThroughTermAt in hpositive.
  pose proof (BProv_andE1 Ax_s G _ _ hpositive) as hpos.
  pose proof (BProv_andE2 Ax_s G _ _ hpositive) as hcommon.
  pose proof (BProv_Ax_s_commonMultipleThroughTermAt_mul_right
    G bound multiple (tSucc sum) hcommon) as hcommonScaled.
  pose proof (BProv_Ax_s_leTermAt_succ_mul_succ_of_pos
    G multiple sum hpos) as hsumLarge.
  assert (hsourceLeSum : BProv Ax_s G (leTermAt sourceCode sum)).
  {
    apply (BProv_Ax_s_leTermAt_of_eq_add_right_terms
      G sourceCode sum head).
    exact (BProv_eqRefl Ax_s G sum).
  }
  pose proof (BProv_Ax_s_leTermAt_succ_succ
    G sourceCode sum hsourceLeSum) as hsourceSucc.
  pose proof (BProv_Ax_s_leTermAt_trans G
    (tSucc sourceCode) (tSucc sum) step hsourceSucc hsumLarge)
    as hsourceLarge.
  pose proof (BProv_Ax_s_add_comm_terms G sourceCode head) as hcomm.
  assert (hheadLeSum : BProv Ax_s G (leTermAt head sum)).
  {
    apply (BProv_Ax_s_leTermAt_of_eq_add_right_terms
      G head sum sourceCode).
    unfold sum.
    exact hcomm.
  }
  pose proof (BProv_Ax_s_leTermAt_succ_succ
    G head sum hheadLeSum) as hheadSucc.
  pose proof (BProv_Ax_s_leTermAt_trans G
    (tSucc head) (tSucc sum) step hheadSucc hsumLarge)
    as hheadLarge.
  unfold betaPrependCodingStepTermAt, step, sum.
  exact (BProv_andI Ax_s G _ _ hcommonScaled
    (BProv_andI Ax_s G _ _ hsourceLarge hheadLarge)).
Qed.

Lemma BProv_Ax_s_betaPrependCodingStepExistsTermAt_of_term :
  forall G bound sourceCode head step,
  BProv Ax_s G
    (betaPrependCodingStepTermAt bound sourceCode head step) ->
  BProv Ax_s G
    (betaPrependCodingStepExistsTermAt bound sourceCode head).
Proof.
  intros G bound sourceCode head step hstep.
  apply (BProv_exI Ax_s G _ step).
  rewrite subst_betaPrependCodingStepTermAt.
  simpl.
  repeat rewrite term_subst_instTerm_rename_succ.
  exact hstep.
Qed.

Lemma BProv_Ax_s_betaPrependCodingStepExistsTermAt_elim_opened :
  forall G bound sourceCode head target,
  BProv Ax_s
    (betaPrependCodingStepExistsTermAtBody bound sourceCode head ::
      map (rename S) G)
    (rename S target) ->
  BProv Ax_s G
    (betaPrependCodingStepExistsTermAt bound sourceCode head) ->
  BProv Ax_s G target.
Proof.
  intros G bound sourceCode head target hopened hex.
  exact (BProv_exE_of_sentences Ax_s G _ target
    sentence_ax_s hex hopened).
Qed.

Lemma BProv_Ax_s_betaPrependCodingStepExistsTermAt :
  forall G bound sourceCode head,
  BProv Ax_s G
    (betaPrependCodingStepExistsTermAt bound sourceCode head).
Proof.
  intros G bound sourceCode head.
  pose proof (BProv_Ax_s_all_positiveCommonMultipleExistsTermAt G)
    as hall.
  pose proof (BProv_allE Ax_s G _ bound hall) as hpositiveRaw.
  rewrite subst_positiveCommonMultipleExistsTermAt in hpositiveRaw.
  simpl in hpositiveRaw.
  set (goal := betaPrependCodingStepExistsTermAt
    bound sourceCode head).
  apply (BProv_Ax_s_positiveCommonMultipleExistsTermAt_elim_opened
    G bound goal); [|exact hpositiveRaw].
  set (positiveBody := positiveCommonMultipleExistsTermAtBody bound).
  set (D := positiveBody :: map (rename S) G).
  set (bound1 := Term.rename S bound).
  set (sourceCode1 := Term.rename S sourceCode).
  set (head1 := Term.rename S head).
  assert (hpositive : BProv Ax_s D
      (positiveCommonMultipleThroughTermAt bound1 (tVar 0))).
  {
    apply BProv_ass.
    unfold D, positiveBody, positiveCommonMultipleExistsTermAtBody,
      bound1.
    simpl. left. reflexivity.
  }
  pose proof
    (BProv_Ax_s_betaPrependCodingStepTermAt_of_positiveCommon
      D bound1 sourceCode1 head1 (tVar 0) hpositive) as hstep.
  pose proof
    (BProv_Ax_s_betaPrependCodingStepExistsTermAt_of_term
      D bound1 sourceCode1 head1
      (tMul (tVar 0) (tSucc (tAdd sourceCode1 head1))) hstep)
    as hex.
  unfold goal.
  rewrite rename_betaPrependCodingStepExistsTermAt.
  exact hex.
Qed.

Lemma BProv_Ax_s_betaTermTermAt_head_of_betaPrependPrefixTermAt :
  forall G sourceCode sourceStep head targetCode targetStep bound,
  BProv Ax_s G
    (betaPrependPrefixTermAt
      sourceCode sourceStep head targetCode targetStep bound) ->
  BProv Ax_s G (betaTermTermAt head targetCode targetStep tZero).
Proof.
  intros G sourceCode sourceStep head targetCode targetStep bound hprefix.
  unfold betaPrependPrefixTermAt in hprefix.
  exact (BProv_andE1 Ax_s G _ _ hprefix).
Qed.

Lemma BProv_Ax_s_betaUnshiftPrefixTermAt_of_betaPrependPrefixTermAt :
  forall G sourceCode sourceStep head targetCode targetStep bound,
  BProv Ax_s G
    (betaPrependPrefixTermAt
      sourceCode sourceStep head targetCode targetStep bound) ->
  BProv Ax_s G
    (betaUnshiftPrefixTermAt
      sourceCode sourceStep targetCode targetStep bound).
Proof.
  intros G sourceCode sourceStep head targetCode targetStep bound hprefix.
  unfold betaPrependPrefixTermAt in hprefix.
  exact (BProv_andE2 Ax_s G _ _ hprefix).
Qed.

Lemma BProv_Ax_s_betaUnshiftPrefixTermAt_entry_of_ltTerm :
  forall G sourceCode sourceStep targetCode targetStep bound idx out,
  BProv Ax_s G
    (betaUnshiftPrefixTermAt
      sourceCode sourceStep targetCode targetStep bound) ->
  BProv Ax_s G (ltTermAt idx bound) ->
  BProv Ax_s G (betaTermTermAt out sourceCode sourceStep idx) ->
  BProv Ax_s G
    (betaTermTermAt out targetCode targetStep (tSucc idx)).
Proof.
  intros G sourceCode sourceStep targetCode targetStep bound idx out
    hprefix hlt hsource.
  pose proof (BProv_allE Ax_s G _ idx hprefix) as hidx.
  cbn [subst] in hidx.
  rewrite subst_ltTermAt in hidx.
  rewrite !subst_betaTermTermAt in hidx.
  simpl in hidx.
  repeat rewrite term_subst_upSubst_instTerm_rename_add_two in hidx.
  repeat rewrite term_subst_instTerm_rename_succ in hidx.
  pose proof (BProv_mp Ax_s G _ _ hidx hlt) as hall.
  pose proof (BProv_allE Ax_s G _ out hall) as hout.
  cbn [subst] in hout.
  rewrite !subst_betaTermTermAt in hout.
  simpl in hout.
  repeat rewrite term_subst_instTerm_rename_succ in hout.
  exact (BProv_mp Ax_s G _ _ hout hsource).
Qed.

Lemma BProv_Ax_s_betaUnshiftPrefixTermAt_succ_entry_of_extension :
  forall G sourceCode sourceStep currentCode targetStep bound sourceOut
    extendedCode idx out,
  BProv Ax_s G
    (betaUnshiftPrefixTermAt
      sourceCode sourceStep currentCode targetStep bound) ->
  BProv Ax_s G
    (betaCodeExtensionTermAt currentCode targetStep
      (tSucc bound) sourceOut extendedCode) ->
  BProv Ax_s G
    (betaTermTermAt sourceOut sourceCode sourceStep bound) ->
  BProv Ax_s G (ltTermAt idx (tSucc bound)) ->
  BProv Ax_s G (betaTermTermAt out sourceCode sourceStep idx) ->
  BProv Ax_s G
    (betaTermTermAt out extendedCode targetStep (tSucc idx)).
Proof.
  intros G sourceCode sourceStep currentCode targetStep bound sourceOut
    extendedCode idx out hprefix hext hsource hltSucc hsourceAtIdx.
  pose proof (BProv_Ax_s_ltTermAt_succ_right_cases
    G idx bound hltSucc) as hcases.
  assert (hltBranch : BProv Ax_s (ltTermAt idx bound :: G)
      (betaTermTermAt out extendedCode targetStep (tSucc idx))).
  {
    set (C := ltTermAt idx bound :: G).
    assert (hlt : BProv Ax_s C (ltTermAt idx bound)).
    { apply BProv_ass. unfold C. simpl. left. reflexivity. }
    pose proof (BProv_context_cons Ax_s G (ltTermAt idx bound) _
      hprefix) as hprefixC.
    pose proof (BProv_context_cons Ax_s G (ltTermAt idx bound) _
      hsourceAtIdx) as hsourceAtIdxC.
    pose proof
      (BProv_Ax_s_betaUnshiftPrefixTermAt_entry_of_ltTerm
        C sourceCode sourceStep currentCode targetStep bound idx out
        hprefixC hlt hsourceAtIdxC) as hcurrent.
    pose proof (BProv_context_cons Ax_s G (ltTermAt idx bound) _
      hext) as hextC.
    pose proof
      (BProv_Ax_s_betaPrefixAgreementTermAt_of_betaCodeExtensionTermAt
        C currentCode targetStep (tSucc bound) sourceOut extendedCode
        hextC) as hagreement.
    pose proof (BProv_Ax_s_ltTermAt_succ_succ C idx bound hlt)
      as hsuccLt.
    exact (BProv_Ax_s_betaPrefixAgreementTermAt_entry_of_ltTerm
      C currentCode extendedCode targetStep (tSucc bound)
      (tSucc idx) out hagreement hsuccLt hcurrent).
  }
  assert (heqBranch : BProv Ax_s (pEq idx bound :: G)
      (betaTermTermAt out extendedCode targetStep (tSucc idx))).
  {
    set (C := pEq idx bound :: G).
    assert (heq : BProv Ax_s C (pEq idx bound)).
    { apply BProv_ass. unfold C. simpl. left. reflexivity. }
    pose proof (BProv_context_cons Ax_s G (pEq idx bound) _
      hsourceAtIdx) as hsourceAtIdxC.
    pose proof (BProv_Ax_s_betaTermTermAt_of_eq_index
      C out sourceCode sourceStep idx bound heq hsourceAtIdxC)
      as hsourceAtBound.
    pose proof (BProv_context_cons Ax_s G (pEq idx bound) _
      hsource) as hsourceC.
    pose proof
      (BProv_Ax_s_eq_of_betaTermTermAt_betaTermTermAt_same_index
        C out sourceOut sourceCode sourceStep bound
        hsourceAtBound hsourceC) as houtEq.
    pose proof (BProv_context_cons Ax_s G (pEq idx bound) _
      hext) as hextC.
    pose proof
      (BProv_Ax_s_betaTermTermAt_of_betaCodeExtensionTermAt
        C currentCode targetStep (tSucc bound) sourceOut extendedCode
        hextC) as htarget.
    exact (BProv_betaTermTermAt_congr Ax_s C
      sourceOut out extendedCode extendedCode targetStep targetStep
      (tSucc bound) (tSucc idx)
      houtEq (BProv_eqRefl Ax_s C extendedCode)
      (BProv_eqRefl Ax_s C targetStep)
      (BProv_eqSym Ax_s C _ _
        (BProv_eq_congr_succ Ax_s C idx bound heq)) htarget).
  }
  exact (BProv_orE Ax_s G
    (ltTermAt idx bound) (pEq idx bound)
    (betaTermTermAt out extendedCode targetStep (tSucc idx))
    hcases hltBranch heqBranch).
Qed.

Lemma BProv_Ax_s_betaUnshiftPrefixTermAt_succ_of_extension :
  forall G sourceCode sourceStep currentCode targetStep bound sourceOut
    extendedCode,
  BProv Ax_s G
    (betaUnshiftPrefixTermAt
      sourceCode sourceStep currentCode targetStep bound) ->
  BProv Ax_s G
    (betaCodeExtensionTermAt currentCode targetStep
      (tSucc bound) sourceOut extendedCode) ->
  BProv Ax_s G
    (betaTermTermAt sourceOut sourceCode sourceStep bound) ->
  BProv Ax_s G
    (betaUnshiftPrefixTermAt
      sourceCode sourceStep extendedCode targetStep (tSucc bound)).
Proof.
  intros G sourceCode sourceStep currentCode targetStep bound sourceOut
    extendedCode hprefix hext hsource.
  set (outerAntecedent :=
    ltTermAt (tVar 0) (tSucc (Term.rename S bound))).
  set (sourceEntry :=
    betaTermTermAt (tVar 0)
      (Term.rename (fun n => n + 2) sourceCode)
      (Term.rename (fun n => n + 2) sourceStep)
      (tVar 1)).
  set (targetEntry :=
    betaTermTermAt (tVar 0)
      (Term.rename (fun n => n + 2) extendedCode)
      (Term.rename (fun n => n + 2) targetStep)
      (tSucc (tVar 1))).
  set (innerBody := pImp sourceEntry targetEntry).
  set (outerBody := pImp outerAntecedent (pAll innerBody)).
  set (C := outerAntecedent :: map (rename S) G).
  set (D := sourceEntry :: map (rename S) C).
  set (sourceCode2 := Term.rename (fun n => n + 2) sourceCode).
  set (sourceStep2 := Term.rename (fun n => n + 2) sourceStep).
  set (currentCode2 := Term.rename (fun n => n + 2) currentCode).
  set (targetStep2 := Term.rename (fun n => n + 2) targetStep).
  set (bound2 := Term.rename (fun n => n + 2) bound).
  set (sourceOut2 := Term.rename (fun n => n + 2) sourceOut).
  set (extendedCode2 := Term.rename (fun n => n + 2) extendedCode).
  assert (hsourceAtIdx : BProv Ax_s D
      (betaTermTermAt (tVar 0) sourceCode2 sourceStep2 (tVar 1))).
  {
    apply BProv_ass.
    unfold D, sourceEntry, sourceCode2, sourceStep2.
    simpl. left. reflexivity.
  }
  assert (hltSucc : BProv Ax_s D
      (ltTermAt (tVar 1) (tSucc bound2))).
  {
    assert (hraw : BProv Ax_s D (rename S outerAntecedent)).
    {
      apply BProv_ass.
      unfold D, C. simpl. right. left. reflexivity.
    }
    unfold outerAntecedent, bound2 in hraw.
    rewrite rename_ltTermAt in hraw.
    simpl in hraw.
    rewrite term_rename_succ_twice_add_two in hraw.
    exact hraw.
  }
  assert (hprefixD : BProv Ax_s D
      (betaUnshiftPrefixTermAt sourceCode2 sourceStep2
        currentCode2 targetStep2 bound2)).
  {
    pose proof (BProv_lift_two_contexts_of_sentences
      Ax_s sentence_ax_s G outerAntecedent sourceEntry _ hprefix) as h.
    repeat rewrite rename_betaUnshiftPrefixTermAt in h.
    repeat rewrite term_rename_succ_twice_add_two in h.
    unfold D, C.
    simpl.
    exact h.
  }
  assert (hextD : BProv Ax_s D
      (betaCodeExtensionTermAt currentCode2 targetStep2
        (tSucc bound2) sourceOut2 extendedCode2)).
  {
    pose proof (BProv_lift_two_contexts_of_sentences
      Ax_s sentence_ax_s G outerAntecedent sourceEntry _ hext) as h.
    repeat rewrite rename_betaCodeExtensionTermAt in h.
    repeat rewrite term_rename_succ_twice_add_two in h.
    unfold D, C.
    simpl.
    exact h.
  }
  assert (hsourceD : BProv Ax_s D
      (betaTermTermAt sourceOut2 sourceCode2 sourceStep2 bound2)).
  {
    pose proof (BProv_lift_two_contexts_of_sentences
      Ax_s sentence_ax_s G outerAntecedent sourceEntry _ hsource) as h.
    repeat rewrite rename_betaTermTermAt in h.
    repeat rewrite term_rename_succ_twice_add_two in h.
    unfold D, C.
    simpl.
    exact h.
  }
  pose proof
    (BProv_Ax_s_betaUnshiftPrefixTermAt_succ_entry_of_extension
      D sourceCode2 sourceStep2 currentCode2 targetStep2 bound2
      sourceOut2 extendedCode2 (tVar 1) (tVar 0)
      hprefixD hextD hsourceD hltSucc hsourceAtIdx) as hnew.
  assert (hinnerImp : BProv Ax_s (map (rename S) C) innerBody).
  {
    unfold D in hnew.
    exact (BProv_impI Ax_s (map (rename S) C)
      sourceEntry targetEntry hnew).
  }
  pose proof (BProv_allI_of_sentences Ax_s C innerBody
    sentence_ax_s hinnerImp) as hinnerAll.
  assert (houterImp : BProv Ax_s (map (rename S) G) outerBody).
  {
    unfold C in hinnerAll.
    exact (BProv_impI Ax_s (map (rename S) G)
      outerAntecedent (pAll innerBody) hinnerAll).
  }
  pose proof (BProv_allI_of_sentences Ax_s G outerBody
    sentence_ax_s houterImp) as hall.
  unfold betaUnshiftPrefixTermAt, outerBody, outerAntecedent,
    innerBody, sourceEntry, targetEntry in *.
  exact hall.
Qed.

Lemma BProv_Ax_s_betaTermTermAt_zero_of_succ_extension :
  forall G head currentCode step bound newOut extendedCode,
  BProv Ax_s G (betaTermTermAt head currentCode step tZero) ->
  BProv Ax_s G
    (betaCodeExtensionTermAt currentCode step
      (tSucc bound) newOut extendedCode) ->
  BProv Ax_s G (betaTermTermAt head extendedCode step tZero).
Proof.
  intros G head currentCode step bound newOut extendedCode hhead hext.
  pose proof
    (BProv_Ax_s_betaPrefixAgreementTermAt_of_betaCodeExtensionTermAt
      G currentCode step (tSucc bound) newOut extendedCode hext)
    as hagreement.
  exact (BProv_Ax_s_betaPrefixAgreementTermAt_entry_of_ltTerm
    G currentCode extendedCode step (tSucc bound) tZero head
    hagreement (BProv_Ax_s_ltTermAt_zero_succ G bound) hhead).
Qed.

Lemma BProv_Ax_s_betaPrependPrefixTermAt_succ_of_extension :
  forall G sourceCode sourceStep head currentCode targetStep bound sourceOut
    extendedCode,
  BProv Ax_s G
    (betaPrependPrefixTermAt
      sourceCode sourceStep head currentCode targetStep bound) ->
  BProv Ax_s G
    (betaCodeExtensionTermAt currentCode targetStep
      (tSucc bound) sourceOut extendedCode) ->
  BProv Ax_s G
    (betaTermTermAt sourceOut sourceCode sourceStep bound) ->
  BProv Ax_s G
    (betaPrependPrefixTermAt
      sourceCode sourceStep head extendedCode targetStep (tSucc bound)).
Proof.
  intros G sourceCode sourceStep head currentCode targetStep bound
    sourceOut extendedCode hprefix hext hsource.
  pose proof (BProv_Ax_s_betaTermTermAt_head_of_betaPrependPrefixTermAt
    G sourceCode sourceStep head currentCode targetStep bound hprefix)
    as hhead.
  pose proof (BProv_Ax_s_betaTermTermAt_zero_of_succ_extension
    G head currentCode targetStep bound sourceOut extendedCode
    hhead hext) as hheadNew.
  pose proof
    (BProv_Ax_s_betaUnshiftPrefixTermAt_of_betaPrependPrefixTermAt
      G sourceCode sourceStep head currentCode targetStep bound hprefix)
    as hunshift.
  pose proof (BProv_Ax_s_betaUnshiftPrefixTermAt_succ_of_extension
    G sourceCode sourceStep currentCode targetStep bound sourceOut
    extendedCode hunshift hext hsource) as hunshiftNew.
  exact (BProv_Ax_s_betaPrependPrefixTermAt_of_components
    G sourceCode sourceStep head extendedCode targetStep (tSucc bound)
    hheadNew hunshiftNew).
Qed.

Lemma BProv_Ax_s_betaUnshiftPrefixTermAt_succ_entry_of_not_exists :
  forall G sourceCode sourceStep currentCode targetStep bound idx out,
  BProv Ax_s G
    (betaUnshiftPrefixTermAt
      sourceCode sourceStep currentCode targetStep bound) ->
  BProv Ax_s G
    (pImp (betaShiftSourceEntryExistsTermAt
      sourceCode sourceStep bound) pBot) ->
  BProv Ax_s G (ltTermAt idx (tSucc bound)) ->
  BProv Ax_s G (betaTermTermAt out sourceCode sourceStep idx) ->
  BProv Ax_s G
    (betaTermTermAt out currentCode targetStep (tSucc idx)).
Proof.
  intros G sourceCode sourceStep currentCode targetStep bound idx out
    hprefix hnone hltSucc hsource.
  pose proof (BProv_Ax_s_ltTermAt_succ_right_cases
    G idx bound hltSucc) as hcases.
  assert (hltBranch : BProv Ax_s (ltTermAt idx bound :: G)
      (betaTermTermAt out currentCode targetStep (tSucc idx))).
  {
    set (C := ltTermAt idx bound :: G).
    assert (hlt : BProv Ax_s C (ltTermAt idx bound)).
    { apply BProv_ass. unfold C. simpl. left. reflexivity. }
    exact (BProv_Ax_s_betaUnshiftPrefixTermAt_entry_of_ltTerm
      C sourceCode sourceStep currentCode targetStep bound idx out
      (BProv_context_cons Ax_s G (ltTermAt idx bound) _ hprefix)
      hlt
      (BProv_context_cons Ax_s G (ltTermAt idx bound) _ hsource)).
  }
  assert (heqBranch : BProv Ax_s (pEq idx bound :: G)
      (betaTermTermAt out currentCode targetStep (tSucc idx))).
  {
    set (C := pEq idx bound :: G).
    assert (heq : BProv Ax_s C (pEq idx bound)).
    { apply BProv_ass. unfold C. simpl. left. reflexivity. }
    pose proof (BProv_context_cons Ax_s G (pEq idx bound) _ hsource)
      as hsourceC.
    pose proof (BProv_Ax_s_betaTermTermAt_of_eq_index
      C out sourceCode sourceStep idx bound heq hsourceC)
      as hsourceAtBound.
    pose proof
      (BProv_Ax_s_betaShiftSourceEntryExistsTermAt_of_term
        C sourceCode sourceStep bound out hsourceAtBound) as hex.
    pose proof (BProv_context_cons Ax_s G (pEq idx bound) _ hnone)
      as hnoneC.
    pose proof (BProv_mp Ax_s C
      (betaShiftSourceEntryExistsTermAt sourceCode sourceStep bound)
      pBot hnoneC hex) as hbot.
    exact (BProv_botE Ax_s C _ hbot).
  }
  exact (BProv_orE Ax_s G
    (ltTermAt idx bound) (pEq idx bound)
    (betaTermTermAt out currentCode targetStep (tSucc idx))
    hcases hltBranch heqBranch).
Qed.

Lemma BProv_Ax_s_betaUnshiftPrefixTermAt_succ_of_not_exists :
  forall G sourceCode sourceStep currentCode targetStep bound,
  BProv Ax_s G
    (betaUnshiftPrefixTermAt
      sourceCode sourceStep currentCode targetStep bound) ->
  BProv Ax_s G
    (pImp (betaShiftSourceEntryExistsTermAt
      sourceCode sourceStep bound) pBot) ->
  BProv Ax_s G
    (betaUnshiftPrefixTermAt
      sourceCode sourceStep currentCode targetStep (tSucc bound)).
Proof.
  intros G sourceCode sourceStep currentCode targetStep bound
    hprefix hnone.
  set (outerAntecedent :=
    ltTermAt (tVar 0) (tSucc (Term.rename S bound))).
  set (sourceEntry :=
    betaTermTermAt (tVar 0)
      (Term.rename (fun n => n + 2) sourceCode)
      (Term.rename (fun n => n + 2) sourceStep)
      (tVar 1)).
  set (targetEntry :=
    betaTermTermAt (tVar 0)
      (Term.rename (fun n => n + 2) currentCode)
      (Term.rename (fun n => n + 2) targetStep)
      (tSucc (tVar 1))).
  set (innerBody := pImp sourceEntry targetEntry).
  set (outerBody := pImp outerAntecedent (pAll innerBody)).
  set (C := outerAntecedent :: map (rename S) G).
  set (D := sourceEntry :: map (rename S) C).
  set (sourceCode2 := Term.rename (fun n => n + 2) sourceCode).
  set (sourceStep2 := Term.rename (fun n => n + 2) sourceStep).
  set (currentCode2 := Term.rename (fun n => n + 2) currentCode).
  set (targetStep2 := Term.rename (fun n => n + 2) targetStep).
  set (bound2 := Term.rename (fun n => n + 2) bound).
  assert (hsourceAtIdx : BProv Ax_s D
      (betaTermTermAt (tVar 0) sourceCode2 sourceStep2 (tVar 1))).
  {
    apply BProv_ass.
    unfold D, sourceEntry, sourceCode2, sourceStep2.
    simpl. left. reflexivity.
  }
  assert (hltSucc : BProv Ax_s D
      (ltTermAt (tVar 1) (tSucc bound2))).
  {
    assert (hraw : BProv Ax_s D (rename S outerAntecedent)).
    {
      apply BProv_ass.
      unfold D, C. simpl. right. left. reflexivity.
    }
    unfold outerAntecedent, bound2 in hraw.
    rewrite rename_ltTermAt in hraw.
    simpl in hraw.
    rewrite term_rename_succ_twice_add_two in hraw.
    exact hraw.
  }
  assert (hprefixD : BProv Ax_s D
      (betaUnshiftPrefixTermAt sourceCode2 sourceStep2
        currentCode2 targetStep2 bound2)).
  {
    pose proof (BProv_lift_two_contexts_of_sentences
      Ax_s sentence_ax_s G outerAntecedent sourceEntry _ hprefix) as h.
    repeat rewrite rename_betaUnshiftPrefixTermAt in h.
    repeat rewrite term_rename_succ_twice_add_two in h.
    unfold D, C.
    simpl.
    exact h.
  }
  assert (hnoneD : BProv Ax_s D
      (pImp
        (betaShiftSourceEntryExistsTermAt
          sourceCode2 sourceStep2 bound2)
        pBot)).
  {
    pose proof (BProv_lift_two_contexts_of_sentences
      Ax_s sentence_ax_s G outerAntecedent sourceEntry _ hnone) as h.
    change (BProv Ax_s
      (sourceEntry :: map (rename S)
        (outerAntecedent :: map (rename S) G))
      (pImp
        (rename S (rename S
          (betaShiftSourceEntryExistsTermAt
            sourceCode sourceStep bound)))
        pBot)) in h.
    repeat rewrite rename_betaShiftSourceEntryExistsTermAt in h.
    repeat rewrite term_rename_succ_twice_add_two in h.
    unfold D, C.
    simpl.
    exact h.
  }
  pose proof
    (BProv_Ax_s_betaUnshiftPrefixTermAt_succ_entry_of_not_exists
      D sourceCode2 sourceStep2 currentCode2 targetStep2 bound2
      (tVar 1) (tVar 0) hprefixD hnoneD hltSucc hsourceAtIdx)
    as hnew.
  assert (hinnerImp : BProv Ax_s (map (rename S) C) innerBody).
  {
    unfold D in hnew.
    exact (BProv_impI Ax_s (map (rename S) C)
      sourceEntry targetEntry hnew).
  }
  pose proof (BProv_allI_of_sentences Ax_s C innerBody
    sentence_ax_s hinnerImp) as hinnerAll.
  assert (houterImp : BProv Ax_s (map (rename S) G) outerBody).
  {
    unfold C in hinnerAll.
    exact (BProv_impI Ax_s (map (rename S) G)
      outerAntecedent (pAll innerBody) hinnerAll).
  }
  pose proof (BProv_allI_of_sentences Ax_s G outerBody
    sentence_ax_s houterImp) as hall.
  unfold betaUnshiftPrefixTermAt, outerBody, outerAntecedent,
    innerBody, sourceEntry, targetEntry in *.
  exact hall.
Qed.

Lemma BProv_Ax_s_betaPrependPrefixTermAt_succ_of_not_exists :
  forall G sourceCode sourceStep head currentCode targetStep bound,
  BProv Ax_s G
    (betaPrependPrefixTermAt
      sourceCode sourceStep head currentCode targetStep bound) ->
  BProv Ax_s G
    (pImp (betaShiftSourceEntryExistsTermAt
      sourceCode sourceStep bound) pBot) ->
  BProv Ax_s G
    (betaPrependPrefixTermAt
      sourceCode sourceStep head currentCode targetStep (tSucc bound)).
Proof.
  intros G sourceCode sourceStep head currentCode targetStep bound
    hprefix hnone.
  pose proof (BProv_Ax_s_betaTermTermAt_head_of_betaPrependPrefixTermAt
    G sourceCode sourceStep head currentCode targetStep bound hprefix)
    as hhead.
  pose proof
    (BProv_Ax_s_betaUnshiftPrefixTermAt_of_betaPrependPrefixTermAt
      G sourceCode sourceStep head currentCode targetStep bound hprefix)
    as hunshift.
  pose proof (BProv_Ax_s_betaUnshiftPrefixTermAt_succ_of_not_exists
    G sourceCode sourceStep currentCode targetStep bound
    hunshift hnone) as hunshiftNext.
  exact (BProv_Ax_s_betaPrependPrefixTermAt_of_components
    G sourceCode sourceStep head currentCode targetStep (tSucc bound)
    hhead hunshiftNext).
Qed.

Lemma BProv_Ax_s_betaPrependPrefixCodeExistsTermAt_succ_of_source :
  forall G sourceCode sourceStep head currentCode targetStep bound sourceOut,
  BProv Ax_s G
    (betaPrependPrefixTermAt
      sourceCode sourceStep head currentCode targetStep bound) ->
  BProv Ax_s G
    (betaTermTermAt sourceOut sourceCode sourceStep bound) ->
  BProv Ax_s G
    (commonMultipleThroughTermAt (tSucc bound) targetStep) ->
  BProv Ax_s G (leTermAt (tSucc sourceCode) targetStep) ->
  BProv Ax_s G
    (betaPrependPrefixCodeExistsTermAt
      sourceCode sourceStep head targetStep (tSucc bound)).
Proof.
  intros G sourceCode sourceStep head currentCode targetStep bound
    sourceOut hprefix hsource hcommon hlarge.
  pose proof
    (BProv_Ax_s_ltTermAt_betaMod_of_betaTermTermAt_le_step_shift
      G sourceOut sourceCode sourceStep bound targetStep (tSucc bound)
      hsource hlarge) as hbound.
  pose proof
    (BProv_Ax_s_betaCodeExtensionExistsTermAt_of_common
      G currentCode targetStep (tSucc bound) sourceOut
      hcommon hbound) as hextEx.
  set (goal := betaPrependPrefixCodeExistsTermAt
    sourceCode sourceStep head targetStep (tSucc bound)).
  apply (BProv_Ax_s_betaCodeExtensionExistsTermAt_elim_opened
    G currentCode targetStep (tSucc bound) sourceOut goal);
    [|exact hextEx].
  set (extBody := betaCodeExtensionExistsTermAtBody
    currentCode targetStep (tSucc bound) sourceOut).
  set (D := extBody :: map (rename S) G).
  set (sourceCode1 := Term.rename S sourceCode).
  set (sourceStep1 := Term.rename S sourceStep).
  set (head1 := Term.rename S head).
  set (currentCode1 := Term.rename S currentCode).
  set (targetStep1 := Term.rename S targetStep).
  set (bound1 := Term.rename S bound).
  set (sourceOut1 := Term.rename S sourceOut).
  assert (hext : BProv Ax_s D
      (betaCodeExtensionTermAt currentCode1 targetStep1
        (tSucc bound1) sourceOut1 (tVar 0))).
  {
    apply BProv_ass.
    unfold D, extBody, betaCodeExtensionExistsTermAtBody,
      currentCode1, targetStep1, bound1, sourceOut1.
    simpl. left. reflexivity.
  }
  pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
    hprefix S) as hprefixRen.
  rewrite rename_betaPrependPrefixTermAt in hprefixRen.
  assert (hprefixD : BProv Ax_s D
      (betaPrependPrefixTermAt sourceCode1 sourceStep1 head1
        currentCode1 targetStep1 bound1)).
  {
    exact (BProv_context_cons Ax_s (map (rename S) G)
      extBody _ hprefixRen).
  }
  pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
    hsource S) as hsourceRen.
  rewrite rename_betaTermTermAt in hsourceRen.
  assert (hsourceD : BProv Ax_s D
      (betaTermTermAt sourceOut1 sourceCode1 sourceStep1 bound1)).
  {
    exact (BProv_context_cons Ax_s (map (rename S) G)
      extBody _ hsourceRen).
  }
  pose proof
    (BProv_Ax_s_betaPrependPrefixTermAt_succ_of_extension
      D sourceCode1 sourceStep1 head1 currentCode1 targetStep1
      bound1 sourceOut1 (tVar 0) hprefixD hext hsourceD)
    as hnext.
  pose proof
    (BProv_Ax_s_betaPrependPrefixCodeExistsTermAt_of_term
      D sourceCode1 sourceStep1 head1 (tVar 0) targetStep1
      (tSucc bound1) hnext) as hex.
  unfold goal.
  now rewrite rename_betaPrependPrefixCodeExistsTermAt.
Qed.

Lemma BProv_Ax_s_betaPrependPrefixCodeExistsTermAt_succ_of_not_exists :
  forall G sourceCode sourceStep head currentCode targetStep bound,
  BProv Ax_s G
    (betaPrependPrefixTermAt
      sourceCode sourceStep head currentCode targetStep bound) ->
  BProv Ax_s G
    (pImp (betaShiftSourceEntryExistsTermAt
      sourceCode sourceStep bound) pBot) ->
  BProv Ax_s G
    (betaPrependPrefixCodeExistsTermAt
      sourceCode sourceStep head targetStep (tSucc bound)).
Proof.
  intros G sourceCode sourceStep head currentCode targetStep bound
    hprefix hnone.
  apply (BProv_Ax_s_betaPrependPrefixCodeExistsTermAt_of_term
    G sourceCode sourceStep head currentCode targetStep (tSucc bound)).
  exact (BProv_Ax_s_betaPrependPrefixTermAt_succ_of_not_exists
    G sourceCode sourceStep head currentCode targetStep bound
    hprefix hnone).
Qed.

Lemma BProv_Ax_s_betaPrependPrefixCodeExistsTermAt_succ_of_entry_exists :
  forall G sourceCode sourceStep head currentCode targetStep bound,
  BProv Ax_s G
    (betaPrependPrefixTermAt
      sourceCode sourceStep head currentCode targetStep bound) ->
  BProv Ax_s G
    (betaShiftSourceEntryExistsTermAt sourceCode sourceStep bound) ->
  BProv Ax_s G
    (commonMultipleThroughTermAt (tSucc bound) targetStep) ->
  BProv Ax_s G (leTermAt (tSucc sourceCode) targetStep) ->
  BProv Ax_s G
    (betaPrependPrefixCodeExistsTermAt
      sourceCode sourceStep head targetStep (tSucc bound)).
Proof.
  intros G sourceCode sourceStep head currentCode targetStep bound
    hprefix hentryEx hcommon hlarge.
  set (goal := betaPrependPrefixCodeExistsTermAt
    sourceCode sourceStep head targetStep (tSucc bound)).
  apply (BProv_Ax_s_betaShiftSourceEntryExistsTermAt_elim_opened
    G sourceCode sourceStep bound goal); [|exact hentryEx].
  set (entryBody := betaShiftSourceEntryExistsTermAtBody
    sourceCode sourceStep bound).
  set (D := entryBody :: map (rename S) G).
  set (sourceCode1 := Term.rename S sourceCode).
  set (sourceStep1 := Term.rename S sourceStep).
  set (head1 := Term.rename S head).
  set (currentCode1 := Term.rename S currentCode).
  set (targetStep1 := Term.rename S targetStep).
  set (bound1 := Term.rename S bound).
  assert (hsource : BProv Ax_s D
      (betaTermTermAt (tVar 0) sourceCode1 sourceStep1 bound1)).
  {
    apply BProv_ass.
    unfold D, entryBody, betaShiftSourceEntryExistsTermAtBody,
      sourceCode1, sourceStep1, bound1.
    simpl. left. reflexivity.
  }
  pose proof (BProv_rename_succ_context_cons_of_sentences
    Ax_s sentence_ax_s G entryBody _ hprefix) as hprefixD.
  rewrite rename_betaPrependPrefixTermAt in hprefixD.
  pose proof (BProv_rename_succ_context_cons_of_sentences
    Ax_s sentence_ax_s G entryBody _ hcommon) as hcommonD.
  rewrite rename_commonMultipleThroughTermAt in hcommonD.
  pose proof (BProv_rename_succ_context_cons_of_sentences
    Ax_s sentence_ax_s G entryBody _ hlarge) as hlargeD.
  rewrite rename_leTermAt in hlargeD.
  pose proof
    (BProv_Ax_s_betaPrependPrefixCodeExistsTermAt_succ_of_source
      D sourceCode1 sourceStep1 head1 currentCode1 targetStep1
      bound1 (tVar 0) hprefixD hsource hcommonD hlargeD)
    as hnext.
  unfold goal.
  now rewrite rename_betaPrependPrefixCodeExistsTermAt.
Qed.

Lemma BProv_Ax_s_betaPrependPrefixCodeExistsTermAt_succ_of_current :
  forall G sourceCode sourceStep head currentCode targetStep bound,
  BProv Ax_s G
    (betaPrependPrefixTermAt
      sourceCode sourceStep head currentCode targetStep bound) ->
  BProv Ax_s G
    (commonMultipleThroughTermAt (tSucc bound) targetStep) ->
  BProv Ax_s G (leTermAt (tSucc sourceCode) targetStep) ->
  BProv Ax_s G
    (betaPrependPrefixCodeExistsTermAt
      sourceCode sourceStep head targetStep (tSucc bound)).
Proof.
  intros G sourceCode sourceStep head currentCode targetStep bound
    hprefix hcommon hlarge.
  set (entryEx := betaShiftSourceEntryExistsTermAt
    sourceCode sourceStep bound).
  assert (hem : BProv Ax_s G
      (pOr entryEx (pImp entryEx pBot))).
  { apply BProv_of_Prov. apply P_lem. }
  assert (hentryBranch : BProv Ax_s (entryEx :: G)
      (betaPrependPrefixCodeExistsTermAt
        sourceCode sourceStep head targetStep (tSucc bound))).
  {
    apply (BProv_Ax_s_betaPrependPrefixCodeExistsTermAt_succ_of_entry_exists
      (entryEx :: G) sourceCode sourceStep head currentCode targetStep bound).
    - exact (BProv_context_cons Ax_s G entryEx _ hprefix).
    - apply BProv_ass_head.
    - exact (BProv_context_cons Ax_s G entryEx _ hcommon).
    - exact (BProv_context_cons Ax_s G entryEx _ hlarge).
  }
  assert (hnoneBranch : BProv Ax_s (pImp entryEx pBot :: G)
      (betaPrependPrefixCodeExistsTermAt
        sourceCode sourceStep head targetStep (tSucc bound))).
  {
    apply (BProv_Ax_s_betaPrependPrefixCodeExistsTermAt_succ_of_not_exists
      (pImp entryEx pBot :: G)
      sourceCode sourceStep head currentCode targetStep bound).
    - exact (BProv_context_cons Ax_s G (pImp entryEx pBot) _ hprefix).
    - apply BProv_ass_head.
  }
  exact (BProv_orE Ax_s G entryEx (pImp entryEx pBot)
    (betaPrependPrefixCodeExistsTermAt
      sourceCode sourceStep head targetStep (tSucc bound))
    hem hentryBranch hnoneBranch).
Qed.

Lemma BProv_Ax_s_betaPrependPrefixCodeExistsTermAt_succ :
  forall G sourceCode sourceStep head targetStep bound,
  BProv Ax_s G
    (betaPrependPrefixCodeExistsTermAt
      sourceCode sourceStep head targetStep bound) ->
  BProv Ax_s G
    (commonMultipleThroughTermAt (tSucc bound) targetStep) ->
  BProv Ax_s G (leTermAt (tSucc sourceCode) targetStep) ->
  BProv Ax_s G
    (betaPrependPrefixCodeExistsTermAt
      sourceCode sourceStep head targetStep (tSucc bound)).
Proof.
  intros G sourceCode sourceStep head targetStep bound
    hex hcommon hlarge.
  set (goal := betaPrependPrefixCodeExistsTermAt
    sourceCode sourceStep head targetStep (tSucc bound)).
  apply (BProv_Ax_s_betaPrependPrefixCodeExistsTermAt_elim_opened
    G sourceCode sourceStep head targetStep bound goal); [|exact hex].
  set (prefixBody := betaPrependPrefixCodeExistsTermAtBody
    sourceCode sourceStep head targetStep bound).
  set (D := prefixBody :: map (rename S) G).
  set (sourceCode1 := Term.rename S sourceCode).
  set (sourceStep1 := Term.rename S sourceStep).
  set (head1 := Term.rename S head).
  set (targetStep1 := Term.rename S targetStep).
  set (bound1 := Term.rename S bound).
  assert (hprefix : BProv Ax_s D
      (betaPrependPrefixTermAt sourceCode1 sourceStep1 head1
        (tVar 0) targetStep1 bound1)).
  {
    apply BProv_ass.
    unfold D, prefixBody, betaPrependPrefixCodeExistsTermAtBody,
      sourceCode1, sourceStep1, head1, targetStep1, bound1.
    simpl. left. reflexivity.
  }
  pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
    hcommon S) as hcommonRen.
  rewrite rename_commonMultipleThroughTermAt in hcommonRen.
  assert (hcommonD : BProv Ax_s D
      (commonMultipleThroughTermAt (tSucc bound1) targetStep1)).
  {
    exact (BProv_context_cons Ax_s (map (rename S) G)
      prefixBody _ hcommonRen).
  }
  pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
    hlarge S) as hlargeRen.
  rewrite rename_leTermAt in hlargeRen.
  assert (hlargeD : BProv Ax_s D
      (leTermAt (tSucc sourceCode1) targetStep1)).
  {
    exact (BProv_context_cons Ax_s (map (rename S) G)
      prefixBody _ hlargeRen).
  }
  pose proof
    (BProv_Ax_s_betaPrependPrefixCodeExistsTermAt_succ_of_current
      D sourceCode1 sourceStep1 head1 (tVar 0) targetStep1 bound1
      hprefix hcommonD hlargeD) as hnext.
  unfold goal.
  now rewrite rename_betaPrependPrefixCodeExistsTermAt.
Qed.

Lemma BProv_Ax_s_all_betaPrependPrefixCodeExistsTermAt_of_codingStep :
  forall G sourceCode sourceStep head targetStep finalBound,
  BProv Ax_s G
    (betaPrependCodingStepTermAt
      finalBound sourceCode head targetStep) ->
  BProv Ax_s G
    (pAll (pImp
      (leTermAt (tVar 0) (Term.rename S finalBound))
      (betaPrependPrefixCodeExistsTermAt
        (Term.rename S sourceCode)
        (Term.rename S sourceStep)
        (Term.rename S head)
        (Term.rename S targetStep)
        (tVar 0)))).
Proof.
  intros G sourceCode sourceStep head targetStep finalBound hcoding.
  set (phi := pImp
    (leTermAt (tVar 0) (Term.rename S finalBound))
    (betaPrependPrefixCodeExistsTermAt
      (Term.rename S sourceCode)
      (Term.rename S sourceStep)
      (Term.rename S head)
      (Term.rename S targetStep)
      (tVar 0))).
  pose proof hcoding as hcodingParts.
  unfold betaPrependCodingStepTermAt in hcodingParts.
  pose proof (BProv_andE2 Ax_s G _ _ hcodingParts) as hlarges.
  pose proof (BProv_andE2 Ax_s G _ _ hlarges) as hlargeHead.
  pose proof (BProv_Ax_s_betaPrependPrefixCodeExistsTermAt_zero
    G sourceCode sourceStep head targetStep hlargeHead) as hbase.
  assert (hzeroImp : BProv Ax_s G
      (pImp (leTermAt tZero finalBound)
        (betaPrependPrefixCodeExistsTermAt
          sourceCode sourceStep head targetStep tZero))).
  {
    apply (BProv_impI Ax_s G _ _).
    exact (BProv_context_cons Ax_s G
      (leTermAt tZero finalBound) _ hbase).
  }
  assert (hzero : BProv Ax_s G (subst substZero phi)).
  {
    unfold phi.
    cbn [subst].
    rewrite subst_leTermAt.
    rewrite subst_betaPrependPrefixCodeExistsTermAt.
    simpl.
    repeat rewrite term_substZero_rename_succ.
    exact hzeroImp.
  }
  pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
    hcoding S) as hcodingRen.
  rewrite rename_betaPrependCodingStepTermAt in hcodingRen.
  set (C := phi :: map (rename S) G).
  assert (hsuccBody : BProv Ax_s C (subst substSuccVar phi)).
  {
    set (sourceCode1 := Term.rename S sourceCode).
    set (sourceStep1 := Term.rename S sourceStep).
    set (head1 := Term.rename S head).
    set (targetStep1 := Term.rename S targetStep).
    set (finalBound1 := Term.rename S finalBound).
    set (leSucc := leTermAt (tSucc (tVar 0)) finalBound1).
    set (prefixSucc := betaPrependPrefixCodeExistsTermAt
      sourceCode1 sourceStep1 head1 targetStep1 (tSucc (tVar 0))).
    set (D := leSucc :: C).
    assert (hleSucc : BProv Ax_s D leSucc).
    { apply BProv_ass. unfold D. simpl. left. reflexivity. }
    pose proof (BProv_Ax_s_leTermAt_pred_of_succ_le
      D (tVar 0) finalBound1 hleSucc) as hlePred.
    assert (hihRaw : BProv Ax_s D phi).
    {
      exact (BProv_context_cons Ax_s C leSucc _
        (BProv_ass Ax_s C phi (or_introl eq_refl))).
    }
    assert (hih : BProv Ax_s D
        (pImp (leTermAt (tVar 0) finalBound1)
          (betaPrependPrefixCodeExistsTermAt
            sourceCode1 sourceStep1 head1 targetStep1 (tVar 0)))).
    {
      unfold phi, sourceCode1, sourceStep1, head1,
        targetStep1, finalBound1 in hihRaw.
      exact hihRaw.
    }
    pose proof (BProv_mp Ax_s D _ _ hih hlePred) as hex.
    assert (hcodingC : BProv Ax_s C
        (betaPrependCodingStepTermAt
          finalBound1 sourceCode1 head1 targetStep1)).
    {
      exact (BProv_context_cons Ax_s (map (rename S) G)
        phi _ hcodingRen).
    }
    assert (hcodingD : BProv Ax_s D
        (betaPrependCodingStepTermAt
          finalBound1 sourceCode1 head1 targetStep1)).
    { exact (BProv_context_cons Ax_s C leSucc _ hcodingC). }
    unfold betaPrependCodingStepTermAt in hcodingD.
    pose proof (BProv_andE1 Ax_s D _ _ hcodingD) as hcommonFinal.
    pose proof (BProv_andE2 Ax_s D _ _ hcodingD) as hlargesD.
    pose proof (BProv_andE1 Ax_s D _ _ hlargesD) as hlargeSource.
    pose proof (BProv_Ax_s_commonMultipleThroughTermAt_of_le
      D (tSucc (tVar 0)) finalBound1 targetStep1
      hcommonFinal hleSucc) as hcommon.
    pose proof
      (BProv_Ax_s_betaPrependPrefixCodeExistsTermAt_succ
        D sourceCode1 sourceStep1 head1 targetStep1 (tVar 0)
        hex hcommon hlargeSource) as hnext.
    assert (himp : BProv Ax_s C (pImp leSucc prefixSucc)).
    {
      unfold D in hnext.
      exact (BProv_impI Ax_s C leSucc prefixSucc hnext).
    }
    unfold phi.
    cbn [subst].
    rewrite subst_leTermAt.
    rewrite subst_betaPrependPrefixCodeExistsTermAt.
    simpl.
    repeat rewrite term_substSuccVar_rename_succ.
    unfold leSucc, prefixSucc, sourceCode1, sourceStep1,
      head1, targetStep1, finalBound1 in himp.
    exact himp.
  }
  assert (hsuccImp : BProv Ax_s (map (rename S) G)
      (pImp phi (subst substSuccVar phi))).
  {
    unfold C in hsuccBody.
    exact (BProv_impI Ax_s (map (rename S) G)
      phi (subst substSuccVar phi) hsuccBody).
  }
  pose proof (BProv_allI_of_sentences Ax_s G _
    sentence_ax_s hsuccImp) as hsuccAll.
  pose proof (BProv_Ax_s_induction_rule G phi hzero hsuccAll) as hall.
  unfold phi in hall.
  exact hall.
Qed.

Lemma BProv_Ax_s_betaPrependPrefixCodeExistsTermAt_of_codingStep :
  forall G sourceCode sourceStep head targetStep finalBound,
  BProv Ax_s G
    (betaPrependCodingStepTermAt
      finalBound sourceCode head targetStep) ->
  BProv Ax_s G
    (betaPrependPrefixCodeExistsTermAt
      sourceCode sourceStep head targetStep finalBound).
Proof.
  intros G sourceCode sourceStep head targetStep finalBound hcoding.
  pose proof
    (BProv_Ax_s_all_betaPrependPrefixCodeExistsTermAt_of_codingStep
      G sourceCode sourceStep head targetStep finalBound hcoding) as hall.
  pose proof (BProv_allE Ax_s G _ finalBound hall) as himp.
  cbn [subst] in himp.
  rewrite subst_leTermAt in himp.
  rewrite subst_betaPrependPrefixCodeExistsTermAt in himp.
  simpl in himp.
  repeat rewrite term_subst_instTerm_rename_succ in himp.
  exact (BProv_mp Ax_s G
    (leTermAt finalBound finalBound)
    (betaPrependPrefixCodeExistsTermAt
      sourceCode sourceStep head targetStep finalBound)
    himp (BProv_Ax_s_leTermAt_refl G finalBound)).
Qed.

Lemma BProv_Ax_s_betaPrependExistsTermAt_of_step :
  forall G sourceCode sourceStep head targetStep bound,
  BProv Ax_s G
    (betaPrependPrefixCodeExistsTermAt
      sourceCode sourceStep head targetStep bound) ->
  BProv Ax_s G
    (betaPrependExistsTermAt sourceCode sourceStep head bound).
Proof.
  intros G sourceCode sourceStep head targetStep bound hcode.
  unfold betaPrependExistsTermAt.
  apply (BProv_exI Ax_s G _ targetStep).
  rewrite subst_betaPrependPrefixCodeExistsTermAt.
  simpl.
  repeat rewrite term_subst_instTerm_rename_succ.
  exact hcode.
Qed.

Lemma BProv_Ax_s_betaPrependExistsTermAt_elim_opened :
  forall G sourceCode sourceStep head bound target,
  BProv Ax_s
    (betaPrependExistsTermAtBody sourceCode sourceStep head bound ::
      map (rename S) G)
    (rename S target) ->
  BProv Ax_s G
    (betaPrependExistsTermAt sourceCode sourceStep head bound) ->
  BProv Ax_s G target.
Proof.
  intros G sourceCode sourceStep head bound target hopened hex.
  unfold betaPrependExistsTermAt in hex.
  unfold betaPrependExistsTermAtBody in hopened.
  exact (BProv_exE_of_sentences Ax_s G _ target
    sentence_ax_s hex hopened).
Qed.

Theorem BProv_Ax_s_betaPrependExistsTermAt :
  forall G sourceCode sourceStep head bound,
  BProv Ax_s G
    (betaPrependExistsTermAt sourceCode sourceStep head bound).
Proof.
  intros G sourceCode sourceStep head bound.
  set (goal := betaPrependExistsTermAt
    sourceCode sourceStep head bound).
  pose proof (BProv_Ax_s_betaPrependCodingStepExistsTermAt
    G bound sourceCode head) as hstepEx.
  apply (BProv_Ax_s_betaPrependCodingStepExistsTermAt_elim_opened
    G bound sourceCode head goal); [|exact hstepEx].
  set (stepBody := betaPrependCodingStepExistsTermAtBody
    bound sourceCode head).
  set (D := stepBody :: map (rename S) G).
  set (sourceCode1 := Term.rename S sourceCode).
  set (sourceStep1 := Term.rename S sourceStep).
  set (head1 := Term.rename S head).
  set (bound1 := Term.rename S bound).
  assert (hcoding : BProv Ax_s D
      (betaPrependCodingStepTermAt
        bound1 sourceCode1 head1 (tVar 0))).
  {
    apply BProv_ass.
    unfold D, stepBody, betaPrependCodingStepExistsTermAtBody,
      sourceCode1, head1, bound1.
    simpl. left. reflexivity.
  }
  pose proof
    (BProv_Ax_s_betaPrependPrefixCodeExistsTermAt_of_codingStep
      D sourceCode1 sourceStep1 head1 (tVar 0) bound1 hcoding)
    as hprefix.
  pose proof (BProv_Ax_s_betaPrependExistsTermAt_of_step
    D sourceCode1 sourceStep1 head1 (tVar 0) bound1 hprefix)
    as hex.
  unfold goal.
  rewrite rename_betaPrependExistsTermAt.
  exact hex.
Qed.

Lemma BProv_Ax_s_betaUnshiftPrefixTermAt_stepWitness_succ_of_components :
  forall G sourceCode sourceStep targetCode targetStep bound idx cur next bit,
  BProv Ax_s G
    (betaUnshiftPrefixTermAt
      sourceCode sourceStep targetCode targetStep bound) ->
  BProv Ax_s G (ltTermAt idx bound) ->
  BProv Ax_s G (ltTermAt (tSucc idx) bound) ->
  BProv Ax_s G (betaTermTermAt cur sourceCode sourceStep idx) ->
  BProv Ax_s G
    (betaTermTermAt next sourceCode sourceStep (tSucc idx)) ->
  BProv Ax_s G (div2StepTermAt cur next bit) ->
  BProv Ax_s G
    (betaDiv2StepWitnessTermAt targetCode targetStep (tSucc idx)).
Proof.
  intros G sourceCode sourceStep targetCode targetStep bound idx cur
    next bit hprefix hltCur hltNext hcur hnext hdiv.
  pose proof (BProv_Ax_s_betaUnshiftPrefixTermAt_entry_of_ltTerm
    G sourceCode sourceStep targetCode targetStep bound idx cur
    hprefix hltCur hcur) as hcurTarget.
  pose proof (BProv_Ax_s_betaUnshiftPrefixTermAt_entry_of_ltTerm
    G sourceCode sourceStep targetCode targetStep bound (tSucc idx) next
    hprefix hltNext hnext) as hnextTarget.
  exact (BProv_Ax_s_betaDiv2StepWitnessTermAt_of_components
    G targetCode targetStep (tSucc idx) cur next bit
    hcurTarget hnextTarget hdiv).
Qed.

Lemma BProv_Ax_s_betaPrependPrefixTermAt_step_zero_of_components :
  forall G sourceCode sourceStep head sourceHead headBit targetCode
    targetStep bound,
  BProv Ax_s G
    (betaPrependPrefixTermAt sourceCode sourceStep head
      targetCode targetStep bound) ->
  BProv Ax_s G (ltTermAt tZero bound) ->
  BProv Ax_s G
    (betaTermTermAt sourceHead sourceCode sourceStep tZero) ->
  BProv Ax_s G (div2StepTermAt head sourceHead headBit) ->
  BProv Ax_s G
    (betaDiv2StepWitnessTermAt targetCode targetStep tZero).
Proof.
  intros G sourceCode sourceStep head sourceHead headBit targetCode
    targetStep bound hprefix hbound hsourceHead hdiv.
  pose proof (BProv_Ax_s_betaTermTermAt_head_of_betaPrependPrefixTermAt
    G sourceCode sourceStep head targetCode targetStep bound hprefix)
    as hhead.
  pose proof
    (BProv_Ax_s_betaUnshiftPrefixTermAt_of_betaPrependPrefixTermAt
      G sourceCode sourceStep head targetCode targetStep bound hprefix)
    as hunshift.
  pose proof (BProv_Ax_s_betaUnshiftPrefixTermAt_entry_of_ltTerm
    G sourceCode sourceStep targetCode targetStep bound tZero sourceHead
    hunshift hbound hsourceHead) as hnext.
  exact (BProv_Ax_s_betaDiv2StepWitnessTermAt_of_components
    G targetCode targetStep tZero head sourceHead headBit
    hhead hnext hdiv).
Qed.

Lemma BProv_Ax_s_betaPrependPrefixTermAt_stepWitness_succ_of_components :
  forall G sourceCode sourceStep head targetCode targetStep last idx cur
    next bit,
  BProv Ax_s G
    (betaPrependPrefixTermAt sourceCode sourceStep head
      targetCode targetStep (tSucc (tSucc last))) ->
  BProv Ax_s G (leTermAt idx last) ->
  BProv Ax_s G (betaTermTermAt cur sourceCode sourceStep idx) ->
  BProv Ax_s G
    (betaTermTermAt next sourceCode sourceStep (tSucc idx)) ->
  BProv Ax_s G (div2StepTermAt cur next bit) ->
  BProv Ax_s G
    (betaDiv2StepWitnessTermAt targetCode targetStep (tSucc idx)).
Proof.
  intros G sourceCode sourceStep head targetCode targetStep last idx
    cur next bit hprefix hle hcur hnext hdiv.
  pose proof
    (BProv_Ax_s_betaUnshiftPrefixTermAt_of_betaPrependPrefixTermAt
      G sourceCode sourceStep head targetCode targetStep
      (tSucc (tSucc last)) hprefix) as hunshift.
  pose proof (BProv_Ax_s_leTermAt_self_succ G last) as hlastSucc.
  pose proof (BProv_Ax_s_leTermAt_trans
    G idx last (tSucc last) hle hlastSucc) as hidxLeSucc.
  pose proof (BProv_Ax_s_ltTermAt_succ_right_of_leTermAt
    G idx (tSucc last) hidxLeSucc) as hltCur.
  pose proof (BProv_Ax_s_leTermAt_succ_succ
    G idx last hle) as hsuccLe.
  pose proof (BProv_Ax_s_ltTermAt_succ_right_of_leTermAt
    G (tSucc idx) (tSucc last) hsuccLe) as hltNext.
  exact
    (BProv_Ax_s_betaUnshiftPrefixTermAt_stepWitness_succ_of_components
      G sourceCode sourceStep targetCode targetStep
      (tSucc (tSucc last)) idx cur next bit
      hunshift hltCur hltNext hcur hnext hdiv).
Qed.

(** Open a source three-witness beta step and transport it to the successor
    index of a complete prepend prefix. *)
Lemma BProv_Ax_s_betaPrependPrefixTermAt_stepWitness_succ_of_sourceWitness :
  forall G sourceCode sourceStep head targetCode targetStep last idx,
  BProv Ax_s G
    (betaPrependPrefixTermAt sourceCode sourceStep head
      targetCode targetStep (tSucc (tSucc last))) ->
  BProv Ax_s G (leTermAt idx last) ->
  BProv Ax_s G
    (betaDiv2StepWitnessTermAt sourceCode sourceStep idx) ->
  BProv Ax_s G
    (betaDiv2StepWitnessTermAt targetCode targetStep (tSucc idx)).
Proof.
  intros G sourceCode sourceStep head targetCode targetStep last idx
    hprefix hle hwitness.
  set (target :=
    betaDiv2StepWitnessTermAt targetCode targetStep (tSucc idx)).
  set (body := pAnd
    (betaTermTermAt (tVar 2)
      (Term.rename (fun n => n + 3) sourceCode)
      (Term.rename (fun n => n + 3) sourceStep)
      (Term.rename (fun n => n + 3) idx))
    (pAnd
      (betaTermTermAt (tVar 1)
        (Term.rename (fun n => n + 3) sourceCode)
        (Term.rename (fun n => n + 3) sourceStep)
        (tSucc (Term.rename (fun n => n + 3) idx)))
      (div2StepTermAt (tVar 2) (tVar 1) (tVar 0)))).
  assert (hwit : BProv Ax_s G (pEx (pEx (pEx body)))).
  { unfold betaDiv2StepWitnessTermAt in hwitness. exact hwitness. }
  apply (BProv_three_exE_of_sentences
    Ax_s sentence_ax_s G body target hwit).
  set (C := body :: map (rename S)
    (pEx body :: map (rename S)
      (pEx (pEx body) :: map (rename S) G))).
  change (BProv Ax_s C (rename S (rename S (rename S target)))).
  set (sourceCode3 :=
    Term.rename S (Term.rename S (Term.rename S sourceCode))).
  set (sourceStep3 :=
    Term.rename S (Term.rename S (Term.rename S sourceStep))).
  set (head3 :=
    Term.rename S (Term.rename S (Term.rename S head))).
  set (targetCode3 :=
    Term.rename S (Term.rename S (Term.rename S targetCode))).
  set (targetStep3 :=
    Term.rename S (Term.rename S (Term.rename S targetStep))).
  set (last3 :=
    Term.rename S (Term.rename S (Term.rename S last))).
  set (idx3 :=
    Term.rename S (Term.rename S (Term.rename S idx))).
  assert (hbody : BProv Ax_s C body).
  { apply BProv_ass. unfold C. simpl. left. reflexivity. }
  assert (hcur : BProv Ax_s C
      (betaTermTermAt (tVar 2) sourceCode3 sourceStep3 idx3)).
  {
    pose proof (BProv_andE1 Ax_s C _ _ hbody) as h.
    unfold body, sourceCode3, sourceStep3, idx3 in *.
    repeat rewrite (term_rename_add_eq_iterTermRenameSucc 3) in h.
    exact h.
  }
  pose proof (BProv_andE2 Ax_s C _ _ hbody) as htail.
  assert (hnext : BProv Ax_s C
      (betaTermTermAt (tVar 1) sourceCode3 sourceStep3
        (tSucc idx3))).
  {
    pose proof (BProv_andE1 Ax_s C _ _ htail) as h.
    unfold body, sourceCode3, sourceStep3, idx3 in *.
    repeat rewrite (term_rename_add_eq_iterTermRenameSucc 3) in h.
    exact h.
  }
  assert (hdiv : BProv Ax_s C
      (div2StepTermAt (tVar 2) (tVar 1) (tVar 0))).
  { exact (BProv_andE2 Ax_s C _ _ htail). }
  assert (hprefixC : BProv Ax_s C
      (betaPrependPrefixTermAt sourceCode3 sourceStep3 head3
        targetCode3 targetStep3 (tSucc (tSucc last3)))).
  {
    pose proof (BProv_lift_three_contexts_of_sentences
      Ax_s sentence_ax_s G (pEx (pEx body)) (pEx body) body
      _ hprefix) as h.
    repeat rewrite rename_betaPrependPrefixTermAt in h.
    unfold C, sourceCode3, sourceStep3, head3,
      targetCode3, targetStep3, last3.
    exact h.
  }
  assert (hleC : BProv Ax_s C (leTermAt idx3 last3)).
  {
    pose proof (BProv_lift_three_contexts_of_sentences
      Ax_s sentence_ax_s G (pEx (pEx body)) (pEx body) body
      _ hle) as h.
    repeat rewrite rename_leTermAt in h.
    unfold C, idx3, last3.
    exact h.
  }
  pose proof
    (BProv_Ax_s_betaPrependPrefixTermAt_stepWitness_succ_of_components
      C sourceCode3 sourceStep3 head3 targetCode3 targetStep3
      last3 idx3 (tVar 2) (tVar 1) (tVar 0)
      hprefixC hleC hcur hnext hdiv) as hshifted.
  unfold target.
  repeat rewrite rename_S_betaDiv2StepWitnessTermAt.
  unfold C, idx3, targetCode3, targetStep3.
  exact hshifted.
Qed.

Lemma subst_div2StepTermAt : forall sigma value half bit,
  subst sigma (div2StepTermAt value half bit) =
    div2StepTermAt
      (Term.subst sigma value)
      (Term.subst sigma half)
      (Term.subst sigma bit).
Proof.
  intros sigma value half bit.
  unfold div2StepTermAt, boolTermAt.
  cbn [subst].
  reflexivity.
Qed.

Lemma rename_div2StepTermAt : forall r value half bit,
  rename r (div2StepTermAt value half bit) =
    div2StepTermAt
      (Term.rename r value)
      (Term.rename r half)
      (Term.rename r bit).
Proof.
  intros r value half bit.
  rename_from_subst subst_div2StepTermAt.
Qed.

Lemma rename_hfMemTermAt_zero_up : forall r setCode,
  rename (up r) (hfMemTermAt 0 setCode) =
    hfMemTermAt 0 (Term.rename (up r) setCode).
Proof.
  intros r setCode.
  unfold hfMemTermAt, betaTermAtConstIdx, betaTermAt, remTermAt,
    ltTermAt, betaDiv2StepsThroughAt, betaDiv2StepWitnessAt,
    betaDiv2BitAt, betaAtSuccIdx, betaAt, remAt, ltAt, leAt,
    div2StepAt, boolAt, zeroAt, oneAt, eqConstAt, betaModTerm.
  simpl.
  repeat rewrite Term.rename_comp.
  reflexivity.
Qed.

Lemma subst_betaDiv2StepWitnessTermAt :
  forall sigma code step idx,
  subst sigma (betaDiv2StepWitnessTermAt code step idx) =
    betaDiv2StepWitnessTermAt
      (Term.subst sigma code)
      (Term.subst sigma step)
      (Term.subst sigma idx).
Proof.
  intros sigma code step idx.
  assert (hshift3 : forall t,
      Term.subst
          (Term.upSubst (Term.upSubst (Term.upSubst sigma)))
          (Term.rename (fun n => n + 3) t) =
        Term.rename (fun n => n + 3) (Term.subst sigma t)).
  {
    intro t.
    change
      (Term.subst (iterUpSubst 3 sigma)
          (Term.rename (fun n => n + 3) t) =
        Term.rename (fun n => n + 3) (Term.subst sigma t)).
    apply term_subst_iterUpSubst_rename_add.
  }
  unfold betaDiv2StepWitnessTermAt.
  cbn [subst].
  rewrite !subst_betaTermTermAt.
  rewrite subst_div2StepTermAt.
  rewrite !hshift3.
  simpl.
  rewrite hshift3.
  reflexivity.
Qed.

Lemma rename_betaDiv2StepWitnessTermAt :
  forall r code step idx,
  rename r (betaDiv2StepWitnessTermAt code step idx) =
    betaDiv2StepWitnessTermAt
      (Term.rename r code) (Term.rename r step) (Term.rename r idx).
Proof.
  intros r code step idx.
  rename_from_subst subst_betaDiv2StepWitnessTermAt.
Qed.

Lemma subst_betaDiv2StepsThroughTermTermAt :
  forall sigma code step last,
  subst sigma (betaDiv2StepsThroughTermTermAt code step last) =
    betaDiv2StepsThroughTermTermAt
      (Term.subst sigma code)
      (Term.subst sigma step)
      (Term.subst sigma last).
Proof.
  intros sigma code step last.
  unfold betaDiv2StepsThroughTermTermAt.
  cbn [subst].
  rewrite subst_leTermAt.
  rewrite subst_betaDiv2StepWitnessTermAt.
  repeat rewrite Term.subst_rename_succ_up.
  reflexivity.
Qed.

Lemma rename_betaDiv2StepsThroughTermTermAt :
  forall r code step last,
  rename r (betaDiv2StepsThroughTermTermAt code step last) =
    betaDiv2StepsThroughTermTermAt
      (Term.rename r code) (Term.rename r step) (Term.rename r last).
Proof.
  intros r code step last.
  rename_from_subst subst_betaDiv2StepsThroughTermTermAt.
Qed.

(** Package the prepended head step and all transported source steps.  A
    direct PA induction on the target index avoids the predecessor-opening
    detour used by the Lean proof. *)
Lemma BProv_Ax_s_betaPrependPrefixTermAt_stepsThrough_of_sourceSteps :
  forall G sourceCode sourceStep head sourceHead headBit targetCode
    targetStep last,
  BProv Ax_s G
    (betaPrependPrefixTermAt sourceCode sourceStep head
      targetCode targetStep (tSucc (tSucc last))) ->
  BProv Ax_s G
    (betaTermTermAt sourceHead sourceCode sourceStep tZero) ->
  BProv Ax_s G (div2StepTermAt head sourceHead headBit) ->
  BProv Ax_s G
    (betaDiv2StepsThroughTermTermAt sourceCode sourceStep last) ->
  BProv Ax_s G
    (betaDiv2StepsThroughTermTermAt
      targetCode targetStep (tSucc last)).
Proof.
  intros G sourceCode sourceStep head sourceHead headBit targetCode
    targetStep last hprefix hsourceHead hheadDiv hsourceSteps.
  set (phi := pImp
    (leTermAt (tVar 0) (tSucc (Term.rename S last)))
    (betaDiv2StepWitnessTermAt
      (Term.rename S targetCode)
      (Term.rename S targetStep)
      (tVar 0))).
  pose proof
    (BProv_Ax_s_betaPrependPrefixTermAt_step_zero_of_components
      G sourceCode sourceStep head sourceHead headBit targetCode
      targetStep (tSucc (tSucc last)) hprefix
      (BProv_Ax_s_ltTermAt_zero_succ G (tSucc last))
      hsourceHead hheadDiv) as hstepZero.
  assert (hzeroImp : BProv Ax_s G
      (pImp (leTermAt tZero (tSucc last))
        (betaDiv2StepWitnessTermAt targetCode targetStep tZero))).
  {
    apply (BProv_impI Ax_s G _ _).
    exact (BProv_context_cons Ax_s G
      (leTermAt tZero (tSucc last)) _ hstepZero).
  }
  assert (hzero : BProv Ax_s G (subst substZero phi)).
  {
    unfold phi.
    cbn [subst].
    rewrite subst_leTermAt.
    rewrite subst_betaDiv2StepWitnessTermAt.
    simpl.
    repeat rewrite term_substZero_rename_succ.
    exact hzeroImp.
  }
  pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
    hprefix S) as hprefixRen.
  rewrite rename_betaPrependPrefixTermAt in hprefixRen.
  pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
    hsourceSteps S) as hstepsRen.
  rewrite rename_betaDiv2StepsThroughTermTermAt in hstepsRen.
  set (C := phi :: map (rename S) G).
  assert (hsuccBody : BProv Ax_s C (subst substSuccVar phi)).
  {
    set (sourceCode1 := Term.rename S sourceCode).
    set (sourceStep1 := Term.rename S sourceStep).
    set (head1 := Term.rename S head).
    set (targetCode1 := Term.rename S targetCode).
    set (targetStep1 := Term.rename S targetStep).
    set (last1 := Term.rename S last).
    set (leSucc := leTermAt (tSucc (tVar 0)) (tSucc last1)).
    set (targetWitness := betaDiv2StepWitnessTermAt
      targetCode1 targetStep1 (tSucc (tVar 0))).
    set (D := leSucc :: C).
    assert (hleSucc : BProv Ax_s D leSucc).
    { apply BProv_ass. unfold D. simpl. left. reflexivity. }
    pose proof (BProv_Ax_s_ltTermAt_of_succ_leTermAt
      D (tVar 0) (tSucc last1) hleSucc) as hpredLt.
    pose proof (BProv_Ax_s_leTermAt_of_ltTermAt_succ_right
      D (tVar 0) last1 hpredLt) as hpredLe.
    assert (hprefixC : BProv Ax_s C
        (betaPrependPrefixTermAt sourceCode1 sourceStep1 head1
          targetCode1 targetStep1 (tSucc (tSucc last1)))).
    {
      exact (BProv_context_cons Ax_s (map (rename S) G)
        phi _ hprefixRen).
    }
    assert (hprefixD : BProv Ax_s D
        (betaPrependPrefixTermAt sourceCode1 sourceStep1 head1
          targetCode1 targetStep1 (tSucc (tSucc last1)))).
    { exact (BProv_context_cons Ax_s C leSucc _ hprefixC). }
    assert (hstepsC : BProv Ax_s C
        (betaDiv2StepsThroughTermTermAt
          sourceCode1 sourceStep1 last1)).
    {
      exact (BProv_context_cons Ax_s (map (rename S) G)
        phi _ hstepsRen).
    }
    assert (hstepsD : BProv Ax_s D
        (betaDiv2StepsThroughTermTermAt
          sourceCode1 sourceStep1 last1)).
    { exact (BProv_context_cons Ax_s C leSucc _ hstepsC). }
    pose proof
      (BProv_Ax_s_betaDiv2StepsThroughTermTermAt_step_of_leTerm
        D sourceCode1 sourceStep1 (tVar 0) last1
        hstepsD hpredLe) as hsourceWitness.
    pose proof
      (BProv_Ax_s_betaPrependPrefixTermAt_stepWitness_succ_of_sourceWitness
        D sourceCode1 sourceStep1 head1 targetCode1 targetStep1
        last1 (tVar 0) hprefixD hpredLe hsourceWitness)
      as htarget.
    assert (himp : BProv Ax_s C (pImp leSucc targetWitness)).
    {
      unfold D in htarget.
      exact (BProv_impI Ax_s C leSucc targetWitness htarget).
    }
    unfold phi.
    cbn [subst].
    rewrite subst_leTermAt.
    rewrite subst_betaDiv2StepWitnessTermAt.
    simpl.
    repeat rewrite term_substSuccVar_rename_succ.
    unfold leSucc, targetWitness, sourceCode1, sourceStep1, head1,
      targetCode1, targetStep1, last1 in himp.
    exact himp.
  }
  assert (hsuccImp : BProv Ax_s (map (rename S) G)
      (pImp phi (subst substSuccVar phi))).
  {
    unfold C in hsuccBody.
    exact (BProv_impI Ax_s (map (rename S) G)
      phi (subst substSuccVar phi) hsuccBody).
  }
  pose proof (BProv_allI_of_sentences Ax_s G _
    sentence_ax_s hsuccImp) as hsuccAll.
  pose proof (BProv_Ax_s_induction_rule G phi hzero hsuccAll) as hall.
  unfold betaDiv2StepsThroughTermTermAt, phi.
  exact hall.
Qed.

Lemma subst_betaDiv2BitTermAt :
  forall sigma bit code step idx,
  subst sigma (betaDiv2BitTermAt bit code step idx) =
    betaDiv2BitTermAt
      (Term.subst sigma bit)
      (Term.subst sigma code)
      (Term.subst sigma step)
      (Term.subst sigma idx).
Proof.
  intros sigma bit code step idx.
  unfold betaDiv2BitTermAt.
  cbn [subst].
  rewrite !subst_betaTermTermAt.
  rewrite subst_div2StepTermAt.
  rewrite !term_subst_up_up_rename_add_two.
  simpl.
  rewrite term_subst_up_up_rename_add_two.
  reflexivity.
Qed.

Lemma rename_betaDiv2BitTermAt :
  forall r bit code step idx,
  rename r (betaDiv2BitTermAt bit code step idx) =
    betaDiv2BitTermAt
      (Term.rename r bit) (Term.rename r code)
      (Term.rename r step) (Term.rename r idx).
Proof.
  intros r bit code step idx.
  rename_from_subst subst_betaDiv2BitTermAt.
Qed.

Lemma subst_betaDiv2BitOneTermExAt :
  forall sigma code step idx,
  subst sigma (betaDiv2BitOneTermExAt code step idx) =
    betaDiv2BitOneTermExAt
      (Term.subst sigma code)
      (Term.subst sigma step)
      (Term.subst sigma idx).
Proof.
  intros sigma code step idx.
  unfold betaDiv2BitOneTermExAt.
  cbn [subst].
  rewrite subst_betaDiv2BitTermAt.
  repeat rewrite Term.subst_rename_succ_up.
  reflexivity.
Qed.

Lemma rename_betaDiv2BitOneTermExAt :
  forall r code step idx,
  rename r (betaDiv2BitOneTermExAt code step idx) =
    betaDiv2BitOneTermExAt
      (Term.rename r code) (Term.rename r step) (Term.rename r idx).
Proof.
  intros r code step idx.
  rename_from_subst subst_betaDiv2BitOneTermExAt.
Qed.

Lemma BProv_Ax_s_betaDiv2BitOneTermExAt_of_term :
  forall G bit code step idx,
  BProv Ax_s G (pEq bit (tSucc tZero)) ->
  BProv Ax_s G (betaDiv2BitTermAt bit code step idx) ->
  BProv Ax_s G (betaDiv2BitOneTermExAt code step idx).
Proof.
  intros G bit code step idx hone hbit.
  unfold betaDiv2BitOneTermExAt.
  apply (BProv_exI Ax_s G _ bit).
  cbn [subst].
  rewrite subst_betaDiv2BitTermAt.
  simpl.
  repeat rewrite term_subst_instTerm_rename_succ.
  exact (BProv_andI Ax_s G _ _ hone hbit).
Qed.

Lemma BProv_Ax_s_betaUnshiftPrefixTermAt_bitTerm_succ_of_components :
  forall G sourceCode sourceStep targetCode targetStep bound idx cur next bit,
  BProv Ax_s G
    (betaUnshiftPrefixTermAt
      sourceCode sourceStep targetCode targetStep bound) ->
  BProv Ax_s G (ltTermAt idx bound) ->
  BProv Ax_s G (ltTermAt (tSucc idx) bound) ->
  BProv Ax_s G (betaTermTermAt cur sourceCode sourceStep idx) ->
  BProv Ax_s G
    (betaTermTermAt next sourceCode sourceStep (tSucc idx)) ->
  BProv Ax_s G (div2StepTermAt cur next bit) ->
  BProv Ax_s G
    (betaDiv2BitTermAt bit targetCode targetStep (tSucc idx)).
Proof.
  intros G sourceCode sourceStep targetCode targetStep bound idx cur
    next bit hprefix hltCur hltNext hcur hnext hdiv.
  pose proof (BProv_Ax_s_betaUnshiftPrefixTermAt_entry_of_ltTerm
    G sourceCode sourceStep targetCode targetStep bound idx cur
    hprefix hltCur hcur) as hcurTarget.
  pose proof (BProv_Ax_s_betaUnshiftPrefixTermAt_entry_of_ltTerm
    G sourceCode sourceStep targetCode targetStep bound (tSucc idx) next
    hprefix hltNext hnext) as hnextTarget.
  exact (BProv_Ax_s_betaDiv2BitTermAt_of_components
    G bit targetCode targetStep (tSucc idx) cur next
    hcurTarget hnextTarget hdiv).
Qed.

Lemma BProv_Ax_s_betaPrependPrefixTermAt_bitTerm_succ_of_components :
  forall G sourceCode sourceStep head targetCode targetStep last idx cur
    next bit,
  BProv Ax_s G
    (betaPrependPrefixTermAt sourceCode sourceStep head
      targetCode targetStep (tSucc (tSucc last))) ->
  BProv Ax_s G (leTermAt idx last) ->
  BProv Ax_s G (betaTermTermAt cur sourceCode sourceStep idx) ->
  BProv Ax_s G
    (betaTermTermAt next sourceCode sourceStep (tSucc idx)) ->
  BProv Ax_s G (div2StepTermAt cur next bit) ->
  BProv Ax_s G
    (betaDiv2BitTermAt bit targetCode targetStep (tSucc idx)).
Proof.
  intros G sourceCode sourceStep head targetCode targetStep last idx
    cur next bit hprefix hle hcur hnext hdiv.
  pose proof
    (BProv_Ax_s_betaUnshiftPrefixTermAt_of_betaPrependPrefixTermAt
      G sourceCode sourceStep head targetCode targetStep
      (tSucc (tSucc last)) hprefix) as hunshift.
  pose proof (BProv_Ax_s_leTermAt_self_succ G last) as hlastSucc.
  pose proof (BProv_Ax_s_leTermAt_trans
    G idx last (tSucc last) hle hlastSucc) as hidxLeSucc.
  pose proof (BProv_Ax_s_ltTermAt_succ_right_of_leTermAt
    G idx (tSucc last) hidxLeSucc) as hltCur.
  pose proof (BProv_Ax_s_leTermAt_succ_succ
    G idx last hle) as hsuccLe.
  pose proof (BProv_Ax_s_ltTermAt_succ_right_of_leTermAt
    G (tSucc idx) (tSucc last) hsuccLe) as hltNext.
  exact (BProv_Ax_s_betaUnshiftPrefixTermAt_bitTerm_succ_of_components
    G sourceCode sourceStep targetCode targetStep
    (tSucc (tSucc last)) idx cur next bit
    hunshift hltCur hltNext hcur hnext hdiv).
Qed.

Lemma BProv_Ax_s_betaPrependPrefixTermAt_bitTerm_succ_of_sourceBit :
  forall G sourceCode sourceStep head targetCode targetStep last idx bit,
  BProv Ax_s G
    (betaPrependPrefixTermAt sourceCode sourceStep head
      targetCode targetStep (tSucc (tSucc last))) ->
  BProv Ax_s G (leTermAt idx last) ->
  BProv Ax_s G (betaDiv2BitTermAt bit sourceCode sourceStep idx) ->
  BProv Ax_s G
    (betaDiv2BitTermAt bit targetCode targetStep (tSucc idx)).
Proof.
  intros G sourceCode sourceStep head targetCode targetStep last idx bit
    hprefix hle hbit.
  set (target :=
    betaDiv2BitTermAt bit targetCode targetStep (tSucc idx)).
  set (body := pAnd
    (betaTermTermAt (tVar 1)
      (Term.rename (fun n => n + 2) sourceCode)
      (Term.rename (fun n => n + 2) sourceStep)
      (Term.rename (fun n => n + 2) idx))
    (pAnd
      (betaTermTermAt (tVar 0)
        (Term.rename (fun n => n + 2) sourceCode)
        (Term.rename (fun n => n + 2) sourceStep)
        (tSucc (Term.rename (fun n => n + 2) idx)))
      (div2StepTermAt (tVar 1) (tVar 0)
        (Term.rename (fun n => n + 2) bit)))).
  assert (hbit' : BProv Ax_s G (pEx (pEx body))).
  { unfold betaDiv2BitTermAt in hbit. exact hbit. }
  apply (BProv_two_exE_of_sentences
    Ax_s sentence_ax_s G body target hbit').
  set (C := body :: map (rename S)
    (pEx body :: map (rename S) G)).
  change (BProv Ax_s C (rename S (rename S target))).
  set (sourceCode2 := Term.rename S (Term.rename S sourceCode)).
  set (sourceStep2 := Term.rename S (Term.rename S sourceStep)).
  set (head2 := Term.rename S (Term.rename S head)).
  set (targetCode2 := Term.rename S (Term.rename S targetCode)).
  set (targetStep2 := Term.rename S (Term.rename S targetStep)).
  set (last2 := Term.rename S (Term.rename S last)).
  set (idx2 := Term.rename S (Term.rename S idx)).
  set (bit2 := Term.rename S (Term.rename S bit)).
  assert (hbody : BProv Ax_s C body).
  { apply BProv_ass. unfold C. simpl. left. reflexivity. }
  assert (hcur : BProv Ax_s C
      (betaTermTermAt (tVar 1) sourceCode2 sourceStep2 idx2)).
  {
    pose proof (BProv_andE1 Ax_s C _ _ hbody) as h.
    unfold body, sourceCode2, sourceStep2, idx2 in *.
    repeat rewrite (term_rename_add_eq_iterTermRenameSucc 2) in h.
    exact h.
  }
  pose proof (BProv_andE2 Ax_s C _ _ hbody) as htail.
  assert (hnext : BProv Ax_s C
      (betaTermTermAt (tVar 0) sourceCode2 sourceStep2
        (tSucc idx2))).
  {
    pose proof (BProv_andE1 Ax_s C _ _ htail) as h.
    unfold body, sourceCode2, sourceStep2, idx2 in *.
    repeat rewrite (term_rename_add_eq_iterTermRenameSucc 2) in h.
    exact h.
  }
  assert (hdiv : BProv Ax_s C
      (div2StepTermAt (tVar 1) (tVar 0) bit2)).
  {
    pose proof (BProv_andE2 Ax_s C _ _ htail) as h.
    unfold body, bit2 in *.
    rewrite (term_rename_add_eq_iterTermRenameSucc 2) in h.
    exact h.
  }
  assert (hprefixC : BProv Ax_s C
      (betaPrependPrefixTermAt sourceCode2 sourceStep2 head2
        targetCode2 targetStep2 (tSucc (tSucc last2)))).
  {
    pose proof (BProv_lift_two_opened_of_sentences
      Ax_s sentence_ax_s G body _ hprefix) as h.
    repeat rewrite rename_betaPrependPrefixTermAt in h.
    unfold C, sourceCode2, sourceStep2, head2,
      targetCode2, targetStep2, last2.
    exact h.
  }
  assert (hleC : BProv Ax_s C (leTermAt idx2 last2)).
  {
    pose proof (BProv_lift_two_opened_of_sentences
      Ax_s sentence_ax_s G body _ hle) as h.
    repeat rewrite rename_leTermAt in h.
    unfold C, idx2, last2.
    exact h.
  }
  pose proof
    (BProv_Ax_s_betaPrependPrefixTermAt_bitTerm_succ_of_components
      C sourceCode2 sourceStep2 head2 targetCode2 targetStep2
      last2 idx2 (tVar 1) (tVar 0) bit2
      hprefixC hleC hcur hnext hdiv) as hshifted.
  unfold target.
  repeat rewrite rename_S_betaDiv2BitTermAt.
  unfold C, idx2, bit2, targetCode2, targetStep2.
  exact hshifted.
Qed.

Lemma BProv_Ax_s_betaPrependPrefixTermAt_bitOneEx_succ_of_sourceBitOneEx :
  forall G sourceCode sourceStep head targetCode targetStep last idx,
  BProv Ax_s G
    (betaPrependPrefixTermAt sourceCode sourceStep head
      targetCode targetStep (tSucc (tSucc last))) ->
  BProv Ax_s G (leTermAt idx last) ->
  BProv Ax_s G (betaDiv2BitOneTermExAt sourceCode sourceStep idx) ->
  BProv Ax_s G
    (betaDiv2BitOneTermExAt targetCode targetStep (tSucc idx)).
Proof.
  intros G sourceCode sourceStep head targetCode targetStep last idx
    hprefix hle hbitEx.
  set (target := betaDiv2BitOneTermExAt
    targetCode targetStep (tSucc idx)).
  set (body := pAnd
    (oneAt 0)
    (betaDiv2BitTermAt (tVar 0)
      (Term.rename S sourceCode)
      (Term.rename S sourceStep)
      (Term.rename S idx))).
  assert (hbitEx' : BProv Ax_s G (pEx body)).
  { unfold betaDiv2BitOneTermExAt in hbitEx. exact hbitEx. }
  assert (hopened : BProv Ax_s (body :: map (rename S) G)
      (rename S target)).
  {
    set (C := body :: map (rename S) G).
    set (sourceCode1 := Term.rename S sourceCode).
    set (sourceStep1 := Term.rename S sourceStep).
    set (head1 := Term.rename S head).
    set (targetCode1 := Term.rename S targetCode).
    set (targetStep1 := Term.rename S targetStep).
    set (last1 := Term.rename S last).
    set (idx1 := Term.rename S idx).
    assert (hbody : BProv Ax_s C body).
    { apply BProv_ass. unfold C. simpl. left. reflexivity. }
    pose proof (BProv_andE1 Ax_s C _ _ hbody) as hone.
    pose proof (BProv_andE2 Ax_s C _ _ hbody) as hsourceBit.
    pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
      hprefix S) as hprefixRen.
    rewrite rename_betaPrependPrefixTermAt in hprefixRen.
    assert (hprefixC : BProv Ax_s C
        (betaPrependPrefixTermAt sourceCode1 sourceStep1 head1
          targetCode1 targetStep1 (tSucc (tSucc last1)))).
    {
      exact (BProv_context_cons Ax_s (map (rename S) G)
        body _ hprefixRen).
    }
    pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
      hle S) as hleRen.
    rewrite rename_leTermAt in hleRen.
    assert (hleC : BProv Ax_s C (leTermAt idx1 last1)).
    {
      exact (BProv_context_cons Ax_s (map (rename S) G)
        body _ hleRen).
    }
    assert (hsourceBitC : BProv Ax_s C
        (betaDiv2BitTermAt (tVar 0) sourceCode1 sourceStep1 idx1)).
    { unfold body, sourceCode1, sourceStep1, idx1 in hsourceBit.
      exact hsourceBit. }
    pose proof
      (BProv_Ax_s_betaPrependPrefixTermAt_bitTerm_succ_of_sourceBit
        C sourceCode1 sourceStep1 head1 targetCode1 targetStep1
        last1 idx1 (tVar 0) hprefixC hleC hsourceBitC)
      as htargetBit.
    pose proof (BProv_Ax_s_betaDiv2BitOneTermExAt_of_term
      C (tVar 0) targetCode1 targetStep1 (tSucc idx1)
      hone htargetBit) as htargetEx.
    unfold target.
    rewrite rename_betaDiv2BitOneTermExAt.
    unfold C, targetCode1, targetStep1, idx1.
    exact htargetEx.
  }
  unfold target.
  exact (BProv_exE_of_sentences Ax_s G body
    (betaDiv2BitOneTermExAt targetCode targetStep (tSucc idx))
    sentence_ax_s hbitEx' hopened).
Qed.

(** Membership introduction with the element/set substitution performed before
    the internally chosen beta-code witnesses. *)
Lemma BProv_Ax_s_subst_hfMemTermAt_of_postsubst_components :
  forall G elem (setCode codeTerm stepTerm : term)
    (sigma : nat -> term),
  BProv Ax_s G
    (subst (instTerm stepTerm)
      (subst (Term.upSubst (instTerm codeTerm))
        (subst (Term.upSubst (Term.upSubst sigma))
          (betaTermAtConstIdx
            (Term.rename (fun n => n + 2) setCode) 1 0 0)))) ->
  BProv Ax_s G
    (subst (instTerm stepTerm)
      (subst (Term.upSubst (instTerm codeTerm))
        (subst (Term.upSubst (Term.upSubst sigma))
          (betaDiv2StepsThroughAt 1 0 (elem + 2))))) ->
  BProv Ax_s G
    (subst (instTerm stepTerm)
      (subst (Term.upSubst (instTerm codeTerm))
        (subst (Term.upSubst (Term.upSubst sigma))
          (pEx (pAnd (oneAt 0)
            (betaDiv2BitAt 0 2 1 (elem + 3))))))) ->
  BProv Ax_s G (subst sigma (hfMemTermAt elem setCode)).
Proof.
  intros G elem setCode codeTerm stepTerm sigma hentry hsteps hbitEx.
  set (bitEx := pEx (pAnd (oneAt 0)
    (betaDiv2BitAt 0 2 1 (elem + 3)))).
  set (tail := pAnd (betaDiv2StepsThroughAt 1 0 (elem + 2)) bitEx).
  set (body := pAnd
    (betaTermAtConstIdx
      (Term.rename (fun n => n + 2) setCode) 1 0 0)
    tail).
  assert (htail : BProv Ax_s G
      (subst (instTerm stepTerm)
        (subst (Term.upSubst (instTerm codeTerm))
          (subst (Term.upSubst (Term.upSubst sigma)) tail)))).
  {
    unfold tail, bitEx.
    simpl.
    exact (BProv_andI Ax_s G _ _ hsteps hbitEx).
  }
  assert (hbody : BProv Ax_s G
      (subst (instTerm stepTerm)
        (subst (Term.upSubst (instTerm codeTerm))
          (subst (Term.upSubst (Term.upSubst sigma)) body)))).
  {
    unfold body, tail, bitEx in *.
    simpl in htail |- *.
    exact (BProv_andI Ax_s G _ _ hentry htail).
  }
  assert (hstepEx : BProv Ax_s G
      (subst (instTerm codeTerm)
        (subst (Term.upSubst sigma) (pEx body)))).
  {
    pose proof (BProv_exI Ax_s G
      (subst (Term.upSubst (instTerm codeTerm))
        (subst (Term.upSubst (Term.upSubst sigma)) body))
      stepTerm hbody) as hex.
    replace (subst (instTerm codeTerm)
        (subst (Term.upSubst sigma) (pEx body)))
      with (pEx
        (subst (Term.upSubst (instTerm codeTerm))
          (subst (Term.upSubst (Term.upSubst sigma)) body))).
    - exact hex.
    - simpl. reflexivity.
  }
  pose proof (BProv_exI Ax_s G
    (subst (Term.upSubst sigma) (pEx body))
    codeTerm hstepEx) as hcodeEx.
  replace (subst sigma (hfMemTermAt elem setCode))
    with (pEx (subst (Term.upSubst sigma) (pEx body))).
  - exact hcodeEx.
  - unfold hfMemTermAt, body, tail, bitEx.
    replace (elem + 2) with (S (S elem)) by lia.
    replace (elem + 3) with (S (S (S elem))) by lia.
    replace (Term.rename (fun n => n + 2) setCode)
      with (Term.rename S (Term.rename S setCode))
      by (rewrite Term.rename_comp;
          apply Term.rename_ext; intro n; lia).
    reflexivity.
Qed.

(** Turn a term-parametric bounded halving trace back into the legacy
    slot-indexed trace used inside [hfMemTermAt].  Keeping this conversion
    separate makes membership packaging below a three-line composition. *)
Lemma BProv_Ax_s_subst_betaDiv2StepsThroughAt_of_term_trace :
  forall G (sigma : nat -> term) code step last,
  BProv Ax_s G
    (betaDiv2StepsThroughTermTermAt
      (sigma code) (sigma step) (sigma last)) ->
  BProv Ax_s G
    (subst sigma (betaDiv2StepsThroughAt code step last)).
Proof.
  intros G sigma code step last hsteps.
  set (leHyp := subst (Term.upSubst sigma) (leAt 0 (S last))).
  set (point := subst (Term.upSubst sigma)
    (betaDiv2StepWitnessAt (S code) (S step) 0)).
  set (body := pImp leHyp point).
  assert (hbody : BProv Ax_s (map (rename S) G) body).
  {
    set (C := leHyp :: map (rename S) G).
    assert (hleRaw : BProv Ax_s C leHyp).
    { apply BProv_ass. unfold C. simpl. left. reflexivity. }
    assert (hle : BProv Ax_s C
        (leTermAt (tVar 0) (Term.rename S (sigma last)))).
    {
      unfold leHyp, leAt, leTermAt in hleRaw |- *.
      simpl in hleRaw |- *.
      exact hleRaw.
    }
    pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
      hsteps S) as hstepsRen.
    rewrite rename_betaDiv2StepsThroughTermTermAt in hstepsRen.
    assert (hstepsC : BProv Ax_s C
        (betaDiv2StepsThroughTermTermAt
          (Term.rename S (sigma code))
          (Term.rename S (sigma step))
          (Term.rename S (sigma last)))).
    {
      exact (BProv_context_cons Ax_s (map (rename S) G)
        leHyp _ hstepsRen).
    }
    pose proof
      (BProv_Ax_s_betaDiv2StepsThroughTermTermAt_step_of_leTerm
        C (Term.rename S (sigma code)) (Term.rename S (sigma step))
        (tVar 0) (Term.rename S (sigma last)) hstepsC hle)
      as hpointTerm.
    pose proof
      (BProv_Ax_s_betaDiv2StepWitnessTermSuccIdxAt_of_termAt
        C (Term.rename S (sigma code)) (Term.rename S (sigma step))
        0 hpointTerm) as hpointWrapped.
    assert (hpoint : BProv Ax_s C point).
    {
      replace point with
        (betaDiv2StepWitnessTermSuccIdxAt
          (Term.rename S (sigma code))
          (Term.rename S (sigma step)) 0).
      - exact hpointWrapped.
      - unfold point, betaDiv2StepWitnessTermSuccIdxAt,
          betaDiv2StepWitnessAt, betaTermTermAtSuccIdx,
          betaTermTermAt, betaAtSuccIdx, betaAt, remTermTermAt,
          remAt, div2StepTermAt, div2StepAt, boolTermAt, boolAt,
          ltTermAt, ltAt, betaModTermTerm, betaModTerm,
          zeroAt, oneAt, eqConstAt.
        simpl.
        repeat rewrite term_rename_up_succ_rename_succ.
        repeat rewrite Term.rename_comp.
        replace
          (Term.rename (fun n => S (S n + 3)) (sigma step))
          with
          (Term.rename (fun n => S (S (S (S (S n)))))
            (sigma step))
          by (apply Term.rename_ext; intro n; lia).
        replace
          (Term.rename (fun n => S (S (S n + 3))) (sigma code))
          with
          (Term.rename (fun n => S (S (S (S (S (S n))))))
            (sigma code))
          by (apply Term.rename_ext; intro n; lia).
        replace
          (Term.rename (fun n => S (S (S n + 3))) (sigma step))
          with
          (Term.rename (fun n => S (S (S (S (S (S n))))))
            (sigma step))
          by (apply Term.rename_ext; intro n; lia).
        replace
          (Term.rename (fun n => S (S (S (S n + 3))))
            (sigma code))
          with
          (Term.rename
            (fun n => S (S (S (S (S (S (S n)))))))
            (sigma code))
          by (apply Term.rename_ext; intro n; lia).
        reflexivity.
    }
    unfold body.
    exact (BProv_impI Ax_s (map (rename S) G) leHyp point hpoint).
  }
  pose proof (BProv_allI_of_sentences Ax_s G body
    sentence_ax_s hbody) as hall.
  replace (subst sigma (betaDiv2StepsThroughAt code step last))
    with (pAll body).
  - exact hall.
  - unfold betaDiv2StepsThroughAt, body, leHyp, point.
    simpl.
    reflexivity.
Qed.

(** Package a fully term-parametric trace as membership at a term-valued
    element index. *)
Lemma BProv_Ax_s_subst_hfMemTermAt_zero_of_term_components :
  forall G (setTerm codeTerm stepTerm elemTerm : term),
  BProv Ax_s G
    (betaTermTermAt setTerm codeTerm stepTerm tZero) ->
  BProv Ax_s G
    (betaDiv2StepsThroughTermTermAt codeTerm stepTerm elemTerm) ->
  BProv Ax_s G
    (betaDiv2BitOneTermExAt codeTerm stepTerm elemTerm) ->
  BProv Ax_s G
    (subst (instTerm elemTerm)
      (hfMemTermAt 0 (Term.rename S setTerm))).
Proof.
  intros G setTerm codeTerm stepTerm elemTerm hentry hsteps hbitEx.
  set (sigma := instTerm elemTerm).
  set (setLift := Term.rename S setTerm).
  set (tau := fun n =>
    Term.subst (instTerm stepTerm)
      (Term.subst (Term.upSubst (instTerm codeTerm))
        (Term.upSubst (Term.upSubst sigma) n))).
  pose proof (BProv_Ax_s_betaTermTermAtConstIdx_of_beta
    G setTerm codeTerm stepTerm 0 hentry) as hentryConst.
  assert (hentry' : BProv Ax_s G
      (subst (instTerm stepTerm)
        (subst (Term.upSubst (instTerm codeTerm))
          (subst (Term.upSubst (Term.upSubst sigma))
            (betaTermAtConstIdx
              (Term.rename (fun n => n + 2) setLift) 1 0 0))))).
  {
    replace
      (subst (instTerm stepTerm)
        (subst (Term.upSubst (instTerm codeTerm))
          (subst (Term.upSubst (Term.upSubst sigma))
            (betaTermAtConstIdx
              (Term.rename (fun n => n + 2) setLift) 1 0 0))))
      with (betaTermTermAtConstIdx
        setTerm codeTerm stepTerm 0).
    - exact hentryConst.
    - unfold sigma, setLift, betaTermTermAtConstIdx,
        betaTermAtConstIdx, betaTermAt, betaTermTermAt,
        remTermAt, remTermTermAt, ltTermAt,
        betaModTerm, betaModTermTerm, eqConstAt.
      simpl.
      normalize_subst_rename_comp.
      replace (Term.rename (fun n => S n + 2) setTerm)
        with (Term.rename (fun n => S (S (S n))) setTerm)
        by (apply Term.rename_ext; intro n; lia).
      normalize_subst_rename.
      reflexivity.
  }
  assert (hstepsTau : BProv Ax_s G
      (betaDiv2StepsThroughTermTermAt (tau 1) (tau 0) (tau 2))).
  {
    replace (betaDiv2StepsThroughTermTermAt (tau 1) (tau 0) (tau 2))
      with (betaDiv2StepsThroughTermTermAt
        codeTerm stepTerm elemTerm).
    - exact hsteps.
    - unfold tau, sigma.
      simpl.
      repeat rewrite term_subst_instTerm_rename_succ.
      repeat rewrite term_subst_instTerm_rename_two_succ.
      replace (Term.rename S (Term.rename S elemTerm))
        with (Term.rename (fun n => n + 2) elemTerm)
        by (rewrite Term.rename_comp;
            apply Term.rename_ext; intro n; lia).
      rewrite term_subst_two_instTerm_rename_add_two.
      reflexivity.
  }
  pose proof
    (BProv_Ax_s_subst_betaDiv2StepsThroughAt_of_term_trace
      G tau 1 0 2 hstepsTau) as hstepsLegacy.
  assert (hsteps' : BProv Ax_s G
      (subst (instTerm stepTerm)
        (subst (Term.upSubst (instTerm codeTerm))
          (subst (Term.upSubst (Term.upSubst sigma))
            (betaDiv2StepsThroughAt 1 0 (0 + 2)))))).
  {
    replace
      (subst (instTerm stepTerm)
        (subst (Term.upSubst (instTerm codeTerm))
          (subst (Term.upSubst (Term.upSubst sigma))
            (betaDiv2StepsThroughAt 1 0 (0 + 2)))))
      with (subst tau (betaDiv2StepsThroughAt 1 0 2)).
    - exact hstepsLegacy.
    - unfold tau. repeat rewrite subst_comp.
      apply subst_ext. intro n.
      exact (Term.subst_comp
        (Term.upSubst (Term.upSubst sigma) n)
        (Term.upSubst (instTerm codeTerm))
        (instTerm stepTerm)).
  }
  assert (hbitTau : BProv Ax_s G
      (betaDiv2BitOneTermExAt (tau 1) (tau 0) (tau 2))).
  {
    replace (betaDiv2BitOneTermExAt (tau 1) (tau 0) (tau 2))
      with (betaDiv2BitOneTermExAt codeTerm stepTerm elemTerm).
    - exact hbitEx.
    - unfold tau, sigma.
      simpl.
      repeat rewrite term_subst_instTerm_rename_succ.
      repeat rewrite term_subst_instTerm_rename_two_succ.
      replace (Term.rename S (Term.rename S elemTerm))
        with (Term.rename (fun n => n + 2) elemTerm)
        by (rewrite Term.rename_comp;
            apply Term.rename_ext; intro n; lia).
      rewrite term_subst_two_instTerm_rename_add_two.
      reflexivity.
  }
  pose proof
    (BProv_Ax_s_subst_bitOneEx_of_betaDiv2BitOneTermExAt
      G tau 1 0 2 hbitTau) as hbitLegacy.
  assert (hbitEx' : BProv Ax_s G
      (subst (instTerm stepTerm)
        (subst (Term.upSubst (instTerm codeTerm))
          (subst (Term.upSubst (Term.upSubst sigma))
            (pEx (pAnd (oneAt 0)
              (betaDiv2BitAt 0 2 1 (0 + 3)))))))).
  {
    replace
      (subst (instTerm stepTerm)
        (subst (Term.upSubst (instTerm codeTerm))
          (subst (Term.upSubst (Term.upSubst sigma))
            (pEx (pAnd (oneAt 0)
              (betaDiv2BitAt 0 2 1 (0 + 3)))))))
      with (subst tau
        (pEx (pAnd (oneAt 0) (betaDiv2BitAt 0 2 1 (2 + 1))))).
    - exact hbitLegacy.
    - unfold tau. repeat rewrite subst_comp.
      apply subst_ext. intro n.
      exact (Term.subst_comp
        (Term.upSubst (Term.upSubst sigma) n)
        (Term.upSubst (instTerm codeTerm))
        (instTerm stepTerm)).
  }
  unfold sigma, setLift in *.
  exact (BProv_Ax_s_subst_hfMemTermAt_of_postsubst_components
    G 0 (Term.rename S setTerm) codeTerm stepTerm
    (instTerm elemTerm) hentry' hsteps' hbitEx').
Qed.

Lemma BProv_Ax_s_betaPrependPrefixTermAt_succ_mem_of_source_trace :
  forall G sourceCode sourceStep head sourceHead headBit targetCode
    targetStep idx,
  BProv Ax_s G
    (betaPrependPrefixTermAt sourceCode sourceStep head
      targetCode targetStep (tSucc (tSucc idx))) ->
  BProv Ax_s G
    (betaTermTermAt sourceHead sourceCode sourceStep tZero) ->
  BProv Ax_s G (div2StepTermAt head sourceHead headBit) ->
  BProv Ax_s G
    (betaDiv2StepsThroughTermTermAt sourceCode sourceStep idx) ->
  BProv Ax_s G
    (betaDiv2BitOneTermExAt sourceCode sourceStep idx) ->
  BProv Ax_s G
    (subst (instTerm (tSucc idx))
      (hfMemTermAt 0 (Term.rename S head))).
Proof.
  intros G sourceCode sourceStep head sourceHead headBit targetCode
    targetStep idx hprefix hsourceHead hheadDiv hsourceSteps
    hsourceBitEx.
  pose proof
    (BProv_Ax_s_betaTermTermAt_head_of_betaPrependPrefixTermAt
      G sourceCode sourceStep head targetCode targetStep
      (tSucc (tSucc idx)) hprefix) as hentry.
  pose proof
    (BProv_Ax_s_betaPrependPrefixTermAt_stepsThrough_of_sourceSteps
      G sourceCode sourceStep head sourceHead headBit targetCode
      targetStep idx hprefix hsourceHead hheadDiv hsourceSteps)
    as htargetSteps.
  pose proof
    (BProv_Ax_s_betaPrependPrefixTermAt_bitOneEx_succ_of_sourceBitOneEx
      G sourceCode sourceStep head targetCode targetStep idx idx
      hprefix (BProv_Ax_s_leTermAt_refl G idx) hsourceBitEx)
    as htargetBitEx.
  exact (BProv_Ax_s_subst_hfMemTermAt_zero_of_term_components
    G head targetCode targetStep (tSucc idx)
    hentry htargetSteps htargetBitEx).
Qed.

Lemma BProv_Ax_s_betaPrependExistsTermAt_succ_mem_of_source_trace :
  forall G sourceCode sourceStep head sourceHead headBit idx,
  BProv Ax_s G
    (betaTermTermAt sourceHead sourceCode sourceStep tZero) ->
  BProv Ax_s G (div2StepTermAt head sourceHead headBit) ->
  BProv Ax_s G
    (betaDiv2StepsThroughTermTermAt sourceCode sourceStep idx) ->
  BProv Ax_s G
    (betaDiv2BitOneTermExAt sourceCode sourceStep idx) ->
  BProv Ax_s G
    (subst (instTerm (tSucc idx))
      (hfMemTermAt 0 (Term.rename S head))).
Proof.
  intros G sourceCode sourceStep head sourceHead headBit idx
    hsourceHead hheadDiv hsourceSteps hsourceBitEx.
  set (target := subst (instTerm (tSucc idx))
    (hfMemTermAt 0 (Term.rename S head))).
  set (bound := tSucc (tSucc idx)).
  pose proof (BProv_Ax_s_betaPrependExistsTermAt
    G sourceCode sourceStep head bound) as hex.
  apply (BProv_Ax_s_betaPrependExistsTermAt_elim_opened
    G sourceCode sourceStep head bound target); [|exact hex].
  set (stepBody := betaPrependExistsTermAtBody
    sourceCode sourceStep head bound).
  set (D1 := stepBody :: map (rename S) G).
  assert (hcodeEx : BProv Ax_s D1
      (betaPrependPrefixCodeExistsTermAt
        (Term.rename S sourceCode)
        (Term.rename S sourceStep)
        (Term.rename S head) (tVar 0)
        (Term.rename S bound))).
  {
    apply BProv_ass.
    unfold D1, stepBody, betaPrependExistsTermAtBody.
    simpl. left. reflexivity.
  }
  apply (BProv_Ax_s_betaPrependPrefixCodeExistsTermAt_elim_opened
    D1 (Term.rename S sourceCode) (Term.rename S sourceStep)
    (Term.rename S head) (tVar 0) (Term.rename S bound)
    (rename S target)); [|exact hcodeEx].
  set (prefixBody := betaPrependPrefixCodeExistsTermAtBody
    (Term.rename S sourceCode)
    (Term.rename S sourceStep)
    (Term.rename S head) (tVar 0) (Term.rename S bound)).
  set (D2 := prefixBody :: map (rename S) D1).
  set (sourceCode2 := Term.rename S (Term.rename S sourceCode)).
  set (sourceStep2 := Term.rename S (Term.rename S sourceStep)).
  set (head2 := Term.rename S (Term.rename S head)).
  set (sourceHead2 := Term.rename S (Term.rename S sourceHead)).
  set (headBit2 := Term.rename S (Term.rename S headBit)).
  set (idx2 := Term.rename S (Term.rename S idx)).
  assert (hprefix : BProv Ax_s D2
      (betaPrependPrefixTermAt sourceCode2 sourceStep2 head2
        (tVar 0) (tVar 1) (tSucc (tSucc idx2)))).
  {
    pose proof (BProv_ass Ax_s D2 prefixBody) as h.
    assert (Hin : In prefixBody D2).
    { unfold D2. simpl. left. reflexivity. }
    specialize (h Hin).
    unfold prefixBody, betaPrependPrefixCodeExistsTermAtBody,
      sourceCode2, sourceStep2, head2, idx2, bound in h |- *.
    simpl in h.
    exact h.
  }
  assert (lift2 : forall f,
      BProv Ax_s G f ->
      BProv Ax_s D2 (rename S (rename S f))).
  {
    intros f hf.
    pose proof (BProv_lift_two_contexts_of_sentences
      Ax_s sentence_ax_s G stepBody prefixBody f hf) as h.
    unfold D2, D1.
    simpl.
    exact h.
  }
  assert (hsourceHead2 : BProv Ax_s D2
      (betaTermTermAt sourceHead2 sourceCode2 sourceStep2 tZero)).
  {
    pose proof (lift2 _ hsourceHead) as h.
    repeat rewrite rename_betaTermTermAt in h.
    unfold sourceHead2, sourceCode2, sourceStep2.
    simpl in h.
    exact h.
  }
  assert (hheadDiv2 : BProv Ax_s D2
      (div2StepTermAt head2 sourceHead2 headBit2)).
  {
    pose proof (lift2 _ hheadDiv) as h.
    repeat rewrite rename_div2StepTermAt in h.
    unfold head2, sourceHead2, headBit2.
    exact h.
  }
  assert (hsourceSteps2 : BProv Ax_s D2
      (betaDiv2StepsThroughTermTermAt
        sourceCode2 sourceStep2 idx2)).
  {
    pose proof (lift2 _ hsourceSteps) as h.
    repeat rewrite rename_betaDiv2StepsThroughTermTermAt in h.
    unfold sourceCode2, sourceStep2, idx2.
    exact h.
  }
  assert (hsourceBitEx2 : BProv Ax_s D2
      (betaDiv2BitOneTermExAt sourceCode2 sourceStep2 idx2)).
  {
    pose proof (lift2 _ hsourceBitEx) as h.
    repeat rewrite rename_betaDiv2BitOneTermExAt in h.
    unfold sourceCode2, sourceStep2, idx2.
    exact h.
  }
  pose proof
    (BProv_Ax_s_betaPrependPrefixTermAt_succ_mem_of_source_trace
      D2 sourceCode2 sourceStep2 head2 sourceHead2 headBit2
      (tVar 0) (tVar 1) idx2 hprefix hsourceHead2 hheadDiv2
      hsourceSteps2 hsourceBitEx2) as hmem.
  set (r := fun n : nat => n + 2).
  set (phi := hfMemTermAt 0 (Term.rename S head)).
  assert (hsetRename :
      Term.rename (up r) (Term.rename S head) =
        Term.rename S head2).
  {
    unfold r, head2.
    repeat rewrite Term.rename_comp.
    apply Term.rename_ext. intro n.
    unfold up. simpl. lia.
  }
  assert (hmemLifted : BProv Ax_s D2
      (subst (instTerm (Term.rename r (tSucc idx)))
        (rename (up r) phi))).
  {
    unfold phi.
    rewrite rename_hfMemTermAt_zero_up.
    rewrite hsetRename.
    replace (Term.rename r (tSucc idx)) with (tSucc idx2).
    - exact hmem.
    - unfold r, idx2.
      simpl.
      rewrite Term.rename_comp.
      apply f_equal.
      apply Term.rename_ext. intro n. lia.
  }
  assert (hrenamed : BProv Ax_s D2 (rename r target)).
  {
    replace (rename r target)
      with (subst (instTerm (Term.rename r (tSucc idx)))
        (rename (up r) phi)).
    - exact hmemLifted.
    - unfold target, phi.
      exact (subst_instTerm_rename_up
        (hfMemTermAt 0 (Term.rename S head)) r (tSucc idx)).
  }
  replace (rename S (rename S target)) with (rename r target).
  - exact hrenamed.
  - unfold r.
    rewrite rename_comp.
    apply rename_ext. intro n. lia.
Qed.

(** Membership lifts across one explicit binary head step. *)
Lemma BProv_Ax_s_hfMemTermAt_succ_of_div2StepTermAt :
  forall G head tailCode headBit,
  BProv Ax_s G (div2StepTermAt head tailCode headBit) ->
  BProv Ax_s G (hfMemTermAt 0 tailCode) ->
  BProv Ax_s G
    (subst (instTerm (tSucc (tVar 0)))
      (hfMemTermAt 0 (Term.rename S head))).
Proof.
  intros G head tailCode headBit hheadDiv hmem.
  set (target := subst (instTerm (tSucc (tVar 0)))
    (hfMemTermAt 0 (Term.rename S head))).
  apply (BProv_Ax_s_hfMemTermAt_elim_opened_code_step
    G target 0 tailCode hmem).
  set (bitBody :=
    pAnd (oneAt 0) (betaDiv2BitAt 0 2 1 (0 + 3))).
  set (traceTail :=
    pAnd (betaDiv2StepsThroughAt 1 0 (0 + 2)) (pEx bitBody)).
  set (body := pAnd
    (betaTermAtConstIdx
      (Term.rename (fun n => n + 2) tailCode) 1 0 0)
    traceTail).
  set (D := body :: map (rename S) (pEx body :: map (rename S) G)).
  set (head2 := Term.rename S (Term.rename S head)).
  set (tail2 := Term.rename S (Term.rename S tailCode)).
  set (headBit2 := Term.rename S (Term.rename S headBit)).
  assert (hbody : BProv Ax_s D body).
  { apply BProv_ass. unfold D. simpl. left. reflexivity. }
  pose proof (BProv_andE1 Ax_s D _ _ hbody) as hentryLegacy.
  pose proof (BProv_andE2 Ax_s D _ _ hbody) as htraceTail.
  assert (hstepsLegacy : BProv Ax_s D
      (betaDiv2StepsThroughAt 1 0 2)).
  {
    pose proof (BProv_andE1 Ax_s D _ _ htraceTail) as h.
    unfold traceTail in h.
    exact h.
  }
  assert (hbitLegacy : BProv Ax_s D
      (pEx (pAnd (oneAt 0) (betaDiv2BitAt 0 2 1 3)))).
  {
    pose proof (BProv_andE2 Ax_s D _ _ htraceTail) as h.
    unfold traceTail, bitBody in h.
    exact h.
  }
  assert (hentryConst : BProv Ax_s D
      (betaTermTermAtConstIdx tail2 (tVar 1) (tVar 0) 0)).
  {
    replace
      (betaTermTermAtConstIdx tail2 (tVar 1) (tVar 0) 0)
      with (betaTermAtConstIdx
        (Term.rename (fun n => n + 2) tailCode) 1 0 0).
    - exact hentryLegacy.
    - unfold tail2, betaTermTermAtConstIdx,
        betaTermAtConstIdx, betaTermAt, betaTermTermAt,
        remTermAt, remTermTermAt, ltTermAt,
        betaModTerm, betaModTermTerm, eqConstAt.
      simpl.
      repeat rewrite Term.rename_comp.
      replace
        (Term.rename (fun n => S (S (S (S (n + 2))))) tailCode)
        with
        (Term.rename (fun n => S (S (S (S (S (S n)))))) tailCode)
        by (apply Term.rename_ext; intro n; lia).
      replace
        (Term.rename (fun n => S (S (S (n + 2)))) tailCode)
        with
        (Term.rename (fun n => S (S (S (S (S n))))) tailCode)
        by (apply Term.rename_ext; intro n; lia).
      reflexivity.
  }
  assert (hidxZero : BProv Ax_s D
      (pEq (Term.numeral 0) tZero)).
  {
    simpl.
    exact (BProv_eqRefl Ax_s D tZero).
  }
  pose proof
    (BProv_Ax_s_betaTermTermAt_of_betaTermTermAtConstIdx_eq_term
      D tail2 (tVar 1) (tVar 0) tZero 0 hentryConst hidxZero)
    as hsourceHead.
  pose proof
    (BProv_Ax_s_betaDiv2StepsThroughTermTermAt_vars_of_legacy
      D 1 0 2 hstepsLegacy) as hsourceSteps.
  set (idSub := fun n : nat => tVar n).
  assert (hbitSub : BProv Ax_s D
      (subst idSub
        (pEx (pAnd (oneAt 0) (betaDiv2BitAt 0 2 1 3))))).
  {
    rewrite subst_id.
    exact hbitLegacy.
  }
  pose proof
    (BProv_Ax_s_betaDiv2BitOneTermExAt_of_subst_bitOneEx
      D idSub 1 0 2 hbitSub) as hsourceBitRaw.
  assert (hsourceBitEx : BProv Ax_s D
      (betaDiv2BitOneTermExAt (tVar 1) (tVar 0) (tVar 2))).
  {
    unfold idSub in hsourceBitRaw.
    exact hsourceBitRaw.
  }
  assert (lift2 : forall f,
      BProv Ax_s G f ->
      BProv Ax_s D (rename S (rename S f))).
  {
    intros f hf.
    pose proof (BProv_lift_two_opened_of_sentences
      Ax_s sentence_ax_s G body f hf) as h.
    unfold D.
    simpl.
    exact h.
  }
  assert (hheadDiv2 : BProv Ax_s D
      (div2StepTermAt head2 tail2 headBit2)).
  {
    pose proof (lift2 _ hheadDiv) as h.
    repeat rewrite rename_div2StepTermAt in h.
    unfold head2, tail2, headBit2.
    exact h.
  }
  pose proof
    (BProv_Ax_s_betaPrependExistsTermAt_succ_mem_of_source_trace
      D (tVar 1) (tVar 0) head2 tail2 headBit2 (tVar 2)
      hsourceHead hheadDiv2 hsourceSteps hsourceBitEx)
    as hderived.
  set (r := fun n : nat => n + 2).
  set (phi := hfMemTermAt 0 (Term.rename S head)).
  assert (hsetRename :
      Term.rename (up r) (Term.rename S head) =
        Term.rename S head2).
  {
    unfold r, head2.
    repeat rewrite Term.rename_comp.
    apply Term.rename_ext. intro n.
    unfold up. simpl. lia.
  }
  assert (hderivedLifted : BProv Ax_s D
      (subst (instTerm (Term.rename r (tSucc (tVar 0))))
        (rename (up r) phi))).
  {
    unfold phi.
    rewrite rename_hfMemTermAt_zero_up.
    rewrite hsetRename.
    replace (Term.rename r (tSucc (tVar 0)))
      with (tSucc (tVar 2)).
    - exact hderived.
    - unfold r. reflexivity.
  }
  assert (hrenamed : BProv Ax_s D (rename r target)).
  {
    replace (rename r target)
      with (subst (instTerm (Term.rename r (tSucc (tVar 0))))
        (rename (up r) phi)).
    - exact hderivedLifted.
    - unfold target, phi.
      exact (subst_instTerm_rename_up
        (hfMemTermAt 0 (Term.rename S head)) r (tSucc (tVar 0))).
  }
  replace (rename S (rename S target)) with (rename r target).
  - exact hrenamed.
  - unfold r.
    rewrite rename_comp.
    apply rename_ext. intro n. lia.
Qed.

Lemma BProv_Ax_s_hfMem_succ_iff_tail_of_div2StepAt :
  forall G head tail bit,
  BProv Ax_s G (div2StepAt head tail bit) ->
  BProv Ax_s G
    (iffForm
      (subst (instTerm (tSucc (tVar 0)))
        (hfMemAt 0 (S head)))
      (hfMemAt 0 tail)).
Proof.
  intros G head tail bit hstep.
  set (succMem := subst (instTerm (tSucc (tVar 0)))
    (hfMemAt 0 (S head))).
  set (tailMem := hfMemAt 0 tail).
  assert (hforward : BProv Ax_s G (pImp succMem tailMem)).
  {
    set (C := succMem :: G).
    assert (hstepC : BProv Ax_s C (div2StepAt head tail bit)).
    { exact (BProv_context_cons Ax_s G succMem _ hstep). }
    assert (hsucc : BProv Ax_s C succMem).
    { apply BProv_ass. unfold C. simpl. left. reflexivity. }
    pose proof
      (BProv_Ax_s_hfMemAt_tail_of_succ_mem_and_div2StepAt
        C head tail bit hstepC hsucc) as htail.
    unfold C, tailMem.
    exact (BProv_impI Ax_s G succMem (hfMemAt 0 tail) htail).
  }
  assert (hreverse : BProv Ax_s G (pImp tailMem succMem)).
  {
    set (C := tailMem :: G).
    assert (hstepC : BProv Ax_s C (div2StepAt head tail bit)).
    { exact (BProv_context_cons Ax_s G tailMem _ hstep). }
    assert (htail : BProv Ax_s C (hfMemTermAt 0 (tVar tail))).
    {
      rewrite hfMemTermAt_var.
      apply BProv_ass. unfold C, tailMem. simpl. left. reflexivity.
    }
    pose proof (BProv_Ax_s_hfMemTermAt_succ_of_div2StepTermAt
      C (tVar head) (tVar tail) (tVar bit) hstepC htail) as hsucc.
    unfold C, succMem, tailMem.
    exact (BProv_impI Ax_s G (hfMemAt 0 tail)
      (subst (instTerm (tSucc (tVar 0))) (hfMemAt 0 (S head)))
      hsucc).
  }
  unfold succMem, tailMem.
  exact (BProv_andI Ax_s G _ _ hforward hreverse).
Qed.

Lemma BProv_Ax_s_betaDiv2StepWitnessTermAt_of_eq_index :
  forall G code step oldIdx newIdx,
  BProv Ax_s G (pEq oldIdx newIdx) ->
  BProv Ax_s G
    (betaDiv2StepWitnessTermAt code step oldIdx) ->
  BProv Ax_s G
    (betaDiv2StepWitnessTermAt code step newIdx).
Proof.
  intros G code step oldIdx newIdx heq hold.
  set (body := betaDiv2StepWitnessTermAt
    (Term.rename S code) (Term.rename S step) (tVar 0)).
  assert (hold' : BProv Ax_s G (subst (instTerm oldIdx) body)).
  {
    unfold body.
    rewrite subst_betaDiv2StepWitnessTermAt.
    simpl.
    repeat rewrite term_subst_instTerm_rename_succ.
    exact hold.
  }
  pose proof (BProv_eqElim Ax_s G oldIdx newIdx body heq hold') as hnew.
  replace (betaDiv2StepWitnessTermAt code step newIdx)
    with (subst (instTerm newIdx) body).
  - exact hnew.
  - unfold body.
    rewrite subst_betaDiv2StepWitnessTermAt.
    simpl.
    repeat rewrite term_subst_instTerm_rename_succ.
    reflexivity.
Qed.

Lemma BProv_Ax_s_betaDiv2StepsThroughTermTermAt_zero_of_step :
  forall G code step,
  BProv Ax_s G
    (betaDiv2StepWitnessTermAt code step tZero) ->
  BProv Ax_s G
    (betaDiv2StepsThroughTermTermAt code step tZero).
Proof.
  intros G code step hstep.
  set (leHyp := leTermAt (tVar 0) tZero).
  set (body := pImp leHyp
    (betaDiv2StepWitnessTermAt
      (Term.rename S code) (Term.rename S step) (tVar 0))).
  assert (hbody : BProv Ax_s (map (rename S) G) body).
  {
    set (C := leHyp :: map (rename S) G).
    assert (hle : BProv Ax_s C (leTermAt (tVar 0) tZero)).
    { apply BProv_ass. unfold C, leHyp. simpl. left. reflexivity. }
    pose proof (BProv_Ax_s_leTermAt_zero_left C (tVar 0)) as hzeroLe.
    pose proof (BProv_Ax_s_eq_of_leTermAt_leTermAt
      C (tVar 0) tZero hle hzeroLe) as heq.
    pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
      hstep S) as hstepRen.
    rewrite rename_betaDiv2StepWitnessTermAt in hstepRen.
    assert (hstepC : BProv Ax_s C
        (betaDiv2StepWitnessTermAt
          (Term.rename S code) (Term.rename S step) tZero)).
    {
      exact (BProv_context_cons Ax_s (map (rename S) G)
        leHyp _ hstepRen).
    }
    pose proof (BProv_Ax_s_betaDiv2StepWitnessTermAt_of_eq_index
      C (Term.rename S code) (Term.rename S step) tZero (tVar 0)
      (BProv_eqSym Ax_s C _ _ heq) hstepC) as hpoint.
    unfold body.
    exact (BProv_impI Ax_s (map (rename S) G) leHyp _ hpoint).
  }
  pose proof (BProv_allI_of_sentences Ax_s G body
    sentence_ax_s hbody) as hall.
  replace (betaDiv2StepsThroughTermTermAt code step tZero)
    with (pAll body).
  - exact hall.
  - unfold betaDiv2StepsThroughTermTermAt, body, leHyp.
    simpl.
    reflexivity.
Qed.

Lemma BProv_Ax_s_betaPrependPrefixTermAt_zero_mem_of_head_step :
  forall G sourceCode sourceStep head sourceHead bit targetCode targetStep,
  BProv Ax_s G
    (betaPrependPrefixTermAt sourceCode sourceStep head
      targetCode targetStep (tSucc (tSucc tZero))) ->
  BProv Ax_s G
    (betaTermTermAt sourceHead sourceCode sourceStep tZero) ->
  BProv Ax_s G (pEq bit (tSucc tZero)) ->
  BProv Ax_s G (div2StepTermAt head sourceHead bit) ->
  BProv Ax_s G
    (subst (instTerm tZero)
      (hfMemTermAt 0 (Term.rename S head))).
Proof.
  intros G sourceCode sourceStep head sourceHead bit targetCode
    targetStep hprefix hsourceHead hone hdiv.
  pose proof
    (BProv_Ax_s_betaTermTermAt_head_of_betaPrependPrefixTermAt
      G sourceCode sourceStep head targetCode targetStep
      (tSucc (tSucc tZero)) hprefix) as hentry.
  pose proof
    (BProv_Ax_s_betaPrependPrefixTermAt_step_zero_of_components
      G sourceCode sourceStep head sourceHead bit
      targetCode targetStep (tSucc (tSucc tZero)) hprefix
      (BProv_Ax_s_ltTermAt_zero_succ G (tSucc tZero))
      hsourceHead hdiv) as hstep.
  pose proof
    (BProv_Ax_s_betaDiv2StepsThroughTermTermAt_zero_of_step
      G targetCode targetStep hstep) as hsteps.
  pose proof
    (BProv_Ax_s_betaUnshiftPrefixTermAt_of_betaPrependPrefixTermAt
      G sourceCode sourceStep head targetCode targetStep
      (tSucc (tSucc tZero)) hprefix) as hunshift.
  pose proof
    (BProv_Ax_s_betaUnshiftPrefixTermAt_entry_of_ltTerm
      G sourceCode sourceStep targetCode targetStep
      (tSucc (tSucc tZero)) tZero sourceHead hunshift
      (BProv_Ax_s_ltTermAt_zero_succ G (tSucc tZero))
      hsourceHead) as hnext.
  pose proof (BProv_Ax_s_betaDiv2BitTermAt_of_components
    G bit targetCode targetStep tZero head sourceHead
    hentry hnext hdiv) as hbitTerm.
  pose proof (BProv_Ax_s_betaDiv2BitOneTermExAt_of_term
    G bit targetCode targetStep tZero hone hbitTerm)
    as hbitEx.
  exact (BProv_Ax_s_subst_hfMemTermAt_zero_of_term_components
    G head targetCode targetStep tZero hentry hsteps hbitEx).
Qed.

Lemma BProv_Ax_s_betaPrependExistsTermAt_zero_mem_of_source_head_step :
  forall G sourceCode sourceStep head sourceHead bit,
  BProv Ax_s G
    (betaTermTermAt sourceHead sourceCode sourceStep tZero) ->
  BProv Ax_s G (pEq bit (tSucc tZero)) ->
  BProv Ax_s G (div2StepTermAt head sourceHead bit) ->
  BProv Ax_s G
    (subst (instTerm tZero)
      (hfMemTermAt 0 (Term.rename S head))).
Proof.
  intros G sourceCode sourceStep head sourceHead bit
    hsourceHead hone hdiv.
  set (target := subst (instTerm tZero)
    (hfMemTermAt 0 (Term.rename S head))).
  set (bound := tSucc (tSucc tZero)).
  pose proof (BProv_Ax_s_betaPrependExistsTermAt
    G sourceCode sourceStep head bound) as hex.
  apply (BProv_Ax_s_betaPrependExistsTermAt_elim_opened
    G sourceCode sourceStep head bound target); [|exact hex].
  set (stepBody := betaPrependExistsTermAtBody
    sourceCode sourceStep head bound).
  set (D1 := stepBody :: map (rename S) G).
  assert (hcodeEx : BProv Ax_s D1
      (betaPrependPrefixCodeExistsTermAt
        (Term.rename S sourceCode)
        (Term.rename S sourceStep)
        (Term.rename S head) (tVar 0)
        (Term.rename S bound))).
  {
    apply BProv_ass.
    unfold D1, stepBody, betaPrependExistsTermAtBody.
    simpl. left. reflexivity.
  }
  apply (BProv_Ax_s_betaPrependPrefixCodeExistsTermAt_elim_opened
    D1 (Term.rename S sourceCode) (Term.rename S sourceStep)
    (Term.rename S head) (tVar 0) (Term.rename S bound)
    (rename S target)); [|exact hcodeEx].
  set (prefixBody := betaPrependPrefixCodeExistsTermAtBody
    (Term.rename S sourceCode)
    (Term.rename S sourceStep)
    (Term.rename S head) (tVar 0) (Term.rename S bound)).
  set (D2 := prefixBody :: map (rename S) D1).
  set (sourceCode2 := Term.rename S (Term.rename S sourceCode)).
  set (sourceStep2 := Term.rename S (Term.rename S sourceStep)).
  set (head2 := Term.rename S (Term.rename S head)).
  set (sourceHead2 := Term.rename S (Term.rename S sourceHead)).
  set (bit2 := Term.rename S (Term.rename S bit)).
  assert (hprefix : BProv Ax_s D2
      (betaPrependPrefixTermAt sourceCode2 sourceStep2 head2
        (tVar 0) (tVar 1) (tSucc (tSucc tZero)))).
  {
    assert (hass : BProv Ax_s D2 prefixBody).
    { apply BProv_ass. unfold D2. simpl. left. reflexivity. }
    unfold prefixBody, betaPrependPrefixCodeExistsTermAtBody,
      sourceCode2, sourceStep2, head2, bound in hass |- *.
    simpl in hass.
    exact hass.
  }
  assert (lift2 : forall f,
      BProv Ax_s G f ->
      BProv Ax_s D2 (rename S (rename S f))).
  {
    intros f hf.
    pose proof (BProv_lift_two_contexts_of_sentences
      Ax_s sentence_ax_s G stepBody prefixBody f hf) as h.
    unfold D2, D1. simpl. exact h.
  }
  assert (hsourceHead2 : BProv Ax_s D2
      (betaTermTermAt sourceHead2 sourceCode2 sourceStep2 tZero)).
  {
    pose proof (lift2 _ hsourceHead) as h.
    repeat rewrite rename_betaTermTermAt in h.
    unfold sourceHead2, sourceCode2, sourceStep2.
    simpl in h. exact h.
  }
  assert (hone2 : BProv Ax_s D2 (pEq bit2 (tSucc tZero))).
  {
    pose proof (lift2 _ hone) as h.
    unfold bit2. simpl in h. exact h.
  }
  assert (hdiv2 : BProv Ax_s D2
      (div2StepTermAt head2 sourceHead2 bit2)).
  {
    pose proof (lift2 _ hdiv) as h.
    repeat rewrite rename_div2StepTermAt in h.
    unfold head2, sourceHead2, bit2. exact h.
  }
  pose proof
    (BProv_Ax_s_betaPrependPrefixTermAt_zero_mem_of_head_step
      D2 sourceCode2 sourceStep2 head2 sourceHead2 bit2
      (tVar 0) (tVar 1) hprefix hsourceHead2 hone2 hdiv2)
    as hmem.
  set (r := fun n : nat => n + 2).
  set (phi := hfMemTermAt 0 (Term.rename S head)).
  assert (hsetRename :
      Term.rename (up r) (Term.rename S head) =
        Term.rename S head2).
  {
    unfold r, head2.
    repeat rewrite Term.rename_comp.
    apply Term.rename_ext. intro n.
    unfold up. simpl. lia.
  }
  assert (hmemLifted : BProv Ax_s D2
      (subst (instTerm (Term.rename r tZero))
        (rename (up r) phi))).
  {
    unfold phi.
    rewrite rename_hfMemTermAt_zero_up.
    rewrite hsetRename.
    simpl.
    exact hmem.
  }
  assert (hrenamed : BProv Ax_s D2 (rename r target)).
  {
    replace (rename r target)
      with (subst (instTerm (Term.rename r tZero))
        (rename (up r) phi)).
    - exact hmemLifted.
    - unfold target, phi.
      exact (subst_instTerm_rename_up
        (hfMemTermAt 0 (Term.rename S head)) r tZero).
  }
  replace (rename S (rename S target)) with (rename r target).
  - exact hrenamed.
  - unfold r. rewrite rename_comp.
    apply rename_ext. intro n. lia.
Qed.

Lemma BProv_Ax_s_hfMemTermAt_zero_of_bit_one_div2StepTermAt :
  forall G head half bit,
  BProv Ax_s G (pEq bit (tSucc tZero)) ->
  BProv Ax_s G (div2StepTermAt head half bit) ->
  BProv Ax_s G
    (subst (instTerm tZero)
      (hfMemTermAt 0 (Term.rename S head))).
Proof.
  intros G head half bit hone hstep.
  assert (hsource : BProv Ax_s G
      (betaTermTermAt half half (tSucc half) tZero)).
  {
    exact (BProv_Ax_s_betaTermTermAt_self_zero_of_succ_le_step
      G half (tSucc half) (BProv_Ax_s_leTermAt_refl G (tSucc half))).
  }
  exact
    (BProv_Ax_s_betaPrependExistsTermAt_zero_mem_of_source_head_step
      G half (tSucc half) head half bit hsource hone hstep).
Qed.

Lemma BProv_Ax_s_hfMemAt_of_eqConst_zero_and_div2StepAt_bit_one :
  forall G elem head half bit,
  BProv Ax_s G (eqConstAt elem 0) ->
  BProv Ax_s G (eqConstAt bit 1) ->
  BProv Ax_s G (div2StepAt head half bit) ->
  BProv Ax_s G (hfMemAt elem head).
Proof.
  intros G elem head half bit helem hbit hstep.
  pose proof
    (BProv_Ax_s_hfMemTermAt_zero_of_bit_one_div2StepTermAt
      G (tVar head) (tVar half) (tVar bit) hbit hstep) as hzero.
  set (phi := hfMemTermAt 0 (Term.rename S (tVar head))).
  assert (heq : BProv Ax_s G (pEq tZero (tVar elem))).
  {
    unfold eqConstAt in helem.
    simpl in helem.
    exact (BProv_eqSym Ax_s G _ _ helem).
  }
  pose proof (BProv_eqElim Ax_s G tZero (tVar elem)
    phi heq hzero) as hmem.
  unfold phi in hmem.
  rewrite subst_instTerm_var_hfMemTermAt_zero_rename_succ in hmem.
  rewrite hfMemTermAt_var in hmem.
  exact hmem.
Qed.

Lemma BProv_Ax_s_hfMem_zero_iff_of_same_div2_bit :
  forall G query newHead newTail oldHead oldTail bit,
  BProv Ax_s G (eqConstAt query 0) ->
  BProv Ax_s G (div2StepAt newHead newTail bit) ->
  BProv Ax_s G (div2StepAt oldHead oldTail bit) ->
  BProv Ax_s G
    (iffForm (hfMemAt query newHead) (hfMemAt query oldHead)).
Proof.
  intros G query newHead newTail oldHead oldTail bit
    hqueryZero hnewStep holdStep.
  pose proof (BProv_andE1 Ax_s G _ _ hnewStep) as hbool.
  set (newMem := hfMemAt query newHead).
  set (oldMem := hfMemAt query oldHead).
  assert (hzeroBit : BProv Ax_s (zeroAt bit :: G)
      (iffForm newMem oldMem)).
  {
    set (C := zeroAt bit :: G).
    assert (hbitZero : BProv Ax_s C (eqConstAt bit 0)).
    { apply BProv_ass_head. }
    assert (hnewStepC : BProv Ax_s C
        (div2StepAt newHead newTail bit)).
    { exact (BProv_context_cons Ax_s G (zeroAt bit) _ hnewStep). }
    assert (holdStepC : BProv Ax_s C
        (div2StepAt oldHead oldTail bit)).
    { exact (BProv_context_cons Ax_s G (zeroAt bit) _ holdStep). }
    pose proof (BProv_Ax_s_doubleEqAt_of_div2StepAt_bit_zero
      C newHead newTail bit hbitZero hnewStepC) as hnewDouble.
    pose proof (BProv_Ax_s_doubleEqAt_of_div2StepAt_bit_zero
      C oldHead oldTail bit hbitZero holdStepC) as holdDouble.
    assert (hforward : BProv Ax_s C (pImp newMem oldMem)).
    {
      set (D := newMem :: C).
      assert (hqueryD : BProv Ax_s D (eqConstAt query 0)).
      {
        unfold D, C.
        exact (BProv_context_prefix Ax_s
          [newMem; zeroAt bit] G _ hqueryZero).
      }
      assert (hdoubleD : BProv Ax_s D
          (doubleEqAt newHead newTail)).
      { exact (BProv_context_cons Ax_s C newMem _ hnewDouble). }
      assert (hmemD : BProv Ax_s D (hfMemAt query newHead)).
      { apply BProv_ass_head. }
      pose proof
        (BProv_Ax_s_hfMemAt_bot_of_eqConst_zero_elem_low_double
          D query newHead newTail hqueryD hdoubleD hmemD) as hbot.
      unfold D.
      exact (BProv_impI Ax_s C newMem oldMem
        (BProv_botE Ax_s D oldMem hbot)).
    }
    assert (hreverse : BProv Ax_s C (pImp oldMem newMem)).
    {
      set (D := oldMem :: C).
      assert (hqueryD : BProv Ax_s D (eqConstAt query 0)).
      {
        unfold D, C.
        exact (BProv_context_prefix Ax_s
          [oldMem; zeroAt bit] G _ hqueryZero).
      }
      assert (hdoubleD : BProv Ax_s D
          (doubleEqAt oldHead oldTail)).
      { exact (BProv_context_cons Ax_s C oldMem _ holdDouble). }
      assert (hmemD : BProv Ax_s D (hfMemAt query oldHead)).
      { apply BProv_ass_head. }
      pose proof
        (BProv_Ax_s_hfMemAt_bot_of_eqConst_zero_elem_low_double
          D query oldHead oldTail hqueryD hdoubleD hmemD) as hbot.
      unfold D.
      exact (BProv_impI Ax_s C oldMem newMem
        (BProv_botE Ax_s D newMem hbot)).
    }
    exact (BProv_andI Ax_s C _ _ hforward hreverse).
  }
  assert (honeBit : BProv Ax_s (oneAt bit :: G)
      (iffForm newMem oldMem)).
  {
    set (C := oneAt bit :: G).
    assert (hbitOne : BProv Ax_s C (eqConstAt bit 1)).
    { apply BProv_ass_head. }
    assert (hnewStepC : BProv Ax_s C
        (div2StepAt newHead newTail bit)).
    { exact (BProv_context_cons Ax_s G (oneAt bit) _ hnewStep). }
    assert (holdStepC : BProv Ax_s C
        (div2StepAt oldHead oldTail bit)).
    { exact (BProv_context_cons Ax_s G (oneAt bit) _ holdStep). }
    assert (hqueryC : BProv Ax_s C (eqConstAt query 0)).
    { exact (BProv_context_cons Ax_s G (oneAt bit) _ hqueryZero). }
    pose proof
      (BProv_Ax_s_hfMemAt_of_eqConst_zero_and_div2StepAt_bit_one
        C query newHead newTail bit hqueryC hbitOne hnewStepC)
      as hnewMem.
    pose proof
      (BProv_Ax_s_hfMemAt_of_eqConst_zero_and_div2StepAt_bit_one
        C query oldHead oldTail bit hqueryC hbitOne holdStepC)
      as holdMem.
    assert (hforward : BProv Ax_s C (pImp newMem oldMem)).
    {
      exact (BProv_impI Ax_s C newMem oldMem
        (BProv_context_cons Ax_s C newMem _ holdMem)).
    }
    assert (hreverse : BProv Ax_s C (pImp oldMem newMem)).
    {
      exact (BProv_impI Ax_s C oldMem newMem
        (BProv_context_cons Ax_s C oldMem _ hnewMem)).
    }
    exact (BProv_andI Ax_s C _ _ hforward hreverse).
  }
  exact (BProv_orE Ax_s G (zeroAt bit) (oneAt bit)
    (iffForm newMem oldMem) hbool hzeroBit honeBit).
Qed.

Lemma BProv_Ax_s_hfAdjoin_zero_head_lift :
  forall G query newHead newTail oldHead oldTail bit elem,
  BProv Ax_s G (eqConstAt query 0) ->
  BProv Ax_s G (div2StepAt newHead newTail bit) ->
  BProv Ax_s G (div2StepAt oldHead oldTail bit) ->
  BProv Ax_s G
    (iffForm
      (hfMemAt query newHead)
      (pOr (hfMemAt query oldHead)
        (pEq (tVar query) (tSucc (tVar elem))))).
Proof.
  intros G query newHead newTail oldHead oldTail bit elem
    hqueryZero hnewStep holdStep.
  set (newMem := hfMemAt query newHead).
  set (oldMem := hfMemAt query oldHead).
  set (succEq := pEq (tVar query) (tSucc (tVar elem))).
  set (rhs := pOr oldMem succEq).
  pose proof (BProv_Ax_s_hfMem_zero_iff_of_same_div2_bit
    G query newHead newTail oldHead oldTail bit
    hqueryZero hnewStep holdStep) as hsame.
  assert (hforward : BProv Ax_s G (pImp newMem rhs)).
  {
    set (C := newMem :: G).
    assert (hsameC : BProv Ax_s C (iffForm newMem oldMem)).
    { exact (BProv_context_cons Ax_s G newMem _ hsame). }
    pose proof (BProv_andE1 Ax_s C _ _ hsameC) as htoOld.
    assert (hnew : BProv Ax_s C newMem).
    { apply BProv_ass_head. }
    pose proof (BProv_mp Ax_s C newMem oldMem htoOld hnew) as hold.
    unfold C, rhs.
    exact (BProv_impI Ax_s G newMem (pOr oldMem succEq)
      (BProv_orI1 Ax_s C oldMem succEq hold)).
  }
  assert (hreverse : BProv Ax_s G (pImp rhs newMem)).
  {
    set (C := rhs :: G).
    assert (hcases : BProv Ax_s C rhs).
    { apply BProv_ass_head. }
    assert (hleft : BProv Ax_s (oldMem :: C) newMem).
    {
      set (D := oldMem :: C).
      assert (hsameD : BProv Ax_s D (iffForm newMem oldMem)).
      {
        unfold D, C.
        exact (BProv_context_prefix Ax_s [oldMem; rhs] G _ hsame).
      }
      pose proof (BProv_andE2 Ax_s D _ _ hsameD) as htoNew.
      assert (hold : BProv Ax_s D oldMem).
      { apply BProv_ass_head. }
      exact (BProv_mp Ax_s D oldMem newMem htoNew hold).
    }
    assert (hright : BProv Ax_s (succEq :: C) newMem).
    {
      set (D := succEq :: C).
      assert (heq : BProv Ax_s D succEq).
      { apply BProv_ass_head. }
      assert (hzero : BProv Ax_s D (pEq (tVar query) tZero)).
      {
        unfold D, C.
        pose proof (BProv_context_prefix Ax_s
          [succEq; rhs] G _ hqueryZero) as h2.
        unfold eqConstAt in h2. simpl in h2. exact h2.
      }
      assert (hbad : BProv Ax_s D
          (pEq (tSucc (tVar elem)) tZero)).
      {
        exact (BProv_eqTrans Ax_s D _ _ _
          (BProv_eqSym Ax_s D _ _ heq) hzero).
      }
      pose proof (BProv_Ax_s_zeroNotSucc_term D (tVar elem)) as hnot.
      pose proof (BProv_mp Ax_s D _ pBot hnot hbad) as hbot.
      exact (BProv_botE Ax_s D newMem hbot).
    }
    pose proof (BProv_orE Ax_s C oldMem succEq newMem
      hcases hleft hright) as hnew.
    unfold C.
    exact (BProv_impI Ax_s G rhs newMem hnew).
  }
  unfold newMem, oldMem, succEq, rhs.
  exact (BProv_andI Ax_s G _ _ hforward hreverse).
Qed.

Lemma BProv_Ax_s_hfAdjoin_positive_head_lift :
  forall G newHead newTail oldHead oldTail bit elem,
  BProv Ax_s G (div2StepAt newHead newTail bit) ->
  BProv Ax_s G (div2StepAt oldHead oldTail bit) ->
  BProv Ax_s G
    (iffForm
      (hfMemAt 0 newTail)
      (pOr (hfMemAt 0 oldTail)
        (pEq (tVar 0) (tVar elem)))) ->
  BProv Ax_s G
    (iffForm
      (subst (instTerm (tSucc (tVar 0)))
        (hfMemAt 0 (S newHead)))
      (pOr
        (subst (instTerm (tSucc (tVar 0)))
          (hfMemAt 0 (S oldHead)))
        (pEq (tSucc (tVar 0)) (tSucc (tVar elem))))).
Proof.
  intros G newHead newTail oldHead oldTail bit elem
    hnewStep holdStep htail.
  set (newSucc := subst (instTerm (tSucc (tVar 0)))
    (hfMemAt 0 (S newHead))).
  set (oldSucc := subst (instTerm (tSucc (tVar 0)))
    (hfMemAt 0 (S oldHead))).
  set (newTailMem := hfMemAt 0 newTail).
  set (oldTailMem := hfMemAt 0 oldTail).
  set (tailEq := pEq (tVar 0) (tVar elem)).
  set (headEq := pEq (tSucc (tVar 0)) (tSucc (tVar elem))).
  set (rhs := pOr oldSucc headEq).
  pose proof (BProv_Ax_s_hfMem_succ_iff_tail_of_div2StepAt
    G newHead newTail bit hnewStep) as hnewIff.
  pose proof (BProv_Ax_s_hfMem_succ_iff_tail_of_div2StepAt
    G oldHead oldTail bit holdStep) as holdIff.
  assert (hforward : BProv Ax_s G (pImp newSucc rhs)).
  {
    set (C := newSucc :: G).
    assert (hnewC : BProv Ax_s C (iffForm newSucc newTailMem)).
    { exact (BProv_context_cons Ax_s G newSucc _ hnewIff). }
    assert (hnew : BProv Ax_s C newSucc).
    { apply BProv_ass_head. }
    pose proof (BProv_andE1 Ax_s C _ _ hnewC) as htoTail.
    pose proof (BProv_mp Ax_s C newSucc newTailMem htoTail hnew)
      as hnewTail.
    assert (htailC : BProv Ax_s C
        (iffForm newTailMem (pOr oldTailMem tailEq))).
    { exact (BProv_context_cons Ax_s G newSucc _ htail). }
    pose proof (BProv_andE1 Ax_s C _ _ htailC) as htoCases.
    pose proof (BProv_mp Ax_s C newTailMem (pOr oldTailMem tailEq)
      htoCases hnewTail) as hcases.
    assert (hleft : BProv Ax_s (oldTailMem :: C) rhs).
    {
      set (D := oldTailMem :: C).
      assert (holdD : BProv Ax_s D (iffForm oldSucc oldTailMem)).
      {
        unfold D, C.
        exact (BProv_context_prefix Ax_s
          [oldTailMem; newSucc] G _ holdIff).
      }
      pose proof (BProv_andE2 Ax_s D _ _ holdD) as htoOld.
      assert (htailAss : BProv Ax_s D oldTailMem).
      { apply BProv_ass_head. }
      pose proof (BProv_mp Ax_s D oldTailMem oldSucc htoOld htailAss)
        as hold.
      unfold rhs.
      exact (BProv_orI1 Ax_s D oldSucc headEq hold).
    }
    assert (hright : BProv Ax_s (tailEq :: C) rhs).
    {
      set (D := tailEq :: C).
      assert (heq : BProv Ax_s D tailEq).
      { apply BProv_ass_head. }
      pose proof (BProv_eq_congr_succ Ax_s D _ _ heq) as hsuccEq.
      unfold rhs.
      exact (BProv_orI2 Ax_s D oldSucc headEq hsuccEq).
    }
    pose proof (BProv_orE Ax_s C oldTailMem tailEq rhs
      hcases hleft hright) as hrhs.
    unfold C.
    exact (BProv_impI Ax_s G newSucc rhs hrhs).
  }
  assert (hreverse : BProv Ax_s G (pImp rhs newSucc)).
  {
    set (C := rhs :: G).
    assert (hcases : BProv Ax_s C rhs).
    { apply BProv_ass_head. }
    assert (hleft : BProv Ax_s (oldSucc :: C) newSucc).
    {
      set (D := oldSucc :: C).
      assert (holdD : BProv Ax_s D (iffForm oldSucc oldTailMem)).
      {
        unfold D, C.
        exact (BProv_context_prefix Ax_s [oldSucc; rhs] G _ holdIff).
      }
      assert (holdAss : BProv Ax_s D oldSucc).
      { apply BProv_ass_head. }
      pose proof (BProv_andE1 Ax_s D _ _ holdD) as htoTail.
      pose proof (BProv_mp Ax_s D oldSucc oldTailMem htoTail holdAss)
        as holdTail.
      assert (htailD : BProv Ax_s D
          (iffForm newTailMem (pOr oldTailMem tailEq))).
      {
        unfold D, C.
        exact (BProv_context_prefix Ax_s [oldSucc; rhs] G _ htail).
      }
      pose proof (BProv_andE2 Ax_s D _ _ htailD) as htoNewTail.
      pose proof (BProv_orI1 Ax_s D oldTailMem tailEq holdTail)
        as htailCases.
      pose proof (BProv_mp Ax_s D (pOr oldTailMem tailEq)
        newTailMem htoNewTail htailCases) as hnewTail.
      assert (hnewD : BProv Ax_s D (iffForm newSucc newTailMem)).
      {
        unfold D, C.
        exact (BProv_context_prefix Ax_s [oldSucc; rhs] G _ hnewIff).
      }
      pose proof (BProv_andE2 Ax_s D _ _ hnewD) as htoNew.
      exact (BProv_mp Ax_s D newTailMem newSucc htoNew hnewTail).
    }
    assert (hright : BProv Ax_s (headEq :: C) newSucc).
    {
      set (D := headEq :: C).
      assert (hhead : BProv Ax_s D headEq).
      { apply BProv_ass_head. }
      pose proof (BProv_Ax_s_succInj_terms D (tVar 0) (tVar elem)) as hinj.
      pose proof (BProv_mp Ax_s D headEq tailEq hinj hhead) as heq.
      assert (htailD : BProv Ax_s D
          (iffForm newTailMem (pOr oldTailMem tailEq))).
      {
        unfold D, C.
        exact (BProv_context_prefix Ax_s [headEq; rhs] G _ htail).
      }
      pose proof (BProv_andE2 Ax_s D _ _ htailD) as htoNewTail.
      pose proof (BProv_orI2 Ax_s D oldTailMem tailEq heq)
        as htailCases.
      pose proof (BProv_mp Ax_s D (pOr oldTailMem tailEq)
        newTailMem htoNewTail htailCases) as hnewTail.
      assert (hnewD : BProv Ax_s D (iffForm newSucc newTailMem)).
      {
        unfold D, C.
        exact (BProv_context_prefix Ax_s [headEq; rhs] G _ hnewIff).
      }
      pose proof (BProv_andE2 Ax_s D _ _ hnewD) as htoNew.
      exact (BProv_mp Ax_s D newTailMem newSucc htoNew hnewTail).
    }
    pose proof (BProv_orE Ax_s C oldSucc headEq newSucc
      hcases hleft hright) as hnew.
    unfold C.
    exact (BProv_impI Ax_s G rhs newSucc hnew).
  }
  unfold newSucc, oldSucc, newTailMem, oldTailMem, tailEq, headEq, rhs.
  exact (BProv_andI Ax_s G _ _ hforward hreverse).
Qed.

Lemma BProv_Ax_s_hfAdjoinGraph_heads_of_same_bit :
  forall G newHead newTail oldHead oldTail bit elem,
  BProv Ax_s G (div2StepAt newHead newTail bit) ->
  BProv Ax_s G (div2StepAt oldHead oldTail bit) ->
  BProv Ax_s G (hfAdjoinGraphAt newTail oldTail elem) ->
  BProv Ax_s G
    (hfAdjoinGraphTermAt
      (tVar newHead) (tVar oldHead) (tSucc (tVar elem))).
Proof.
  intros G newHead newTail oldHead oldTail bit elem
    hnewStep holdStep htail.
  set (phi := iffForm
    (hfMemAt 0 (S newHead))
    (pOr (hfMemAt 0 (S oldHead))
      (pEq (tVar 0) (tSucc (tVar (S elem)))))).
  assert (hzero : BProv Ax_s G (subst substZero phi)).
  {
    set (zeroEq := eqConstAt 0 0).
    pose proof (BProv_exists_eqConstAt Ax_s G 0) as hex.
    assert (hopened : BProv Ax_s
        (zeroEq :: map (rename S) G)
        (rename S (subst substZero phi))).
    {
      set (C := zeroEq :: map (rename S) G).
      assert (hqueryZero : BProv Ax_s C (eqConstAt 0 0)).
      { apply BProv_ass_head. }
      pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
        hnewStep S) as hnewRen.
      assert (hnewC : BProv Ax_s C
          (div2StepAt (S newHead) (S newTail) (S bit))).
      {
        pose proof (BProv_context_cons Ax_s (map (rename S) G)
          zeroEq _ hnewRen) as h.
        unfold div2StepAt, boolAt, zeroAt, oneAt, eqConstAt in h |- *.
        simpl in h |- *.
        exact h.
      }
      pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
        holdStep S) as holdRen.
      assert (holdC : BProv Ax_s C
          (div2StepAt (S oldHead) (S oldTail) (S bit))).
      {
        pose proof (BProv_context_cons Ax_s (map (rename S) G)
          zeroEq _ holdRen) as h.
        unfold div2StepAt, boolAt, zeroAt, oneAt, eqConstAt in h |- *.
        simpl in h |- *.
        exact h.
      }
      pose proof (BProv_Ax_s_hfAdjoin_zero_head_lift
        C 0 (S newHead) (S newTail) (S oldHead) (S oldTail)
        (S bit) (S elem) hqueryZero hnewC holdC) as hpoint.
      assert (hpointSub : BProv Ax_s C
          (subst (instTerm (tVar 0)) (rename (up S) phi))).
      {
        rewrite subst_instTerm_var_zero_rename_up_succ.
        unfold phi.
        exact hpoint.
      }
      assert (hzeroSub : BProv Ax_s C
          (subst (instTerm tZero) (rename (up S) phi))).
      {
        unfold eqConstAt in hqueryZero.
        simpl in hqueryZero.
        exact (BProv_eqElim Ax_s C (tVar 0) tZero
          (rename (up S) phi) hqueryZero hpointSub).
      }
      replace (rename S (subst substZero phi))
        with (subst (instTerm tZero) (rename (up S) phi)).
      - exact hzeroSub.
      - pose proof (subst_instTerm_rename_up phi S tZero) as hnorm.
        unfold substZero, instTerm in hnorm.
        exact hnorm.
    }
    exact (BProv_exE_of_sentences Ax_s G zeroEq
      (subst substZero phi) sentence_ax_s hex hopened).
  }
  assert (hsuccBody : BProv Ax_s
      (phi :: map (rename S) G) (subst substSuccVar phi)).
  {
    set (C := phi :: map (rename S) G).
    pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
      hnewStep S) as hnewRen.
    assert (hnewC : BProv Ax_s C
        (div2StepAt (S newHead) (S newTail) (S bit))).
    {
      pose proof (BProv_context_cons Ax_s (map (rename S) G)
        phi _ hnewRen) as h.
      unfold div2StepAt, boolAt, zeroAt, oneAt, eqConstAt in h |- *.
      simpl in h |- *.
      exact h.
    }
    pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
      holdStep S) as holdRen.
    assert (holdC : BProv Ax_s C
        (div2StepAt (S oldHead) (S oldTail) (S bit))).
    {
      pose proof (BProv_context_cons Ax_s (map (rename S) G)
        phi _ holdRen) as h.
      unfold div2StepAt, boolAt, zeroAt, oneAt, eqConstAt in h |- *.
      simpl in h |- *.
      exact h.
    }
    pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
      htail S) as htailRen.
    rewrite rename_S_hfAdjoinGraphAt in htailRen.
    assert (htailC : BProv Ax_s C
        (hfAdjoinGraphAt (S newTail) (S oldTail) (S elem))).
    { exact (BProv_context_cons Ax_s (map (rename S) G)
        phi _ htailRen). }
    pose proof (BProv_hfAdjoinGraphAt_point
      Ax_s C 0 (S newTail) (S oldTail) (S elem) htailC)
      as htailPoint.
    pose proof (BProv_Ax_s_hfAdjoin_positive_head_lift
      C (S newHead) (S newTail) (S oldHead) (S oldTail)
      (S bit) (S elem) hnewC holdC htailPoint) as hlift.
    exact hlift.
  }
  assert (hsuccImp : BProv Ax_s (map (rename S) G)
      (pImp phi (subst substSuccVar phi))).
  {
    exact (BProv_impI Ax_s (map (rename S) G)
      phi (subst substSuccVar phi) hsuccBody).
  }
  pose proof (BProv_allI_of_sentences Ax_s G _
    sentence_ax_s hsuccImp) as hsucc.
  pose proof (BProv_Ax_s_induction_rule G phi hzero hsucc) as hall.
  unfold hfAdjoinGraphTermAt, phi.
  simpl.
  exact hall.
Qed.

Lemma BProv_Ax_s_hfAdjoin_positive_zero_lift :
  forall G newHead oldHead tail newBit oldBit,
  BProv Ax_s G (div2StepAt newHead tail newBit) ->
  BProv Ax_s G (div2StepAt oldHead tail oldBit) ->
  BProv Ax_s G
    (iffForm
      (subst (instTerm (tSucc (tVar 0)))
        (hfMemAt 0 (S newHead)))
      (pOr
        (subst (instTerm (tSucc (tVar 0)))
          (hfMemAt 0 (S oldHead)))
        (pEq (tSucc (tVar 0)) tZero))).
Proof.
  intros G newHead oldHead tail newBit oldBit hnewStep holdStep.
  set (newSucc := subst (instTerm (tSucc (tVar 0)))
    (hfMemAt 0 (S newHead))).
  set (oldSucc := subst (instTerm (tSucc (tVar 0)))
    (hfMemAt 0 (S oldHead))).
  set (tailMem := hfMemAt 0 tail).
  set (badEq := pEq (tSucc (tVar 0)) tZero).
  set (rhs := pOr oldSucc badEq).
  pose proof (BProv_Ax_s_hfMem_succ_iff_tail_of_div2StepAt
    G newHead tail newBit hnewStep) as hnewIff.
  pose proof (BProv_Ax_s_hfMem_succ_iff_tail_of_div2StepAt
    G oldHead tail oldBit holdStep) as holdIff.
  assert (hforward : BProv Ax_s G (pImp newSucc rhs)).
  {
    set (C := newSucc :: G).
    assert (hnewC : BProv Ax_s C (iffForm newSucc tailMem)).
    { exact (BProv_context_cons Ax_s G newSucc _ hnewIff). }
    assert (hnew : BProv Ax_s C newSucc).
    { apply BProv_ass_head. }
    pose proof (BProv_andE1 Ax_s C _ _ hnewC) as htoTail.
    pose proof (BProv_mp Ax_s C newSucc tailMem htoTail hnew) as htail.
    assert (holdC : BProv Ax_s C (iffForm oldSucc tailMem)).
    { exact (BProv_context_cons Ax_s G newSucc _ holdIff). }
    pose proof (BProv_andE2 Ax_s C _ _ holdC) as htoOld.
    pose proof (BProv_mp Ax_s C tailMem oldSucc htoOld htail) as hold.
    unfold C, rhs.
    exact (BProv_impI Ax_s G newSucc (pOr oldSucc badEq)
      (BProv_orI1 Ax_s C oldSucc badEq hold)).
  }
  assert (hreverse : BProv Ax_s G (pImp rhs newSucc)).
  {
    set (C := rhs :: G).
    assert (hcases : BProv Ax_s C rhs).
    { apply BProv_ass_head. }
    assert (hleft : BProv Ax_s (oldSucc :: C) newSucc).
    {
      set (D := oldSucc :: C).
      assert (holdD : BProv Ax_s D (iffForm oldSucc tailMem)).
      {
        unfold D, C.
        exact (BProv_context_prefix Ax_s [oldSucc; rhs] G _ holdIff).
      }
      assert (hold : BProv Ax_s D oldSucc).
      { apply BProv_ass_head. }
      pose proof (BProv_andE1 Ax_s D _ _ holdD) as htoTail.
      pose proof (BProv_mp Ax_s D oldSucc tailMem htoTail hold) as htail.
      assert (hnewD : BProv Ax_s D (iffForm newSucc tailMem)).
      {
        unfold D, C.
        exact (BProv_context_prefix Ax_s [oldSucc; rhs] G _ hnewIff).
      }
      pose proof (BProv_andE2 Ax_s D _ _ hnewD) as htoNew.
      exact (BProv_mp Ax_s D tailMem newSucc htoNew htail).
    }
    assert (hright : BProv Ax_s (badEq :: C) newSucc).
    {
      set (D := badEq :: C).
      assert (hbad : BProv Ax_s D badEq).
      { apply BProv_ass_head. }
      pose proof (BProv_Ax_s_zeroNotSucc_term D (tVar 0)) as hnot.
      pose proof (BProv_mp Ax_s D badEq pBot hnot hbad) as hbot.
      exact (BProv_botE Ax_s D newSucc hbot).
    }
    pose proof (BProv_orE Ax_s C oldSucc badEq newSucc
      hcases hleft hright) as hnew.
    unfold C.
    exact (BProv_impI Ax_s G rhs newSucc hnew).
  }
  unfold newSucc, oldSucc, tailMem, badEq, rhs.
  exact (BProv_andI Ax_s G _ _ hforward hreverse).
Qed.

Lemma BProv_Ax_s_hfAdjoinGraph_zero_of_shared_tail :
  forall G newHead oldHead tail newBit oldBit,
  BProv Ax_s G (eqConstAt newBit 1) ->
  BProv Ax_s G (div2StepAt newHead tail newBit) ->
  BProv Ax_s G (div2StepAt oldHead tail oldBit) ->
  BProv Ax_s G
    (hfAdjoinGraphTermAt (tVar newHead) (tVar oldHead) tZero).
Proof.
  intros G newHead oldHead tail newBit oldBit
    hnewBitOne hnewStep holdStep.
  set (phi := iffForm
    (hfMemAt 0 (S newHead))
    (pOr (hfMemAt 0 (S oldHead)) (pEq (tVar 0) tZero))).
  assert (hzero : BProv Ax_s G (subst substZero phi)).
  {
    set (zeroEq := eqConstAt 0 0).
    pose proof (BProv_exists_eqConstAt Ax_s G 0) as hex.
    assert (hopened : BProv Ax_s
        (zeroEq :: map (rename S) G)
        (rename S (subst substZero phi))).
    {
      set (C := zeroEq :: map (rename S) G).
      assert (hqueryZero : BProv Ax_s C (eqConstAt 0 0)).
      { apply BProv_ass_head. }
      pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
        hnewStep S) as hnewRen.
      assert (hnewC : BProv Ax_s C
          (div2StepAt (S newHead) (S tail) (S newBit))).
      {
        pose proof (BProv_context_cons Ax_s (map (rename S) G)
          zeroEq _ hnewRen) as h.
        unfold div2StepAt, boolAt, zeroAt, oneAt, eqConstAt in h |- *.
        simpl in h |- *. exact h.
      }
      pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
        hnewBitOne S) as hbitRen.
      assert (hbitC : BProv Ax_s C (eqConstAt (S newBit) 1)).
      {
        pose proof (BProv_context_cons Ax_s (map (rename S) G)
          zeroEq _ hbitRen) as h.
        unfold eqConstAt in h |- *. simpl in h |- *. exact h.
      }
      pose proof
        (BProv_Ax_s_hfMemAt_of_eqConst_zero_and_div2StepAt_bit_one
          C 0 (S newHead) (S tail) (S newBit)
          hqueryZero hbitC hnewC) as hnewMem.
      set (newMem := hfMemAt 0 (S newHead)).
      set (oldMem := hfMemAt 0 (S oldHead)).
      set (queryEq := pEq (tVar 0) tZero).
      set (rhs := pOr oldMem queryEq).
      assert (hpoint : BProv Ax_s C (iffForm newMem rhs)).
      {
        assert (hforward : BProv Ax_s C (pImp newMem rhs)).
        {
          set (D := newMem :: C).
          assert (heq : BProv Ax_s D queryEq).
          {
            pose proof (BProv_context_cons Ax_s C newMem _ hqueryZero) as h.
            unfold queryEq, eqConstAt in h |- *. simpl in h |- *. exact h.
          }
          unfold D, rhs.
          exact (BProv_impI Ax_s C newMem (pOr oldMem queryEq)
            (BProv_orI2 Ax_s D oldMem queryEq heq)).
        }
        assert (hreverse : BProv Ax_s C (pImp rhs newMem)).
        {
          exact (BProv_impI Ax_s C rhs newMem
            (BProv_context_cons Ax_s C rhs _ hnewMem)).
        }
        exact (BProv_andI Ax_s C _ _ hforward hreverse).
      }
      assert (hpointSub : BProv Ax_s C
          (subst (instTerm (tVar 0)) (rename (up S) phi))).
      {
        rewrite subst_instTerm_var_zero_rename_up_succ.
        unfold phi, newMem, oldMem, queryEq, rhs.
        exact hpoint.
      }
      assert (hzeroSub : BProv Ax_s C
          (subst (instTerm tZero) (rename (up S) phi))).
      {
        unfold eqConstAt in hqueryZero. simpl in hqueryZero.
        exact (BProv_eqElim Ax_s C (tVar 0) tZero
          (rename (up S) phi) hqueryZero hpointSub).
      }
      replace (rename S (subst substZero phi))
        with (subst (instTerm tZero) (rename (up S) phi)).
      - exact hzeroSub.
      - pose proof (subst_instTerm_rename_up phi S tZero) as hnorm.
        unfold substZero, instTerm in hnorm.
        exact hnorm.
    }
    exact (BProv_exE_of_sentences Ax_s G zeroEq
      (subst substZero phi) sentence_ax_s hex hopened).
  }
  assert (hsuccBody : BProv Ax_s
      (phi :: map (rename S) G) (subst substSuccVar phi)).
  {
    set (C := phi :: map (rename S) G).
    pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
      hnewStep S) as hnewRen.
    assert (hnewC : BProv Ax_s C
        (div2StepAt (S newHead) (S tail) (S newBit))).
    {
      pose proof (BProv_context_cons Ax_s (map (rename S) G)
        phi _ hnewRen) as h.
      unfold div2StepAt, boolAt, zeroAt, oneAt, eqConstAt in h |- *.
      simpl in h |- *. exact h.
    }
    pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
      holdStep S) as holdRen.
    assert (holdC : BProv Ax_s C
        (div2StepAt (S oldHead) (S tail) (S oldBit))).
    {
      pose proof (BProv_context_cons Ax_s (map (rename S) G)
        phi _ holdRen) as h.
      unfold div2StepAt, boolAt, zeroAt, oneAt, eqConstAt in h |- *.
      simpl in h |- *. exact h.
    }
    pose proof (BProv_Ax_s_hfAdjoin_positive_zero_lift
      C (S newHead) (S oldHead) (S tail) (S newBit) (S oldBit)
      hnewC holdC) as hlift.
    exact hlift.
  }
  assert (hsuccImp : BProv Ax_s (map (rename S) G)
      (pImp phi (subst substSuccVar phi))).
  {
    exact (BProv_impI Ax_s (map (rename S) G)
      phi (subst substSuccVar phi) hsuccBody).
  }
  pose proof (BProv_allI_of_sentences Ax_s G _
    sentence_ax_s hsuccImp) as hsucc.
  pose proof (BProv_Ax_s_induction_rule G phi hzero hsucc) as hall.
  unfold hfAdjoinGraphTermAt, phi.
  simpl.
  exact hall.
Qed.

Lemma BProv_exists_eq_term : forall B G (t : term),
  BProv B G (pEx (pEq (tVar 0) (Term.rename S t))).
Proof.
  intros B G t.
  apply (BProv_exI B G _ t).
  simpl.
  rewrite term_subst_instTerm_rename_succ.
  exact (BProv_eqRefl B G t).
Qed.

Lemma BProv_Ax_s_div2StepAt_of_named_head_and_old_step :
  forall G newHead newTail oldHead oldTail bit,
  BProv Ax_s G
    (pEq (tVar newHead)
      (tAdd (tAdd (tVar newTail) (tVar newTail)) (tVar bit))) ->
  BProv Ax_s G (div2StepAt oldHead oldTail bit) ->
  BProv Ax_s G (div2StepAt newHead newTail bit).
Proof.
  intros G newHead newTail oldHead oldTail bit hname holdStep.
  pose proof (BProv_andE1 Ax_s G _ _ holdStep) as hbool.
  unfold div2StepAt.
  exact (BProv_andI Ax_s G _ _ hbool hname).
Qed.

Lemma BProv_Ax_s_hfAdjoinExistsTermAt_succ_of_step_and_tail_graph :
  forall G oldHead oldTail bit newTail elem,
  BProv Ax_s G (div2StepAt oldHead oldTail bit) ->
  BProv Ax_s G (hfAdjoinGraphAt newTail oldTail elem) ->
  BProv Ax_s G
    (hfAdjoinExistsTermAt (tVar oldHead) (tSucc (tVar elem))).
Proof.
  intros G oldHead oldTail bit newTail elem holdStep htail.
  set (newHeadTerm := tAdd
    (tAdd (tVar newTail) (tVar newTail)) (tVar bit)).
  set (nameBody := pEq (tVar 0) (Term.rename S newHeadTerm)).
  set (target := hfAdjoinExistsTermAt
    (tVar oldHead) (tSucc (tVar elem))).
  pose proof (BProv_exists_eq_term Ax_s G newHeadTerm) as hnameEx.
  apply (BProv_exE_of_sentences Ax_s G nameBody target
    sentence_ax_s hnameEx).
  set (H := nameBody :: map (rename S) G).
  assert (hname : BProv Ax_s H
      (pEq (tVar 0)
        (tAdd (tAdd (tVar (S newTail)) (tVar (S newTail)))
          (tVar (S bit))))).
  {
    apply BProv_ass.
    unfold H, nameBody, newHeadTerm.
    simpl. left. reflexivity.
  }
  pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
    holdStep S) as holdRen.
  assert (holdH : BProv Ax_s H
      (div2StepAt (S oldHead) (S oldTail) (S bit))).
  {
    pose proof (BProv_context_cons Ax_s (map (rename S) G)
      nameBody _ holdRen) as h.
    unfold div2StepAt, boolAt, zeroAt, oneAt, eqConstAt in h |- *.
    simpl in h |- *. exact h.
  }
  pose proof
    (BProv_Ax_s_div2StepAt_of_named_head_and_old_step
      H 0 (S newTail) (S oldHead) (S oldTail) (S bit)
      hname holdH) as hnewStep.
  pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
    htail S) as htailRen.
  rewrite rename_S_hfAdjoinGraphAt in htailRen.
  assert (htailH : BProv Ax_s H
      (hfAdjoinGraphAt (S newTail) (S oldTail) (S elem))).
  { exact (BProv_context_cons Ax_s (map (rename S) G)
      nameBody _ htailRen). }
  pose proof (BProv_Ax_s_hfAdjoinGraph_heads_of_same_bit
    H 0 (S newTail) (S oldHead) (S oldTail) (S bit) (S elem)
    hnewStep holdH htailH) as hgraph.
  pose proof (BProv_hfAdjoinExistsTermAt_of_term
    Ax_s H (tVar 0) (tVar (S oldHead)) (tSucc (tVar (S elem)))
    hgraph) as hex.
  unfold H, target.
  rewrite rename_hfAdjoinExistsTermAt.
  simpl.
  exact hex.
Qed.

Lemma BProv_Ax_s_hfAdjoinExistsTermAt_zero :
  forall G oldCode,
  BProv Ax_s G
    (hfAdjoinExistsTermAt (tVar oldCode) tZero).
Proof.
  intros G oldCode.
  set (target := hfAdjoinExistsTermAt (tVar oldCode) tZero).
  apply (BProv_Ax_s_of_div2TotalAt_opened_step
    G oldCode target (BProv_Ax_s_div2TotalAt G oldCode)).
  set (J := div2TotalOpenedStepContext G oldCode).
  assert (holdStep : BProv Ax_s J
      (div2StepAt (oldCode + 2) 1 0)).
  {
    apply BProv_ass.
    unfold J, div2TotalOpenedStepContext.
    simpl. left. reflexivity.
  }
  set (newTerm := tSucc (tAdd (tVar 1) (tVar 1))).
  set (nameBody := pEq (tVar 0) (Term.rename S newTerm)).
  pose proof (BProv_exists_eq_term Ax_s J newTerm) as hnameEx.
  apply (BProv_exE_of_sentences Ax_s J nameBody
    (rename S (rename S target)) sentence_ax_s hnameEx).
  set (H := nameBody :: map (rename S) J).
  set (oneEq := eqConstAt 0 1).
  pose proof (BProv_exists_eqConstAt Ax_s H 1) as honeEx.
  apply (BProv_exE_of_sentences Ax_s H oneEq
    (rename S (rename S (rename S target)))
    sentence_ax_s honeEx).
  set (K := oneEq :: map (rename S) H).
  assert (hone : BProv Ax_s K (eqConstAt 0 1)).
  { apply BProv_ass. unfold K, oneEq. simpl. left. reflexivity. }
  assert (hname : BProv Ax_s K
      (pEq (tVar 1) (tSucc (tAdd (tVar 3) (tVar 3))))).
  {
    apply BProv_ass.
    unfold K, H, nameBody, newTerm.
    simpl. right. left. reflexivity.
  }
  assert (hnewOdd : BProv Ax_s K (oddDoubleEqAt 1 3)).
  { unfold oddDoubleEqAt. exact hname. }
  pose proof (BProv_Ax_s_div2StepAt_of_oddDoubleEqAt_bit_one
    K 1 3 0 hnewOdd hone) as hnewStep.
  assert (holdK : BProv Ax_s K
      (div2StepAt (oldCode + 4) 3 2)).
  {
    replace (div2StepAt (oldCode + 4) 3 2)
      with (rename S (rename S
        (div2StepAt (oldCode + 2) 1 0))).
    - apply BProv_ass.
      unfold K, H, J, div2TotalOpenedStepContext.
      simpl. right. right. left. reflexivity.
    - unfold div2StepAt, boolAt, zeroAt, oneAt, eqConstAt.
      simpl.
      replace (S (S (oldCode + 2))) with (oldCode + 4) by lia.
      reflexivity.
  }
  pose proof (BProv_Ax_s_hfAdjoinGraph_zero_of_shared_tail
    K 1 (oldCode + 4) 3 0 2 hone hnewStep holdK) as hgraph.
  pose proof (BProv_hfAdjoinExistsTermAt_of_term
    Ax_s K (tVar 1) (tVar (oldCode + 4)) tZero hgraph) as hex.
  unfold target.
  repeat rewrite rename_hfAdjoinExistsTermAt.
  simpl.
  replace (S (S (S (S oldCode)))) with (oldCode + 4) by lia.
  exact hex.
Qed.

Definition hfAdjoinTotalTermAt (elemCode : term) : formula :=
  pAll (hfAdjoinExistsTermAt
    (tVar 0) (Term.rename S elemCode)).

Lemma subst_hfAdjoinTotalTermAt : forall sigma elemCode,
  subst sigma (hfAdjoinTotalTermAt elemCode) =
    hfAdjoinTotalTermAt (Term.subst sigma elemCode).
Proof.
  intros sigma elemCode.
  unfold hfAdjoinTotalTermAt.
  cbn [subst].
  rewrite subst_hfAdjoinExistsTermAt.
  simpl.
  rewrite Term.subst_rename_succ_up.
  reflexivity.
Qed.

Lemma rename_hfAdjoinTotalTermAt : forall r elemCode,
  rename r (hfAdjoinTotalTermAt elemCode) =
    hfAdjoinTotalTermAt (Term.rename r elemCode).
Proof.
  intros r elemCode.
  rewrite <- subst_var_rename.
  rewrite subst_hfAdjoinTotalTermAt.
  rewrite term_subst_var_rename.
  reflexivity.
Qed.

Lemma BProv_hfAdjoinExistsTermAt_of_total :
  forall B G elemCode oldCode,
  BProv B G (hfAdjoinTotalTermAt elemCode) ->
  BProv B G (hfAdjoinExistsTermAt oldCode elemCode).
Proof.
  intros B G elemCode oldCode htotal.
  unfold hfAdjoinTotalTermAt in htotal.
  pose proof (BProv_allE B G _ oldCode htotal) as hraw.
  rewrite subst_hfAdjoinExistsTermAt in hraw.
  simpl in hraw.
  repeat rewrite term_subst_instTerm_rename_succ in hraw.
  exact hraw.
Qed.

Lemma BProv_Ax_s_hfAdjoinTotalTermAt_zero :
  BProv Ax_s [] (hfAdjoinTotalTermAt tZero).
Proof.
  pose proof (BProv_Ax_s_hfAdjoinExistsTermAt_zero [] 0) as hbody.
  pose proof (BProv_allI_of_sentences Ax_s [] _
    sentence_ax_s hbody) as hall.
  unfold hfAdjoinTotalTermAt.
  simpl.
  exact hall.
Qed.

Lemma BProv_Ax_s_hfAdjoinTotalTermAt_succ :
  BProv Ax_s [hfAdjoinTotalTermAt (tVar 0)]
    (hfAdjoinTotalTermAt (tSucc (tVar 0))).
Proof.
  set (phi := hfAdjoinTotalTermAt (tVar 0)).
  set (body := hfAdjoinExistsTermAt
    (tVar 0) (tSucc (tVar 1))).
  assert (hbody : BProv Ax_s [rename S phi] body).
  {
    set (G1 := [rename S phi]).
    change (BProv Ax_s G1 body).
    apply (BProv_Ax_s_of_div2TotalAt_opened_step
      G1 0 body (BProv_Ax_s_div2TotalAt G1 0)).
    set (H := div2TotalOpenedStepContext G1 0).
    assert (holdStep : BProv Ax_s H (div2StepAt 2 1 0)).
    {
      apply BProv_ass.
      unfold H, div2TotalOpenedStepContext.
      simpl. left. reflexivity.
    }
    assert (hihRaw : BProv Ax_s H
        (rename S (rename S (rename S phi)))).
    {
      apply BProv_ass.
      unfold H, G1, div2TotalOpenedStepContext.
      simpl. right. right. left. reflexivity.
    }
    assert (htotal : BProv Ax_s H
        (hfAdjoinTotalTermAt (tVar 3))).
    {
      repeat rewrite rename_hfAdjoinTotalTermAt in hihRaw.
      unfold phi in hihRaw.
      simpl in hihRaw.
      exact hihRaw.
    }
    pose proof (BProv_hfAdjoinExistsTermAt_of_total
      Ax_s H (tVar 3) (tVar 1) htotal) as htailEx.
    apply (BProv_Ax_s_hfAdjoinExistsTermAt_elim_opened
      H (tVar 1) (tVar 3) (rename S (rename S body)));
      [|exact htailEx].
    set (graphBody := hfAdjoinGraphTermAt
      (tVar 0) (tVar 2) (tVar 4)).
    set (K := graphBody :: map (rename S) H).
    assert (htail : BProv Ax_s K (hfAdjoinGraphAt 0 2 4)).
    {
      unfold hfAdjoinGraphAt, K, graphBody.
      apply BProv_ass_head.
    }
    pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s H _
      holdStep S) as holdRen.
    assert (holdK : BProv Ax_s K (div2StepAt 3 2 1)).
    {
      pose proof (BProv_context_cons Ax_s (map (rename S) H)
        graphBody _ holdRen) as h.
      unfold div2StepAt, boolAt, zeroAt, oneAt, eqConstAt in h |- *.
      simpl in h |- *. exact h.
    }
    pose proof
      (BProv_Ax_s_hfAdjoinExistsTermAt_succ_of_step_and_tail_graph
        K 3 2 1 0 4 holdK htail) as hresult.
    unfold body.
    repeat rewrite rename_hfAdjoinExistsTermAt.
    simpl.
    exact hresult.
  }
  pose proof (BProv_allI_of_sentences Ax_s [phi] body
    sentence_ax_s hbody) as hall.
  unfold phi, body, hfAdjoinTotalTermAt in *.
  simpl in hall |- *.
  exact hall.
Qed.

Theorem BProv_Ax_s_all_hfAdjoinTotalTermAt :
  BProv Ax_s [] (pAll (hfAdjoinTotalTermAt (tVar 0))).
Proof.
  set (phi := hfAdjoinTotalTermAt (tVar 0)).
  assert (hzero : BProv Ax_s [] (subst substZero phi)).
  {
    unfold phi.
    rewrite subst_hfAdjoinTotalTermAt.
    simpl.
    exact BProv_Ax_s_hfAdjoinTotalTermAt_zero.
  }
  assert (hsuccBody : BProv Ax_s [phi] (subst substSuccVar phi)).
  {
    unfold phi.
    rewrite subst_hfAdjoinTotalTermAt.
    simpl.
    exact BProv_Ax_s_hfAdjoinTotalTermAt_succ.
  }
  assert (hsuccImp : BProv Ax_s []
      (pImp phi (subst substSuccVar phi))).
  {
    exact (BProv_impI Ax_s [] phi (subst substSuccVar phi) hsuccBody).
  }
  pose proof (BProv_allI_of_sentences Ax_s [] _
    sentence_ax_s hsuccImp) as hsucc.
  exact (BProv_Ax_s_induction_rule [] phi hzero hsucc).
Qed.

Lemma BProv_Ax_s_hfAdjoinTotalTermAt_of_all :
  forall G elemCode,
  BProv Ax_s G (hfAdjoinTotalTermAt elemCode).
Proof.
  intros G elemCode.
  pose proof (BProv_weaken_nil Ax_s G _
    BProv_Ax_s_all_hfAdjoinTotalTermAt) as hall.
  pose proof (BProv_allE Ax_s G _ elemCode hall) as hraw.
  rewrite subst_hfAdjoinTotalTermAt in hraw.
  simpl in hraw.
  exact hraw.
Qed.

Theorem PAHFAdjoinExistence_proof : PAHFAdjoinExistence.
Proof.
  intros G oldCode elemCode.
  exact (BProv_hfAdjoinExistsTermAt_of_total
    Ax_s G elemCode oldCode
    (BProv_Ax_s_hfAdjoinTotalTermAt_of_all G elemCode)).
Qed.
