(* ===================================================================== *)
(*  PAHFBetaShiftPrefix.v                                                *)
(*                                                                       *)
(*  Internal PA construction of a beta code obtained by dropping the     *)
(*  head of another beta code.  The CRT/capacity layer is supplied by     *)
(*  PAHFOrdinalCodeTotalInduction; this file supplies the fixed-step      *)
(*  shifted-prefix induction and packages it as the public shifted-tail   *)
(*  existential from PAHF.v.                                             *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF PAHFProofCalculus PAHFOrdinalCode PAHFOrdinalCodeTotal
  PAHFOrdinalCodeTotalCapacity PAHFOrdinalCodeTotalInduction.

Import ListNotations.
Import PA PA.Term PA.Formula.

(* Compatibility aliases: the canonical definitions now live in [PA.Formula]. *)
Definition betaShiftPrefixTermAt := PA.Formula.betaShiftPrefixTermAt.

Definition betaShiftPrefixCodeExistsTermAt :=
  PA.Formula.betaShiftPrefixCodeExistsTermAt.

Definition betaShiftPrefixCodeExistsTermAtBody :=
  PA.Formula.betaShiftPrefixCodeExistsTermAtBody.

(** A local endpoint-output wrapper.  It is intentionally local to this
    construction so the prefix layer does not depend on membership-tail
    modules that consume its final theorem. *)
Definition betaShiftSourceEntryExistsTermAt
    (code step idx : term) : formula :=
  pEx (betaTermTermAt (tVar 0)
    (Term.rename S code)
    (Term.rename S step)
    (Term.rename S idx)).

Definition betaShiftSourceEntryExistsTermAtBody
    (code step idx : term) : formula :=
  betaTermTermAt (tVar 0)
    (Term.rename S code)
    (Term.rename S step)
    (Term.rename S idx).

Lemma subst_betaShiftPrefixTermAt :
  forall sigma oldCode oldStep newCode newStep bound,
  subst sigma
      (betaShiftPrefixTermAt oldCode oldStep newCode newStep bound) =
    betaShiftPrefixTermAt
      (Term.subst sigma oldCode)
      (Term.subst sigma oldStep)
      (Term.subst sigma newCode)
      (Term.subst sigma newStep)
      (Term.subst sigma bound).
Proof.
  intros sigma oldCode oldStep newCode newStep bound.
  exact (PA.Formula.subst_betaShiftPrefixTermAt
    sigma oldCode oldStep newCode newStep bound).
Qed.

Lemma rename_betaShiftPrefixTermAt :
  forall r oldCode oldStep newCode newStep bound,
  rename r
      (betaShiftPrefixTermAt oldCode oldStep newCode newStep bound) =
    betaShiftPrefixTermAt
      (Term.rename r oldCode)
      (Term.rename r oldStep)
      (Term.rename r newCode)
      (Term.rename r newStep)
      (Term.rename r bound).
Proof.
  intros r oldCode oldStep newCode newStep bound.
  exact (PA.Formula.rename_betaShiftPrefixTermAt
    r oldCode oldStep newCode newStep bound).
Qed.

Lemma subst_betaShiftPrefixCodeExistsTermAt :
  forall sigma oldCode oldStep newStep bound,
  subst sigma
      (betaShiftPrefixCodeExistsTermAt oldCode oldStep newStep bound) =
    betaShiftPrefixCodeExistsTermAt
      (Term.subst sigma oldCode)
      (Term.subst sigma oldStep)
      (Term.subst sigma newStep)
      (Term.subst sigma bound).
Proof.
  intros sigma oldCode oldStep newStep bound.
  exact (PA.Formula.subst_betaShiftPrefixCodeExistsTermAt
    sigma oldCode oldStep newStep bound).
Qed.

Lemma rename_betaShiftPrefixCodeExistsTermAt :
  forall r oldCode oldStep newStep bound,
  rename r
      (betaShiftPrefixCodeExistsTermAt oldCode oldStep newStep bound) =
    betaShiftPrefixCodeExistsTermAt
      (Term.rename r oldCode)
      (Term.rename r oldStep)
      (Term.rename r newStep)
      (Term.rename r bound).
Proof.
  intros r oldCode oldStep newStep bound.
  exact (PA.Formula.rename_betaShiftPrefixCodeExistsTermAt
    r oldCode oldStep newStep bound).
Qed.

Lemma subst_betaShiftSourceEntryExistsTermAt :
  forall sigma code step idx,
  subst sigma (betaShiftSourceEntryExistsTermAt code step idx) =
    betaShiftSourceEntryExistsTermAt
      (Term.subst sigma code)
      (Term.subst sigma step)
      (Term.subst sigma idx).
Proof.
  intros sigma code step idx.
  unfold betaShiftSourceEntryExistsTermAt.
  cbn [subst].
  rewrite subst_betaTermTermAt.
  repeat rewrite Term.subst_rename_succ_up.
  reflexivity.
Qed.

Lemma rename_betaShiftSourceEntryExistsTermAt :
  forall r code step idx,
  rename r (betaShiftSourceEntryExistsTermAt code step idx) =
    betaShiftSourceEntryExistsTermAt
      (Term.rename r code)
      (Term.rename r step)
      (Term.rename r idx).
Proof.
  intros r code step idx.
  rename_from_subst subst_betaShiftSourceEntryExistsTermAt.
Qed.

Lemma BProv_Ax_s_betaShiftSourceEntryExistsTermAt_of_term :
  forall G code step idx out,
  BProv Ax_s G (betaTermTermAt out code step idx) ->
  BProv Ax_s G (betaShiftSourceEntryExistsTermAt code step idx).
Proof.
  intros G code step idx out hentry.
  unfold betaShiftSourceEntryExistsTermAt.
  apply (BProv_exI Ax_s G
    (betaTermTermAt (tVar 0)
      (Term.rename S code) (Term.rename S step) (Term.rename S idx))
    out).
  rewrite subst_betaTermTermAt.
  simpl.
  repeat rewrite term_subst_instTerm_rename_succ.
  exact hentry.
Qed.

Lemma BProv_Ax_s_betaShiftSourceEntryExistsTermAt_elim_opened :
  forall G code step idx target,
  BProv Ax_s
    (betaShiftSourceEntryExistsTermAtBody code step idx ::
      map (rename S) G)
    (rename S target) ->
  BProv Ax_s G (betaShiftSourceEntryExistsTermAt code step idx) ->
  BProv Ax_s G target.
Proof.
  intros G code step idx target hopened hex.
  unfold betaShiftSourceEntryExistsTermAt in hex.
  unfold betaShiftSourceEntryExistsTermAtBody in hopened.
  exact (BProv_exE_of_sentences Ax_s G
    (betaTermTermAt (tVar 0)
      (Term.rename S code) (Term.rename S step) (Term.rename S idx))
    target sentence_ax_s hex hopened).
Qed.

Lemma BProv_Ax_s_betaShiftPrefixTermAt_zero :
  forall G oldCode oldStep newCode newStep,
  BProv Ax_s G
    (betaShiftPrefixTermAt
      oldCode oldStep newCode newStep tZero).
Proof.
  intros G oldCode oldStep newCode newStep.
  set (antecedent := ltTermAt (tVar 0) tZero).
  set (innerBody := pImp
    (betaTermTermAt (tVar 0)
      (Term.rename (fun n => n + 2) oldCode)
      (Term.rename (fun n => n + 2) oldStep)
      (tSucc (tVar 1)))
    (betaTermTermAt (tVar 0)
      (Term.rename (fun n => n + 2) newCode)
      (Term.rename (fun n => n + 2) newStep)
      (tVar 1))).
  set (body := pImp antecedent (pAll innerBody)).
  set (C := antecedent :: map (rename S) G).
  assert (hlt : BProv Ax_s C (ltTermAt (tVar 0) tZero)).
  {
    apply BProv_ass.
    unfold C, antecedent. simpl. left. reflexivity.
  }
  assert (hle : BProv Ax_s C (leTermAt tZero (tVar 0))).
  { apply BProv_Ax_s_leTermAt_zero_left. }
  assert (hbot : BProv Ax_s C pBot).
  {
    exact (BProv_Ax_s_ltTermAt_leTermAt_bot
      C (tVar 0) tZero hlt hle).
  }
  assert (hinner : BProv Ax_s C (pAll innerBody)).
  { exact (BProv_botE Ax_s C (pAll innerBody) hbot). }
  assert (himp : BProv Ax_s (map (rename S) G) body).
  {
    unfold C in hinner.
    exact (BProv_impI Ax_s (map (rename S) G)
      antecedent (pAll innerBody) hinner).
  }
  assert (hall : BProv Ax_s G (pAll body)).
  {
    exact (BProv_allI_of_sentences Ax_s G body
      sentence_ax_s himp).
  }
  unfold betaShiftPrefixTermAt, body, antecedent, innerBody in *.
  simpl in hall |- *.
  exact hall.
Qed.

Lemma BProv_Ax_s_betaShiftPrefixCodeExistsTermAt_of_term :
  forall G oldCode oldStep newCode newStep bound,
  BProv Ax_s G
    (betaShiftPrefixTermAt
      oldCode oldStep newCode newStep bound) ->
  BProv Ax_s G
    (betaShiftPrefixCodeExistsTermAt
      oldCode oldStep newStep bound).
Proof.
  intros G oldCode oldStep newCode newStep bound hprefix.
  unfold betaShiftPrefixCodeExistsTermAt.
  apply (BProv_exI Ax_s G
    (betaShiftPrefixTermAt
      (Term.rename S oldCode) (Term.rename S oldStep)
      (tVar 0) (Term.rename S newStep) (Term.rename S bound))
    newCode).
  rewrite subst_betaShiftPrefixTermAt.
  simpl.
  repeat rewrite term_subst_instTerm_rename_succ.
  exact hprefix.
Qed.

Lemma BProv_Ax_s_betaShiftPrefixCodeExistsTermAt_elim_opened :
  forall G oldCode oldStep newStep bound target,
  BProv Ax_s
    (betaShiftPrefixCodeExistsTermAtBody
        oldCode oldStep newStep bound :: map (rename S) G)
    (rename S target) ->
  BProv Ax_s G
    (betaShiftPrefixCodeExistsTermAt
      oldCode oldStep newStep bound) ->
  BProv Ax_s G target.
Proof.
  intros G oldCode oldStep newStep bound target hopened hex.
  unfold betaShiftPrefixCodeExistsTermAt in hex.
  unfold betaShiftPrefixCodeExistsTermAtBody in hopened.
  exact (BProv_exE_of_sentences Ax_s G
    (betaShiftPrefixTermAt
      (Term.rename S oldCode) (Term.rename S oldStep)
      (tVar 0) (Term.rename S newStep) (Term.rename S bound))
    target sentence_ax_s hex hopened).
Qed.

Lemma BProv_Ax_s_betaShiftPrefixCodeExistsTermAt_zero :
  forall G oldCode oldStep newStep,
  BProv Ax_s G
    (betaShiftPrefixCodeExistsTermAt
      oldCode oldStep newStep tZero).
Proof.
  intros G oldCode oldStep newStep.
  apply (BProv_Ax_s_betaShiftPrefixCodeExistsTermAt_of_term
    G oldCode oldStep tZero newStep tZero).
  apply BProv_Ax_s_betaShiftPrefixTermAt_zero.
Qed.

(** Every bounded remainder is at most its dividend. *)
Lemma BProv_Ax_s_leTermAt_of_remTermTermAt_shift :
  forall G rem value modulus,
  BProv Ax_s G (remTermTermAt rem value modulus) ->
  BProv Ax_s G (leTermAt rem value).
Proof.
  intros G rem value modulus hrem.
  set (target := leTermAt rem value).
  apply (BProv_Ax_s_remTermTermAt_elim_opened
    G target rem value modulus); [|exact hrem].
  set (body := pAnd
    (ltTermAt (Term.rename S rem) (Term.rename S modulus))
    (pEq (Term.rename S value)
      (tAdd
        (tMul (tVar 0) (Term.rename S modulus))
        (Term.rename S rem)))).
  set (D := body :: map (rename S) G).
  set (rem1 := Term.rename S rem).
  set (value1 := Term.rename S value).
  set (modulus1 := Term.rename S modulus).
  set (base := tMul (tVar 0) modulus1).
  assert (hbody : BProv Ax_s D body).
  { apply BProv_ass. unfold D. simpl. left. reflexivity. }
  assert (hvalue : BProv Ax_s D
      (pEq value1 (tAdd base rem1))).
  {
    unfold body, value1, modulus1, base in hbody.
    exact (BProv_andE2 Ax_s D _ _ hbody).
  }
  pose proof (BProv_Ax_s_add_comm_terms D base rem1) as hcomm.
  assert (hvalue' : BProv Ax_s D
      (pEq value1 (tAdd rem1 base))).
  { exact (BProv_eqTrans Ax_s D _ _ _ hvalue hcomm). }
  pose proof (BProv_Ax_s_leTermAt_of_eq_add_right_terms
    D rem1 value1 base hvalue') as hle.
  unfold target.
  rewrite rename_leTermAt.
  unfold rem1, value1 in hle.
  exact hle.
Qed.

Lemma BProv_Ax_s_leTermAt_output_of_betaTermTermAt_shift :
  forall G out code step idx,
  BProv Ax_s G (betaTermTermAt out code step idx) ->
  BProv Ax_s G (leTermAt out code).
Proof.
  intros G out code step idx hbeta.
  apply BProv_Ax_s_leTermAt_of_remTermTermAt_shift with
    (modulus := betaModTermTerm step idx).
  exact (BProv_Ax_s_remTermTermAt_of_betaTermTermAt
    G out code step idx hbeta).
Qed.

Lemma BProv_Ax_s_ltTermAt_betaMod_of_betaTermTermAt_le_step_shift :
  forall G out sourceCode sourceStep sourceIdx targetStep targetIdx,
  BProv Ax_s G
    (betaTermTermAt out sourceCode sourceStep sourceIdx) ->
  BProv Ax_s G (leTermAt (tSucc sourceCode) targetStep) ->
  BProv Ax_s G
    (ltTermAt out (betaModTermTerm targetStep targetIdx)).
Proof.
  intros G out sourceCode sourceStep sourceIdx targetStep targetIdx
    hbeta hlarge.
  pose proof
    (BProv_Ax_s_leTermAt_output_of_betaTermTermAt_shift
      G out sourceCode sourceStep sourceIdx hbeta) as houtLe.
  pose proof (BProv_Ax_s_leTermAt_succ_succ
    G out sourceCode houtLe) as hsuccOutLe.
  pose proof (BProv_Ax_s_leTermAt_trans G
    (tSucc out) (tSucc sourceCode) targetStep
    hsuccOutLe hlarge) as hsuccOutStep.
  pose proof (BProv_Ax_s_leTermAt_step_betaModTermTerm
    G targetStep targetIdx) as hstepMod.
  pose proof (BProv_Ax_s_leTermAt_trans G
    (tSucc out) targetStep (betaModTermTerm targetStep targetIdx)
    hsuccOutStep hstepMod) as hsuccOutMod.
  exact (BProv_Ax_s_ltTermAt_of_succ_leTermAt
    G out (betaModTermTerm targetStep targetIdx) hsuccOutMod).
Qed.

Lemma BProv_Ax_s_betaShiftPrefixTermAt_entry_of_ltTerm :
  forall G oldCode oldStep newCode newStep bound idx out,
  BProv Ax_s G
    (betaShiftPrefixTermAt
      oldCode oldStep newCode newStep bound) ->
  BProv Ax_s G (ltTermAt idx bound) ->
  BProv Ax_s G
    (betaTermTermAt out oldCode oldStep (tSucc idx)) ->
  BProv Ax_s G
    (betaTermTermAt out newCode newStep idx).
Proof.
  intros G oldCode oldStep newCode newStep bound idx out
    hprefix hlt hold.
  pose proof (BProv_allE Ax_s G _ idx hprefix) as hidx.
  cbn [subst] in hidx.
  rewrite subst_ltTermAt in hidx.
  rewrite !subst_betaTermTermAt in hidx.
  simpl in hidx.
  repeat rewrite term_subst_upSubst_instTerm_rename_add_two in hidx.
  repeat rewrite term_subst_instTerm_rename_succ in hidx.
  assert (hall : BProv Ax_s G
      (pAll (pImp
        (betaTermTermAt (tVar 0)
          (Term.rename S oldCode)
          (Term.rename S oldStep)
          (tSucc (Term.rename S idx)))
        (betaTermTermAt (tVar 0)
          (Term.rename S newCode)
          (Term.rename S newStep)
          (Term.rename S idx))))).
  { exact (BProv_mp Ax_s G _ _ hidx hlt). }
  pose proof (BProv_allE Ax_s G _ out hall) as hout.
  cbn [subst] in hout.
  rewrite !subst_betaTermTermAt in hout.
  simpl in hout.
  repeat rewrite term_subst_instTerm_rename_succ in hout.
  exact (BProv_mp Ax_s G
    (betaTermTermAt out oldCode oldStep (tSucc idx))
    (betaTermTermAt out newCode newStep idx)
    hout hold).
Qed.

Lemma BProv_Ax_s_betaShiftPrefixTermAt_succ_entry_of_extension :
  forall G oldCode oldStep currentCode newStep bound sourceOut
    extendedCode idx out,
  BProv Ax_s G
    (betaShiftPrefixTermAt
      oldCode oldStep currentCode newStep bound) ->
  BProv Ax_s G
    (betaCodeExtensionTermAt
      currentCode newStep bound sourceOut extendedCode) ->
  BProv Ax_s G
    (betaTermTermAt sourceOut oldCode oldStep (tSucc bound)) ->
  BProv Ax_s G (ltTermAt idx (tSucc bound)) ->
  BProv Ax_s G
    (betaTermTermAt out oldCode oldStep (tSucc idx)) ->
  BProv Ax_s G
    (betaTermTermAt out extendedCode newStep idx).
Proof.
  intros G oldCode oldStep currentCode newStep bound sourceOut
    extendedCode idx out hprefix hext hsource hltSucc hold.
  pose proof (BProv_Ax_s_ltTermAt_succ_right_cases
    G idx bound hltSucc) as hcases.
  assert (hltBranch : BProv Ax_s (ltTermAt idx bound :: G)
      (betaTermTermAt out extendedCode newStep idx)).
  {
    set (C := ltTermAt idx bound :: G).
    assert (hlt : BProv Ax_s C (ltTermAt idx bound)).
    { apply BProv_ass. unfold C. simpl. left. reflexivity. }
    pose proof (BProv_context_cons Ax_s G (ltTermAt idx bound) _
      hprefix) as hprefixC.
    pose proof (BProv_context_cons Ax_s G (ltTermAt idx bound) _
      hold) as holdC.
    pose proof
      (BProv_Ax_s_betaShiftPrefixTermAt_entry_of_ltTerm
        C oldCode oldStep currentCode newStep bound idx out
        hprefixC hlt holdC) as hcurrent.
    pose proof (BProv_context_cons Ax_s G (ltTermAt idx bound) _
      hext) as hextC.
    pose proof
      (BProv_Ax_s_betaPrefixAgreementTermAt_of_betaCodeExtensionTermAt
        C currentCode newStep bound sourceOut extendedCode hextC)
      as hagreement.
    exact (BProv_Ax_s_betaPrefixAgreementTermAt_entry_of_ltTerm
      C currentCode extendedCode newStep bound idx out
      hagreement hlt hcurrent).
  }
  assert (heqBranch : BProv Ax_s (pEq idx bound :: G)
      (betaTermTermAt out extendedCode newStep idx)).
  {
    set (C := pEq idx bound :: G).
    assert (heq : BProv Ax_s C (pEq idx bound)).
    { apply BProv_ass. unfold C. simpl. left. reflexivity. }
    pose proof (BProv_eq_congr_succ Ax_s C idx bound heq) as hsuccEq.
    pose proof (BProv_context_cons Ax_s G (pEq idx bound) _
      hold) as holdC.
    pose proof (BProv_Ax_s_betaTermTermAt_of_eq_index C
      out oldCode oldStep (tSucc idx) (tSucc bound)
      hsuccEq holdC) as holdAtBound.
    pose proof (BProv_context_cons Ax_s G (pEq idx bound) _
      hsource) as hsourceC.
    pose proof
      (BProv_Ax_s_eq_of_betaTermTermAt_betaTermTermAt_same_index
        C out sourceOut oldCode oldStep (tSucc bound)
        holdAtBound hsourceC) as houtEq.
    pose proof (BProv_context_cons Ax_s G (pEq idx bound) _
      hext) as hextC.
    pose proof
      (BProv_Ax_s_betaTermTermAt_of_betaCodeExtensionTermAt
        C currentCode newStep bound sourceOut extendedCode hextC)
      as htarget.
    exact (BProv_betaTermTermAt_congr Ax_s C
      sourceOut out extendedCode extendedCode newStep newStep bound idx
      houtEq (BProv_eqRefl Ax_s C extendedCode)
      (BProv_eqRefl Ax_s C newStep)
      (BProv_eqSym Ax_s C idx bound heq) htarget).
  }
  exact (BProv_orE Ax_s G
    (ltTermAt idx bound) (pEq idx bound)
    (betaTermTermAt out extendedCode newStep idx)
    hcases hltBranch heqBranch).
Qed.

Lemma BProv_Ax_s_betaShiftPrefixTermAt_succ_of_extension :
  forall G oldCode oldStep currentCode newStep bound sourceOut extendedCode,
  BProv Ax_s G
    (betaShiftPrefixTermAt
      oldCode oldStep currentCode newStep bound) ->
  BProv Ax_s G
    (betaCodeExtensionTermAt
      currentCode newStep bound sourceOut extendedCode) ->
  BProv Ax_s G
    (betaTermTermAt sourceOut oldCode oldStep (tSucc bound)) ->
  BProv Ax_s G
    (betaShiftPrefixTermAt
      oldCode oldStep extendedCode newStep (tSucc bound)).
Proof.
  intros G oldCode oldStep currentCode newStep bound sourceOut
    extendedCode hprefix hext hsource.
  set (outerAntecedent :=
    ltTermAt (tVar 0) (tSucc (Term.rename S bound))).
  set (oldEntry :=
    betaTermTermAt (tVar 0)
      (Term.rename (fun n => n + 2) oldCode)
      (Term.rename (fun n => n + 2) oldStep)
      (tSucc (tVar 1))).
  set (newEntry :=
    betaTermTermAt (tVar 0)
      (Term.rename (fun n => n + 2) extendedCode)
      (Term.rename (fun n => n + 2) newStep)
      (tVar 1)).
  set (innerBody := pImp oldEntry newEntry).
  set (outerBody := pImp outerAntecedent (pAll innerBody)).
  set (C := outerAntecedent :: map (rename S) G).
  set (D := oldEntry :: map (rename S) C).
  set (oldCode2 := Term.rename (fun n => n + 2) oldCode).
  set (oldStep2 := Term.rename (fun n => n + 2) oldStep).
  set (currentCode2 := Term.rename (fun n => n + 2) currentCode).
  set (newStep2 := Term.rename (fun n => n + 2) newStep).
  set (bound2 := Term.rename (fun n => n + 2) bound).
  set (sourceOut2 := Term.rename (fun n => n + 2) sourceOut).
  set (extendedCode2 := Term.rename (fun n => n + 2) extendedCode).
  assert (hold : BProv Ax_s D
      (betaTermTermAt (tVar 0) oldCode2 oldStep2 (tSucc (tVar 1)))).
  {
    apply BProv_ass.
    unfold D, oldEntry, oldCode2, oldStep2.
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
  pose proof (BProv_lift_two_contexts_of_sentences
    Ax_s sentence_ax_s G outerAntecedent oldEntry _ hprefix) as hprefixD0.
  rewrite rename_betaShiftPrefixTermAt in hprefixD0.
  rewrite rename_betaShiftPrefixTermAt in hprefixD0.
  repeat rewrite term_rename_succ_twice_add_two in hprefixD0.
  assert (hprefixD : BProv Ax_s D
      (betaShiftPrefixTermAt oldCode2 oldStep2
        currentCode2 newStep2 bound2)).
  { unfold D, C in hprefixD0. exact hprefixD0. }
  pose proof (BProv_lift_two_contexts_of_sentences
    Ax_s sentence_ax_s G outerAntecedent oldEntry _ hext) as hextD0.
  rewrite rename_betaCodeExtensionTermAt in hextD0.
  rewrite rename_betaCodeExtensionTermAt in hextD0.
  repeat rewrite term_rename_succ_twice_add_two in hextD0.
  assert (hextD : BProv Ax_s D
      (betaCodeExtensionTermAt currentCode2 newStep2 bound2
        sourceOut2 extendedCode2)).
  { unfold D, C in hextD0. exact hextD0. }
  pose proof (BProv_lift_two_contexts_of_sentences
    Ax_s sentence_ax_s G outerAntecedent oldEntry _ hsource) as hsourceD0.
  rewrite rename_betaTermTermAt in hsourceD0.
  rewrite rename_betaTermTermAt in hsourceD0.
  repeat rewrite term_rename_succ_twice_add_two in hsourceD0.
  assert (hsourceD : BProv Ax_s D
      (betaTermTermAt sourceOut2 oldCode2 oldStep2 (tSucc bound2))).
  { unfold D, C in hsourceD0. exact hsourceD0. }
  pose proof
    (BProv_Ax_s_betaShiftPrefixTermAt_succ_entry_of_extension
      D oldCode2 oldStep2 currentCode2 newStep2 bound2 sourceOut2
      extendedCode2 (tVar 1) (tVar 0)
      hprefixD hextD hsourceD hltSucc hold) as hnew.
  assert (hinnerImp : BProv Ax_s (map (rename S) C) innerBody).
  {
    unfold D in hnew.
    exact (BProv_impI Ax_s (map (rename S) C)
      oldEntry newEntry hnew).
  }
  assert (hinnerAll : BProv Ax_s C (pAll innerBody)).
  {
    exact (BProv_allI_of_sentences Ax_s C innerBody
      sentence_ax_s hinnerImp).
  }
  assert (houterImp : BProv Ax_s (map (rename S) G) outerBody).
  {
    unfold C in hinnerAll.
    exact (BProv_impI Ax_s (map (rename S) G)
      outerAntecedent (pAll innerBody) hinnerAll).
  }
  assert (hall : BProv Ax_s G (pAll outerBody)).
  {
    exact (BProv_allI_of_sentences Ax_s G outerBody
      sentence_ax_s houterImp).
  }
  unfold betaShiftPrefixTermAt, outerBody, outerAntecedent,
    innerBody, oldEntry, newEntry in *.
  exact hall.
Qed.

Lemma BProv_Ax_s_betaShiftPrefixTermAt_succ_entry_of_not_exists :
  forall G oldCode oldStep currentCode newStep bound idx out,
  BProv Ax_s G
    (betaShiftPrefixTermAt
      oldCode oldStep currentCode newStep bound) ->
  BProv Ax_s G
    (pImp
      (betaShiftSourceEntryExistsTermAt
        oldCode oldStep (tSucc bound))
      pBot) ->
  BProv Ax_s G (ltTermAt idx (tSucc bound)) ->
  BProv Ax_s G
    (betaTermTermAt out oldCode oldStep (tSucc idx)) ->
  BProv Ax_s G
    (betaTermTermAt out currentCode newStep idx).
Proof.
  intros G oldCode oldStep currentCode newStep bound idx out
    hprefix hnone hltSucc hold.
  pose proof (BProv_Ax_s_ltTermAt_succ_right_cases
    G idx bound hltSucc) as hcases.
  assert (hltBranch : BProv Ax_s (ltTermAt idx bound :: G)
      (betaTermTermAt out currentCode newStep idx)).
  {
    set (C := ltTermAt idx bound :: G).
    assert (hlt : BProv Ax_s C (ltTermAt idx bound)).
    { apply BProv_ass. unfold C. simpl. left. reflexivity. }
    exact (BProv_Ax_s_betaShiftPrefixTermAt_entry_of_ltTerm
      C oldCode oldStep currentCode newStep bound idx out
      (BProv_context_cons Ax_s G (ltTermAt idx bound) _ hprefix)
      hlt
      (BProv_context_cons Ax_s G (ltTermAt idx bound) _ hold)).
  }
  assert (heqBranch : BProv Ax_s (pEq idx bound :: G)
      (betaTermTermAt out currentCode newStep idx)).
  {
    set (C := pEq idx bound :: G).
    assert (heq : BProv Ax_s C (pEq idx bound)).
    { apply BProv_ass. unfold C. simpl. left. reflexivity. }
    pose proof (BProv_context_cons Ax_s G (pEq idx bound) _ hold)
      as holdC.
    pose proof (BProv_Ax_s_betaTermTermAt_of_eq_index C
      out oldCode oldStep (tSucc idx) (tSucc bound)
      (BProv_eq_congr_succ Ax_s C idx bound heq) holdC)
      as holdAtBound.
    pose proof
      (BProv_Ax_s_betaShiftSourceEntryExistsTermAt_of_term
        C oldCode oldStep (tSucc bound) out holdAtBound) as hex.
    pose proof (BProv_context_cons Ax_s G (pEq idx bound) _ hnone)
      as hnoneC.
    pose proof (BProv_mp Ax_s C
      (betaShiftSourceEntryExistsTermAt oldCode oldStep (tSucc bound))
      pBot hnoneC hex) as hbot.
    exact (BProv_botE Ax_s C
      (betaTermTermAt out currentCode newStep idx) hbot).
  }
  exact (BProv_orE Ax_s G
    (ltTermAt idx bound) (pEq idx bound)
    (betaTermTermAt out currentCode newStep idx)
    hcases hltBranch heqBranch).
Qed.

Lemma BProv_Ax_s_betaShiftPrefixTermAt_succ_of_not_exists :
  forall G oldCode oldStep currentCode newStep bound,
  BProv Ax_s G
    (betaShiftPrefixTermAt
      oldCode oldStep currentCode newStep bound) ->
  BProv Ax_s G
    (pImp
      (betaShiftSourceEntryExistsTermAt
        oldCode oldStep (tSucc bound))
      pBot) ->
  BProv Ax_s G
    (betaShiftPrefixTermAt
      oldCode oldStep currentCode newStep (tSucc bound)).
Proof.
  intros G oldCode oldStep currentCode newStep bound hprefix hnone.
  set (outerAntecedent :=
    ltTermAt (tVar 0) (tSucc (Term.rename S bound))).
  set (oldEntry :=
    betaTermTermAt (tVar 0)
      (Term.rename (fun n => n + 2) oldCode)
      (Term.rename (fun n => n + 2) oldStep)
      (tSucc (tVar 1))).
  set (newEntry :=
    betaTermTermAt (tVar 0)
      (Term.rename (fun n => n + 2) currentCode)
      (Term.rename (fun n => n + 2) newStep)
      (tVar 1)).
  set (innerBody := pImp oldEntry newEntry).
  set (outerBody := pImp outerAntecedent (pAll innerBody)).
  set (C := outerAntecedent :: map (rename S) G).
  set (D := oldEntry :: map (rename S) C).
  set (oldCode2 := Term.rename (fun n => n + 2) oldCode).
  set (oldStep2 := Term.rename (fun n => n + 2) oldStep).
  set (currentCode2 := Term.rename (fun n => n + 2) currentCode).
  set (newStep2 := Term.rename (fun n => n + 2) newStep).
  set (bound2 := Term.rename (fun n => n + 2) bound).
  assert (hold : BProv Ax_s D
      (betaTermTermAt (tVar 0) oldCode2 oldStep2 (tSucc (tVar 1)))).
  {
    apply BProv_ass.
    unfold D, oldEntry, oldCode2, oldStep2.
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
  pose proof (BProv_lift_two_contexts_of_sentences
    Ax_s sentence_ax_s G outerAntecedent oldEntry _ hprefix) as hprefixD0.
  rewrite rename_betaShiftPrefixTermAt in hprefixD0.
  rewrite rename_betaShiftPrefixTermAt in hprefixD0.
  repeat rewrite term_rename_succ_twice_add_two in hprefixD0.
  assert (hprefixD : BProv Ax_s D
      (betaShiftPrefixTermAt oldCode2 oldStep2
        currentCode2 newStep2 bound2)).
  { unfold D, C in hprefixD0. exact hprefixD0. }
  pose proof (BProv_lift_two_contexts_of_sentences
    Ax_s sentence_ax_s G outerAntecedent oldEntry _ hnone) as hnoneD0.
  change (BProv Ax_s D
    (pImp
      (rename S (rename S
        (betaShiftSourceEntryExistsTermAt
          oldCode oldStep (tSucc bound))))
      pBot)) in hnoneD0.
  rewrite rename_betaShiftSourceEntryExistsTermAt in hnoneD0.
  rewrite rename_betaShiftSourceEntryExistsTermAt in hnoneD0.
  repeat rewrite term_rename_succ_twice_add_two in hnoneD0.
  assert (hnoneD : BProv Ax_s D
      (pImp
        (betaShiftSourceEntryExistsTermAt
          oldCode2 oldStep2 (tSucc bound2))
        pBot)).
  { unfold D, C in hnoneD0. exact hnoneD0. }
  pose proof
    (BProv_Ax_s_betaShiftPrefixTermAt_succ_entry_of_not_exists
      D oldCode2 oldStep2 currentCode2 newStep2 bound2
      (tVar 1) (tVar 0) hprefixD hnoneD hltSucc hold) as hnew.
  assert (hinnerImp : BProv Ax_s (map (rename S) C) innerBody).
  {
    unfold D in hnew.
    exact (BProv_impI Ax_s (map (rename S) C)
      oldEntry newEntry hnew).
  }
  assert (hinnerAll : BProv Ax_s C (pAll innerBody)).
  {
    exact (BProv_allI_of_sentences Ax_s C innerBody
      sentence_ax_s hinnerImp).
  }
  assert (houterImp : BProv Ax_s (map (rename S) G) outerBody).
  {
    unfold C in hinnerAll.
    exact (BProv_impI Ax_s (map (rename S) G)
      outerAntecedent (pAll innerBody) hinnerAll).
  }
  assert (hall : BProv Ax_s G (pAll outerBody)).
  {
    exact (BProv_allI_of_sentences Ax_s G outerBody
      sentence_ax_s houterImp).
  }
  unfold betaShiftPrefixTermAt, outerBody, outerAntecedent,
    innerBody, oldEntry, newEntry in *.
  exact hall.
Qed.

Lemma BProv_Ax_s_betaShiftPrefixCodeExistsTermAt_succ_of_source :
  forall G oldCode oldStep currentCode newStep bound sourceOut,
  BProv Ax_s G
    (betaShiftPrefixTermAt
      oldCode oldStep currentCode newStep bound) ->
  BProv Ax_s G
    (betaTermTermAt sourceOut oldCode oldStep (tSucc bound)) ->
  BProv Ax_s G (commonMultipleThroughTermAt bound newStep) ->
  BProv Ax_s G (leTermAt (tSucc oldCode) newStep) ->
  BProv Ax_s G
    (betaShiftPrefixCodeExistsTermAt
      oldCode oldStep newStep (tSucc bound)).
Proof.
  intros G oldCode oldStep currentCode newStep bound sourceOut
    hprefix hsource hcommon hlarge.
  pose proof
    (BProv_Ax_s_ltTermAt_betaMod_of_betaTermTermAt_le_step_shift
      G sourceOut oldCode oldStep (tSucc bound) newStep bound
      hsource hlarge) as hbound.
  pose proof
    (BProv_Ax_s_betaCodeExtensionExistsTermAt_of_common
      G currentCode newStep bound sourceOut hcommon hbound) as hextEx.
  set (goal := betaShiftPrefixCodeExistsTermAt
    oldCode oldStep newStep (tSucc bound)).
  apply (BProv_Ax_s_betaCodeExtensionExistsTermAt_elim_opened
    G currentCode newStep bound sourceOut goal); [|exact hextEx].
  set (extBody := betaCodeExtensionExistsTermAtBody
    currentCode newStep bound sourceOut).
  set (D := extBody :: map (rename S) G).
  set (oldCode1 := Term.rename S oldCode).
  set (oldStep1 := Term.rename S oldStep).
  set (currentCode1 := Term.rename S currentCode).
  set (newStep1 := Term.rename S newStep).
  set (bound1 := Term.rename S bound).
  set (sourceOut1 := Term.rename S sourceOut).
  assert (hext : BProv Ax_s D
      (betaCodeExtensionTermAt currentCode1 newStep1 bound1
        sourceOut1 (tVar 0))).
  {
    apply BProv_ass.
    unfold D, extBody, betaCodeExtensionExistsTermAtBody,
      currentCode1, newStep1, bound1, sourceOut1.
    simpl. left. reflexivity.
  }
  pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
    hprefix S) as hprefixRen.
  rewrite rename_betaShiftPrefixTermAt in hprefixRen.
  assert (hprefixD : BProv Ax_s D
      (betaShiftPrefixTermAt oldCode1 oldStep1
        currentCode1 newStep1 bound1)).
  {
    exact (BProv_context_cons Ax_s (map (rename S) G)
      extBody _ hprefixRen).
  }
  pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
    hsource S) as hsourceRen.
  rewrite rename_betaTermTermAt in hsourceRen.
  assert (hsourceD : BProv Ax_s D
      (betaTermTermAt sourceOut1 oldCode1 oldStep1 (tSucc bound1))).
  {
    exact (BProv_context_cons Ax_s (map (rename S) G)
      extBody _ hsourceRen).
  }
  pose proof
    (BProv_Ax_s_betaShiftPrefixTermAt_succ_of_extension
      D oldCode1 oldStep1 currentCode1 newStep1 bound1
      sourceOut1 (tVar 0) hprefixD hext hsourceD) as hnext.
  pose proof
    (BProv_Ax_s_betaShiftPrefixCodeExistsTermAt_of_term
      D oldCode1 oldStep1 (tVar 0) newStep1 (tSucc bound1)
      hnext) as hex.
  unfold goal.
  rewrite rename_betaShiftPrefixCodeExistsTermAt.
  exact hex.
Qed.

Lemma BProv_Ax_s_betaShiftPrefixCodeExistsTermAt_succ_of_not_exists :
  forall G oldCode oldStep currentCode newStep bound,
  BProv Ax_s G
    (betaShiftPrefixTermAt
      oldCode oldStep currentCode newStep bound) ->
  BProv Ax_s G
    (pImp
      (betaShiftSourceEntryExistsTermAt
        oldCode oldStep (tSucc bound))
      pBot) ->
  BProv Ax_s G
    (betaShiftPrefixCodeExistsTermAt
      oldCode oldStep newStep (tSucc bound)).
Proof.
  intros G oldCode oldStep currentCode newStep bound hprefix hnone.
  apply (BProv_Ax_s_betaShiftPrefixCodeExistsTermAt_of_term
    G oldCode oldStep currentCode newStep (tSucc bound)).
  exact (BProv_Ax_s_betaShiftPrefixTermAt_succ_of_not_exists
    G oldCode oldStep currentCode newStep bound hprefix hnone).
Qed.

Lemma BProv_Ax_s_betaShiftPrefixCodeExistsTermAt_succ_of_entry_exists :
  forall G oldCode oldStep currentCode newStep bound,
  BProv Ax_s G
    (betaShiftPrefixTermAt
      oldCode oldStep currentCode newStep bound) ->
  BProv Ax_s G
    (betaShiftSourceEntryExistsTermAt
      oldCode oldStep (tSucc bound)) ->
  BProv Ax_s G (commonMultipleThroughTermAt bound newStep) ->
  BProv Ax_s G (leTermAt (tSucc oldCode) newStep) ->
  BProv Ax_s G
    (betaShiftPrefixCodeExistsTermAt
      oldCode oldStep newStep (tSucc bound)).
Proof.
  intros G oldCode oldStep currentCode newStep bound
    hprefix hentryEx hcommon hlarge.
  set (goal := betaShiftPrefixCodeExistsTermAt
    oldCode oldStep newStep (tSucc bound)).
  apply (BProv_Ax_s_betaShiftSourceEntryExistsTermAt_elim_opened
    G oldCode oldStep (tSucc bound) goal); [|exact hentryEx].
  set (entryBody := betaShiftSourceEntryExistsTermAtBody
    oldCode oldStep (tSucc bound)).
  set (D := entryBody :: map (rename S) G).
  set (oldCode1 := Term.rename S oldCode).
  set (oldStep1 := Term.rename S oldStep).
  set (currentCode1 := Term.rename S currentCode).
  set (newStep1 := Term.rename S newStep).
  set (bound1 := Term.rename S bound).
  assert (hsource : BProv Ax_s D
      (betaTermTermAt (tVar 0) oldCode1 oldStep1 (tSucc bound1))).
  {
    apply BProv_ass.
    unfold D, entryBody, betaShiftSourceEntryExistsTermAtBody,
      oldCode1, oldStep1, bound1.
    simpl. left. reflexivity.
  }
  pose proof (BProv_rename_succ_context_cons_of_sentences
    Ax_s sentence_ax_s G entryBody _ hprefix) as hprefixD.
  rewrite rename_betaShiftPrefixTermAt in hprefixD.
  pose proof (BProv_rename_succ_context_cons_of_sentences
    Ax_s sentence_ax_s G entryBody _ hcommon) as hcommonD.
  rewrite rename_commonMultipleThroughTermAt in hcommonD.
  pose proof (BProv_rename_succ_context_cons_of_sentences
    Ax_s sentence_ax_s G entryBody _ hlarge) as hlargeD.
  rewrite rename_leTermAt in hlargeD.
  pose proof
    (BProv_Ax_s_betaShiftPrefixCodeExistsTermAt_succ_of_source
      D oldCode1 oldStep1 currentCode1 newStep1 bound1 (tVar 0)
      hprefixD hsource hcommonD hlargeD) as hnext.
  unfold goal.
  rewrite rename_betaShiftPrefixCodeExistsTermAt.
  exact hnext.
Qed.

Lemma BProv_Ax_s_betaShiftPrefixCodeExistsTermAt_succ_of_current :
  forall G oldCode oldStep currentCode newStep bound,
  BProv Ax_s G
    (betaShiftPrefixTermAt
      oldCode oldStep currentCode newStep bound) ->
  BProv Ax_s G (commonMultipleThroughTermAt bound newStep) ->
  BProv Ax_s G (leTermAt (tSucc oldCode) newStep) ->
  BProv Ax_s G
    (betaShiftPrefixCodeExistsTermAt
      oldCode oldStep newStep (tSucc bound)).
Proof.
  intros G oldCode oldStep currentCode newStep bound
    hprefix hcommon hlarge.
  set (entryEx := betaShiftSourceEntryExistsTermAt
    oldCode oldStep (tSucc bound)).
  assert (hem : BProv Ax_s G
      (pOr entryEx (pImp entryEx pBot))).
  { apply BProv_of_Prov. apply P_lem. }
  assert (hentryBranch : BProv Ax_s (entryEx :: G)
      (betaShiftPrefixCodeExistsTermAt
        oldCode oldStep newStep (tSucc bound))).
  {
    apply (BProv_Ax_s_betaShiftPrefixCodeExistsTermAt_succ_of_entry_exists
      (entryEx :: G) oldCode oldStep currentCode newStep bound).
    - exact (BProv_context_cons Ax_s G entryEx _ hprefix).
    - apply BProv_ass_head.
    - exact (BProv_context_cons Ax_s G entryEx _ hcommon).
    - exact (BProv_context_cons Ax_s G entryEx _ hlarge).
  }
  assert (hnoneBranch : BProv Ax_s (pImp entryEx pBot :: G)
      (betaShiftPrefixCodeExistsTermAt
        oldCode oldStep newStep (tSucc bound))).
  {
    apply (BProv_Ax_s_betaShiftPrefixCodeExistsTermAt_succ_of_not_exists
      (pImp entryEx pBot :: G)
      oldCode oldStep currentCode newStep bound).
    - exact (BProv_context_cons Ax_s G (pImp entryEx pBot) _ hprefix).
    - apply BProv_ass_head.
  }
  exact (BProv_orE Ax_s G entryEx (pImp entryEx pBot)
    (betaShiftPrefixCodeExistsTermAt
      oldCode oldStep newStep (tSucc bound))
    hem hentryBranch hnoneBranch).
Qed.

Lemma BProv_Ax_s_betaShiftPrefixCodeExistsTermAt_succ :
  forall G oldCode oldStep newStep bound,
  BProv Ax_s G
    (betaShiftPrefixCodeExistsTermAt
      oldCode oldStep newStep bound) ->
  BProv Ax_s G (commonMultipleThroughTermAt bound newStep) ->
  BProv Ax_s G (leTermAt (tSucc oldCode) newStep) ->
  BProv Ax_s G
    (betaShiftPrefixCodeExistsTermAt
      oldCode oldStep newStep (tSucc bound)).
Proof.
  intros G oldCode oldStep newStep bound hex hcommon hlarge.
  set (goal := betaShiftPrefixCodeExistsTermAt
    oldCode oldStep newStep (tSucc bound)).
  apply (BProv_Ax_s_betaShiftPrefixCodeExistsTermAt_elim_opened
    G oldCode oldStep newStep bound goal); [|exact hex].
  set (prefixBody := betaShiftPrefixCodeExistsTermAtBody
    oldCode oldStep newStep bound).
  set (D := prefixBody :: map (rename S) G).
  set (oldCode1 := Term.rename S oldCode).
  set (oldStep1 := Term.rename S oldStep).
  set (newStep1 := Term.rename S newStep).
  set (bound1 := Term.rename S bound).
  assert (hprefix : BProv Ax_s D
      (betaShiftPrefixTermAt
        oldCode1 oldStep1 (tVar 0) newStep1 bound1)).
  {
    apply BProv_ass.
    unfold D, prefixBody, betaShiftPrefixCodeExistsTermAtBody,
      oldCode1, oldStep1, newStep1, bound1.
    simpl. left. reflexivity.
  }
  pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
    hcommon S) as hcommonRen.
  rewrite rename_commonMultipleThroughTermAt in hcommonRen.
  assert (hcommonD : BProv Ax_s D
      (commonMultipleThroughTermAt bound1 newStep1)).
  {
    exact (BProv_context_cons Ax_s (map (rename S) G)
      prefixBody _ hcommonRen).
  }
  pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
    hlarge S) as hlargeRen.
  rewrite rename_leTermAt in hlargeRen.
  assert (hlargeD : BProv Ax_s D
      (leTermAt (tSucc oldCode1) newStep1)).
  {
    exact (BProv_context_cons Ax_s (map (rename S) G)
      prefixBody _ hlargeRen).
  }
  pose proof
    (BProv_Ax_s_betaShiftPrefixCodeExistsTermAt_succ_of_current
      D oldCode1 oldStep1 (tVar 0) newStep1 bound1
      hprefix hcommonD hlargeD) as hnext.
  unfold goal.
  rewrite rename_betaShiftPrefixCodeExistsTermAt.
  exact hnext.
Qed.

Lemma BProv_Ax_s_all_betaShiftPrefixCodeExistsTermAt_of_codingStep :
  forall G oldCode oldStep newStep finalBound,
  BProv Ax_s G
    (betaCodingStepTermAt finalBound oldCode newStep) ->
  BProv Ax_s G
    (pAll (pImp
      (leTermAt (tVar 0) (Term.rename S finalBound))
      (betaShiftPrefixCodeExistsTermAt
        (Term.rename S oldCode)
        (Term.rename S oldStep)
        (Term.rename S newStep)
        (tVar 0)))).
Proof.
  intros G oldCode oldStep newStep finalBound hcoding.
  set (phi := pImp
    (leTermAt (tVar 0) (Term.rename S finalBound))
    (betaShiftPrefixCodeExistsTermAt
      (Term.rename S oldCode)
      (Term.rename S oldStep)
      (Term.rename S newStep)
      (tVar 0))).
  pose proof (BProv_Ax_s_betaShiftPrefixCodeExistsTermAt_zero
    G oldCode oldStep newStep) as hbase.
  assert (hzeroImp : BProv Ax_s G
      (pImp (leTermAt tZero finalBound)
        (betaShiftPrefixCodeExistsTermAt
          oldCode oldStep newStep tZero))).
  {
    apply (BProv_impI Ax_s G
      (leTermAt tZero finalBound)
      (betaShiftPrefixCodeExistsTermAt
        oldCode oldStep newStep tZero)).
    exact (BProv_context_cons Ax_s G
      (leTermAt tZero finalBound) _ hbase).
  }
  assert (hzero : BProv Ax_s G (subst substZero phi)).
  {
    unfold phi.
    cbn [subst].
    rewrite subst_leTermAt.
    rewrite subst_betaShiftPrefixCodeExistsTermAt.
    simpl.
    repeat rewrite term_substZero_rename_succ.
    exact hzeroImp.
  }
  pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
    hcoding S) as hcodingRen.
  rewrite rename_betaCodingStepTermAt in hcodingRen.
  set (C := phi :: map (rename S) G).
  assert (hsuccBody : BProv Ax_s C (subst substSuccVar phi)).
  {
    set (oldCode1 := Term.rename S oldCode).
    set (oldStep1 := Term.rename S oldStep).
    set (newStep1 := Term.rename S newStep).
    set (finalBound1 := Term.rename S finalBound).
    set (leSucc := leTermAt (tSucc (tVar 0)) finalBound1).
    set (prefixSucc := betaShiftPrefixCodeExistsTermAt
      oldCode1 oldStep1 newStep1 (tSucc (tVar 0))).
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
          (betaShiftPrefixCodeExistsTermAt
            oldCode1 oldStep1 newStep1 (tVar 0)))).
    {
      unfold phi, oldCode1, oldStep1, newStep1, finalBound1 in hihRaw.
      exact hihRaw.
    }
    pose proof (BProv_mp Ax_s D
      (leTermAt (tVar 0) finalBound1)
      (betaShiftPrefixCodeExistsTermAt
        oldCode1 oldStep1 newStep1 (tVar 0))
      hih hlePred) as hex.
    assert (hcodingC : BProv Ax_s C
        (betaCodingStepTermAt finalBound1 oldCode1 newStep1)).
    {
      exact (BProv_context_cons Ax_s (map (rename S) G)
        phi _ hcodingRen).
    }
    assert (hcodingD : BProv Ax_s D
        (betaCodingStepTermAt finalBound1 oldCode1 newStep1)).
    { exact (BProv_context_cons Ax_s C leSucc _ hcodingC). }
    assert (hcommonFinal : BProv Ax_s D
        (commonMultipleThroughTermAt finalBound1 newStep1)).
    {
      unfold betaCodingStepTermAt in hcodingD.
      exact (BProv_andE1 Ax_s D _ _ hcodingD).
    }
    assert (hlarge : BProv Ax_s D
        (leTermAt (tSucc oldCode1) newStep1)).
    {
      unfold betaCodingStepTermAt in hcodingD.
      exact (BProv_andE2 Ax_s D _ _ hcodingD).
    }
    pose proof (BProv_Ax_s_commonMultipleThroughTermAt_of_le
      D (tVar 0) finalBound1 newStep1 hcommonFinal hlePred)
      as hcommon.
    pose proof
      (BProv_Ax_s_betaShiftPrefixCodeExistsTermAt_succ
        D oldCode1 oldStep1 newStep1 (tVar 0)
        hex hcommon hlarge) as hnext.
    assert (himp : BProv Ax_s C (pImp leSucc prefixSucc)).
    {
      unfold D in hnext.
      exact (BProv_impI Ax_s C leSucc prefixSucc hnext).
    }
    unfold phi.
    cbn [subst].
    rewrite subst_leTermAt.
    rewrite subst_betaShiftPrefixCodeExistsTermAt.
    simpl.
    repeat rewrite term_substSuccVar_rename_succ.
    unfold leSucc, prefixSucc, oldCode1, oldStep1,
      newStep1, finalBound1 in himp.
    exact himp.
  }
  assert (hsuccImp : BProv Ax_s (map (rename S) G)
      (pImp phi (subst substSuccVar phi))).
  {
    unfold C in hsuccBody.
    exact (BProv_impI Ax_s (map (rename S) G)
      phi (subst substSuccVar phi) hsuccBody).
  }
  pose proof (BProv_allI_of_sentences Ax_s G
    (pImp phi (subst substSuccVar phi)) sentence_ax_s hsuccImp)
    as hsuccAll.
  pose proof (BProv_Ax_s_induction_rule G phi hzero hsuccAll) as hall.
  unfold phi in hall.
  exact hall.
Qed.

Lemma BProv_Ax_s_betaShiftPrefixCodeExistsTermAt_of_codingStep :
  forall G oldCode oldStep newStep finalBound,
  BProv Ax_s G
    (betaCodingStepTermAt finalBound oldCode newStep) ->
  BProv Ax_s G
    (betaShiftPrefixCodeExistsTermAt
      oldCode oldStep newStep finalBound).
Proof.
  intros G oldCode oldStep newStep finalBound hcoding.
  pose proof
    (BProv_Ax_s_all_betaShiftPrefixCodeExistsTermAt_of_codingStep
      G oldCode oldStep newStep finalBound hcoding) as hall.
  pose proof (BProv_allE Ax_s G _ finalBound hall) as himp.
  cbn [subst] in himp.
  rewrite subst_leTermAt in himp.
  rewrite subst_betaShiftPrefixCodeExistsTermAt in himp.
  simpl in himp.
  repeat rewrite term_subst_instTerm_rename_succ in himp.
  exact (BProv_mp Ax_s G
    (leTermAt finalBound finalBound)
    (betaShiftPrefixCodeExistsTermAt
      oldCode oldStep newStep finalBound)
    himp (BProv_Ax_s_leTermAt_refl G finalBound)).
Qed.

Lemma BProv_Ax_s_betaShiftTailThroughTermAt_of_shiftPrefix_succ :
  forall G oldCode oldStep newCode newStep last,
  BProv Ax_s G
    (betaShiftPrefixTermAt
      (tVar oldCode) (tVar oldStep)
      newCode newStep (tSucc last)) ->
  BProv Ax_s G
    (betaShiftTailThroughTermAt
      oldCode oldStep newCode newStep last).
Proof.
  intros G oldCode oldStep newCode newStep last hprefix.
  set (leHyp :=
    leTermAt (tVar 0) (Term.rename S last)).
  set (oldEntry :=
    betaTermTermAt (tVar 0)
      (tVar (oldCode + 2)) (tVar (oldStep + 2))
      (tSucc (tVar 1))).
  set (newEntry :=
    betaTermTermAt (tVar 0)
      (Term.rename (fun n => n + 2) newCode)
      (Term.rename (fun n => n + 2) newStep)
      (tVar 1)).
  set (witness := pAll (pImp oldEntry newEntry)).
  set (outerBody := pImp leHyp witness).
  set (C := leHyp :: map (rename S) G).
  assert (hle : BProv Ax_s C
      (leTermAt (tVar 0) (Term.rename S last))).
  {
    apply BProv_ass.
    unfold C, leHyp. simpl. left. reflexivity.
  }
  pose proof (BProv_Ax_s_ltTermAt_succ_right_of_leTermAt
    C (tVar 0) (Term.rename S last) hle) as hlt.
  pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
    hprefix S) as hprefixRen.
  rewrite rename_betaShiftPrefixTermAt in hprefixRen.
  assert (hprefixC : BProv Ax_s C
      (betaShiftPrefixTermAt
        (tVar (oldCode + 1)) (tVar (oldStep + 1))
        (Term.rename S newCode) (Term.rename S newStep)
        (tSucc (Term.rename S last)))).
  {
    pose proof (BProv_context_cons Ax_s (map (rename S) G)
      leHyp _ hprefixRen) as hctx.
    change (BProv Ax_s C
      (betaShiftPrefixTermAt
        (tVar (S oldCode)) (tVar (S oldStep))
        (Term.rename S newCode) (Term.rename S newStep)
        (tSucc (Term.rename S last)))) in hctx.
    replace (S oldCode) with (oldCode + 1) in hctx by lia.
    replace (S oldStep) with (oldStep + 1) in hctx by lia.
    exact hctx.
  }
  pose proof (BProv_allE Ax_s C _ (tVar 0) hprefixC) as himp.
  cbn [subst] in himp.
  rewrite subst_ltTermAt in himp.
  rewrite !subst_betaTermTermAt in himp.
  simpl in himp.
  repeat rewrite term_subst_upSubst_instTerm_rename_add_two in himp.
  repeat rewrite term_subst_instTerm_rename_succ in himp.
  assert (hupVar : forall n,
      Term.upSubst (instTerm (tVar 0)) (n + 1 + 2) =
      tVar (n + 2)).
  {
    intro n.
    replace (n + 1 + 2) with (S (S (S n))) by lia.
    replace (n + 2) with (S (S n)) by lia.
    simpl. reflexivity.
  }
  rewrite (hupVar oldCode), (hupVar oldStep) in himp.
  repeat rewrite term_rename_succ_twice_add_two in himp.
  assert (hwitness : BProv Ax_s C witness).
  {
    unfold witness, oldEntry, newEntry.
    exact (BProv_mp Ax_s C
      (ltTermAt (tVar 0) (tSucc (Term.rename S last)))
      (pAll (pImp
        (betaTermTermAt (tVar 0)
          (tVar (oldCode + 2)) (tVar (oldStep + 2))
          (tSucc (tVar 1)))
        (betaTermTermAt (tVar 0)
          (Term.rename (fun n => n + 2) newCode)
          (Term.rename (fun n => n + 2) newStep)
          (tVar 1))))
      himp hlt).
  }
  assert (houterImp : BProv Ax_s (map (rename S) G) outerBody).
  {
    unfold C in hwitness.
    exact (BProv_impI Ax_s (map (rename S) G)
      leHyp witness hwitness).
  }
  assert (hall : BProv Ax_s G (pAll outerBody)).
  {
    exact (BProv_allI_of_sentences Ax_s G outerBody
      sentence_ax_s houterImp).
  }
  unfold betaShiftTailThroughTermAt, outerBody, leHyp,
    witness, oldEntry, newEntry in *.
  exact hall.
Qed.

Lemma rename_S_betaShiftTailExistsTermAt_prefix :
  forall oldCode oldStep last,
  rename S (betaShiftTailExistsTermAt oldCode oldStep last) =
  betaShiftTailExistsTermAt
    (S oldCode) (S oldStep) (Term.rename S last).
Proof.
  intros oldCode oldStep last.
  exact (PA.Formula.rename_betaShiftTailExistsTermAt
    S oldCode oldStep last).
Qed.

Theorem BProv_Ax_s_betaShiftTailExistsTermAt :
  forall G oldCode oldStep last,
  BProv Ax_s G
    (betaShiftTailExistsTermAt oldCode oldStep last).
Proof.
  intros G oldCode oldStep last.
  set (goal := betaShiftTailExistsTermAt oldCode oldStep last).
  pose proof (BProv_Ax_s_betaCodingStepExistsTermAt
    G (tSucc last) (tVar oldCode)) as hstepEx.
  apply (BProv_Ax_s_betaCodingStepExistsTermAt_elim_opened
    G (tSucc last) (tVar oldCode) goal); [|exact hstepEx].
  set (stepBody := betaCodingStepExistsTermAtBody
    (tSucc last) (tVar oldCode)).
  set (D := stepBody :: map (rename S) G).
  set (last1 := Term.rename S last).
  set (oldCode1 := tVar (S oldCode)).
  set (oldStep1 := tVar (S oldStep)).
  assert (hcoding : BProv Ax_s D
      (betaCodingStepTermAt
        (tSucc last1) oldCode1 (tVar 0))).
  {
    apply BProv_ass.
    unfold D, stepBody, betaCodingStepExistsTermAtBody,
      last1, oldCode1.
    simpl. left. reflexivity.
  }
  pose proof
    (BProv_Ax_s_betaShiftPrefixCodeExistsTermAt_of_codingStep
      D oldCode1 oldStep1 (tVar 0) (tSucc last1) hcoding)
    as hprefixEx.
  set (prefixBody := betaShiftPrefixCodeExistsTermAtBody
    oldCode1 oldStep1 (tVar 0) (tSucc last1)).
  apply (BProv_Ax_s_betaShiftPrefixCodeExistsTermAt_elim_opened
    D oldCode1 oldStep1 (tVar 0) (tSucc last1)
    (rename S goal)); [|exact hprefixEx].
  set (E := prefixBody :: map (rename S) D).
  set (last2 := Term.rename (fun n => n + 2) last).
  assert (hprefix : BProv Ax_s E
      (betaShiftPrefixTermAt
        (tVar (oldCode + 2)) (tVar (oldStep + 2))
        (tVar 0) (tVar 1) (tSucc last2))).
  {
    apply BProv_ass.
    unfold E, prefixBody, betaShiftPrefixCodeExistsTermAtBody,
      PA.Formula.betaShiftPrefixCodeExistsTermAtBody,
      oldCode1, oldStep1, last1, last2.
    simpl.
    repeat rewrite term_rename_succ_twice_add_two.
    replace (S (S oldCode)) with (oldCode + 2) by lia.
    replace (S (S oldStep)) with (oldStep + 2) by lia.
    left. reflexivity.
  }
  pose proof
    (BProv_Ax_s_betaShiftTailThroughTermAt_of_shiftPrefix_succ
      E (oldCode + 2) (oldStep + 2)
      (tVar 0) (tVar 1) last2 hprefix) as hthrough.
  pose proof (BProv_Ax_s_betaShiftTailExistsTermAt_of_through
    E (oldCode + 2) (oldStep + 2)
    (tVar 0) (tVar 1) last2 hthrough) as htailEx.
  unfold goal.
  rewrite rename_S_betaShiftTailExistsTermAt_prefix.
  rewrite rename_S_betaShiftTailExistsTermAt_prefix.
  replace (S (S oldCode)) with (oldCode + 2) by lia.
  replace (S (S oldStep)) with (oldStep + 2) by lia.
  replace (Term.rename S (Term.rename S last)) with last2.
  2:{ unfold last2. symmetry. apply term_rename_succ_twice_add_two. }
  exact htailEx.
Qed.

Theorem BProv_Ax_s_all_betaShiftTailExistsTermAt :
  forall G oldCode oldStep,
  BProv Ax_s G
    (pAll (betaShiftTailExistsTermAt
      (S oldCode) (S oldStep) (tVar 0))).
Proof.
  intros G oldCode oldStep.
  pose proof (BProv_Ax_s_betaShiftTailExistsTermAt
    (map (rename S) G) (S oldCode) (S oldStep) (tVar 0))
    as hbody.
  exact (BProv_allI_of_sentences Ax_s G
    (betaShiftTailExistsTermAt
      (S oldCode) (S oldStep) (tVar 0))
    sentence_ax_s hbody).
Qed.
