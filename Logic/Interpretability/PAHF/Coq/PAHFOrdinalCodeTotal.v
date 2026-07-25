(* ===================================================================== *)
(*  PAHFOrdinalCodeTotal.v                                                *)
(*                                                                       *)
(*  Internal PA totality of the Ackermann finite-ordinal code graph.      *)
(*  This layer starts with the reusable trace body and its explicit zero   *)
(*  witness; the capacity induction below extends that witness uniformly.  *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF PAHFProofCalculus PAHFOrdinalCode.

Import ListNotations.
Import PA PA.Term PA.Formula.

(* The recurrence is vacuous at raw input zero. *)
Lemma BProv_Ax_s_ordinalCodeStepsTermAt_zero :
  forall G sequenceCode sequenceStep,
  BProv Ax_s G
    (ordinalCodeStepsTermAt sequenceCode sequenceStep tZero).
Proof.
  intros G sequenceCode sequenceStep.
  set (antecedent := ltTermAt (tVar 0) tZero).
  set (consequent := ordinalCodeStepWitnessTermAt
    (Term.rename S sequenceCode) (Term.rename S sequenceStep) (tVar 0)).
  set (C := antecedent :: map (rename S) G).
  assert (hlt : BProv Ax_s C antecedent).
  { apply BProv_ass. unfold C. simpl. left. reflexivity. }
  assert (hle : BProv Ax_s C (leTermAt tZero (tVar 0))).
  { apply BProv_Ax_s_leTermAt_zero_left. }
  assert (hbot : BProv Ax_s C pBot).
  {
    unfold antecedent in hlt.
    exact (BProv_Ax_s_ltTermAt_leTermAt_bot C (tVar 0) tZero hlt hle).
  }
  assert (hconsequent : BProv Ax_s C consequent).
  { exact (BProv_botE Ax_s C consequent hbot). }
  assert (himp : BProv Ax_s (map (rename S) G)
    (pImp antecedent consequent)).
  {
    unfold C in hconsequent.
    exact (BProv_impI Ax_s (map (rename S) G)
      antecedent consequent hconsequent).
  }
  assert (hall : BProv Ax_s G (pAll (pImp antecedent consequent))).
  {
    exact (BProv_allI_of_sentences Ax_s G
      (pImp antecedent consequent) sentence_ax_s himp).
  }
  unfold ordinalCodeStepsTermAt.
  change (BProv Ax_s G (pAll (pImp antecedent consequent))).
  exact hall.
Qed.

(* Binder-free body packaged by [ordinalCodeGraphTermAt]. *)
Definition ordinalCodeGraphBodyTermAt
    (sequenceCode sequenceStep raw coded : term) : formula :=
  pAnd
    (betaTermTermAt tZero sequenceCode sequenceStep tZero)
    (pAnd
      (betaTermTermAt coded sequenceCode sequenceStep raw)
      (ordinalCodeStepsTermAt sequenceCode sequenceStep raw)).

Lemma subst_ordinalCodeGraphBodyTermAt :
  forall sigma sequenceCode sequenceStep raw coded,
  subst sigma
      (ordinalCodeGraphBodyTermAt sequenceCode sequenceStep raw coded) =
    ordinalCodeGraphBodyTermAt
      (Term.subst sigma sequenceCode)
      (Term.subst sigma sequenceStep)
      (Term.subst sigma raw)
      (Term.subst sigma coded).
Proof.
  intros sigma sequenceCode sequenceStep raw coded.
  unfold ordinalCodeGraphBodyTermAt.
  cbn [subst].
  rewrite !subst_betaTermTermAt.
  rewrite subst_ordinalCodeStepsTermAt.
  reflexivity.
Qed.

Lemma rename_ordinalCodeGraphBodyTermAt :
  forall r sequenceCode sequenceStep raw coded,
  rename r
      (ordinalCodeGraphBodyTermAt sequenceCode sequenceStep raw coded) =
    ordinalCodeGraphBodyTermAt
      (Term.rename r sequenceCode)
      (Term.rename r sequenceStep)
      (Term.rename r raw)
      (Term.rename r coded).
Proof.
  intros r sequenceCode sequenceStep raw coded.
  rename_from_subst subst_ordinalCodeGraphBodyTermAt.
Qed.

Lemma subst_instTerm_ordinalCodeGraphBody_inner :
  forall sequenceCode sequenceStep raw coded,
  subst (instTerm sequenceStep)
      (ordinalCodeGraphBodyTermAt
        (Term.rename S sequenceCode) (tVar 0)
        (Term.rename S raw) (Term.rename S coded)) =
    ordinalCodeGraphBodyTermAt
      sequenceCode sequenceStep raw coded.
Proof.
  intros sequenceCode sequenceStep raw coded.
  rewrite subst_ordinalCodeGraphBodyTermAt.
  simpl.
  repeat rewrite term_subst_instTerm_rename_succ.
  reflexivity.
Qed.

Lemma subst_instTerm_ordinalCodeGraphBody_outer :
  forall sequenceCode raw coded,
  subst (instTerm sequenceCode)
      (pEx (ordinalCodeGraphBodyTermAt
        (tVar 1) (tVar 0)
        (Term.rename (fun n => n + 2) raw)
        (Term.rename (fun n => n + 2) coded))) =
    pEx (ordinalCodeGraphBodyTermAt
      (Term.rename S sequenceCode) (tVar 0)
      (Term.rename S raw) (Term.rename S coded)).
Proof.
  intros sequenceCode raw coded.
  cbn [subst].
  rewrite subst_ordinalCodeGraphBodyTermAt.
  simpl.
  repeat rewrite term_subst_upSubst_instTerm_rename_add_two.
  reflexivity.
Qed.

Lemma BProv_ordinalCodeGraphTermAt_of_body :
  forall B G sequenceCode sequenceStep raw coded,
  BProv B G
    (ordinalCodeGraphBodyTermAt sequenceCode sequenceStep raw coded) ->
  BProv B G (ordinalCodeGraphTermAt raw coded).
Proof.
  intros B G sequenceCode sequenceStep raw coded hbody.
  assert (hinnerInst : BProv B G
    (subst (instTerm sequenceStep)
      (ordinalCodeGraphBodyTermAt
        (Term.rename S sequenceCode) (tVar 0)
        (Term.rename S raw) (Term.rename S coded)))).
  {
    rewrite subst_instTerm_ordinalCodeGraphBody_inner.
    exact hbody.
  }
  assert (hinner : BProv B G
    (pEx (ordinalCodeGraphBodyTermAt
      (Term.rename S sequenceCode) (tVar 0)
      (Term.rename S raw) (Term.rename S coded)))).
  {
    exact (BProv_exI B G _ sequenceStep hinnerInst).
  }
  assert (houterInst : BProv B G
    (subst (instTerm sequenceCode)
      (pEx (ordinalCodeGraphBodyTermAt
        (tVar 1) (tVar 0)
        (Term.rename (fun n => n + 2) raw)
        (Term.rename (fun n => n + 2) coded))))).
  {
    rewrite subst_instTerm_ordinalCodeGraphBody_outer.
    exact hinner.
  }
  assert (hgraph : BProv B G
    (pEx (pEx (ordinalCodeGraphBodyTermAt
      (tVar 1) (tVar 0)
      (Term.rename (fun n => n + 2) raw)
      (Term.rename (fun n => n + 2) coded))))).
  {
    exact (BProv_exI B G _ sequenceCode houterInst).
  }
  unfold ordinalCodeGraphTermAt, ordinalCodeGraphBodyTermAt in *.
  exact hgraph.
Qed.

(** Eliminate the graph's two sequence witnesses while retaining its
    binder-free body as a local assumption.  Keeping this rule next to the
    introduction rule above gives later graph arguments a common interface
    and hides the repeated de Bruijn context calculation. *)
Lemma BProv_ordinalCodeGraphTermAt_elim_opened : forall
  (B : formula -> Prop) (hB : Sentences B) G raw coded target,
  BProv B G (ordinalCodeGraphTermAt raw coded) ->
  let body := ordinalCodeGraphBodyTermAt
    (tVar 1) (tVar 0)
    (Term.rename (fun n => n + 2) raw)
    (Term.rename (fun n => n + 2) coded) in
  let inner := pEx body in
  BProv B (body :: map (rename S) (inner :: map (rename S) G))
    (rename S (rename S target)) ->
  BProv B G target.
Proof.
  intros B hB G raw coded target hgraph.
  cbn.
  set (body := ordinalCodeGraphBodyTermAt
    (tVar 1) (tVar 0)
    (Term.rename (fun n => n + 2) raw)
    (Term.rename (fun n => n + 2) coded)).
  intro hopened.
  apply (BProv_two_exE_of_sentences B hB G body target).
  - unfold ordinalCodeGraphTermAt, body, ordinalCodeGraphBodyTermAt in *.
    exact hgraph.
  - exact hopened.
Qed.

(* Explicit graph witness for zero. *)
Lemma BProv_Ax_s_ordinalCodeGraphTermAt_zero : forall G,
  BProv Ax_s G (ordinalCodeGraphTermAt tZero tZero).
Proof.
  intro G.
  assert (hrefl : BProv Ax_s G (pEq tZero tZero)).
  { apply BProv_eqRefl. }
  assert (hentry : BProv Ax_s G
    (betaTermTermAt tZero tZero tZero tZero)).
  {
    exact (BProv_Ax_s_betaTermTermAt_zero_of_eq_step_zero
      G tZero tZero tZero hrefl).
  }
  assert (hsteps : BProv Ax_s G
    (ordinalCodeStepsTermAt tZero tZero tZero)).
  { apply BProv_Ax_s_ordinalCodeStepsTermAt_zero. }
  apply (BProv_ordinalCodeGraphTermAt_of_body
    Ax_s G tZero tZero tZero tZero).
  unfold ordinalCodeGraphBodyTermAt.
  exact (BProv_andI Ax_s G _ _ hentry
    (BProv_andI Ax_s G _ _ hentry hsteps)).
Qed.

Lemma BProv_Ax_s_ordinalCodeGraphTermAt_zero_exists : forall G,
  BProv Ax_s G
    (pEx (ordinalCodeGraphTermAt (Term.rename S tZero) (tVar 0))).
Proof.
  intro G.
  apply (BProv_exI Ax_s G
    (ordinalCodeGraphTermAt (Term.rename S tZero) (tVar 0)) tZero).
  rewrite subst_ordinalCodeGraphTermAt.
  simpl.
  apply BProv_Ax_s_ordinalCodeGraphTermAt_zero.
Qed.

(* Package explicit adjacent beta entries and their Ackermann edge. *)
Lemma BProv_Ax_s_ordinalCodeStepWitnessTermAt_of_components :
  forall G sequenceCode sequenceStep index current next,
  BProv Ax_s G
    (betaTermTermAt current sequenceCode sequenceStep index) ->
  BProv Ax_s G
    (betaTermTermAt next sequenceCode sequenceStep (tSucc index)) ->
  BProv Ax_s G (hfAdjoinGraphTermAt next current current) ->
  BProv Ax_s G
    (ordinalCodeStepWitnessTermAt sequenceCode sequenceStep index).
Proof.
  intros G sequenceCode sequenceStep index current next
    hcurrent hnext hadjoin.
  set (components := pAnd
    (betaTermTermAt current sequenceCode sequenceStep index)
    (pAnd
      (betaTermTermAt next sequenceCode sequenceStep (tSucc index))
      (hfAdjoinGraphTermAt next current current))).
  assert (hcomponents : BProv Ax_s G components).
  {
    unfold components.
    exact (BProv_andI Ax_s G _ _ hcurrent
      (BProv_andI Ax_s G _ _ hnext hadjoin)).
  }
  apply (BProv_exI Ax_s G _ current).
  apply (BProv_exI Ax_s G _ next).
  cbn [subst].
  rewrite !subst_betaTermTermAt.
  rewrite !subst_hfAdjoinGraphTermAt.
  simpl.
  normalize_subst_rename.
  unfold components in hcomponents.
  exact hcomponents.
Qed.

Lemma BProv_Ax_s_ordinalCodeStepsTermAt_step_of_ltTerm :
  forall G sequenceCode sequenceStep raw index,
  BProv Ax_s G
    (ordinalCodeStepsTermAt sequenceCode sequenceStep raw) ->
  BProv Ax_s G (ltTermAt index raw) ->
  BProv Ax_s G
    (ordinalCodeStepWitnessTermAt sequenceCode sequenceStep index).
Proof.
  intros G sequenceCode sequenceStep raw index hsteps hlt.
  pose proof (BProv_allE Ax_s G _ index hsteps) as himp.
  cbn [subst] in himp.
  rewrite subst_ltTermAt in himp.
  rewrite subst_ordinalCodeStepWitnessTermAt in himp.
  simpl in himp.
  repeat rewrite term_subst_instTerm_rename_succ in himp.
  exact (BProv_mp Ax_s G (ltTermAt index raw)
    (ordinalCodeStepWitnessTermAt sequenceCode sequenceStep index)
    himp hlt).
Qed.

(* Extensional agreement of two beta codes below a term-valued bound. *)
Definition betaPrefixAgreementTermAt
    (oldCode newCode step bound : term) : formula :=
  pAll
    (pImp
      (ltTermAt (tVar 0) (Term.rename S bound))
      (pAll
        (pImp
          (betaTermTermAt (tVar 0)
            (Term.rename (fun n => n + 2) oldCode)
            (Term.rename (fun n => n + 2) step)
            (tVar 1))
          (betaTermTermAt (tVar 0)
            (Term.rename (fun n => n + 2) newCode)
            (Term.rename (fun n => n + 2) step)
            (tVar 1))))).

Definition betaCodeExtensionTermAt
    (oldCode step target newOut newCode : term) : formula :=
  pAnd
    (betaPrefixAgreementTermAt oldCode newCode step target)
    (betaTermTermAt newOut newCode step target).

Definition betaCodeExtensionExistsTermAt
    (oldCode step target newOut : term) : formula :=
  pEx
    (betaCodeExtensionTermAt
      (Term.rename S oldCode)
      (Term.rename S step)
      (Term.rename S target)
      (Term.rename S newOut)
      (tVar 0)).

Lemma subst_betaPrefixAgreementTermAt :
  forall sigma oldCode newCode step bound,
  subst sigma
      (betaPrefixAgreementTermAt oldCode newCode step bound) =
    betaPrefixAgreementTermAt
      (Term.subst sigma oldCode)
      (Term.subst sigma newCode)
      (Term.subst sigma step)
      (Term.subst sigma bound).
Proof.
  intros sigma oldCode newCode step bound.
  unfold betaPrefixAgreementTermAt.
  cbn [subst].
  rewrite subst_ltTermAt.
  rewrite !subst_betaTermTermAt.
  repeat rewrite Term.subst_rename_succ_up.
  rewrite !term_subst_up_up_rename_add_two.
  reflexivity.
Qed.

Lemma rename_betaPrefixAgreementTermAt :
  forall r oldCode newCode step bound,
  rename r
      (betaPrefixAgreementTermAt oldCode newCode step bound) =
    betaPrefixAgreementTermAt
      (Term.rename r oldCode)
      (Term.rename r newCode)
      (Term.rename r step)
      (Term.rename r bound).
Proof.
  intros r oldCode newCode step bound.
  rename_from_subst subst_betaPrefixAgreementTermAt.
Qed.

Lemma subst_betaCodeExtensionTermAt :
  forall sigma oldCode step target newOut newCode,
  subst sigma
      (betaCodeExtensionTermAt oldCode step target newOut newCode) =
    betaCodeExtensionTermAt
      (Term.subst sigma oldCode)
      (Term.subst sigma step)
      (Term.subst sigma target)
      (Term.subst sigma newOut)
      (Term.subst sigma newCode).
Proof.
  intros sigma oldCode step target newOut newCode.
  unfold betaCodeExtensionTermAt.
  cbn [subst].
  rewrite subst_betaPrefixAgreementTermAt.
  rewrite subst_betaTermTermAt.
  reflexivity.
Qed.

Lemma rename_betaCodeExtensionTermAt :
  forall r oldCode step target newOut newCode,
  rename r
      (betaCodeExtensionTermAt oldCode step target newOut newCode) =
    betaCodeExtensionTermAt
      (Term.rename r oldCode)
      (Term.rename r step)
      (Term.rename r target)
      (Term.rename r newOut)
      (Term.rename r newCode).
Proof.
  intros r oldCode step target newOut newCode.
  rename_from_subst subst_betaCodeExtensionTermAt.
Qed.

Lemma BProv_Ax_s_betaTermTermAt_of_betaCodeExtensionTermAt :
  forall G oldCode step target newOut newCode,
  BProv Ax_s G
    (betaCodeExtensionTermAt oldCode step target newOut newCode) ->
  BProv Ax_s G
    (betaTermTermAt newOut newCode step target).
Proof.
  intros G oldCode step target newOut newCode hext.
  unfold betaCodeExtensionTermAt in hext.
  exact (BProv_andE2 Ax_s G _ _ hext).
Qed.

Lemma BProv_Ax_s_betaPrefixAgreementTermAt_of_betaCodeExtensionTermAt :
  forall G oldCode step target newOut newCode,
  BProv Ax_s G
    (betaCodeExtensionTermAt oldCode step target newOut newCode) ->
  BProv Ax_s G
    (betaPrefixAgreementTermAt oldCode newCode step target).
Proof.
  intros G oldCode step target newOut newCode hext.
  unfold betaCodeExtensionTermAt in hext.
  exact (BProv_andE1 Ax_s G _ _ hext).
Qed.

Lemma BProv_Ax_s_betaPrefixAgreementTermAt_entry_of_ltTerm :
  forall G oldCode newCode step bound index out,
  BProv Ax_s G
    (betaPrefixAgreementTermAt oldCode newCode step bound) ->
  BProv Ax_s G (ltTermAt index bound) ->
  BProv Ax_s G
    (betaTermTermAt out oldCode step index) ->
  BProv Ax_s G
    (betaTermTermAt out newCode step index).
Proof.
  intros G oldCode newCode step bound index out
    hagreement hlt hold.
  pose proof (BProv_allE Ax_s G _ index hagreement) as hidx.
  cbn [subst] in hidx.
  rewrite subst_ltTermAt in hidx.
  rewrite !subst_betaTermTermAt in hidx.
  simpl in hidx.
  repeat rewrite term_subst_upSubst_instTerm_rename_add_two in hidx.
  repeat rewrite term_subst_instTerm_rename_succ in hidx.
  assert (hall : BProv Ax_s G
    (pAll
      (pImp
        (betaTermTermAt (tVar 0)
          (Term.rename S oldCode)
          (Term.rename S step)
          (Term.rename S index))
        (betaTermTermAt (tVar 0)
          (Term.rename S newCode)
          (Term.rename S step)
          (Term.rename S index))))).
  {
    exact (BProv_mp Ax_s G (ltTermAt index bound) _ hidx hlt).
  }
  pose proof (BProv_allE Ax_s G _ out hall) as hout.
  cbn [subst] in hout.
  rewrite !subst_betaTermTermAt in hout.
  simpl in hout.
  repeat rewrite term_subst_instTerm_rename_succ in hout.
  exact (BProv_mp Ax_s G
    (betaTermTermAt out oldCode step index)
    (betaTermTermAt out newCode step index)
    hout hold).
Qed.

Lemma term_rename_succ_twice_add_two : forall t,
  Term.rename S (Term.rename S t) =
    Term.rename (fun n => n + 2) t.
Proof.
  intro t.
  rewrite Term.rename_comp.
  apply Term.rename_ext.
  intro n. lia.
Qed.

Lemma rename_succ_twice_betaPrefixAgreementTermAt :
  forall oldCode newCode step bound,
  rename S (rename S
      (betaPrefixAgreementTermAt oldCode newCode step bound)) =
    betaPrefixAgreementTermAt
      (Term.rename (fun n => n + 2) oldCode)
      (Term.rename (fun n => n + 2) newCode)
      (Term.rename (fun n => n + 2) step)
      (Term.rename (fun n => n + 2) bound).
Proof.
  intros oldCode newCode step bound.
  rewrite !rename_betaPrefixAgreementTermAt.
  rewrite !term_rename_succ_twice_add_two.
  reflexivity.
Qed.

Lemma rename_succ_twice_ltTermAt : forall a b,
  rename S (rename S (ltTermAt a b)) =
    ltTermAt
      (Term.rename (fun n => n + 2) a)
      (Term.rename (fun n => n + 2) b).
Proof.
  intros a b.
  rewrite !rename_ltTermAt.
  rewrite !term_rename_succ_twice_add_two.
  reflexivity.
Qed.

Lemma rename_succ_twice_ordinalCodeStepWitnessTermAt :
  forall sequenceCode sequenceStep index,
  rename S (rename S
      (ordinalCodeStepWitnessTermAt sequenceCode sequenceStep index)) =
    ordinalCodeStepWitnessTermAt
      (Term.rename (fun n => n + 2) sequenceCode)
      (Term.rename (fun n => n + 2) sequenceStep)
      (Term.rename (fun n => n + 2) index).
Proof.
  intros sequenceCode sequenceStep index.
  rewrite !rename_ordinalCodeStepWitnessTermAt.
  rewrite !term_rename_succ_twice_add_two.
  reflexivity.
Qed.

(* Prefix agreement transports both beta entries of an existing trace edge. *)
Lemma BProv_Ax_s_ordinalCodeStepWitnessTermAt_of_prefixAgreement :
  forall G oldCode newCode step bound index,
  BProv Ax_s G
    (betaPrefixAgreementTermAt oldCode newCode step bound) ->
  BProv Ax_s G (ltTermAt index bound) ->
  BProv Ax_s G (ltTermAt (tSucc index) bound) ->
  BProv Ax_s G
    (ordinalCodeStepWitnessTermAt oldCode step index) ->
  BProv Ax_s G
    (ordinalCodeStepWitnessTermAt newCode step index).
Proof.
  intros G oldCode newCode step bound index
    hagreement hltCurrent hltNext hwitness.
  set (target :=
    ordinalCodeStepWitnessTermAt newCode step index).
  set (body :=
    pAnd
      (betaTermTermAt (tVar 1)
        (Term.rename (fun n => n + 2) oldCode)
        (Term.rename (fun n => n + 2) step)
        (Term.rename (fun n => n + 2) index))
      (pAnd
        (betaTermTermAt (tVar 0)
          (Term.rename (fun n => n + 2) oldCode)
          (Term.rename (fun n => n + 2) step)
          (tSucc (Term.rename (fun n => n + 2) index)))
        (hfAdjoinGraphTermAt (tVar 0) (tVar 1) (tVar 1)))).
  assert (hwit : BProv Ax_s G (pEx (pEx body))).
  {
    unfold ordinalCodeStepWitnessTermAt in hwitness.
    fold body in hwitness.
    exact hwitness.
  }
  apply (BProv_two_exE_of_sentences
    Ax_s sentence_ax_s G body target hwit).
  set (C := body :: map (rename S) (pEx body :: map (rename S) G)).
  change (BProv Ax_s C (rename S (rename S target))).
      set (oldCode2 := Term.rename (fun n => n + 2) oldCode).
      set (newCode2 := Term.rename (fun n => n + 2) newCode).
      set (step2 := Term.rename (fun n => n + 2) step).
      set (bound2 := Term.rename (fun n => n + 2) bound).
      set (index2 := Term.rename (fun n => n + 2) index).
      assert (hbody : BProv Ax_s C body).
      {
        apply BProv_ass.
        unfold C. simpl. left. reflexivity.
      }
      pose proof (BProv_andE1 Ax_s C _ _ hbody) as hcurrent.
      change (BProv Ax_s C
        (betaTermTermAt (tVar 1) oldCode2 step2 index2))
        in hcurrent.
      pose proof (BProv_andE2 Ax_s C _ _ hbody) as htail.
      change (BProv Ax_s C
        (pAnd
          (betaTermTermAt (tVar 0) oldCode2 step2 (tSucc index2))
          (hfAdjoinGraphTermAt (tVar 0) (tVar 1) (tVar 1))))
        in htail.
      pose proof (BProv_andE1 Ax_s C _ _ htail) as hnext.
      pose proof (BProv_andE2 Ax_s C _ _ htail) as hadjoin.

      pose proof (BProv_lift_two_opened_of_sentences
        Ax_s sentence_ax_s G body _ hagreement) as hagreementC.
      change (BProv Ax_s C
        (rename S (rename S
          (betaPrefixAgreementTermAt oldCode newCode step bound))))
        in hagreementC.
      rewrite rename_succ_twice_betaPrefixAgreementTermAt
        in hagreementC.
      change (BProv Ax_s C
        (betaPrefixAgreementTermAt oldCode2 newCode2 step2 bound2))
        in hagreementC.

      pose proof (BProv_lift_two_opened_of_sentences
        Ax_s sentence_ax_s G body _ hltCurrent) as hltCurrentC.
      change (BProv Ax_s C
        (rename S (rename S (ltTermAt index bound))))
        in hltCurrentC.
      rewrite rename_succ_twice_ltTermAt in hltCurrentC.
      change (BProv Ax_s C (ltTermAt index2 bound2)) in hltCurrentC.

      pose proof (BProv_lift_two_opened_of_sentences
        Ax_s sentence_ax_s G body _ hltNext) as hltNextC.
      change (BProv Ax_s C
        (rename S (rename S (ltTermAt (tSucc index) bound))))
        in hltNextC.
      rewrite rename_succ_twice_ltTermAt in hltNextC.
      change (BProv Ax_s C (ltTermAt (tSucc index2) bound2))
        in hltNextC.

      pose proof
        (BProv_Ax_s_betaPrefixAgreementTermAt_entry_of_ltTerm
          C oldCode2 newCode2 step2 bound2 index2 (tVar 1)
          hagreementC hltCurrentC hcurrent) as hcurrentNew.
      pose proof
        (BProv_Ax_s_betaPrefixAgreementTermAt_entry_of_ltTerm
          C oldCode2 newCode2 step2 bound2 (tSucc index2) (tVar 0)
          hagreementC hltNextC hnext) as hnextNew.
      pose proof
        (BProv_Ax_s_ordinalCodeStepWitnessTermAt_of_components
          C newCode2 step2 index2 (tVar 1) (tVar 0)
          hcurrentNew hnextNew hadjoin) as hnew.
      unfold target.
      rewrite rename_succ_twice_ordinalCodeStepWitnessTermAt.
      change (BProv Ax_s C
        (ordinalCodeStepWitnessTermAt newCode2 step2 index2)).
      exact hnew.
Qed.

(* A one-entry beta-code extension preserves the old recurrence and adds the
   new final Ackermann edge. *)
Lemma BProv_Ax_s_ordinalCodeStepsTermAt_succ_of_extension :
  forall G oldSequenceCode newSequenceCode sequenceStep
      raw oldCoded newCoded,
  BProv Ax_s G
    (ordinalCodeStepsTermAt oldSequenceCode sequenceStep raw) ->
  BProv Ax_s G
    (betaTermTermAt oldCoded oldSequenceCode sequenceStep raw) ->
  BProv Ax_s G
    (betaCodeExtensionTermAt oldSequenceCode sequenceStep
      (tSucc raw) newCoded newSequenceCode) ->
  BProv Ax_s G
    (hfAdjoinGraphTermAt newCoded oldCoded oldCoded) ->
  BProv Ax_s G
    (ordinalCodeStepsTermAt
      newSequenceCode sequenceStep (tSucc raw)).
Proof.
  intros G oldSequenceCode newSequenceCode sequenceStep
    raw oldCoded newCoded hsteps hendpoint hextension hadjoin.
  set (antecedent :=
    ltTermAt (tVar 0) (tSucc (Term.rename S raw))).
  set (consequent :=
    ordinalCodeStepWitnessTermAt
      (Term.rename S newSequenceCode)
      (Term.rename S sequenceStep)
      (tVar 0)).
  set (C := antecedent :: map (rename S) G).
  assert (hbody : BProv Ax_s C consequent).
  {
    set (oldSequenceCode1 := Term.rename S oldSequenceCode).
    set (newSequenceCode1 := Term.rename S newSequenceCode).
    set (sequenceStep1 := Term.rename S sequenceStep).
    set (raw1 := Term.rename S raw).
    set (oldCoded1 := Term.rename S oldCoded).
    set (newCoded1 := Term.rename S newCoded).
    assert (hltSucc : BProv Ax_s C
      (ltTermAt (tVar 0) (tSucc raw1))).
    {
      apply BProv_ass.
      unfold C, antecedent, raw1. simpl. left. reflexivity.
    }
    pose proof (BProv_Ax_s_ltTermAt_succ_right_cases
      C (tVar 0) raw1 hltSucc) as hcases.

    pose proof (BProv_rename_succ_context_cons_of_sentences
      Ax_s sentence_ax_s G antecedent _ hsteps) as hstepsC.
    rewrite rename_ordinalCodeStepsTermAt in hstepsC.
    change (BProv Ax_s C
      (ordinalCodeStepsTermAt oldSequenceCode1 sequenceStep1 raw1))
      in hstepsC.

    pose proof (BProv_rename_succ_context_cons_of_sentences
      Ax_s sentence_ax_s G antecedent _ hendpoint) as hendpointC.
    rewrite rename_betaTermTermAt in hendpointC.
    change (BProv Ax_s C
      (betaTermTermAt oldCoded1 oldSequenceCode1 sequenceStep1 raw1))
      in hendpointC.

    pose proof (BProv_rename_succ_context_cons_of_sentences
      Ax_s sentence_ax_s G antecedent _ hextension) as hextensionC.
    rewrite rename_betaCodeExtensionTermAt in hextensionC.
    change (BProv Ax_s C
      (betaCodeExtensionTermAt oldSequenceCode1 sequenceStep1
        (tSucc raw1) newCoded1 newSequenceCode1)) in hextensionC.
    pose proof
      (BProv_Ax_s_betaPrefixAgreementTermAt_of_betaCodeExtensionTermAt
        C oldSequenceCode1 sequenceStep1 (tSucc raw1)
        newCoded1 newSequenceCode1 hextensionC) as hagreementC.

    pose proof (BProv_rename_succ_context_cons_of_sentences
      Ax_s sentence_ax_s G antecedent _ hadjoin) as hadjoinC.
    rewrite rename_hfAdjoinGraphTermAt in hadjoinC.
    change (BProv Ax_s C
      (hfAdjoinGraphTermAt newCoded1 oldCoded1 oldCoded1))
      in hadjoinC.

    assert (hbelow : BProv Ax_s
      (ltTermAt (tVar 0) raw1 :: C) consequent).
    {
      set (D := ltTermAt (tVar 0) raw1 :: C).
      assert (hlt : BProv Ax_s D (ltTermAt (tVar 0) raw1)).
      {
        apply BProv_ass.
        unfold D. simpl. left. reflexivity.
      }
      pose proof (BProv_context_cons Ax_s C
        (ltTermAt (tVar 0) raw1) _ hstepsC) as hstepsD.
      pose proof
        (BProv_Ax_s_ordinalCodeStepsTermAt_step_of_ltTerm
          D oldSequenceCode1 sequenceStep1 raw1 (tVar 0)
          hstepsD hlt) as holdWitness.
      pose proof (BProv_context_cons Ax_s C
        (ltTermAt (tVar 0) raw1) _ hagreementC) as hagreementD.
      pose proof (BProv_context_cons Ax_s C
        (ltTermAt (tVar 0) raw1) _ hltSucc) as hltCurrent.
      pose proof (BProv_Ax_s_ltTermAt_succ_succ
        D (tVar 0) raw1 hlt) as hltNext.
      pose proof
        (BProv_Ax_s_ordinalCodeStepWitnessTermAt_of_prefixAgreement
          D oldSequenceCode1 newSequenceCode1 sequenceStep1
          (tSucc raw1) (tVar 0)
          hagreementD hltCurrent hltNext holdWitness) as hnewWitness.
      change (BProv Ax_s D consequent) in hnewWitness.
      exact hnewWitness.
    }

    assert (hequal : BProv Ax_s
      (pEq (tVar 0) raw1 :: C) consequent).
    {
      set (D := pEq (tVar 0) raw1 :: C).
      assert (heqVarRaw : BProv Ax_s D (pEq (tVar 0) raw1)).
      {
        apply BProv_ass.
        unfold D. simpl. left. reflexivity.
      }
      pose proof (BProv_eqSym Ax_s D (tVar 0) raw1 heqVarRaw)
        as heqRawVar.
      pose proof (BProv_context_cons Ax_s C
        (pEq (tVar 0) raw1) _ hagreementC) as hagreementD.
      pose proof (BProv_context_cons Ax_s C
        (pEq (tVar 0) raw1) _ hendpointC) as hendpointD.
      assert (hltRaw : BProv Ax_s D
        (ltTermAt raw1 (tSucc raw1))).
      {
        apply BProv_Ax_s_ltTermAt_succ_right_of_leTermAt.
        apply BProv_Ax_s_leTermAt_refl.
      }
      pose proof
        (BProv_Ax_s_betaPrefixAgreementTermAt_entry_of_ltTerm
          D oldSequenceCode1 newSequenceCode1 sequenceStep1
          (tSucc raw1) raw1 oldCoded1
          hagreementD hltRaw hendpointD) as holdAtRaw.
      pose proof
        (BProv_Ax_s_betaTermTermAt_of_eq_index
          D oldCoded1 newSequenceCode1 sequenceStep1 raw1 (tVar 0)
          heqRawVar holdAtRaw) as holdAtIndex.
      pose proof
        (BProv_Ax_s_betaTermTermAt_of_betaCodeExtensionTermAt
          C oldSequenceCode1 sequenceStep1 (tSucc raw1)
          newCoded1 newSequenceCode1 hextensionC) as hnewAtSuccRawC.
      pose proof (BProv_context_cons Ax_s C
        (pEq (tVar 0) raw1) _ hnewAtSuccRawC) as hnewAtSuccRaw.
      pose proof (BProv_eq_congr_succ Ax_s D raw1 (tVar 0)
        heqRawVar) as heqSucc.
      pose proof
        (BProv_Ax_s_betaTermTermAt_of_eq_index
          D newCoded1 newSequenceCode1 sequenceStep1
          (tSucc raw1) (tSucc (tVar 0))
          heqSucc hnewAtSuccRaw) as hnewAtSuccIndex.
      pose proof (BProv_context_cons Ax_s C
        (pEq (tVar 0) raw1) _ hadjoinC) as hadjoinD.
      pose proof
        (BProv_Ax_s_ordinalCodeStepWitnessTermAt_of_components
          D newSequenceCode1 sequenceStep1 (tVar 0)
          oldCoded1 newCoded1 holdAtIndex hnewAtSuccIndex hadjoinD)
        as hnewWitness.
      change (BProv Ax_s D consequent) in hnewWitness.
      exact hnewWitness.
    }
    exact (BProv_orE Ax_s C
      (ltTermAt (tVar 0) raw1) (pEq (tVar 0) raw1)
      consequent hcases hbelow hequal).
  }
  assert (himp : BProv Ax_s (map (rename S) G)
    (pImp antecedent consequent)).
  {
    unfold C in hbody.
    exact (BProv_impI Ax_s (map (rename S) G)
      antecedent consequent hbody).
  }
  assert (hall : BProv Ax_s G (pAll (pImp antecedent consequent))).
  {
    exact (BProv_allI_of_sentences Ax_s G
      (pImp antecedent consequent) sentence_ax_s himp).
  }
  unfold ordinalCodeStepsTermAt.
  change (BProv Ax_s G (pAll (pImp antecedent consequent))).
  exact hall.
Qed.

Lemma BProv_Ax_s_ordinalCodeGraphBodyTermAt_succ_of_extension :
  forall G oldSequenceCode newSequenceCode sequenceStep
      raw oldCoded newCoded,
  BProv Ax_s G
    (ordinalCodeGraphBodyTermAt
      oldSequenceCode sequenceStep raw oldCoded) ->
  BProv Ax_s G
    (betaCodeExtensionTermAt oldSequenceCode sequenceStep
      (tSucc raw) newCoded newSequenceCode) ->
  BProv Ax_s G
    (hfAdjoinGraphTermAt newCoded oldCoded oldCoded) ->
  BProv Ax_s G
    (ordinalCodeGraphBodyTermAt
      newSequenceCode sequenceStep (tSucc raw) newCoded).
Proof.
  intros G oldSequenceCode newSequenceCode sequenceStep
    raw oldCoded newCoded hbody hextension hadjoin.
  pose proof (BProv_andE1 Ax_s G _ _ hbody) as hhead.
  change (BProv Ax_s G
    (betaTermTermAt tZero oldSequenceCode sequenceStep tZero))
    in hhead.
  pose proof (BProv_andE2 Ax_s G _ _ hbody) as htail.
  change (BProv Ax_s G
    (pAnd
      (betaTermTermAt oldCoded oldSequenceCode sequenceStep raw)
      (ordinalCodeStepsTermAt oldSequenceCode sequenceStep raw)))
    in htail.
  pose proof (BProv_andE1 Ax_s G _ _ htail) as hendpoint.
  pose proof (BProv_andE2 Ax_s G _ _ htail) as hsteps.
  pose proof
    (BProv_Ax_s_betaPrefixAgreementTermAt_of_betaCodeExtensionTermAt
      G oldSequenceCode sequenceStep (tSucc raw)
      newCoded newSequenceCode hextension) as hagreement.
  pose proof
    (BProv_Ax_s_betaPrefixAgreementTermAt_entry_of_ltTerm
      G oldSequenceCode newSequenceCode sequenceStep
      (tSucc raw) tZero tZero hagreement
      (BProv_Ax_s_ltTermAt_zero_succ G raw) hhead) as hheadNew.
  pose proof
    (BProv_Ax_s_betaTermTermAt_of_betaCodeExtensionTermAt
      G oldSequenceCode sequenceStep (tSucc raw)
      newCoded newSequenceCode hextension) as hendpointNew.
  pose proof
    (BProv_Ax_s_ordinalCodeStepsTermAt_succ_of_extension
      G oldSequenceCode newSequenceCode sequenceStep
      raw oldCoded newCoded hsteps hendpoint hextension hadjoin)
    as hstepsNew.
  unfold ordinalCodeGraphBodyTermAt.
  exact (BProv_andI Ax_s G _ _ hheadNew
    (BProv_andI Ax_s G _ _ hendpointNew hstepsNew)).
Qed.
