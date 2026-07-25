(* ===================================================================== *)
(*  PAHFOrdinalCodeInjective.v                                           *)
(*                                                                       *)
(*  Raw-input injectivity of the PA-internal finite-ordinal code graph.   *)
(*                                                                       *)
(*  The arithmetic trace argument below is unconditional once PA proves  *)
(*  the two elementary translated HF self-successor laws.  The final     *)
(*  constructor discharges those laws from the existing                  *)
(*  [TranslatedHFFinAxiomProofs] interface.                               *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List.
From Stdlib Require Import Logic.FunctionalExtensionality.
From FirstOrder Require Import Fol Calculus Completeness.
From PAHF Require Import PAHF
  PAHFProofCalculus
  PAHFOrdinalCode PAHFOrdinalCodeTotal PAHFOrdinalCodeTotalCapacity
  PAHFOrdinalCodeTotalInduction
  PAHFRoundTripArithmetic
  (* The injectivity interface itself remains in the round-trip layer. *)
  PAHFRoundTripEquality.

Import ListNotations.
Import PA PA.Term PA.Formula.

(** On ordinal-like HF objects, two self-successors with a common output
    have equal inputs. *)
Definition HF_selfSuccInjectiveSentence : form :=
  fAll (fAll (fAll
    (fImp
      (HF_succAt 0 2)
      (fImp
        (HF_succAt 0 1)
        (fEq 2 1))))).

Lemma HF_selfSuccInjectiveSentence_sentence :
  Fol.Sentence HF_selfSuccInjectiveSentence.
Proof.
  intros i hi.
  unfold HF_selfSuccInjectiveSentence, HF_ordinalLikeAt,
    HF_transitiveAt, HF_memTotalOnAt, HF_succAt, HF_adjoinAt,
    fIff in hi.
  simpl in hi.
  lia.
Qed.

Lemma BProv_HFFin_selfSuccInjectiveSentence :
  Completeness.BProv HFFinAx_s [] HF_selfSuccInjectiveSentence.
Proof.
  apply Completeness.completeness_inf.
  - exact Sentences_HFFin.
  - exact HF_selfSuccInjectiveSentence_sentence.
  - intros V mem v hHF.
    pose (M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s V mem v hHF).
    intros a b out hsuccA hsuccB.
    assert (hsuccA' : out = foam_adjoin V M a a).
    {
      exact (proj1 (foam_HF_succAt_spec V M
        (scons V out (scons V b (scons V a v))) 0 2) hsuccA).
    }
    assert (hsuccB' : out = foam_adjoin V M b b).
    {
      exact (proj1 (foam_HF_succAt_spec V M
        (scons V out (scons V b (scons V a v))) 0 1) hsuccB).
    }
    assert (hasucc : foam_mem V M a (foam_adjoin V M b b)).
    {
      rewrite <- hsuccB', hsuccA'.
      apply foam_adjoin_self_mem.
    }
    destruct (proj1 (foam_adjoin_spec V M a b b) hasucc)
      as [hab | hab].
    + assert (hbsucc : foam_mem V M b (foam_adjoin V M a a)).
      {
        rewrite <- hsuccA', hsuccB'.
        apply foam_adjoin_self_mem.
      }
      destruct (proj1 (foam_adjoin_spec V M b a a) hbsucc)
        as [hba | hba].
      * exfalso. exact (foam_mem_asymm V M a b hab hba).
      * symmetry. exact hba.
    + exact hab.
Qed.

(** No HF self-successor is empty. *)
Definition HF_selfSuccNonemptySentence : form :=
  fAll (fAll
    (fImp
      (HF_succAt 0 1)
      (fImp
        (HF_emptyAt 0)
        fBot))).

Lemma HF_selfSuccNonemptySentence_sentence :
  Fol.Sentence HF_selfSuccNonemptySentence.
Proof.
  intros i hi.
  unfold HF_selfSuccNonemptySentence, HF_succAt, HF_adjoinAt,
    HF_emptyAt, fIff in hi.
  simpl in hi.
  lia.
Qed.

Lemma BProv_HFFin_selfSuccNonemptySentence :
  Completeness.BProv HFFinAx_s [] HF_selfSuccNonemptySentence.
Proof.
  apply Completeness.completeness_inf.
  - exact Sentences_HFFin.
  - exact HF_selfSuccNonemptySentence_sentence.
  - intros V mem v hHF.
    pose (M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s V mem v hHF).
    intros a out hsucc hempty.
    assert (hsucc' : out = foam_adjoin V M a a).
    {
      exact (proj1 (foam_HF_succAt_spec V M
        (scons V out (scons V a v)) 0 1) hsucc).
    }
    assert (hempty' : out = foam_empty V M).
    {
      exact (proj1 (foam_HF_emptyAt_empty V M
        (scons V out (scons V a v)) 0) hempty).
    }
    assert (haMem : foam_mem V M a (foam_adjoin V M a a)).
    { apply foam_adjoin_self_mem. }
    rewrite <- hsucc', hempty' in haMem.
    exact (foam_empty_spec V M a haMem).
Qed.

(** Term-parametric empty-code predicate. *)
Definition hfEmptyTermAt (setCode : term) : formula :=
  pAll (pImp
    (hfMemTermAt 0 (Term.rename S setCode))
    pBot).

(** PA renderings of the two closed HF facts. *)
Definition selfSuccInjectivePAFormula : formula :=
  pAll (pAll (pAll
    (pImp
      (hfAdjoinGraphTermAt (tVar 0) (tVar 2) (tVar 2))
      (pImp
        (hfAdjoinGraphTermAt (tVar 0) (tVar 1) (tVar 1))
        (pEq (tVar 2) (tVar 1)))))).

Definition selfSuccNonemptyPAFormula : formula :=
  pAll (pAll
    (pImp
      (hfAdjoinGraphTermAt (tVar 0) (tVar 1) (tVar 1))
      (pImp (hfEmptyTermAt (tVar 0)) pBot))).

Lemma translateHFFormula_selfSuccInjectiveSentence :
  translateHFFormula HF_selfSuccInjectiveSentence =
    selfSuccInjectivePAFormula.
Proof. reflexivity. Qed.

Lemma translateHFFormula_selfSuccNonemptySentence :
  translateHFFormula HF_selfSuccNonemptySentence =
    selfSuccNonemptyPAFormula.
Proof. reflexivity. Qed.

(** The exact translated-HF residue used by raw graph injectivity. *)
Record PAOrdinalSelfSuccessorProofs : Prop := {
  pa_selfSucc_injective : BProv Ax_s [] selfSuccInjectivePAFormula;
  pa_selfSucc_nonempty : BProv Ax_s [] selfSuccNonemptyPAFormula
}.

Definition PAOrdinalSelfSuccessorProofs_of_translatedHFFin
    (P : TranslatedHFFinAxiomProofs) :
  PAOrdinalSelfSuccessorProofs.
Proof.
  constructor.
  - rewrite <- translateHFFormula_selfSuccInjectiveSentence.
    apply (BProv_lift_translatedHFFinAx_to_PA
      (BProv_Ax_s_of_translatedHFFinAx_of_proofs P)).
    apply BProv_translateHFFormula_of_BProv_HFFin.
    exact BProv_HFFin_selfSuccInjectiveSentence.
  - rewrite <- translateHFFormula_selfSuccNonemptySentence.
    apply (BProv_lift_translatedHFFinAx_to_PA
      (BProv_Ax_s_of_translatedHFFinAx_of_proofs P)).
    apply BProv_translateHFFormula_of_BProv_HFFin.
    exact BProv_HFFin_selfSuccNonemptySentence.
Defined.

(** Eliminate the two beta-sequence witnesses while retaining the fully
    opened trace body as a finite-context assumption. *)
Lemma BProv_Ax_s_ordinalCodeGraphTermAt_elim_opened : forall
    G raw coded target,
  BProv Ax_s G (ordinalCodeGraphTermAt raw coded) ->
  let body := ordinalCodeGraphBodyTermAt
    (tVar 1) (tVar 0)
    (Term.rename (fun n => n + 2) raw)
    (Term.rename (fun n => n + 2) coded) in
  let inner := pEx body in
  BProv Ax_s
    (body :: map (rename S) (inner :: map (rename S) G))
    (rename S (rename S target)) ->
  BProv Ax_s G target.
Proof.
  intros G raw coded target hgraph.
  exact (BProv_ordinalCodeGraphTermAt_elim_opened
    Ax_s sentence_ax_s G raw coded target hgraph).
Qed.

(** [codedOrdinalDomain] has only slot zero free, so lifting a substitution
    under a fresh binder leaves it unchanged. *)
Lemma subst_up_inst_codedOrdinalDomain : forall current,
  subst (Term.upSubst (instTerm current)) codedOrdinalDomain =
    codedOrdinalDomain.
Proof.
  intro current.
  transitivity (subst (fun n => tVar n) codedOrdinalDomain).
  - apply subst_ext_free.
    intros n hn.
    pose proof (codedOrdinalDomain_free n hn) as hn0.
    subst n. reflexivity.
  - apply subst_id.
Qed.

Lemma subst_hfEmptyTermAt : forall sigma setCode,
  subst sigma (hfEmptyTermAt setCode) =
    hfEmptyTermAt (Term.subst sigma setCode).
Proof.
  intros sigma setCode.
  unfold hfEmptyTermAt.
  cbn [subst].
  rewrite subst_up_hfMemTermAt_zero_rename_succ.
  reflexivity.
Qed.

(** Instantiate the closed self-successor injectivity theorem at arbitrary
    PA terms. *)
Lemma BProv_Ax_s_hfAdjoinGraphTermAt_injective_self : forall
    (P : PAOrdinalSelfSuccessorProofs) G a b out,
  BProv Ax_s G (hfAdjoinGraphTermAt out a a) ->
  BProv Ax_s G (hfAdjoinGraphTermAt out b b) ->
  BProv Ax_s G (pEq a b).
Proof.
  intros P G a b out hsuccA hsuccB.
  assert (hall : BProv Ax_s G selfSuccInjectivePAFormula).
  { exact (BProv_weaken_nil Ax_s G _ (pa_selfSucc_injective P)). }
  pose proof (BProv_allE Ax_s G _ a hall) as haRaw.
  pose proof (BProv_allE Ax_s G _ b haRaw) as hbRaw.
  pose proof (BProv_allE Ax_s G _ out hbRaw) as houtRaw.
  assert (haTermNorm :
      Term.subst (instTerm out)
        (Term.subst (Term.upSubst (instTerm b))
          (Term.rename S (Term.rename S a))) = a).
  {
    rewrite Term.subst_rename_succ_up.
    rewrite term_subst_instTerm_rename_succ.
    rewrite term_subst_instTerm_rename_succ.
    reflexivity.
  }
  assert (hbTermNorm :
      Term.subst (instTerm out)
        (Term.subst (Term.upSubst (instTerm b))
          (Term.rename S (tVar 0))) = b).
  {
    rewrite Term.subst_rename_succ_up.
    simpl.
    rewrite term_subst_instTerm_rename_succ.
    reflexivity.
  }
  assert (houtExpanded : BProv Ax_s G
      (pImp
        (hfAdjoinGraphTermAt out a a)
        (pImp
          (hfAdjoinGraphTermAt out b b)
          (pEq a b)))).
  {
    unfold selfSuccInjectivePAFormula in houtRaw.
    cbn [subst] in houtRaw.
    rewrite !subst_hfAdjoinGraphTermAt in houtRaw.
    repeat rewrite Term.subst_rename_succ_up in houtRaw.
    repeat rewrite term_subst_instTerm_rename_succ in houtRaw.
    cbn [instTerm Term.subst Term.upSubst] in houtRaw.
    rewrite haTermNorm, hbTermNorm in houtRaw.
    exact houtRaw.
  }
  exact (BProv_mp Ax_s G _ _
    (BProv_mp Ax_s G _ _ houtExpanded hsuccA) hsuccB).
Qed.

Lemma BProv_Ax_s_bot_of_hfAdjoinGraphTermAt_hfEmptyTermAt : forall
    (P : PAOrdinalSelfSuccessorProofs) G a out,
  BProv Ax_s G (hfAdjoinGraphTermAt out a a) ->
  BProv Ax_s G (hfEmptyTermAt out) ->
  BProv Ax_s G pBot.
Proof.
  intros P G a out hsucc hempty.
  assert (hall : BProv Ax_s G selfSuccNonemptyPAFormula).
  { exact (BProv_weaken_nil Ax_s G _ (pa_selfSucc_nonempty P)). }
  pose proof (BProv_allE Ax_s G _ a hall) as haRaw.
  pose proof (BProv_allE Ax_s G _ out haRaw) as houtRaw.
  assert (himp : BProv Ax_s G
      (pImp
        (hfAdjoinGraphTermAt out a a)
        (pImp (hfEmptyTermAt out) pBot))).
  {
    unfold selfSuccNonemptyPAFormula in houtRaw.
    cbn [subst] in houtRaw.
    rewrite !subst_hfAdjoinGraphTermAt in houtRaw.
    rewrite !subst_hfEmptyTermAt in houtRaw.
    repeat rewrite Term.subst_rename_succ_up in houtRaw.
    repeat rewrite term_subst_instTerm_rename_succ in houtRaw.
    cbn [instTerm Term.subst Term.upSubst] in houtRaw.
    repeat rewrite term_subst_instTerm_rename_succ in houtRaw.
    exact houtRaw.
  }
  exact (BProv_mp Ax_s G _ _
    (BProv_mp Ax_s G _ _ himp hsucc) hempty).
Qed.

(** Directly expose the common beta index at raw zero. *)
Lemma BProv_Ax_s_eq_zero_of_ordinalCodeGraphTermAt_zero : forall
    G coded,
  BProv Ax_s G (ordinalCodeGraphTermAt tZero coded) ->
  BProv Ax_s G (pEq coded tZero).
Proof.
  intros G coded hgraph.
  set (target := pEq coded tZero).
  apply (BProv_Ax_s_ordinalCodeGraphTermAt_elim_opened
    G tZero coded target hgraph).
  set (body := ordinalCodeGraphBodyTermAt
    (tVar 1) (tVar 0)
    (Term.rename (fun n => n + 2) tZero)
    (Term.rename (fun n => n + 2) coded)).
  set (inner := pEx body).
  set (C := body :: map (rename S) (inner :: map (rename S) G)).
  assert (hbody : BProv Ax_s C body).
  { apply BProv_ass. unfold C. simpl. now left. }
  assert (hzero : BProv Ax_s C
      (betaTermTermAt tZero (tVar 1) (tVar 0) tZero)).
  {
    unfold body, ordinalCodeGraphBodyTermAt in hbody.
    exact (BProv_andE1 Ax_s C _ _ hbody).
  }
  assert (hend : BProv Ax_s C
      (betaTermTermAt
        (Term.rename (fun n => n + 2) coded)
        (tVar 1) (tVar 0) tZero)).
  {
    unfold body, ordinalCodeGraphBodyTermAt in hbody.
    pose proof (BProv_andE2 Ax_s C _ _ hbody) as htail.
    simpl in htail.
    exact (BProv_andE1 Ax_s C _ _ htail).
  }
  pose proof (BProv_Ax_s_eq_of_betaTermTermAt_betaTermTermAt_same_index
    C tZero (Term.rename (fun n => n + 2) coded)
    (tVar 1) (tVar 0) tZero hzero hend) as heq.
  unfold C, inner, body, target.
  cbn [rename].
  replace (Term.rename S (Term.rename S coded))
    with (Term.rename (fun n => n + 2) coded).
  2: {
    rewrite Term.rename_comp.
    apply Term.rename_ext. intro n. lia.
  }
  exact heq.
Qed.

(** Restrict a bounded recurrence proof to a smaller raw bound. *)
Lemma BProv_Ax_s_ordinalCodeStepsTermAt_of_leTerm : forall
    G sequenceCode sequenceStep low high,
  BProv Ax_s G
    (ordinalCodeStepsTermAt sequenceCode sequenceStep high) ->
  BProv Ax_s G (leTermAt low high) ->
  BProv Ax_s G
    (ordinalCodeStepsTermAt sequenceCode sequenceStep low).
Proof.
  intros G sequenceCode sequenceStep low high hsteps hle.
  set (antecedent := ltTermAt (tVar 0) (Term.rename S low)).
  set (consequent := ordinalCodeStepWitnessTermAt
    (Term.rename S sequenceCode)
    (Term.rename S sequenceStep) (tVar 0)).
  set (Q := map (rename S) G).
  set (C := antecedent :: Q).
  assert (hbody : BProv Ax_s C consequent).
  {
    assert (hltLow : BProv Ax_s C
        (ltTermAt (tVar 0) (Term.rename S low))).
    { apply BProv_ass. unfold C, antecedent. simpl. now left. }
    assert (hleC : BProv Ax_s C
        (leTermAt (Term.rename S low) (Term.rename S high))).
    {
      pose proof (BProv_rename_succ_context_cons_of_sentences
        Ax_s sentence_ax_s G antecedent _ hle) as h.
      unfold C, Q.
      rewrite rename_leTermAt in h.
      exact h.
    }
    assert (hltHigh : BProv Ax_s C
        (ltTermAt (tVar 0) (Term.rename S high))).
    {
      exact (BProv_Ax_s_ltTermAt_of_lt_leTermAt C
        (tVar 0) (Term.rename S low) (Term.rename S high)
        hltLow hleC).
    }
    assert (hstepsC : BProv Ax_s C
        (ordinalCodeStepsTermAt
          (Term.rename S sequenceCode)
          (Term.rename S sequenceStep)
          (Term.rename S high))).
    {
      pose proof (BProv_rename_succ_context_cons_of_sentences
        Ax_s sentence_ax_s G antecedent _ hsteps) as h.
      unfold C, Q.
      rewrite rename_ordinalCodeStepsTermAt in h.
      exact h.
    }
    exact (BProv_Ax_s_ordinalCodeStepsTermAt_step_of_ltTerm
      C (Term.rename S sequenceCode) (Term.rename S sequenceStep)
      (Term.rename S high) (tVar 0) hstepsC hltHigh).
  }
  assert (himp : BProv Ax_s Q (pImp antecedent consequent)).
  { unfold C in hbody. exact (BProv_impI Ax_s Q _ _ hbody). }
  assert (hall := BProv_allI_of_sentences Ax_s G
    (pImp antecedent consequent) sentence_ax_s himp).
  unfold ordinalCodeStepsTermAt, antecedent, consequent in hall.
  exact hall.
Qed.

(** Equality replacement in the output slot of the adjunction graph. *)
Lemma BProv_hfAdjoinGraphTermAt_of_new_eq_term : forall
    (B : formula -> Prop) G oldNew newNew oldCode elemCode,
  BProv B G (pEq oldNew newNew) ->
  BProv B G (hfAdjoinGraphTermAt oldNew oldCode elemCode) ->
  BProv B G (hfAdjoinGraphTermAt newNew oldCode elemCode).
Proof.
  intros B G oldNew newNew oldCode elemCode heq hgraph.
  set (context := hfAdjoinGraphTermAt
    (tVar 0) (Term.rename S oldCode) (Term.rename S elemCode)).
  assert (hinst : BProv B G (subst (instTerm oldNew) context)).
  {
    unfold context.
    rewrite subst_hfAdjoinGraphTermAt.
    simpl.
    repeat rewrite term_subst_instTerm_rename_succ.
    exact hgraph.
  }
  pose proof (BProv_eqElim B G oldNew newNew context heq hinst) as hnew.
  unfold context in hnew.
  rewrite subst_hfAdjoinGraphTermAt in hnew.
  simpl in hnew.
  repeat rewrite term_subst_instTerm_rename_succ in hnew.
  exact hnew.
Qed.

Definition ordinalCodePredEdgeTermAt (raw coded : term) : formula :=
  pEx
    (pAnd
      (ordinalCodeGraphTermAt
        (Term.rename S raw) (tVar 0))
      (hfAdjoinGraphTermAt
        (Term.rename S coded) (tVar 0) (tVar 0))).

Lemma subst_ordinalCodePredEdgeTermAt : forall sigma raw coded,
  subst sigma (ordinalCodePredEdgeTermAt raw coded) =
    ordinalCodePredEdgeTermAt
      (Term.subst sigma raw) (Term.subst sigma coded).
Proof.
  intros sigma raw coded.
  unfold ordinalCodePredEdgeTermAt.
  cbn [subst].
  rewrite subst_ordinalCodeGraphTermAt.
  rewrite subst_hfAdjoinGraphTermAt.
  repeat rewrite Term.subst_rename_succ_up.
  reflexivity.
Qed.

Lemma rename_ordinalCodePredEdgeTermAt : forall r raw coded,
  rename r (ordinalCodePredEdgeTermAt raw coded) =
    ordinalCodePredEdgeTermAt
      (Term.rename r raw) (Term.rename r coded).
Proof.
  intros r raw coded.
  rename_from_subst subst_ordinalCodePredEdgeTermAt.
Qed.

(** Invert a successor-stage code graph into its predecessor graph and its
    final Ackermann-adjoin edge. *)
Lemma BProv_Ax_s_ordinalCodePredEdgeTermAt_of_succ_graph : forall
    G raw coded,
  BProv Ax_s G (ordinalCodeGraphTermAt (tSucc raw) coded) ->
  BProv Ax_s G (ordinalCodePredEdgeTermAt raw coded).
Proof.
  intros G raw coded hgraph.
  set (target := ordinalCodePredEdgeTermAt raw coded).
  apply (BProv_Ax_s_ordinalCodeGraphTermAt_elim_opened
    G (tSucc raw) coded target hgraph).
  set (graphBody := ordinalCodeGraphBodyTermAt
    (tVar 1) (tVar 0)
    (Term.rename (fun n => n + 2) (tSucc raw))
    (Term.rename (fun n => n + 2) coded)).
  set (graphInner := pEx graphBody).
  set (C := graphBody ::
    map (rename S) (graphInner :: map (rename S) G)).
  assert (hbodyC : BProv Ax_s C graphBody).
  { apply BProv_ass. unfold C. simpl. now left. }
  set (raw2 := Term.rename (fun n => n + 2) raw).
  set (coded2 := Term.rename (fun n => n + 2) coded).
  assert (hzeroC : BProv Ax_s C
      (betaTermTermAt tZero (tVar 1) (tVar 0) tZero)).
  {
    unfold graphBody, ordinalCodeGraphBodyTermAt in hbodyC.
    exact (BProv_andE1 Ax_s C _ _ hbodyC).
  }
  pose proof (BProv_andE2 Ax_s C _ _ hbodyC) as htailC.
  assert (hendC : BProv Ax_s C
      (betaTermTermAt coded2 (tVar 1) (tVar 0) (tSucc raw2))).
  {
    unfold graphBody, ordinalCodeGraphBodyTermAt in htailC.
    unfold raw2, coded2.
    simpl in htailC.
    exact (BProv_andE1 Ax_s C _ _ htailC).
  }
  assert (hstepsC : BProv Ax_s C
      (ordinalCodeStepsTermAt (tVar 1) (tVar 0) (tSucc raw2))).
  {
    unfold graphBody, ordinalCodeGraphBodyTermAt in htailC.
    unfold raw2.
    simpl in htailC.
    exact (BProv_andE2 Ax_s C _ _ htailC).
  }
  assert (hltC : BProv Ax_s C (ltTermAt raw2 (tSucc raw2))).
  {
    apply BProv_Ax_s_ltTermAt_succ_right_of_leTermAt.
    apply BProv_Ax_s_leTermAt_refl.
  }
  assert (hstepC : BProv Ax_s C
      (ordinalCodeStepWitnessTermAt (tVar 1) (tVar 0) raw2)).
  {
    exact (BProv_Ax_s_ordinalCodeStepsTermAt_step_of_ltTerm
      C (tVar 1) (tVar 0) (tSucc raw2) raw2 hstepsC hltC).
  }
  set (raw4 := Term.rename (fun n => n + 4) raw).
  set (coded4 := Term.rename (fun n => n + 4) coded).
  set (stepBody :=
    pAnd
      (betaTermTermAt (tVar 1) (tVar 3) (tVar 2) raw4)
      (pAnd
        (betaTermTermAt (tVar 0) (tVar 3) (tVar 2) (tSucc raw4))
        (hfAdjoinGraphTermAt (tVar 0) (tVar 1) (tVar 1)))).
  set (stepInner := pEx stepBody).
  assert (hstepEx : BProv Ax_s C (pEx (pEx stepBody))).
  {
    unfold ordinalCodeStepWitnessTermAt in hstepC.
    unfold stepBody, raw4.
    unfold raw2 in hstepC.
    cbn [Term.rename] in hstepC.
    repeat rewrite Term.rename_comp in hstepC.
    replace (fun x : nat => x + 2 + 2) with
      (fun x => x + 4) in hstepC
      by (apply functional_extensionality; intro x; lia).
    exact hstepC.
  }
  apply (BProv_two_exE_of_sentences Ax_s sentence_ax_s
    C stepBody (rename S (rename S target)) hstepEx).
  set (D := stepBody ::
    map (rename S) (stepInner :: map (rename S) C)).
  change (BProv Ax_s D
    (rename S (rename S (rename S (rename S target))))).
  assert (hstepBodyD : BProv Ax_s D stepBody).
  { apply BProv_ass. unfold D. simpl. now left. }
  assert (lift2ToD : forall phi,
      BProv Ax_s C phi ->
      BProv Ax_s D (rename S (rename S phi))).
  {
    intros phi hphi.
    pose proof (BProv_lift_two_contexts_of_sentences
      Ax_s sentence_ax_s C stepInner stepBody phi hphi) as h.
    unfold D. exact h.
  }
  pose proof (lift2ToD _ hzeroC) as hzeroDRaw.
  assert (hzeroD : BProv Ax_s D
      (betaTermTermAt tZero (tVar 3) (tVar 2) tZero)).
  {
    rewrite !rename_betaTermTermAt in hzeroDRaw.
    simpl in hzeroDRaw.
    exact hzeroDRaw.
  }
  pose proof (lift2ToD _ hendC) as hendDRaw.
  assert (hendD : BProv Ax_s D
      (betaTermTermAt coded4 (tVar 3) (tVar 2) (tSucc raw4))).
  {
    rewrite !rename_betaTermTermAt in hendDRaw.
    unfold raw2, coded2, raw4, coded4 in *.
    repeat rewrite Term.rename_comp in hendDRaw.
    replace (fun x : nat => S (S (x + 2))) with
      (fun x => x + 4) in hendDRaw
      by (apply functional_extensionality; intro x; lia).
    cbn [Term.rename] in hendDRaw.
    repeat rewrite Term.rename_comp in hendDRaw.
    replace (fun x : nat => S (S (x + 2))) with
      (fun x => x + 4) in hendDRaw
      by (apply functional_extensionality; intro x; lia).
    exact hendDRaw.
  }
  pose proof (lift2ToD _ hstepsC) as hstepsDRaw.
  assert (hstepsD : BProv Ax_s D
      (ordinalCodeStepsTermAt (tVar 3) (tVar 2) (tSucc raw4))).
  {
    rewrite !rename_ordinalCodeStepsTermAt in hstepsDRaw.
    unfold raw2, raw4 in *.
    repeat rewrite Term.rename_comp in hstepsDRaw.
    replace (fun x : nat => S (S (x + 2))) with
      (fun x => x + 4) in hstepsDRaw
      by (apply functional_extensionality; intro x; lia).
    cbn [Term.rename] in hstepsDRaw.
    repeat rewrite Term.rename_comp in hstepsDRaw.
    replace (fun x : nat => S (S (x + 2))) with
      (fun x => x + 4) in hstepsDRaw
      by (apply functional_extensionality; intro x; lia).
    exact hstepsDRaw.
  }
  assert (hcurrentD : BProv Ax_s D
      (betaTermTermAt (tVar 1) (tVar 3) (tVar 2) raw4)).
  {
    unfold stepBody in hstepBodyD.
    exact (BProv_andE1 Ax_s D _ _ hstepBodyD).
  }
  pose proof (BProv_andE2 Ax_s D _ _ hstepBodyD) as hstepTailD.
  assert (hnextD : BProv Ax_s D
      (betaTermTermAt (tVar 0) (tVar 3) (tVar 2) (tSucc raw4))).
  {
    unfold stepBody in hstepTailD.
    exact (BProv_andE1 Ax_s D _ _ hstepTailD).
  }
  assert (hadjoinD : BProv Ax_s D
      (hfAdjoinGraphTermAt (tVar 0) (tVar 1) (tVar 1))).
  {
    unfold stepBody in hstepTailD.
    exact (BProv_andE2 Ax_s D _ _ hstepTailD).
  }
  assert (hnextEq : BProv Ax_s D (pEq (tVar 0) coded4)).
  {
    exact (BProv_Ax_s_eq_of_betaTermTermAt_betaTermTermAt_same_index
      D coded4 (tVar 0) (tVar 3) (tVar 2) (tSucc raw4)
      hendD hnextD).
  }
  assert (hadjoinCodedD : BProv Ax_s D
      (hfAdjoinGraphTermAt coded4 (tVar 1) (tVar 1))).
  {
    exact (BProv_hfAdjoinGraphTermAt_of_new_eq_term
      Ax_s D (tVar 0) coded4 (tVar 1) (tVar 1)
      hnextEq hadjoinD).
  }
  assert (hleD : BProv Ax_s D (leTermAt raw4 (tSucc raw4))).
  { apply BProv_Ax_s_leTermAt_self_succ. }
  assert (hstepsLowD : BProv Ax_s D
      (ordinalCodeStepsTermAt (tVar 3) (tVar 2) raw4)).
  {
    exact (BProv_Ax_s_ordinalCodeStepsTermAt_of_leTerm
      D (tVar 3) (tVar 2) raw4 (tSucc raw4) hstepsD hleD).
  }
  assert (hpredGraphD : BProv Ax_s D
      (ordinalCodeGraphTermAt raw4 (tVar 1))).
  {
    apply (BProv_ordinalCodeGraphTermAt_of_body
      Ax_s D (tVar 3) (tVar 2) raw4 (tVar 1)).
    unfold ordinalCodeGraphBodyTermAt.
    exact (BProv_andI Ax_s D _ _ hzeroD
      (BProv_andI Ax_s D _ _ hcurrentD hstepsLowD)).
  }
  assert (hpairD : BProv Ax_s D
      (pAnd
        (ordinalCodeGraphTermAt raw4 (tVar 1))
        (hfAdjoinGraphTermAt coded4 (tVar 1) (tVar 1)))).
  { exact (BProv_andI Ax_s D _ _ hpredGraphD hadjoinCodedD). }
  assert (hexD : BProv Ax_s D
      (ordinalCodePredEdgeTermAt raw4 coded4)).
  {
    unfold ordinalCodePredEdgeTermAt.
    apply (BProv_exI Ax_s D _ (tVar 1)).
    cbn [subst].
    rewrite subst_ordinalCodeGraphTermAt.
    rewrite subst_hfAdjoinGraphTermAt.
    simpl.
    repeat rewrite term_subst_instTerm_rename_succ.
    exact hpairD.
  }
  unfold D, stepInner, stepBody, C, graphInner, graphBody,
    target, raw4, coded4 in *.
  rewrite !rename_ordinalCodePredEdgeTermAt.
  cbn [rename].
  repeat rewrite Term.rename_comp.
  replace (fun x : nat => S (S (S (S x)))) with
    (fun x => x + 4)
    by (apply functional_extensionality; intro x; lia).
  exact hexD.
Qed.

Lemma BProv_Ax_s_hfEmptyTermAt_zero :
  BProv Ax_s [] (hfEmptyTermAt tZero).
Proof.
  pose proof (BProv_Ax_s_HF_empty_zero_body_of_member_bot
    BProv_Ax_s_HF_empty_zero_member_bot) as hraw.
  unfold hfEmptyTermAt.
  cbn [subst] in hraw.
  simpl in hraw.
  exact hraw.
Qed.

(** The zero-stage trace and any successor-stage trace have distinct
    endpoints. *)
Lemma BProv_Ax_s_bot_of_ordinalCodeGraphTermAt_zero_succ : forall
    (P : PAOrdinalSelfSuccessorProofs) G raw coded,
  BProv Ax_s G (ordinalCodeGraphTermAt tZero coded) ->
  BProv Ax_s G (ordinalCodeGraphTermAt (tSucc raw) coded) ->
  BProv Ax_s G pBot.
Proof.
  intros P G raw coded hzero hsucc.
  pose proof (BProv_Ax_s_eq_zero_of_ordinalCodeGraphTermAt_zero
    G coded hzero) as hcodedZero.
  pose proof (BProv_Ax_s_ordinalCodePredEdgeTermAt_of_succ_graph
    G raw coded hsucc) as hedge.
  set (edgeBody :=
    pAnd
      (ordinalCodeGraphTermAt (Term.rename S raw) (tVar 0))
      (hfAdjoinGraphTermAt
        (Term.rename S coded) (tVar 0) (tVar 0))).
  set (C := edgeBody :: map (rename S) G).
  assert (hopened : BProv Ax_s C (rename S pBot)).
  {
    assert (hedgeBody : BProv Ax_s C edgeBody).
    { apply BProv_ass. unfold C. simpl. now left. }
    assert (hadjoin : BProv Ax_s C
        (hfAdjoinGraphTermAt
          (Term.rename S coded) (tVar 0) (tVar 0))).
    {
      unfold edgeBody in hedgeBody.
      exact (BProv_andE2 Ax_s C _ _ hedgeBody).
    }
    assert (hcodedZeroC : BProv Ax_s C
        (pEq (Term.rename S coded) tZero)).
    {
      pose proof (BProv_rename_succ_context_cons_of_sentences
        Ax_s sentence_ax_s G edgeBody _ hcodedZero) as hctx.
      unfold C.
      simpl in hctx.
      exact hctx.
    }
    assert (hadjoinZero : BProv Ax_s C
        (hfAdjoinGraphTermAt tZero (tVar 0) (tVar 0))).
    {
      exact (BProv_hfAdjoinGraphTermAt_of_new_eq_term
        Ax_s C (Term.rename S coded) tZero (tVar 0) (tVar 0)
        hcodedZeroC hadjoin).
    }
    assert (hempty : BProv Ax_s C (hfEmptyTermAt tZero)).
    { exact (BProv_weaken_nil Ax_s C _ BProv_Ax_s_hfEmptyTermAt_zero). }
    simpl.
    exact (BProv_Ax_s_bot_of_hfAdjoinGraphTermAt_hfEmptyTermAt
      P C (tVar 0) tZero hadjoinZero hempty).
  }
  apply (BProv_exE_of_sentences Ax_s G edgeBody pBot
    sentence_ax_s).
  - unfold ordinalCodePredEdgeTermAt in hedge.
    exact hedge.
  - unfold C in hopened.
    simpl in hopened.
    exact hopened.
Qed.

(** A zero-stage endpoint has no raw preimage other than zero. *)
Lemma BProv_Ax_s_eq_zero_of_ordinalCodeGraphTermAt_common : forall
    (P : PAOrdinalSelfSuccessorProofs) G raw coded,
  BProv Ax_s G (ordinalCodeGraphTermAt tZero coded) ->
  BProv Ax_s G (ordinalCodeGraphTermAt raw coded) ->
  BProv Ax_s G (pEq tZero raw).
Proof.
  intros P G raw coded hzero hraw.
  set (target := pEq tZero raw).
  set (succBody :=
    pEq (Term.rename S raw) (tSucc (tVar 0))).
  pose proof (BProv_Ax_s_zeroOrSuccPred_term G raw) as hcases.
  change (BProv Ax_s G
    (pOr (pEq raw tZero) (pEx succBody))) in hcases.
  assert (hzeroBranch : BProv Ax_s (pEq raw tZero :: G) target).
  {
    apply BProv_eqSym.
    apply BProv_ass. simpl. now left.
  }
  set (H := pEx succBody :: G).
  assert (hsuccBranch : BProv Ax_s H target).
  {
    set (C := succBody :: map (rename S) H).
    assert (hopened : BProv Ax_s C (rename S target)).
    {
      assert (hsuccEq : BProv Ax_s C succBody).
      { apply BProv_ass. unfold C. simpl. now left. }
      assert (lift : forall phi,
          BProv Ax_s G phi -> BProv Ax_s C (rename S phi)).
      {
        intros phi hphi.
        pose proof (BProv_context_cons Ax_s G
          (pEx succBody) _ hphi) as hinnerCtx.
        pose proof (BProv_rename_succ_context_cons_of_sentences
          Ax_s sentence_ax_s H succBody _ hinnerCtx) as hbodyCtx.
        unfold C, H.
        simpl.
        exact hbodyCtx.
      }
      pose proof (lift _ hzero) as hzeroCraw.
      assert (hzeroC : BProv Ax_s C
          (ordinalCodeGraphTermAt tZero (Term.rename S coded))).
      {
        rewrite rename_ordinalCodeGraphTermAt in hzeroCraw.
        simpl in hzeroCraw.
        exact hzeroCraw.
      }
      pose proof (lift _ hraw) as hrawCraw.
      assert (hrawC : BProv Ax_s C
          (ordinalCodeGraphTermAt
            (Term.rename S raw) (Term.rename S coded))).
      {
        rewrite rename_ordinalCodeGraphTermAt in hrawCraw.
        exact hrawCraw.
      }
      assert (hsuccC : BProv Ax_s C
          (ordinalCodeGraphTermAt
            (tSucc (tVar 0)) (Term.rename S coded))).
      {
        exact (BProv_ordinalCodeGraphTermAt_congr_raw
          Ax_s C (Term.rename S raw) (tSucc (tVar 0))
          (Term.rename S coded) hsuccEq hrawC).
      }
      pose proof (BProv_Ax_s_bot_of_ordinalCodeGraphTermAt_zero_succ
        P C (tVar 0) (Term.rename S coded) hzeroC hsuccC) as hbot.
      exact (BProv_botE Ax_s C (rename S target) hbot).
    }
    apply (BProv_exE_of_sentences Ax_s H succBody target
      sentence_ax_s).
    - apply BProv_ass. unfold H. simpl. now left.
    - unfold C in hopened. exact hopened.
  }
  exact (BProv_orE Ax_s G (pEq raw tZero) (pEx succBody) target
    hcases hzeroBranch hsuccBranch).
Qed.

(** Raw-input induction invariant: every competing raw input reaching the
    same endpoint equals the selected raw input. *)
Definition ordinalCodeInjectiveTermAt (raw : term) : formula :=
  pAll (pAll
    (pImp
      (ordinalCodeGraphTermAt
        (Term.rename S (Term.rename S raw)) (tVar 0))
      (pImp
        (ordinalCodeGraphTermAt (tVar 1) (tVar 0))
        (pEq
          (Term.rename S (Term.rename S raw))
          (tVar 1))))).

Lemma subst_ordinalCodeInjectiveTermAt : forall sigma raw,
  subst sigma (ordinalCodeInjectiveTermAt raw) =
    ordinalCodeInjectiveTermAt (Term.subst sigma raw).
Proof.
  intros sigma raw.
  unfold ordinalCodeInjectiveTermAt.
  cbn [subst].
  rewrite !subst_ordinalCodeGraphTermAt.
  rewrite !Term.subst_rename_succ_up.
  reflexivity.
Qed.

Lemma rename_ordinalCodeInjectiveTermAt : forall r raw,
  rename r (ordinalCodeInjectiveTermAt raw) =
    ordinalCodeInjectiveTermAt (Term.rename r raw).
Proof.
  intros r raw.
  rewrite <- subst_var_rename.
  rewrite subst_ordinalCodeInjectiveTermAt.
  rewrite term_subst_var_rename.
  reflexivity.
Qed.

Lemma BProv_eq_of_ordinalCodeInjectiveTermAt : forall
    G left right coded,
  BProv Ax_s G (ordinalCodeInjectiveTermAt left) ->
  BProv Ax_s G (ordinalCodeGraphTermAt left coded) ->
  BProv Ax_s G (ordinalCodeGraphTermAt right coded) ->
  BProv Ax_s G (pEq left right).
Proof.
  intros G left right coded hinjective hleft hright.
  pose proof (BProv_allE Ax_s G _ right hinjective) as hrightRaw.
  pose proof (BProv_allE Ax_s G _ coded hrightRaw) as hcodedRaw.
  assert (himp : BProv Ax_s G
      (pImp
        (ordinalCodeGraphTermAt left coded)
        (pImp
          (ordinalCodeGraphTermAt right coded)
          (pEq left right)))).
  {
    unfold ordinalCodeInjectiveTermAt in hcodedRaw.
    cbn [subst] in hcodedRaw.
    rewrite !subst_ordinalCodeGraphTermAt in hcodedRaw.
    repeat rewrite Term.subst_rename_succ_up in hcodedRaw.
    repeat rewrite term_subst_instTerm_rename_succ in hcodedRaw.
    cbn [instTerm Term.subst Term.upSubst] in hcodedRaw.
    repeat rewrite term_subst_instTerm_rename_succ in hcodedRaw.
    exact hcodedRaw.
  }
  exact (BProv_mp Ax_s G _ _
    (BProv_mp Ax_s G _ _ himp hleft) hright).
Qed.

Lemma BProv_Ax_s_ordinalCodeInjectiveTermAt_zero : forall
    (P : PAOrdinalSelfSuccessorProofs) G,
  BProv Ax_s G (ordinalCodeInjectiveTermAt tZero).
Proof.
  intros P G.
  set (Q1 := map (rename S) G).
  set (Q2 := map (rename S) Q1).
  set (leftGraph := ordinalCodeGraphTermAt tZero (tVar 0)).
  set (rightGraph := ordinalCodeGraphTermAt (tVar 1) (tVar 0)).
  set (target := pEq tZero (tVar 1)).
  set (C := leftGraph :: Q2).
  set (D := rightGraph :: C).
  assert (hbody : BProv Ax_s Q2
      (pImp leftGraph (pImp rightGraph target))).
  {
    assert (hleft : BProv Ax_s D leftGraph).
    { apply BProv_ass. unfold D, C. simpl. now right; left. }
    assert (hright : BProv Ax_s D rightGraph).
    { apply BProv_ass. unfold D. simpl. now left. }
    assert (heq : BProv Ax_s D target).
    {
      unfold leftGraph, rightGraph, target in *.
      exact (BProv_Ax_s_eq_zero_of_ordinalCodeGraphTermAt_common
        P D (tVar 1) (tVar 0) hleft hright).
    }
    assert (hrightImp : BProv Ax_s C (pImp rightGraph target)).
    { unfold D in heq. exact (BProv_impI Ax_s C _ _ heq). }
    unfold C in hrightImp.
    exact (BProv_impI Ax_s Q2 _ _ hrightImp).
  }
  assert (hinner : BProv Ax_s Q1
      (pAll (pImp
        (ordinalCodeGraphTermAt tZero (tVar 0))
        (pImp
          (ordinalCodeGraphTermAt (tVar 1) (tVar 0))
          (pEq tZero (tVar 1)))))).
  {
    pose proof (BProv_allI_of_sentences Ax_s Q1 _
      sentence_ax_s hbody) as h.
    unfold Q2, leftGraph, rightGraph, target in h.
    exact h.
  }
  pose proof (BProv_allI_of_sentences Ax_s G _
    sentence_ax_s hinner) as houter.
  unfold ordinalCodeInjectiveTermAt, Q1.
  simpl in houter.
  exact houter.
Qed.

(** Equality of two successor-stage endpoints reduces to predecessor
    equality through the common final self-adjoin edge. *)
Lemma BProv_Ax_s_eq_succ_of_common_ordinalCodeGraphs : forall
    (P : PAOrdinalSelfSuccessorProofs) G left right coded,
  BProv Ax_s G (ordinalCodeInjectiveTermAt left) ->
  BProv Ax_s G (ordinalCodeGraphTermAt (tSucc left) coded) ->
  BProv Ax_s G (ordinalCodeGraphTermAt (tSucc right) coded) ->
  BProv Ax_s G (pEq (tSucc left) (tSucc right)).
Proof.
  intros P G left right coded hinjective hleft hright.
  set (target := pEq (tSucc left) (tSucc right)).
  pose proof (BProv_Ax_s_ordinalCodePredEdgeTermAt_of_succ_graph
    G left coded hleft) as hedgeLeft.
  pose proof (BProv_Ax_s_ordinalCodePredEdgeTermAt_of_succ_graph
    G right coded hright) as hedgeRight.
  set (left1 := Term.rename S left).
  set (right1 := Term.rename S right).
  set (coded1 := Term.rename S coded).
  set (leftBody :=
    pAnd
      (ordinalCodeGraphTermAt left1 (tVar 0))
      (hfAdjoinGraphTermAt coded1 (tVar 0) (tVar 0))).
  set (C := leftBody :: map (rename S) G).
  assert (hopenedLeft : BProv Ax_s C (rename S target)).
  {
    assert (hleftBody : BProv Ax_s C leftBody).
    { apply BProv_ass. unfold C. simpl. now left. }
    assert (hleftPred : BProv Ax_s C
        (ordinalCodeGraphTermAt left1 (tVar 0))).
    {
      unfold leftBody in hleftBody.
      exact (BProv_andE1 Ax_s C _ _ hleftBody).
    }
    assert (hleftAdjoin : BProv Ax_s C
        (hfAdjoinGraphTermAt coded1 (tVar 0) (tVar 0))).
    {
      unfold leftBody in hleftBody.
      exact (BProv_andE2 Ax_s C _ _ hleftBody).
    }
    assert (hedgeRightC : BProv Ax_s C
        (ordinalCodePredEdgeTermAt right1 coded1)).
    {
      pose proof (BProv_rename_succ_context_cons_of_sentences
        Ax_s sentence_ax_s G leftBody _ hedgeRight) as hctx.
      unfold C, right1, coded1.
      rewrite rename_ordinalCodePredEdgeTermAt in hctx.
      exact hctx.
    }
    set (left2 := Term.rename S left1).
    set (right2 := Term.rename S right1).
    set (coded2 := Term.rename S coded1).
    set (rightBody :=
      pAnd
        (ordinalCodeGraphTermAt right2 (tVar 0))
        (hfAdjoinGraphTermAt coded2 (tVar 0) (tVar 0))).
    set (D := rightBody :: map (rename S) C).
    assert (hopenedRight : BProv Ax_s D
        (rename S (rename S target))).
    {
      assert (hrightBody : BProv Ax_s D rightBody).
      { apply BProv_ass. unfold D. simpl. now left. }
      assert (hrightPred : BProv Ax_s D
          (ordinalCodeGraphTermAt right2 (tVar 0))).
      {
        unfold rightBody in hrightBody.
        exact (BProv_andE1 Ax_s D _ _ hrightBody).
      }
      assert (hrightAdjoin : BProv Ax_s D
          (hfAdjoinGraphTermAt coded2 (tVar 0) (tVar 0))).
      {
        unfold rightBody in hrightBody.
        exact (BProv_andE2 Ax_s D _ _ hrightBody).
      }
      assert (hleftBodyRen : BProv Ax_s D (rename S leftBody)).
      {
        apply BProv_ass. unfold D, C. simpl. now right; left.
      }
      assert (hleftPredD : BProv Ax_s D
          (ordinalCodeGraphTermAt left2 (tVar 1))).
      {
        pose proof (BProv_andE1 Ax_s D _ _ hleftBodyRen) as h.
        change (BProv Ax_s D
          (rename S (ordinalCodeGraphTermAt left1 (tVar 0)))) in h.
        rewrite rename_ordinalCodeGraphTermAt in h.
        unfold left1, left2.
        simpl in h.
        exact h.
      }
      assert (hleftAdjoinD : BProv Ax_s D
          (hfAdjoinGraphTermAt coded2 (tVar 1) (tVar 1))).
      {
        pose proof (BProv_andE2 Ax_s D _ _ hleftBodyRen) as h.
        change (BProv Ax_s D
          (rename S
            (hfAdjoinGraphTermAt coded1 (tVar 0) (tVar 0)))) in h.
        rewrite rename_hfAdjoinGraphTermAt in h.
        unfold coded1, coded2.
        simpl in h.
        exact h.
      }
      assert (hcodedEq : BProv Ax_s D (pEq (tVar 1) (tVar 0))).
      {
        exact (BProv_Ax_s_hfAdjoinGraphTermAt_injective_self
          P D (tVar 1) (tVar 0) coded2
          hleftAdjoinD hrightAdjoin).
      }
      assert (hrightPred' : BProv Ax_s D
          (ordinalCodeGraphTermAt right2 (tVar 1))).
      {
        exact (BProv_ordinalCodeGraphTermAt_congr_coded
          Ax_s D right2 (tVar 0) (tVar 1)
          (BProv_eqSym Ax_s D _ _ hcodedEq) hrightPred).
      }
      pose proof (BProv_lift_two_contexts_of_sentences
        Ax_s sentence_ax_s G leftBody rightBody _ hinjective)
        as hinjectiveCtx.
      assert (hinjectiveD : BProv Ax_s D
          (ordinalCodeInjectiveTermAt left2)).
      {
        unfold D, C, left1, left2.
        rewrite !rename_ordinalCodeInjectiveTermAt in hinjectiveCtx.
        exact hinjectiveCtx.
      }
      assert (hrawEq : BProv Ax_s D (pEq left2 right2)).
      {
        exact (BProv_eq_of_ordinalCodeInjectiveTermAt
          D left2 right2 (tVar 1) hinjectiveD hleftPredD hrightPred').
      }
      pose proof (BProv_eq_congr_succ Ax_s D left2 right2 hrawEq)
        as hsuccEq.
      unfold target, left1, right1, left2, right2 in *.
      cbn [rename Term.rename].
      repeat rewrite Term.rename_comp.
      unfold left2, left1, right2, right1 in hsuccEq.
      repeat rewrite Term.rename_comp in hsuccEq.
      exact hsuccEq.
    }
    apply (BProv_exE_of_sentences Ax_s C rightBody (rename S target)
      sentence_ax_s).
    - unfold ordinalCodePredEdgeTermAt in hedgeRightC.
      unfold rightBody, right1, right2, coded1, coded2 in *.
      exact hedgeRightC.
    - unfold D in hopenedRight. exact hopenedRight.
  }
  apply (BProv_exE_of_sentences Ax_s G leftBody target
    sentence_ax_s).
  - unfold ordinalCodePredEdgeTermAt in hedgeLeft.
    unfold leftBody, left1, coded1 in *.
    exact hedgeLeft.
  - unfold C in hopenedLeft. exact hopenedLeft.
Qed.

Lemma BProv_Ax_s_ordinalCodeInjectiveTermAt_succ : forall
    (P : PAOrdinalSelfSuccessorProofs) G raw,
  BProv Ax_s G (ordinalCodeInjectiveTermAt raw) ->
  BProv Ax_s G (ordinalCodeInjectiveTermAt (tSucc raw)).
Proof.
  intros P G raw hinjective.
  set (Q1 := map (rename S) G).
  set (Q2 := map (rename S) Q1).
  set (raw2 := Term.rename S (Term.rename S raw)).
  set (leftGraph := ordinalCodeGraphTermAt (tSucc raw2) (tVar 0)).
  set (rightGraph := ordinalCodeGraphTermAt (tVar 1) (tVar 0)).
  set (target := pEq (tSucc raw2) (tVar 1)).
  pose proof (BProv_iterRenameSucc_of_sentences
    Ax_s sentence_ax_s 2 G _ hinjective) as hinjectiveRen2.
  cbn [iterRenameContextSucc iterRenameSucc] in hinjectiveRen2.
  assert (hinjectiveQ2 : BProv Ax_s Q2
      (ordinalCodeInjectiveTermAt raw2)).
  {
    unfold Q1, Q2, raw2.
    rewrite !rename_ordinalCodeInjectiveTermAt in hinjectiveRen2.
    exact hinjectiveRen2.
  }
  set (C := leftGraph :: Q2).
  set (D := rightGraph :: C).
  assert (hbody : BProv Ax_s Q2
      (pImp leftGraph (pImp rightGraph target))).
  {
    assert (hleft : BProv Ax_s D leftGraph).
    { apply BProv_ass. unfold D, C. simpl. now right; left. }
    assert (hright : BProv Ax_s D rightGraph).
    { apply BProv_ass. unfold D. simpl. now left. }
    pose proof (BProv_Ax_s_zeroOrSuccPred_term D (tVar 1)) as hcases.
    set (succBody :=
      pEq (Term.rename S (tVar 1)) (tSucc (tVar 0))).
    change (BProv Ax_s D
      (pOr (pEq (tVar 1) tZero) (pEx succBody))) in hcases.
    set (Z := pEq (tVar 1) tZero :: D).
    assert (hzeroBranch : BProv Ax_s Z target).
    {
      assert (heq : BProv Ax_s Z (pEq (tVar 1) tZero)).
      { apply BProv_ass. unfold Z. simpl. now left. }
      assert (hleftZ : BProv Ax_s Z leftGraph).
      { apply BProv_ass. unfold Z, D, C. simpl. now right; right; left. }
      assert (hrightZ : BProv Ax_s Z rightGraph).
      { apply BProv_ass. unfold Z, D. simpl. now right; left. }
      assert (hzeroGraph : BProv Ax_s Z
          (ordinalCodeGraphTermAt tZero (tVar 0))).
      {
        exact (BProv_ordinalCodeGraphTermAt_congr_raw
          Ax_s Z (tVar 1) tZero (tVar 0) heq hrightZ).
      }
      pose proof (BProv_Ax_s_bot_of_ordinalCodeGraphTermAt_zero_succ
        P Z raw2 (tVar 0) hzeroGraph hleftZ) as hbot.
      exact (BProv_botE Ax_s Z target hbot).
    }
    set (H := pEx succBody :: D).
    assert (hsuccBranch : BProv Ax_s H target).
    {
      set (E := succBody :: map (rename S) H).
      assert (hopened : BProv Ax_s E (rename S target)).
      {
        assert (hsuccEq : BProv Ax_s E succBody).
        { apply BProv_ass. unfold E. simpl. now left. }
        set (raw3 := Term.rename S raw2).
        assert (hleftE : BProv Ax_s E
            (ordinalCodeGraphTermAt (tSucc raw3) (tVar 1))).
        {
          assert (hraw : BProv Ax_s E (rename S leftGraph)).
          { apply BProv_ass. unfold E, H, D, C. simpl. now right; right; right; left. }
          change (BProv Ax_s E
            (rename S
              (ordinalCodeGraphTermAt (tSucc raw2) (tVar 0)))) in hraw.
          rewrite rename_ordinalCodeGraphTermAt in hraw.
          unfold raw3.
          simpl in hraw.
          exact hraw.
        }
        assert (hrightE : BProv Ax_s E
            (ordinalCodeGraphTermAt (tVar 2) (tVar 1))).
        {
          assert (hraw : BProv Ax_s E (rename S rightGraph)).
          { apply BProv_ass. unfold E, H, D. simpl. now right; right; left. }
          change (BProv Ax_s E
            (rename S
              (ordinalCodeGraphTermAt (tVar 1) (tVar 0)))) in hraw.
          rewrite rename_ordinalCodeGraphTermAt in hraw.
          simpl in hraw.
          exact hraw.
        }
        assert (hrightSuccE : BProv Ax_s E
            (ordinalCodeGraphTermAt (tSucc (tVar 0)) (tVar 1))).
        {
          exact (BProv_ordinalCodeGraphTermAt_congr_raw
            Ax_s E (tVar 2) (tSucc (tVar 0)) (tVar 1)
            hsuccEq hrightE).
        }
        assert (hinjectiveE : BProv Ax_s E
            (ordinalCodeInjectiveTermAt raw3)).
        {
          assert (hinjectiveH : BProv Ax_s H
              (ordinalCodeInjectiveTermAt raw2)).
          {
            unfold H, D, C.
            exact (BProv_context_prefix Ax_s
              [pEx succBody; rightGraph; leftGraph]
              Q2 _ hinjectiveQ2).
          }
          pose proof (BProv_rename_succ_context_cons_of_sentences
            Ax_s sentence_ax_s H succBody _ hinjectiveH) as hbodyCtx.
          unfold E, raw3.
          rewrite rename_ordinalCodeInjectiveTermAt in hbodyCtx.
          exact hbodyCtx.
        }
        pose proof (BProv_Ax_s_eq_succ_of_common_ordinalCodeGraphs
          P E raw3 (tVar 0) (tVar 1)
          hinjectiveE hleftE hrightSuccE) as hsuccRawEq.
        assert (htarget : BProv Ax_s E
            (pEq (tSucc raw3) (tVar 2))).
        {
          exact (BProv_eqTrans Ax_s E _ _ _ hsuccRawEq
            (BProv_eqSym Ax_s E _ _ hsuccEq)).
        }
        unfold target, raw3.
        cbn [rename Term.rename].
        exact htarget.
      }
      apply (BProv_exE_of_sentences Ax_s H succBody target
        sentence_ax_s).
      - apply BProv_ass. unfold H. simpl. now left.
      - unfold E in hopened. exact hopened.
    }
    assert (heq : BProv Ax_s D target).
    {
      exact (BProv_orE Ax_s D (pEq (tVar 1) tZero)
        (pEx succBody) target hcases hzeroBranch hsuccBranch).
    }
    assert (hrightImp : BProv Ax_s C (pImp rightGraph target)).
    { unfold D in heq. exact (BProv_impI Ax_s C _ _ heq). }
    unfold C in hrightImp.
    exact (BProv_impI Ax_s Q2 _ _ hrightImp).
  }
  assert (hinner : BProv Ax_s Q1
      (pAll (pImp leftGraph (pImp rightGraph target)))).
  { exact (BProv_allI_of_sentences Ax_s Q1 _ sentence_ax_s hbody). }
  pose proof (BProv_allI_of_sentences Ax_s G _
    sentence_ax_s hinner) as houter.
  unfold ordinalCodeInjectiveTermAt, Q1, raw2,
    leftGraph, rightGraph, target in *.
  cbn [rename Term.rename].
  exact houter.
Qed.

(** PA induction closes the raw-input invariant at every input. *)
Lemma BProv_Ax_s_all_ordinalCodeInjective : forall
    P : PAOrdinalSelfSuccessorProofs,
  BProv Ax_s []
    (pAll (ordinalCodeInjectiveTermAt (tVar 0))).
Proof.
  intro P.
  set (phi := ordinalCodeInjectiveTermAt (tVar 0)).
  assert (hzero : BProv Ax_s [] (subst substZero phi)).
  {
    pose proof (BProv_Ax_s_ordinalCodeInjectiveTermAt_zero P []) as hbase.
    unfold phi.
    rewrite subst_ordinalCodeInjectiveTermAt.
    simpl.
    exact hbase.
  }
  assert (hsuccImp : BProv Ax_s []
      (pImp phi (subst substSuccVar phi))).
  {
    set (C := [phi]).
    assert (hih : BProv Ax_s C phi).
    { apply BProv_ass. unfold C. simpl. now left. }
    assert (hnext : BProv Ax_s C
        (ordinalCodeInjectiveTermAt (tSucc (tVar 0)))).
    {
      exact (BProv_Ax_s_ordinalCodeInjectiveTermAt_succ
        P C (tVar 0) hih).
    }
    assert (hnextSub : BProv Ax_s C (subst substSuccVar phi)).
    {
      unfold phi.
      rewrite subst_ordinalCodeInjectiveTermAt.
      simpl.
      exact hnext.
    }
    unfold C in hnextSub.
    exact (BProv_impI Ax_s [] phi _ hnextSub).
  }
  assert (hsucc : BProv Ax_s []
      (pAll (pImp phi (subst substSuccVar phi)))).
  {
    exact (BProv_allI_of_sentences Ax_s [] _ sentence_ax_s hsuccImp).
  }
  unfold phi.
  exact (BProv_Ax_s_induction_rule []
    (ordinalCodeInjectiveTermAt (tVar 0)) hzero hsucc).
Qed.

(** Exact raw-input injectivity, conditional only on the two translated HF
    self-successor facts isolated by [PAOrdinalSelfSuccessorProofs]. *)
Definition PAOrdinalCodeGraphInjectiveProof_of_selfSuccessorProofs
    (P : PAOrdinalSelfSuccessorProofs) :
  PAOrdinalCodeGraphInjectiveProof.
Proof.
  intros G raw1 raw2 coded hgraph1 hgraph2.
  assert (hall : BProv Ax_s G
      (pAll (ordinalCodeInjectiveTermAt (tVar 0)))).
  {
    exact (BProv_weaken_nil Ax_s G _
      (BProv_Ax_s_all_ordinalCodeInjective P)).
  }
  pose proof (BProv_allE Ax_s G _ raw1 hall) as hpointRaw.
  assert (hpoint : BProv Ax_s G
      (ordinalCodeInjectiveTermAt raw1)).
  {
    rewrite subst_ordinalCodeInjectiveTermAt in hpointRaw.
    simpl in hpointRaw.
    exact hpointRaw.
  }
  exact (BProv_eq_of_ordinalCodeInjectiveTermAt
    G raw1 raw2 coded hpoint hgraph1 hgraph2).
Defined.

(** The complete ported injectivity tower.  The premise is the existing
    translated-HFFin axiom certificate; once that record is assembled, no
    further graph arithmetic is required. *)
Definition PAOrdinalCodeGraphInjectiveProof_of_TranslatedHFFinAxiomProofs
    (P : TranslatedHFFinAxiomProofs) :
  PAOrdinalCodeGraphInjectiveProof :=
  PAOrdinalCodeGraphInjectiveProof_of_selfSuccessorProofs
    (PAOrdinalSelfSuccessorProofs_of_translatedHFFin P).
