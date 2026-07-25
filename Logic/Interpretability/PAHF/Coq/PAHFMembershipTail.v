(* ===================================================================== *)
(*  PAHFMembershipTail.v                                                 *)
(*                                                                       *)
(*  Term-parametric beta-trace adapters used to prove that successor     *)
(*  membership descends through a binary head step.                      *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List.
From PAHF Require Import PAHF PAHFProofCalculus PAHFBetaShiftPrefix PAHFTranslatedHFFin
  PAHFMembershipBound PAHFMembershipBoundSucc.

Import ListNotations.
Import PA PA.Term PA.Formula.

(** Eliminate code and step witnesses after an arbitrary substitution has
    already been applied to term-parametric membership. *)
Lemma BProv_Ax_s_subst_hfMemTermAt_elim_opened_code_step :
  forall G target elem setCode sigma,
  BProv Ax_s G (subst sigma (hfMemTermAt elem setCode)) ->
  (let bitBody :=
      pAnd (oneAt 0) (betaDiv2BitAt 0 2 1 (S (S (S elem)))) in
   let tail :=
      pAnd (betaDiv2StepsThroughAt 1 0 (S (S elem))) (pEx bitBody) in
   let body :=
      pAnd
        (betaTermAtConstIdx
          (Term.rename S (Term.rename S setCode)) 1 0 0)
        tail in
   let stepEx := subst (Term.upSubst sigma) (pEx body) in
   let openedBody := subst (Term.upSubst (Term.upSubst sigma)) body in
   BProv Ax_s
     (openedBody :: map (rename S) (stepEx :: map (rename S) G))
     (rename S (rename S target))) ->
  BProv Ax_s G target.
Proof.
  intros G target elem setCode sigma hmem hopened.
  set (bitBody :=
    pAnd (oneAt 0) (betaDiv2BitAt 0 2 1 (S (S (S elem))))).
  set (tail :=
    pAnd (betaDiv2StepsThroughAt 1 0 (S (S elem))) (pEx bitBody)).
  set (body :=
    pAnd
      (betaTermAtConstIdx
        (Term.rename S (Term.rename S setCode)) 1 0 0)
      tail).
  set (stepEx := subst (Term.upSubst sigma) (pEx body)).
  set (openedBody := subst (Term.upSubst (Term.upSubst sigma)) body).
  assert (hmem' : BProv Ax_s G (pEx stepEx)).
  {
    unfold hfMemTermAt in hmem.
    unfold stepEx, openedBody, body, tail, bitBody.
    exact hmem.
  }
  unfold stepEx in hmem'.
  change (BProv Ax_s G (pEx (pEx openedBody))) in hmem'.
  apply (BProv_two_exE_of_sentences
    Ax_s sentence_ax_s G openedBody target hmem').
  exact hopened.
Qed.

(** Recover a fully term-parametric beta entry from its term-indexed wrapper. *)
Lemma BProv_Ax_s_betaTermTermAt_of_betaTermAtTermIdx :
  forall G out idxTerm code step,
  BProv Ax_s G (betaTermAtTermIdx out code step idxTerm) ->
  BProv Ax_s G
    (betaTermTermAt out (tVar code) (tVar step) idxTerm).
Proof.
  intros G out idxTerm code step hbeta.
  set (body := pAnd
    (pEq (tVar 0) (Term.rename S idxTerm))
    (betaTermAt (Term.rename S out) (S code) (S step) 0)).
  assert (hbody : BProv Ax_s (body :: map (rename S) G)
      (rename S
        (betaTermTermAt out (tVar code) (tVar step) idxTerm))).
  {
    set (C := body :: map (rename S) G).
    assert (hidxSlot : BProv Ax_s C
        (pEq (tVar 0) (Term.rename S idxTerm))).
    {
      unfold C, body.
      exact (BProv_Ax_s_betaTermAtTermIdx_opened_body_idx
        G out idxTerm code step).
    }
    assert (hraw : BProv Ax_s C
        (betaTermAt (Term.rename S out) (S code) (S step) 0)).
    {
      unfold C, body.
      exact (BProv_Ax_s_betaTermAtTermIdx_opened_body_beta
        G out idxTerm code step).
    }
    assert (hrawTerm : BProv Ax_s C
        (betaTermTermAt (Term.rename S out)
          (tVar (S code)) (tVar (S step)) (tVar 0))).
    { rewrite <- betaTermAt_eq_betaTermTermAt_var. exact hraw. }
    assert (htarget : BProv Ax_s C
        (betaTermTermAt (Term.rename S out)
          (tVar (S code)) (tVar (S step))
          (Term.rename S idxTerm))).
    {
      exact (BProv_Ax_s_betaTermTermAt_of_eq_index C
        (Term.rename S out) (tVar (S code)) (tVar (S step))
        (tVar 0) (Term.rename S idxTerm) hidxSlot hrawTerm).
    }
    unfold body, betaTermTermAt, remTermTermAt, ltTermAt,
      betaModTermTerm in *.
    simpl in *.
    repeat rewrite Term.rename_comp in *.
    exact htarget.
  }
  unfold betaTermAtTermIdx in hbeta.
  unfold body in hbody.
  exact (BProv_exE_of_sentences Ax_s G
    (pAnd
      (pEq (tVar 0) (Term.rename S idxTerm))
      (betaTermAt (Term.rename S out) (S code) (S step) 0))
    (betaTermTermAt out (tVar code) (tVar step) idxTerm)
    sentence_ax_s hbeta hbody).
Qed.

(** Eliminate a term-bounded beta-halving trace at an arbitrary index term. *)
Lemma BProv_Ax_s_betaDiv2StepsThroughTermAt_step_termIdx_of_leTerm :
  forall G code step idxTerm lastTerm,
  BProv Ax_s G
    (betaDiv2StepsThroughTermAt code step lastTerm) ->
  BProv Ax_s G (leTermAt idxTerm lastTerm) ->
  BProv Ax_s G
    (betaDiv2StepWitnessAtTermIdx code step idxTerm).
Proof.
  intros G code step idxTerm lastTerm hsteps hle.
  set (rawWitness := betaDiv2StepWitnessAt (S code) (S step) 0).
  set (body := pAnd
    (pEq (tVar 0) (Term.rename S idxTerm)) rawWitness).
  pose proof (BProv_allE Ax_s G
    (pImp (leTermAt (tVar 0) (Term.rename S lastTerm)) rawWitness)
    idxTerm hsteps) as himpRaw.
  assert (himp : BProv Ax_s G
      (pImp (leTermAt idxTerm lastTerm)
        (subst (instTerm idxTerm) rawWitness))).
  {
    unfold rawWitness, leTermAt in *.
    simpl in *.
    repeat rewrite Term.rename_comp in *.
    repeat rewrite term_subst_instTerm_rename_succ in *.
    repeat rewrite term_subst_instTerm_rename_two_succ in *.
    repeat rewrite term_subst_upSubst_instTerm_rename_two_succ in *.
    repeat rewrite term_subst_upSubst_instTerm_rename_three_succ in *.
    repeat rewrite term_subst_up_up_instTerm_rename_four_succ in *.
    exact himpRaw.
  }
  assert (hwitSubst : BProv Ax_s G
      (subst (instTerm idxTerm) rawWitness)).
  {
    exact (BProv_mp Ax_s G (leTermAt idxTerm lastTerm)
      (subst (instTerm idxTerm) rawWitness) himp hle).
  }
  assert (hidxInst : BProv Ax_s G
      (subst (instTerm idxTerm)
        (pEq (tVar 0) (Term.rename S idxTerm)))).
  {
    simpl.
    rewrite term_subst_instTerm_rename_succ.
    apply BProv_eqRefl.
  }
  assert (hbody : BProv Ax_s G (subst (instTerm idxTerm) body)).
  {
    unfold body.
    exact (BProv_andI Ax_s G _ _ hidxInst hwitSubst).
  }
  unfold betaDiv2StepWitnessAtTermIdx, body, rawWitness.
  exact (BProv_exI Ax_s G
    (pAnd
      (pEq (tVar 0) (Term.rename S idxTerm))
      (betaDiv2StepWitnessAt (S code) (S step) 0))
    idxTerm hbody).
Qed.

Lemma BProv_Ax_s_betaDiv2StepsThroughTermAt_step_succ_termIdx_of_leTerm :
  forall G code step idxTerm lastTerm,
  BProv Ax_s G
    (betaDiv2StepsThroughTermAt code step (tSucc lastTerm)) ->
  BProv Ax_s G (leTermAt idxTerm lastTerm) ->
  BProv Ax_s G
    (betaDiv2StepWitnessAtTermIdx code step (tSucc idxTerm)).
Proof.
  intros G code step idxTerm lastTerm hsteps hle.
  apply (BProv_Ax_s_betaDiv2StepsThroughTermAt_step_termIdx_of_leTerm
    G code step (tSucc idxTerm) (tSucc lastTerm) hsteps).
  exact (BProv_Ax_s_leTermAt_succ_succ G idxTerm lastTerm hle).
Qed.

(** Package explicit term-parametric beta entries and a halving equation. *)
Lemma BProv_Ax_s_betaDiv2StepWitnessTermAt_of_components :
  forall G code step idx cur next bit,
  BProv Ax_s G (betaTermTermAt cur code step idx) ->
  BProv Ax_s G (betaTermTermAt next code step (tSucc idx)) ->
  BProv Ax_s G (div2StepTermAt cur next bit) ->
  BProv Ax_s G (betaDiv2StepWitnessTermAt code step idx).
Proof.
  intros G code step idx cur next bit hcur hnext hdiv.
  set (body := pAnd
    (betaTermTermAt (tVar 2)
      (Term.rename (fun n => n + 3) code)
      (Term.rename (fun n => n + 3) step)
      (Term.rename (fun n => n + 3) idx))
    (pAnd
      (betaTermTermAt (tVar 1)
        (Term.rename (fun n => n + 3) code)
        (Term.rename (fun n => n + 3) step)
        (tSucc (Term.rename (fun n => n + 3) idx)))
      (div2StepTermAt (tVar 2) (tVar 1) (tVar 0)))).
  assert (hcurBody : BProv Ax_s G
      (subst (instTerm bit)
        (subst (Term.upSubst (instTerm next))
          (subst (Term.upSubst (Term.upSubst (instTerm cur)))
            (betaTermTermAt (tVar 2)
              (Term.rename (fun n => n + 3) code)
              (Term.rename (fun n => n + 3) step)
              (Term.rename (fun n => n + 3) idx)))))).
  {
    replace (subst (instTerm bit)
        (subst (Term.upSubst (instTerm next))
          (subst (Term.upSubst (Term.upSubst (instTerm cur)))
            (betaTermTermAt (tVar 2)
              (Term.rename (fun n => n + 3) code)
              (Term.rename (fun n => n + 3) step)
              (Term.rename (fun n => n + 3) idx)))))
      with (betaTermTermAt cur code step idx).
    - exact hcur.
    - unfold betaTermTermAt, remTermTermAt, ltTermAt,
        betaModTermTerm.
      simpl.
      normalize_subst_rename_comp.
      repeat rewrite
        (term_subst_three_instTerm_rename_add_three step cur next bit).
      repeat rewrite
        (term_subst_three_instTerm_rename_add_three code cur next bit).
      repeat rewrite
        (term_subst_three_instTerm_rename_add_three idx cur next bit).
      reflexivity.
  }
  assert (hnextBody : BProv Ax_s G
      (subst (instTerm bit)
        (subst (Term.upSubst (instTerm next))
          (subst (Term.upSubst (Term.upSubst (instTerm cur)))
            (betaTermTermAt (tVar 1)
              (Term.rename (fun n => n + 3) code)
              (Term.rename (fun n => n + 3) step)
              (tSucc (Term.rename (fun n => n + 3) idx))))))).
  {
    replace (subst (instTerm bit)
        (subst (Term.upSubst (instTerm next))
          (subst (Term.upSubst (Term.upSubst (instTerm cur)))
            (betaTermTermAt (tVar 1)
              (Term.rename (fun n => n + 3) code)
              (Term.rename (fun n => n + 3) step)
              (tSucc (Term.rename (fun n => n + 3) idx))))))
      with (betaTermTermAt next code step (tSucc idx)).
    - exact hnext.
    - unfold betaTermTermAt, remTermTermAt, ltTermAt,
        betaModTermTerm.
      simpl.
      normalize_subst_rename_comp.
      repeat rewrite
        (term_subst_three_instTerm_rename_add_three step cur next bit).
      repeat rewrite
        (term_subst_three_instTerm_rename_add_three code cur next bit).
      repeat rewrite
        (term_subst_three_instTerm_rename_add_three idx cur next bit).
      reflexivity.
  }
  assert (hdivBody : BProv Ax_s G
      (subst (instTerm bit)
        (subst (Term.upSubst (instTerm next))
          (subst (Term.upSubst (Term.upSubst (instTerm cur)))
            (div2StepTermAt (tVar 2) (tVar 1) (tVar 0)))))).
  {
    replace (subst (instTerm bit)
        (subst (Term.upSubst (instTerm next))
          (subst (Term.upSubst (Term.upSubst (instTerm cur)))
            (div2StepTermAt (tVar 2) (tVar 1) (tVar 0)))))
      with (div2StepTermAt cur next bit).
    - exact hdiv.
    - unfold div2StepTermAt, boolTermAt.
      simpl.
      repeat rewrite Term.subst_rename_succ_up.
      repeat rewrite term_rename_up_succ_rename_succ.
      normalize_subst_rename_comp.
      reflexivity.
  }
  assert (htailBody : BProv Ax_s G
      (subst (instTerm bit)
        (subst (Term.upSubst (instTerm next))
          (subst (Term.upSubst (Term.upSubst (instTerm cur)))
            (pAnd
              (betaTermTermAt (tVar 1)
                (Term.rename (fun n => n + 3) code)
                (Term.rename (fun n => n + 3) step)
                (tSucc (Term.rename (fun n => n + 3) idx)))
              (div2StepTermAt (tVar 2) (tVar 1) (tVar 0))))))).
  { simpl. exact (BProv_andI Ax_s G _ _ hnextBody hdivBody). }
  assert (hbody : BProv Ax_s G
      (subst (instTerm bit)
        (subst (Term.upSubst (instTerm next))
          (subst (Term.upSubst (Term.upSubst (instTerm cur))) body)))).
  { unfold body. simpl. exact (BProv_andI Ax_s G _ _ hcurBody htailBody). }
  assert (hbitEx : BProv Ax_s G
      (subst (instTerm next)
        (subst (Term.upSubst (instTerm cur)) (pEx body)))).
  {
    exact (BProv_exI Ax_s G
      (subst (Term.upSubst (instTerm next))
        (subst (Term.upSubst (Term.upSubst (instTerm cur))) body))
      bit hbody).
  }
  assert (hnextEx : BProv Ax_s G
      (subst (instTerm cur) (pEx (pEx body)))).
  {
    exact (BProv_exI Ax_s G
      (subst (Term.upSubst (instTerm cur)) (pEx body))
      next hbitEx).
  }
  unfold betaDiv2StepWitnessTermAt, body.
  exact (BProv_exI Ax_s G (pEx (pEx
    (pAnd
      (betaTermTermAt (tVar 2)
        (Term.rename (fun n => n + 3) code)
        (Term.rename (fun n => n + 3) step)
        (Term.rename (fun n => n + 3) idx))
      (pAnd
        (betaTermTermAt (tVar 1)
          (Term.rename (fun n => n + 3) code)
          (Term.rename (fun n => n + 3) step)
          (tSucc (Term.rename (fun n => n + 3) idx)))
        (div2StepTermAt (tVar 2) (tVar 1) (tVar 0))))))
    cur hnextEx).
Qed.

(** Copy one opened old binary step into the shifted beta trace. *)
Lemma BProv_Ax_s_betaShiftTailThroughTermAt_stepWitness_of_components :
  forall G oldCode oldStep newCode newStep lastTerm idxTerm cur next bit,
  BProv Ax_s G
    (betaShiftTailThroughTermAt oldCode oldStep
      newCode newStep (tSucc lastTerm)) ->
  BProv Ax_s G (leTermAt idxTerm lastTerm) ->
  BProv Ax_s G
    (betaTermTermAt cur (tVar oldCode) (tVar oldStep)
      (tSucc idxTerm)) ->
  BProv Ax_s G
    (betaTermTermAt next (tVar oldCode) (tVar oldStep)
      (tSucc (tSucc idxTerm))) ->
  BProv Ax_s G (div2StepTermAt cur next bit) ->
  BProv Ax_s G
    (betaDiv2StepWitnessTermAt newCode newStep idxTerm).
Proof.
  intros G oldCode oldStep newCode newStep lastTerm idxTerm
    cur next bit htail hle hcurOld hnextOld hdiv.
  assert (hleCurrent : BProv Ax_s G
      (leTermAt idxTerm (tSucc lastTerm))).
  {
    exact (BProv_Ax_s_leTermAt_trans G idxTerm lastTerm
      (tSucc lastTerm) hle
      (BProv_Ax_s_leTermAt_self_succ G lastTerm)).
  }
  assert (hcurNew : BProv Ax_s G
      (betaTermTermAt cur newCode newStep idxTerm)).
  {
    exact (BProv_Ax_s_betaShiftTailThroughTermAt_entry_of_leTerm
      G oldCode oldStep newCode newStep (tSucc lastTerm)
      idxTerm cur htail hleCurrent hcurOld).
  }
  assert (hleNext : BProv Ax_s G
      (leTermAt (tSucc idxTerm) (tSucc lastTerm))).
  { exact (BProv_Ax_s_leTermAt_succ_succ G idxTerm lastTerm hle). }
  assert (hnextNew : BProv Ax_s G
      (betaTermTermAt next newCode newStep (tSucc idxTerm))).
  {
    exact (BProv_Ax_s_betaShiftTailThroughTermAt_entry_of_leTerm
      G oldCode oldStep newCode newStep (tSucc lastTerm)
      (tSucc idxTerm) next htail hleNext hnextOld).
  }
  exact (BProv_Ax_s_betaDiv2StepWitnessTermAt_of_components
    G newCode newStep idxTerm cur next bit hcurNew hnextNew hdiv).
Qed.

(** Package explicit term-parametric entries as a beta bit read. *)
Lemma BProv_Ax_s_betaDiv2BitTermAt_of_components :
  forall G bit code step idx cur next,
  BProv Ax_s G (betaTermTermAt cur code step idx) ->
  BProv Ax_s G (betaTermTermAt next code step (tSucc idx)) ->
  BProv Ax_s G (div2StepTermAt cur next bit) ->
  BProv Ax_s G (betaDiv2BitTermAt bit code step idx).
Proof.
  intros G bit code step idx cur next hcur hnext hdiv.
  set (body := pAnd
    (betaTermTermAt (tVar 1)
      (Term.rename (fun n => n + 2) code)
      (Term.rename (fun n => n + 2) step)
      (Term.rename (fun n => n + 2) idx))
    (pAnd
      (betaTermTermAt (tVar 0)
        (Term.rename (fun n => n + 2) code)
        (Term.rename (fun n => n + 2) step)
        (tSucc (Term.rename (fun n => n + 2) idx)))
      (div2StepTermAt (tVar 1) (tVar 0)
        (Term.rename (fun n => n + 2) bit)))).
  assert (hcurBody : BProv Ax_s G
      (subst (instTerm next)
        (subst (Term.upSubst (instTerm cur))
          (betaTermTermAt (tVar 1)
            (Term.rename (fun n => n + 2) code)
            (Term.rename (fun n => n + 2) step)
            (Term.rename (fun n => n + 2) idx))))).
  {
    replace (subst (instTerm next)
        (subst (Term.upSubst (instTerm cur))
          (betaTermTermAt (tVar 1)
            (Term.rename (fun n => n + 2) code)
            (Term.rename (fun n => n + 2) step)
            (Term.rename (fun n => n + 2) idx))))
      with (betaTermTermAt cur code step idx).
    - exact hcur.
    - unfold betaTermTermAt, remTermTermAt, ltTermAt,
        betaModTermTerm.
      simpl.
      normalize_subst_rename_comp.
      repeat rewrite (term_subst_two_instTerm_rename_add_two code cur next).
      repeat rewrite (term_subst_two_instTerm_rename_add_two step cur next).
      repeat rewrite (term_subst_two_instTerm_rename_add_two idx cur next).
      repeat rewrite Term.rename_comp.
      reflexivity.
  }
  assert (hnextBody : BProv Ax_s G
      (subst (instTerm next)
        (subst (Term.upSubst (instTerm cur))
          (betaTermTermAt (tVar 0)
            (Term.rename (fun n => n + 2) code)
            (Term.rename (fun n => n + 2) step)
            (tSucc (Term.rename (fun n => n + 2) idx)))))).
  {
    replace (subst (instTerm next)
        (subst (Term.upSubst (instTerm cur))
          (betaTermTermAt (tVar 0)
            (Term.rename (fun n => n + 2) code)
            (Term.rename (fun n => n + 2) step)
            (tSucc (Term.rename (fun n => n + 2) idx)))))
      with (betaTermTermAt next code step (tSucc idx)).
    - exact hnext.
    - unfold betaTermTermAt, remTermTermAt, ltTermAt,
        betaModTermTerm.
      simpl.
      normalize_subst_rename_comp.
      repeat rewrite (term_subst_two_instTerm_rename_add_two code cur next).
      repeat rewrite (term_subst_two_instTerm_rename_add_two step cur next).
      repeat rewrite (term_subst_two_instTerm_rename_add_two idx cur next).
      repeat rewrite Term.rename_comp.
      reflexivity.
  }
  assert (hdivBody : BProv Ax_s G
      (subst (instTerm next)
        (subst (Term.upSubst (instTerm cur))
          (div2StepTermAt (tVar 1) (tVar 0)
            (Term.rename (fun n => n + 2) bit))))).
  {
    replace (subst (instTerm next)
        (subst (Term.upSubst (instTerm cur))
          (div2StepTermAt (tVar 1) (tVar 0)
            (Term.rename (fun n => n + 2) bit))))
      with (div2StepTermAt cur next bit).
    - exact hdiv.
    - unfold div2StepTermAt, boolTermAt.
      simpl.
      repeat rewrite Term.subst_rename_succ_up.
      repeat rewrite term_rename_up_succ_rename_succ.
      normalize_subst_rename_comp.
      repeat rewrite (term_subst_two_instTerm_rename_add_two bit cur next).
      repeat rewrite Term.rename_comp.
      reflexivity.
  }
  assert (htailBody : BProv Ax_s G
      (subst (instTerm next)
        (subst (Term.upSubst (instTerm cur))
          (pAnd
            (betaTermTermAt (tVar 0)
              (Term.rename (fun n => n + 2) code)
              (Term.rename (fun n => n + 2) step)
              (tSucc (Term.rename (fun n => n + 2) idx)))
            (div2StepTermAt (tVar 1) (tVar 0)
              (Term.rename (fun n => n + 2) bit)))))).
  { simpl. exact (BProv_andI Ax_s G _ _ hnextBody hdivBody). }
  assert (hbody : BProv Ax_s G
      (subst (instTerm next)
        (subst (Term.upSubst (instTerm cur)) body))).
  { unfold body. simpl. exact (BProv_andI Ax_s G _ _ hcurBody htailBody). }
  assert (hnextEx : BProv Ax_s G
      (subst (instTerm cur) (pEx body))).
  {
    exact (BProv_exI Ax_s G
      (subst (Term.upSubst (instTerm cur)) body) next hbody).
  }
  unfold betaDiv2BitTermAt, body.
  exact (BProv_exI Ax_s G (pEx
    (pAnd
      (betaTermTermAt (tVar 1)
        (Term.rename (fun n => n + 2) code)
        (Term.rename (fun n => n + 2) step)
        (Term.rename (fun n => n + 2) idx))
      (pAnd
        (betaTermTermAt (tVar 0)
          (Term.rename (fun n => n + 2) code)
          (Term.rename (fun n => n + 2) step)
          (tSucc (Term.rename (fun n => n + 2) idx)))
        (div2StepTermAt (tVar 1) (tVar 0)
          (Term.rename (fun n => n + 2) bit))))) cur hnextEx).
Qed.

Lemma BProv_Ax_s_betaShiftTailThroughTermAt_bitTerm_of_components :
  forall G oldCode oldStep newCode newStep lastTerm idxTerm
    bit cur next,
  BProv Ax_s G
    (betaShiftTailThroughTermAt oldCode oldStep
      newCode newStep (tSucc lastTerm)) ->
  BProv Ax_s G (leTermAt idxTerm lastTerm) ->
  BProv Ax_s G
    (betaTermTermAt cur (tVar oldCode) (tVar oldStep)
      (tSucc idxTerm)) ->
  BProv Ax_s G
    (betaTermTermAt next (tVar oldCode) (tVar oldStep)
      (tSucc (tSucc idxTerm))) ->
  BProv Ax_s G (div2StepTermAt cur next bit) ->
  BProv Ax_s G (betaDiv2BitTermAt bit newCode newStep idxTerm).
Proof.
  intros G oldCode oldStep newCode newStep lastTerm idxTerm
    bit cur next htail hle hcurOld hnextOld hdiv.
  assert (hleCurrent : BProv Ax_s G
      (leTermAt idxTerm (tSucc lastTerm))).
  {
    exact (BProv_Ax_s_leTermAt_trans G idxTerm lastTerm
      (tSucc lastTerm) hle
      (BProv_Ax_s_leTermAt_self_succ G lastTerm)).
  }
  assert (hcurNew : BProv Ax_s G
      (betaTermTermAt cur newCode newStep idxTerm)).
  {
    exact (BProv_Ax_s_betaShiftTailThroughTermAt_entry_of_leTerm
      G oldCode oldStep newCode newStep (tSucc lastTerm)
      idxTerm cur htail hleCurrent hcurOld).
  }
  assert (hleNext : BProv Ax_s G
      (leTermAt (tSucc idxTerm) (tSucc lastTerm))).
  { exact (BProv_Ax_s_leTermAt_succ_succ G idxTerm lastTerm hle). }
  assert (hnextNew : BProv Ax_s G
      (betaTermTermAt next newCode newStep (tSucc idxTerm))).
  {
    exact (BProv_Ax_s_betaShiftTailThroughTermAt_entry_of_leTerm
      G oldCode oldStep newCode newStep (tSucc lastTerm)
      (tSucc idxTerm) next htail hleNext hnextOld).
  }
  exact (BProv_Ax_s_betaDiv2BitTermAt_of_components
    G bit newCode newStep idxTerm cur next hcurNew hnextNew hdiv).
Qed.

Lemma rename_S_betaShiftTailThroughTermAt :
  forall oldCode oldStep newCode newStep lastTerm,
  rename S
    (betaShiftTailThroughTermAt oldCode oldStep
      newCode newStep lastTerm) =
  betaShiftTailThroughTermAt (S oldCode) (S oldStep)
    (Term.rename S newCode) (Term.rename S newStep)
    (Term.rename S lastTerm).
Proof.
  intros oldCode oldStep newCode newStep lastTerm.
  exact (PA.Formula.rename_betaShiftTailThroughTermAt
    S oldCode oldStep newCode newStep lastTerm).
Qed.

Lemma rename_S_betaDiv2StepWitnessTermAt :
  forall code step idx,
  rename S (betaDiv2StepWitnessTermAt code step idx) =
  betaDiv2StepWitnessTermAt
    (Term.rename S code) (Term.rename S step) (Term.rename S idx).
Proof.
  intros code step idx.
  unfold betaDiv2StepWitnessTermAt, betaTermTermAt,
    remTermTermAt, div2StepTermAt, boolTermAt, ltTermAt,
    betaModTermTerm.
  simpl.
  repeat rewrite term_rename_up_succ_rename_succ.
  repeat rewrite Term.rename_comp.
  assert (hidxStep : forall t,
      Term.rename
        (fun n => Fol.up (Fol.up (Fol.up (Fol.up S)))
          (S (n + 3))) t =
      Term.rename (fun n => S (S n + 3)) t).
  {
    intro t. apply Term.rename_ext. intro n.
    replace (n + 3) with (S (S (S n))) by lia.
    replace (S n + 3) with (S (S (S (S n)))) by lia.
    reflexivity.
  }
  repeat rewrite hidxStep.
  assert (hcode : forall t,
      Term.rename
        (fun n => Fol.up (Fol.up (Fol.up (Fol.up (Fol.up S))))
          (S (S (n + 3)))) t =
      Term.rename (fun n => S (S (S n + 3))) t).
  {
    intro t. apply Term.rename_ext. intro n.
    replace (n + 3) with (S (S (S n))) by lia.
    replace (S n + 3) with (S (S (S (S n)))) by lia.
    reflexivity.
  }
  repeat rewrite hcode.
  reflexivity.
Qed.

Lemma rename_S_betaDiv2BitTermAt :
  forall bit code step idx,
  rename S (betaDiv2BitTermAt bit code step idx) =
  betaDiv2BitTermAt (Term.rename S bit) (Term.rename S code)
    (Term.rename S step) (Term.rename S idx).
Proof.
  intros bit code step idx.
  unfold betaDiv2BitTermAt, betaTermTermAt, remTermTermAt,
    div2StepTermAt, boolTermAt, ltTermAt, betaModTermTerm.
  simpl.
  repeat rewrite term_rename_up_succ_rename_succ.
  repeat rewrite Term.rename_comp.
  assert (hidxStep : forall t,
      Term.rename
        (fun n => Fol.up (Fol.up (Fol.up S)) (S (n + 2))) t =
      Term.rename (fun n => S (S n + 2)) t).
  {
    intro t. apply Term.rename_ext. intro n.
    replace (n + 2) with (S (S n)) by lia.
    replace (S n + 2) with (S (S (S n))) by lia.
    reflexivity.
  }
  repeat rewrite hidxStep.
  assert (hcode : forall t,
      Term.rename
        (fun n => Fol.up (Fol.up (Fol.up (Fol.up S)))
          (S (S (n + 2)))) t =
      Term.rename (fun n => S (S (S n + 2))) t).
  {
    intro t. apply Term.rename_ext. intro n.
    replace (n + 2) with (S (S n)) by lia.
    replace (S n + 2) with (S (S (S n))) by lia.
    reflexivity.
  }
  repeat rewrite hcode.
  assert (hbit : forall t,
      Term.rename (fun n => Fol.up (Fol.up S) (n + 2)) t =
      Term.rename (fun n => S n + 2) t).
  {
    intro t. apply Term.rename_ext. intro n.
    replace (n + 2) with (S (S n)) by lia.
    replace (S n + 2) with (S (S (S n))) by lia.
    reflexivity.
  }
  repeat rewrite hbit.
  reflexivity.
Qed.

Lemma rename_S_betaDiv2BitOneTermExAt :
  forall code step idx,
  rename S (betaDiv2BitOneTermExAt code step idx) =
  betaDiv2BitOneTermExAt
    (Term.rename S code) (Term.rename S step) (Term.rename S idx).
Proof.
  intros code step idx.
  unfold betaDiv2BitOneTermExAt, oneAt, zeroAt, eqConstAt,
    betaDiv2BitTermAt, betaTermTermAt, remTermTermAt,
    div2StepTermAt, boolTermAt, ltTermAt, betaModTermTerm.
  simpl.
  repeat rewrite term_rename_up_succ_rename_succ.
  repeat rewrite Term.rename_comp.
  assert (hidxStep : forall t,
      Term.rename
        (fun n => Fol.up (Fol.up (Fol.up (Fol.up S)))
          (S (S n + 2))) t =
      Term.rename (fun n => S (S (S n) + 2)) t).
  {
    intro t. apply Term.rename_ext. intro n.
    replace (S n + 2) with (S (S (S n))) by lia.
    replace (S (S n) + 2) with (S (S (S (S n)))) by lia.
    reflexivity.
  }
  repeat rewrite hidxStep.
  assert (hcode : forall t,
      Term.rename
        (fun n => Fol.up (Fol.up (Fol.up (Fol.up (Fol.up S))))
          (S (S (S n + 2)))) t =
      Term.rename (fun n => S (S (S (S n) + 2))) t).
  {
    intro t. apply Term.rename_ext. intro n.
    replace (S n + 2) with (S (S (S n))) by lia.
    replace (S (S n) + 2) with (S (S (S (S n)))) by lia.
    reflexivity.
  }
  repeat rewrite hcode.
  reflexivity.
Qed.

Lemma rename_S_betaTermTermAt :
  forall out code step idx,
  rename S (betaTermTermAt out code step idx) =
  betaTermTermAt (Term.rename S out) (Term.rename S code)
    (Term.rename S step) (Term.rename S idx).
Proof.
  intros out code step idx.
  unfold betaTermTermAt, remTermTermAt, ltTermAt, betaModTermTerm.
  simpl.
  repeat rewrite term_rename_up_succ_rename_succ.
  repeat rewrite Term.rename_comp.
  reflexivity.
Qed.

Lemma rename_S_betaDiv2StepsThroughTermAt :
  forall code step lastTerm,
  rename S (betaDiv2StepsThroughTermAt code step lastTerm) =
  betaDiv2StepsThroughTermAt (S code) (S step)
    (Term.rename S lastTerm).
Proof.
  intros code step lastTerm.
  unfold betaDiv2StepsThroughTermAt, leTermAt,
    betaDiv2StepWitnessAt, betaAtSuccIdx, betaAt, remAt, ltAt,
    div2StepAt, boolAt, zeroAt, oneAt, eqConstAt, betaModTerm.
  simpl.
  repeat rewrite term_rename_up_succ_rename_succ.
  repeat rewrite Term.rename_comp.
  reflexivity.
Qed.

Lemma BProv_Ax_s_betaTermTermAt_of_betaAt_eq_index :
  forall G out code step idx idxTerm,
  BProv Ax_s G (betaAt out code step idx) ->
  BProv Ax_s G (pEq idxTerm (tVar idx)) ->
  BProv Ax_s G
    (betaTermTermAt (tVar out) (tVar code) (tVar step) idxTerm).
Proof.
  intros G out code step idx idxTerm hbeta hidx.
  assert (hraw : BProv Ax_s G
      (betaTermTermAt (tVar out) (tVar code) (tVar step)
        (tVar idx))).
  {
    rewrite <- betaTermAt_eq_betaTermTermAt_var.
    rewrite betaTermAt_var.
    exact hbeta.
  }
  exact (BProv_Ax_s_betaTermTermAt_of_eq_index G
    (tVar out) (tVar code) (tVar step) (tVar idx) idxTerm
    (BProv_eqSym Ax_s G idxTerm (tVar idx) hidx) hraw).
Qed.

Lemma BProv_Ax_s_betaTermTermAt_succ_of_betaTermTermAtSuccIdx_eq_term :
  forall G out code step idx idxTerm,
  BProv Ax_s G (betaTermTermAtSuccIdx out code step idx) ->
  BProv Ax_s G (pEq idxTerm (tVar idx)) ->
  BProv Ax_s G (betaTermTermAt out code step (tSucc idxTerm)).
Proof.
  intros G out code step idx idxTerm hwrap hidx.
  set (target := betaTermTermAt out code step (tSucc idxTerm)).
  set (body := pAnd
    (pEq (tVar 0) (tSucc (tVar (S idx))))
    (betaTermTermAt (Term.rename S out)
      (Term.rename S code) (Term.rename S step) (tVar 0))).
  assert (hopened : BProv Ax_s (body :: map (rename S) G)
      (rename S target)).
  {
    set (C := body :: map (rename S) G).
    assert (hbody : BProv Ax_s C body).
    { apply BProv_ass. unfold C. simpl. left. reflexivity. }
    assert (hslot : BProv Ax_s C
        (pEq (tVar 0) (tSucc (tVar (S idx))))).
    { exact (BProv_andE1 Ax_s C _ _ hbody). }
    assert (hraw : BProv Ax_s C
        (betaTermTermAt (Term.rename S out)
          (Term.rename S code) (Term.rename S step) (tVar 0))).
    { exact (BProv_andE2 Ax_s C _ _ hbody). }
    pose proof (BProv_rename_succ_context_cons_of_sentences
      Ax_s sentence_ax_s G body _ hidx) as hidxC.
    simpl in hidxC.
    assert (hsuccIdx : BProv Ax_s C
        (pEq (tSucc (Term.rename S idxTerm))
          (tSucc (tVar (S idx))))).
    { exact (BProv_eq_congr_succ Ax_s C _ _ hidxC). }
    assert (hidxForRaw : BProv Ax_s C
        (pEq (tVar 0) (tSucc (Term.rename S idxTerm)))).
    {
      exact (BProv_eqTrans Ax_s C _ _ _ hslot
        (BProv_eqSym Ax_s C _ _ hsuccIdx)).
    }
    assert (htarget : BProv Ax_s C
        (betaTermTermAt (Term.rename S out)
          (Term.rename S code) (Term.rename S step)
          (tSucc (Term.rename S idxTerm)))).
    {
      exact (BProv_Ax_s_betaTermTermAt_of_eq_index C
        (Term.rename S out) (Term.rename S code) (Term.rename S step)
        (tVar 0) (tSucc (Term.rename S idxTerm)) hidxForRaw hraw).
    }
    unfold target.
    rewrite rename_S_betaTermTermAt.
    simpl.
    exact htarget.
  }
  unfold betaTermTermAtSuccIdx in hwrap.
  unfold body in hopened.
  unfold target.
  exact (BProv_exE_of_sentences Ax_s G
    (pAnd
      (pEq (tVar 0) (tSucc (tVar (S idx))))
      (betaTermTermAt (Term.rename S out)
        (Term.rename S code) (Term.rename S step) (tVar 0)))
    (betaTermTermAt out code step (tSucc idxTerm))
    sentence_ax_s hwrap hopened).
Qed.

Lemma BProv_Ax_s_betaTermTermAt_succ_of_betaAtSuccIdx_eq_index :
  forall G out code step idx idxTerm,
  BProv Ax_s G (betaAtSuccIdx out code step idx) ->
  BProv Ax_s G (pEq idxTerm (tVar idx)) ->
  BProv Ax_s G
    (betaTermTermAt (tVar out) (tVar code) (tVar step)
      (tSucc idxTerm)).
Proof.
  intros G out code step idx idxTerm hbeta hidx.
  assert (hwrap : BProv Ax_s G
      (betaTermTermAtSuccIdx
        (tVar out) (tVar code) (tVar step) idx)).
  {
    replace (betaTermTermAtSuccIdx
        (tVar out) (tVar code) (tVar step) idx)
      with (betaAtSuccIdx out code step idx) by reflexivity.
    exact hbeta.
  }
  exact
    (BProv_Ax_s_betaTermTermAt_succ_of_betaTermTermAtSuccIdx_eq_term
      G (tVar out) (tVar code) (tVar step) idx idxTerm hwrap hidx).
Qed.

(** Convert a legacy slot-indexed three-witness step to the fully
    term-parametric form, transporting its index through a PA equality. *)
Lemma BProv_Ax_s_betaDiv2StepWitnessAt_to_termAt_of_idxEq :
  forall G code step idx idxTerm,
  BProv Ax_s G (betaDiv2StepWitnessAt code step idx) ->
  BProv Ax_s G (pEq idxTerm (tVar idx)) ->
  BProv Ax_s G
    (betaDiv2StepWitnessTermAt
      (tVar code) (tVar step) idxTerm).
Proof.
  intros G code step idx idxTerm hwitness hidx.
  set (target := betaDiv2StepWitnessTermAt
    (tVar code) (tVar step) idxTerm).
  set (body := pAnd
    (betaAt 2 (S (S (S code))) (S (S (S step)))
      (S (S (S idx))))
    (pAnd
      (betaAtSuccIdx 1 (S (S (S code))) (S (S (S step)))
        (S (S (S idx))))
      (div2StepAt 2 1 0))).
  assert (hwit : BProv Ax_s G (pEx (pEx (pEx body)))).
  { unfold betaDiv2StepWitnessAt in hwitness. unfold body. exact hwitness. }
  apply (BProv_three_exE_of_sentences
    Ax_s sentence_ax_s G body target hwit).
  set (C := body :: map (rename S)
    (pEx body :: map (rename S)
      (pEx (pEx body) :: map (rename S) G))).
  change (BProv Ax_s C (rename S (rename S (rename S target)))).
        set (idx3 := Term.rename S (Term.rename S (Term.rename S idxTerm))).
        assert (hbody : BProv Ax_s C body).
        { apply BProv_ass. unfold C. simpl. left. reflexivity. }
        assert (hcurRaw : BProv Ax_s C
            (betaAt 2 (S (S (S code))) (S (S (S step)))
              (S (S (S idx))))).
        { exact (BProv_andE1 Ax_s C _ _ hbody). }
        assert (htailBody : BProv Ax_s C
            (pAnd
              (betaAtSuccIdx 1 (S (S (S code))) (S (S (S step)))
                (S (S (S idx))))
              (div2StepAt 2 1 0))).
        { exact (BProv_andE2 Ax_s C _ _ hbody). }
        assert (hnextRaw : BProv Ax_s C
            (betaAtSuccIdx 1 (S (S (S code))) (S (S (S step)))
              (S (S (S idx))))).
        { exact (BProv_andE1 Ax_s C _ _ htailBody). }
        assert (hdivRaw : BProv Ax_s C (div2StepAt 2 1 0)).
        { exact (BProv_andE2 Ax_s C _ _ htailBody). }
        pose proof (BProv_lift_three_contexts_of_sentences
          Ax_s sentence_ax_s G
          (pEx (pEx body)) (pEx body) body _ hidx) as hidxCtx.
        simpl in hidxCtx.
        assert (hidxC : BProv Ax_s C
            (pEq idx3 (tVar (S (S (S idx)))))).
        {
          unfold C, idx3.
          exact hidxCtx.
        }
        assert (hcurTerm : BProv Ax_s C
            (betaTermTermAt (tVar 2)
              (tVar (S (S (S code)))) (tVar (S (S (S step))))
              idx3)).
        {
          exact (BProv_Ax_s_betaTermTermAt_of_betaAt_eq_index C
            2 (S (S (S code))) (S (S (S step)))
            (S (S (S idx))) idx3 hcurRaw hidxC).
        }
        assert (hnextTerm : BProv Ax_s C
            (betaTermTermAt (tVar 1)
              (tVar (S (S (S code)))) (tVar (S (S (S step))))
              (tSucc idx3))).
        {
          exact
            (BProv_Ax_s_betaTermTermAt_succ_of_betaAtSuccIdx_eq_index C
              1 (S (S (S code))) (S (S (S step)))
              (S (S (S idx))) idx3 hnextRaw hidxC).
        }
        assert (hdivTerm : BProv Ax_s C
            (div2StepTermAt (tVar 2) (tVar 1) (tVar 0))).
        {
          replace (div2StepTermAt (tVar 2) (tVar 1) (tVar 0))
            with (div2StepAt 2 1 0) by reflexivity.
          exact hdivRaw.
        }
        pose proof (BProv_Ax_s_betaDiv2StepWitnessTermAt_of_components
          C (tVar (S (S (S code)))) (tVar (S (S (S step))))
          idx3 (tVar 2) (tVar 1) (tVar 0)
          hcurTerm hnextTerm hdivTerm) as hpacked.
        unfold target.
        repeat rewrite rename_S_betaDiv2StepWitnessTermAt.
        unfold C, idx3.
        simpl.
        exact hpacked.
Qed.

(** Remove the outer term-index wrapper around a legacy step witness. *)
Lemma BProv_Ax_s_betaDiv2StepWitnessAtTermIdx_to_termAt :
  forall G code step idxTerm,
  BProv Ax_s G
    (betaDiv2StepWitnessAtTermIdx code step idxTerm) ->
  BProv Ax_s G
    (betaDiv2StepWitnessTermAt
      (tVar code) (tVar step) idxTerm).
Proof.
  intros G code step idxTerm hwitness.
  set (target := betaDiv2StepWitnessTermAt
    (tVar code) (tVar step) idxTerm).
  set (body := pAnd
    (pEq (tVar 0) (Term.rename S idxTerm))
    (betaDiv2StepWitnessAt (S code) (S step) 0)).
  assert (hopened : BProv Ax_s (body :: map (rename S) G)
      (rename S target)).
  {
    set (C := body :: map (rename S) G).
    assert (hbody : BProv Ax_s C body).
    { apply BProv_ass. unfold C. simpl. left. reflexivity. }
    assert (hidx : BProv Ax_s C
        (pEq (tVar 0) (Term.rename S idxTerm))).
    { exact (BProv_andE1 Ax_s C _ _ hbody). }
    assert (hwitRaw : BProv Ax_s C
        (betaDiv2StepWitnessAt (S code) (S step) 0)).
    { exact (BProv_andE2 Ax_s C _ _ hbody). }
    assert (hterm : BProv Ax_s C
        (betaDiv2StepWitnessTermAt
          (tVar (S code)) (tVar (S step))
          (Term.rename S idxTerm))).
    {
      exact (BProv_Ax_s_betaDiv2StepWitnessAt_to_termAt_of_idxEq C
        (S code) (S step) 0 (Term.rename S idxTerm)
        hwitRaw (BProv_eqSym Ax_s C _ _ hidx)).
    }
    unfold target.
    rewrite rename_S_betaDiv2StepWitnessTermAt.
    simpl.
    exact hterm.
  }
  unfold betaDiv2StepWitnessAtTermIdx in hwitness.
  unfold body in hopened.
  unfold target.
  exact (BProv_exE_of_sentences Ax_s G
    (pAnd
      (pEq (tVar 0) (Term.rename S idxTerm))
      (betaDiv2StepWitnessAt (S code) (S step) 0))
    (betaDiv2StepWitnessTermAt (tVar code) (tVar step) idxTerm)
    sentence_ax_s hwitness hopened).
Qed.

(** Open an old three-witness beta step and copy it one position down the
    shifted trace. *)
Lemma BProv_Ax_s_betaShiftTailThroughTermAt_stepWitness_of_oldWitness :
  forall G oldCode oldStep newCode newStep lastTerm idxTerm,
  BProv Ax_s G
    (betaShiftTailThroughTermAt oldCode oldStep
      newCode newStep (tSucc lastTerm)) ->
  BProv Ax_s G (leTermAt idxTerm lastTerm) ->
  BProv Ax_s G
    (betaDiv2StepWitnessTermAt
      (tVar oldCode) (tVar oldStep) (tSucc idxTerm)) ->
  BProv Ax_s G
    (betaDiv2StepWitnessTermAt newCode newStep idxTerm).
Proof.
  intros G oldCode oldStep newCode newStep lastTerm idxTerm
    htail hle hwitness.
  set (target :=
    betaDiv2StepWitnessTermAt newCode newStep idxTerm).
  set (body := pAnd
    (betaTermTermAt (tVar 2)
      (Term.rename S (Term.rename S (Term.rename S (tVar oldCode))))
      (Term.rename S (Term.rename S (Term.rename S (tVar oldStep))))
      (Term.rename S (Term.rename S (Term.rename S (tSucc idxTerm)))))
    (pAnd
      (betaTermTermAt (tVar 1)
        (Term.rename S (Term.rename S (Term.rename S (tVar oldCode))))
        (Term.rename S (Term.rename S (Term.rename S (tVar oldStep))))
        (tSucc
          (Term.rename S (Term.rename S (Term.rename S (tSucc idxTerm))))))
      (div2StepTermAt (tVar 2) (tVar 1) (tVar 0)))).
  assert (hwit : BProv Ax_s G (pEx (pEx (pEx body)))).
  {
    unfold betaDiv2StepWitnessTermAt in hwitness.
    unfold body.
    repeat rewrite (term_rename_add_eq_iterTermRenameSucc 3) in hwitness.
    exact hwitness.
  }
  apply (BProv_three_exE_of_sentences
    Ax_s sentence_ax_s G body target hwit).
  set (C := body :: map (rename S)
    (pEx body :: map (rename S)
      (pEx (pEx body) :: map (rename S) G))).
  change (BProv Ax_s C (rename S (rename S (rename S target)))).
        set (idx3 := Term.rename S (Term.rename S (Term.rename S idxTerm))).
        set (last3 := Term.rename S (Term.rename S (Term.rename S lastTerm))).
        set (newCode3 := Term.rename S (Term.rename S (Term.rename S newCode))).
        set (newStep3 := Term.rename S (Term.rename S (Term.rename S newStep))).
        assert (hbody : BProv Ax_s C body).
        { apply BProv_ass. unfold C. simpl. left. reflexivity. }
        assert (hcurOld : BProv Ax_s C
            (betaTermTermAt (tVar 2)
              (tVar (S (S (S oldCode)))) (tVar (S (S (S oldStep))))
              (tSucc idx3))).
        {
          pose proof (BProv_andE1 Ax_s C _ _ hbody) as hcur.
          unfold body, idx3 in *.
          simpl in *.
          exact hcur.
        }
        assert (htailBody : BProv Ax_s C
            (pAnd
              (betaTermTermAt (tVar 1)
                (tVar (S (S (S oldCode)))) (tVar (S (S (S oldStep))))
                (tSucc (tSucc idx3)))
              (div2StepTermAt (tVar 2) (tVar 1) (tVar 0)))).
        {
          pose proof (BProv_andE2 Ax_s C _ _ hbody) as hrest.
          unfold body, idx3 in *.
          simpl in *.
          exact hrest.
        }
        assert (hnextOld : BProv Ax_s C
            (betaTermTermAt (tVar 1)
              (tVar (S (S (S oldCode)))) (tVar (S (S (S oldStep))))
              (tSucc (tSucc idx3)))).
        { exact (BProv_andE1 Ax_s C _ _ htailBody). }
        assert (hdiv : BProv Ax_s C
            (div2StepTermAt (tVar 2) (tVar 1) (tVar 0))).
        { exact (BProv_andE2 Ax_s C _ _ htailBody). }
        assert (htailC : BProv Ax_s C
            (betaShiftTailThroughTermAt (S (S (S oldCode)))
              (S (S (S oldStep)))
              newCode3 newStep3 (tSucc last3))).
        {
          pose proof (BProv_lift_three_contexts_of_sentences
            Ax_s sentence_ax_s G (pEx (pEx body)) (pEx body) body
            _ htail) as h.
          repeat rewrite rename_S_betaShiftTailThroughTermAt in h.
          unfold C, newCode3, newStep3, last3.
          exact h.
        }
        assert (hleC : BProv Ax_s C (leTermAt idx3 last3)).
        {
          pose proof (BProv_lift_three_contexts_of_sentences
            Ax_s sentence_ax_s G (pEx (pEx body)) (pEx body) body
            _ hle) as h.
          repeat rewrite rename_S_leTermAt in h.
          unfold C, idx3, last3.
          exact h.
        }
        pose proof
          (BProv_Ax_s_betaShiftTailThroughTermAt_stepWitness_of_components
            C (S (S (S oldCode))) (S (S (S oldStep)))
            newCode3 newStep3
            last3 idx3 (tVar 2) (tVar 1) (tVar 0)
            htailC hleC hcurOld hnextOld hdiv) as hshifted.
        unfold target.
        repeat rewrite rename_S_betaDiv2StepWitnessTermAt.
        unfold C, idx3, newCode3, newStep3.
        exact hshifted.
Qed.

Lemma BProv_Ax_s_betaShiftTailThroughTermAt_stepWitness_of_oldSteps :
  forall G oldCode oldStep newCode newStep lastTerm idxTerm,
  BProv Ax_s G
    (betaShiftTailThroughTermAt oldCode oldStep
      newCode newStep (tSucc lastTerm)) ->
  BProv Ax_s G
    (betaDiv2StepsThroughTermAt oldCode oldStep (tSucc lastTerm)) ->
  BProv Ax_s G (leTermAt idxTerm lastTerm) ->
  BProv Ax_s G
    (betaDiv2StepWitnessTermAt newCode newStep idxTerm).
Proof.
  intros G oldCode oldStep newCode newStep lastTerm idxTerm
    htail hsteps hle.
  assert (holdSlot : BProv Ax_s G
      (betaDiv2StepWitnessAtTermIdx oldCode oldStep
        (tSucc idxTerm))).
  {
    exact
      (BProv_Ax_s_betaDiv2StepsThroughTermAt_step_succ_termIdx_of_leTerm
        G oldCode oldStep idxTerm lastTerm hsteps hle).
  }
  assert (holdTerm : BProv Ax_s G
      (betaDiv2StepWitnessTermAt
        (tVar oldCode) (tVar oldStep) (tSucc idxTerm))).
  {
    exact (BProv_Ax_s_betaDiv2StepWitnessAtTermIdx_to_termAt
      G oldCode oldStep (tSucc idxTerm) holdSlot).
  }
  exact
    (BProv_Ax_s_betaShiftTailThroughTermAt_stepWitness_of_oldWitness
      G oldCode oldStep newCode newStep lastTerm idxTerm
      htail hle holdTerm).
Qed.

(** Package all pointwise shifted steps under the new term-parametric trace
    bound. *)
Lemma BProv_Ax_s_betaShiftTailThroughTermAt_stepsThrough_of_oldSteps :
  forall G oldCode oldStep newCode newStep lastTerm,
  BProv Ax_s G
    (betaShiftTailThroughTermAt oldCode oldStep
      newCode newStep (tSucc lastTerm)) ->
  BProv Ax_s G
    (betaDiv2StepsThroughTermAt oldCode oldStep (tSucc lastTerm)) ->
  BProv Ax_s G
    (betaDiv2StepsThroughTermTermAt newCode newStep lastTerm).
Proof.
  intros G oldCode oldStep newCode newStep lastTerm htail hsteps.
  set (body := pImp
    (leTermAt (tVar 0) (Term.rename S lastTerm))
    (betaDiv2StepWitnessTermAt
      (Term.rename S newCode) (Term.rename S newStep) (tVar 0))).
  assert (hbody : BProv Ax_s (map (rename S) G) body).
  {
    set (leHyp := leTermAt (tVar 0) (Term.rename S lastTerm)).
    set (C := leHyp :: map (rename S) G).
    assert (hle : BProv Ax_s C
        (leTermAt (tVar 0) (Term.rename S lastTerm))).
    { apply BProv_ass. unfold C, leHyp. simpl. left. reflexivity. }
    pose proof (BProv_rename_succ_context_cons_of_sentences
      Ax_s sentence_ax_s G leHyp _ htail) as htailCtx.
    rewrite rename_S_betaShiftTailThroughTermAt in htailCtx.
    simpl in htailCtx.
    assert (htailC : BProv Ax_s C
        (betaShiftTailThroughTermAt (S oldCode) (S oldStep)
          (Term.rename S newCode) (Term.rename S newStep)
          (tSucc (Term.rename S lastTerm)))).
    {
      exact htailCtx.
    }
    pose proof (BProv_rename_succ_context_cons_of_sentences
      Ax_s sentence_ax_s G leHyp _ hsteps) as hstepsCtx.
    rewrite rename_S_betaDiv2StepsThroughTermAt in hstepsCtx.
    simpl in hstepsCtx.
    assert (hstepsC : BProv Ax_s C
        (betaDiv2StepsThroughTermAt (S oldCode) (S oldStep)
          (tSucc (Term.rename S lastTerm)))).
    {
      exact hstepsCtx.
    }
    assert (hpoint : BProv Ax_s C
        (betaDiv2StepWitnessTermAt
          (Term.rename S newCode) (Term.rename S newStep) (tVar 0))).
    {
      exact
        (BProv_Ax_s_betaShiftTailThroughTermAt_stepWitness_of_oldSteps
          C (S oldCode) (S oldStep)
          (Term.rename S newCode) (Term.rename S newStep)
          (Term.rename S lastTerm) (tVar 0)
          htailC hstepsC hle).
    }
    unfold body, leHyp, C.
    exact (BProv_impI Ax_s (map (rename S) G)
      (leTermAt (tVar 0) (Term.rename S lastTerm))
      (betaDiv2StepWitnessTermAt
        (Term.rename S newCode) (Term.rename S newStep) (tVar 0))
      hpoint).
  }
  unfold betaDiv2StepsThroughTermTermAt, body.
  exact (BProv_allI_of_sentences Ax_s G
    (pImp
      (leTermAt (tVar 0) (Term.rename S lastTerm))
      (betaDiv2StepWitnessTermAt
        (Term.rename S newCode) (Term.rename S newStep) (tVar 0)))
    sentence_ax_s hbody).
Qed.

(** Open an old term-parametric bit read and copy it down the shifted tail. *)
Lemma BProv_Ax_s_betaShiftTailThroughTermAt_bitTerm_of_oldBit :
  forall G oldCode oldStep newCode newStep lastTerm idxTerm bit,
  BProv Ax_s G
    (betaShiftTailThroughTermAt oldCode oldStep
      newCode newStep (tSucc lastTerm)) ->
  BProv Ax_s G (leTermAt idxTerm lastTerm) ->
  BProv Ax_s G
    (betaDiv2BitTermAt bit (tVar oldCode) (tVar oldStep)
      (tSucc idxTerm)) ->
  BProv Ax_s G (betaDiv2BitTermAt bit newCode newStep idxTerm).
Proof.
  intros G oldCode oldStep newCode newStep lastTerm idxTerm bit
    htail hle hbit.
  set (target := betaDiv2BitTermAt bit newCode newStep idxTerm).
  set (body := pAnd
    (betaTermTermAt (tVar 1)
      (Term.rename S (Term.rename S (tVar oldCode)))
      (Term.rename S (Term.rename S (tVar oldStep)))
      (Term.rename S (Term.rename S (tSucc idxTerm))))
    (pAnd
      (betaTermTermAt (tVar 0)
        (Term.rename S (Term.rename S (tVar oldCode)))
        (Term.rename S (Term.rename S (tVar oldStep)))
        (tSucc (Term.rename S (Term.rename S (tSucc idxTerm)))))
      (div2StepTermAt (tVar 1) (tVar 0)
        (Term.rename S (Term.rename S bit))))).
  assert (hbit' : BProv Ax_s G (pEx (pEx body))).
  {
    unfold betaDiv2BitTermAt in hbit.
    unfold body.
    repeat rewrite (term_rename_add_eq_iterTermRenameSucc 2) in hbit.
    exact hbit.
  }
  apply (BProv_two_exE_of_sentences
    Ax_s sentence_ax_s G body target hbit').
  set (C := body :: map (rename S)
    (pEx body :: map (rename S) G)).
  change (BProv Ax_s C (rename S (rename S target))).
      set (idx2 := Term.rename S (Term.rename S idxTerm)).
      set (last2 := Term.rename S (Term.rename S lastTerm)).
      set (bit2 := Term.rename S (Term.rename S bit)).
      set (newCode2 := Term.rename S (Term.rename S newCode)).
      set (newStep2 := Term.rename S (Term.rename S newStep)).
      assert (hbody : BProv Ax_s C body).
      { apply BProv_ass. unfold C. simpl. left. reflexivity. }
      assert (hcurOld : BProv Ax_s C
          (betaTermTermAt (tVar 1)
            (tVar (S (S oldCode))) (tVar (S (S oldStep)))
            (tSucc idx2))).
      {
        pose proof (BProv_andE1 Ax_s C _ _ hbody) as hcur.
        unfold body, idx2 in *.
        simpl in *.
        exact hcur.
      }
      assert (htailBody : BProv Ax_s C
          (pAnd
            (betaTermTermAt (tVar 0)
              (tVar (S (S oldCode))) (tVar (S (S oldStep)))
              (tSucc (tSucc idx2)))
            (div2StepTermAt (tVar 1) (tVar 0) bit2))).
      {
        pose proof (BProv_andE2 Ax_s C _ _ hbody) as hrest.
        unfold body, idx2, bit2 in *.
        simpl in *.
        exact hrest.
      }
      assert (hnextOld : BProv Ax_s C
          (betaTermTermAt (tVar 0)
            (tVar (S (S oldCode))) (tVar (S (S oldStep)))
            (tSucc (tSucc idx2)))).
      { exact (BProv_andE1 Ax_s C _ _ htailBody). }
      assert (hdiv : BProv Ax_s C
          (div2StepTermAt (tVar 1) (tVar 0) bit2)).
      { exact (BProv_andE2 Ax_s C _ _ htailBody). }
      assert (htailC : BProv Ax_s C
          (betaShiftTailThroughTermAt (S (S oldCode)) (S (S oldStep))
            newCode2 newStep2 (tSucc last2))).
      {
        pose proof (BProv_lift_two_opened_of_sentences
          Ax_s sentence_ax_s G body _ htail) as h.
        repeat rewrite rename_S_betaShiftTailThroughTermAt in h.
        unfold C, newCode2, newStep2, last2.
        exact h.
      }
      assert (hleC : BProv Ax_s C (leTermAt idx2 last2)).
      {
        pose proof (BProv_lift_two_opened_of_sentences
          Ax_s sentence_ax_s G body _ hle) as h.
        repeat rewrite rename_S_leTermAt in h.
        unfold C, idx2, last2.
        exact h.
      }
      pose proof
        (BProv_Ax_s_betaShiftTailThroughTermAt_bitTerm_of_components
          C (S (S oldCode)) (S (S oldStep)) newCode2 newStep2
          last2 idx2 bit2 (tVar 1) (tVar 0)
          htailC hleC hcurOld hnextOld hdiv) as hshifted.
      unfold target.
      repeat rewrite rename_S_betaDiv2BitTermAt.
      unfold C, idx2, bit2, newCode2, newStep2.
      exact hshifted.
Qed.

(** Preserve the final bit-1 existential while shifting a beta tail. *)
Lemma BProv_Ax_s_betaShiftTailThroughTermAt_bitOneEx_of_oldBitOneEx :
  forall G oldCode oldStep newCode newStep lastTerm idxTerm,
  BProv Ax_s G
    (betaShiftTailThroughTermAt oldCode oldStep
      newCode newStep (tSucc lastTerm)) ->
  BProv Ax_s G (leTermAt idxTerm lastTerm) ->
  BProv Ax_s G
    (betaDiv2BitOneTermExAt
      (tVar oldCode) (tVar oldStep) (tSucc idxTerm)) ->
  BProv Ax_s G (betaDiv2BitOneTermExAt newCode newStep idxTerm).
Proof.
  intros G oldCode oldStep newCode newStep lastTerm idxTerm
    htail hle hbitEx.
  set (target := betaDiv2BitOneTermExAt newCode newStep idxTerm).
  set (body := pAnd
    (oneAt 0)
    (betaDiv2BitTermAt (tVar 0)
      (Term.rename S (tVar oldCode))
      (Term.rename S (tVar oldStep))
      (Term.rename S (tSucc idxTerm)))).
  assert (hbitEx' : BProv Ax_s G (pEx body)).
  { unfold betaDiv2BitOneTermExAt in hbitEx. unfold body. exact hbitEx. }
  assert (hopened : BProv Ax_s (body :: map (rename S) G)
      (rename S target)).
  {
    set (C := body :: map (rename S) G).
    set (idx1 := Term.rename S idxTerm).
    set (last1 := Term.rename S lastTerm).
    set (newCode1 := Term.rename S newCode).
    set (newStep1 := Term.rename S newStep).
    assert (hbody : BProv Ax_s C body).
    { apply BProv_ass. unfold C. simpl. left. reflexivity. }
    assert (hone : BProv Ax_s C (oneAt 0)).
    { exact (BProv_andE1 Ax_s C _ _ hbody). }
    assert (holdBit : BProv Ax_s C
        (betaDiv2BitTermAt (tVar 0)
          (tVar (S oldCode)) (tVar (S oldStep))
          (tSucc idx1))).
    {
      pose proof (BProv_andE2 Ax_s C _ _ hbody) as hb.
      unfold body, idx1 in *.
      simpl in *.
      exact hb.
    }
    pose proof (BProv_rename_succ_context_cons_of_sentences
      Ax_s sentence_ax_s G body _ htail) as htailCtx.
    rewrite rename_S_betaShiftTailThroughTermAt in htailCtx.
    simpl in htailCtx.
    assert (htailC : BProv Ax_s C
        (betaShiftTailThroughTermAt (S oldCode) (S oldStep)
          newCode1 newStep1 (tSucc last1))).
    {
      unfold C, newCode1, newStep1, last1.
      exact htailCtx.
    }
    pose proof (BProv_rename_succ_context_cons_of_sentences
      Ax_s sentence_ax_s G body _ hle) as hleCtx.
    rewrite rename_S_leTermAt in hleCtx.
    assert (hleC : BProv Ax_s C (leTermAt idx1 last1)).
    {
      unfold C, idx1, last1.
      exact hleCtx.
    }
    assert (hnewBit : BProv Ax_s C
        (betaDiv2BitTermAt (tVar 0) newCode1 newStep1 idx1)).
    {
      exact (BProv_Ax_s_betaShiftTailThroughTermAt_bitTerm_of_oldBit
        C (S oldCode) (S oldStep) newCode1 newStep1
        last1 idx1 (tVar 0) htailC hleC holdBit).
    }
    assert (hnewBody : BProv Ax_s C
        (pAnd (oneAt 0)
          (betaDiv2BitTermAt (tVar 0) newCode1 newStep1 idx1))).
    { exact (BProv_andI Ax_s C _ _ hone hnewBit). }
    set (newBody := pAnd
      (oneAt 0)
      (betaDiv2BitTermAt (tVar 0)
        (Term.rename S newCode1)
        (Term.rename S newStep1)
        (Term.rename S idx1))).
    assert (hnewBodySubst : BProv Ax_s C
        (subst (instTerm (tVar 0)) newBody)).
    {
      replace (subst (instTerm (tVar 0)) newBody)
        with (pAnd (oneAt 0)
          (betaDiv2BitTermAt (tVar 0) newCode1 newStep1 idx1)).
      - exact hnewBody.
      - unfold newBody, betaDiv2BitTermAt, betaTermTermAt,
          remTermTermAt, div2StepTermAt, boolTermAt, ltTermAt,
          betaModTermTerm, oneAt, zeroAt, eqConstAt.
        simpl.
        assert (hrename3 : forall t,
            Term.rename (fun n => S n + 2) t =
            Term.rename (fun n => S (S (S n))) t).
        {
          intro t. apply Term.rename_ext. intro n. lia.
        }
        repeat rewrite Term.rename_comp.
        repeat rewrite hrename3.
        assert (hrename4 : forall t,
            Term.rename (fun n => S (S n + 2)) t =
            Term.rename (fun n => S (S (S (S n)))) t).
        {
          intro t. apply Term.rename_ext. intro n. lia.
        }
        repeat rewrite hrename4.
        assert (hrename5 : forall t,
            Term.rename (fun n => S (S (S n + 2))) t =
            Term.rename (fun n => S (S (S (S (S n))))) t).
        {
          intro t. apply Term.rename_ext. intro n. lia.
        }
        repeat rewrite hrename5.
        normalize_subst_rename_comp.
        reflexivity.
    }
    assert (hnewEx : BProv Ax_s C (pEx newBody)).
    { exact (BProv_exI Ax_s C newBody (tVar 0) hnewBodySubst). }
    unfold target.
    rewrite rename_S_betaDiv2BitOneTermExAt.
    unfold betaDiv2BitOneTermExAt, newBody,
      newCode1, newStep1, idx1 in *.
    exact hnewEx.
  }
  unfold target.
  exact (BProv_exE_of_sentences Ax_s G body
    (betaDiv2BitOneTermExAt newCode newStep idxTerm)
    sentence_ax_s hbitEx' hopened).
Qed.

Lemma rename_S_div2StepAt : forall value half bit,
  rename S (div2StepAt value half bit) =
  div2StepAt (S value) (S half) (S bit).
Proof.
  intros value half bit.
  unfold div2StepAt, boolAt, zeroAt, oneAt, eqConstAt.
  simpl. reflexivity.
Qed.

(** Every term-valued Boolean is below the closed numeral two. *)
Lemma BProv_Ax_s_ltTermAt_two_of_boolTermAt :
  forall G bit,
  BProv Ax_s G (boolTermAt bit) ->
  BProv Ax_s G (ltTermAt bit (Term.numeral 2)).
Proof.
  intros G bit hbool.
  unfold boolTermAt in hbool.
  apply (BProv_orE Ax_s G (pEq bit tZero) (pEq bit (tSucc tZero))
    (ltTermAt bit (Term.numeral 2)) hbool).
  - set (C := pEq bit tZero :: G).
    assert (heq : BProv Ax_s C (pEq bit tZero)).
    { apply BProv_ass. unfold C. simpl. left. reflexivity. }
    assert (hlt0 : BProv Ax_s C
        (ltTermAt tZero (Term.numeral 2))).
    {
      exact (BProv_Ax_s_ltConst_closed C 0 2 ltac:(lia)).
    }
    exact (BProv_ltTermAt_of_eq_left Ax_s C tZero bit
      (Term.numeral 2) (BProv_eqSym Ax_s C _ _ heq) hlt0).
  - set (C := pEq bit (tSucc tZero) :: G).
    assert (heq : BProv Ax_s C (pEq bit (tSucc tZero))).
    { apply BProv_ass. unfold C. simpl. left. reflexivity. }
    assert (hlt1 : BProv Ax_s C
        (ltTermAt (Term.numeral 1) (Term.numeral 2))).
    {
      exact (BProv_Ax_s_ltConst_closed C 1 2 ltac:(lia)).
    }
    replace (Term.numeral 1) with (tSucc tZero) in hlt1
      by reflexivity.
    exact (BProv_ltTermAt_of_eq_left Ax_s C (tSucc tZero) bit
      (Term.numeral 2) (BProv_eqSym Ax_s C _ _ heq) hlt1).
Qed.

(** Binary-halving quotient functionality for fully term-parametric steps. *)
Lemma BProv_Ax_s_eq_next_of_div2StepTermAt_pair :
  forall G curHidden curKnown nextHidden knownHalf bitHidden knownBit,
  BProv Ax_s G (pEq curHidden curKnown) ->
  BProv Ax_s G
    (div2StepTermAt curHidden nextHidden bitHidden) ->
  BProv Ax_s G
    (div2StepTermAt curKnown knownHalf knownBit) ->
  BProv Ax_s G (pEq nextHidden knownHalf).
Proof.
  intros G curHidden curKnown nextHidden knownHalf bitHidden knownBit
    hcurEq hhidden hknown.
  assert (hhiddenBool : BProv Ax_s G (boolTermAt bitHidden)).
  {
    unfold div2StepTermAt in hhidden.
    exact (BProv_andE1 Ax_s G _ _ hhidden).
  }
  assert (hhiddenEq : BProv Ax_s G
      (pEq curHidden
        (tAdd (tAdd nextHidden nextHidden) bitHidden))).
  {
    unfold div2StepTermAt in hhidden.
    exact (BProv_andE2 Ax_s G _ _ hhidden).
  }
  assert (hknownBool : BProv Ax_s G (boolTermAt knownBit)).
  {
    unfold div2StepTermAt in hknown.
    exact (BProv_andE1 Ax_s G _ _ hknown).
  }
  assert (hknownEq : BProv Ax_s G
      (pEq curKnown (tAdd (tAdd knownHalf knownHalf) knownBit))).
  {
    unfold div2StepTermAt in hknown.
    exact (BProv_andE2 Ax_s G _ _ hknown).
  }
  set (two := Term.numeral 2).
  assert (hhiddenLt : BProv Ax_s G (ltTermAt bitHidden two)).
  {
    unfold two.
    exact (BProv_Ax_s_ltTermAt_two_of_boolTermAt G bitHidden hhiddenBool).
  }
  assert (hknownLt : BProv Ax_s G (ltTermAt knownBit two)).
  {
    unfold two.
    exact (BProv_Ax_s_ltTermAt_two_of_boolTermAt G knownBit hknownBool).
  }
  assert (hhiddenMul : BProv Ax_s G
      (pEq (tMul nextHidden two) (tAdd nextHidden nextHidden))).
  {
    unfold two.
    exact (BProv_Ax_s_mul_two_right_terms G nextHidden).
  }
  assert (hhiddenShape : BProv Ax_s G
      (pEq (tAdd (tMul nextHidden two) bitHidden)
        (tAdd (tAdd nextHidden nextHidden) bitHidden))).
  {
    exact (BProv_eq_congr_add_left Ax_s G _ _ bitHidden hhiddenMul).
  }
  assert (hhiddenDecomp : BProv Ax_s G
      (pEq curHidden (tAdd (tMul nextHidden two) bitHidden))).
  {
    exact (BProv_eqTrans Ax_s G _ _ _ hhiddenEq
      (BProv_eqSym Ax_s G _ _ hhiddenShape)).
  }
  assert (hknownMul : BProv Ax_s G
      (pEq (tMul knownHalf two) (tAdd knownHalf knownHalf))).
  {
    unfold two.
    exact (BProv_Ax_s_mul_two_right_terms G knownHalf).
  }
  assert (hknownShape : BProv Ax_s G
      (pEq (tAdd (tMul knownHalf two) knownBit)
        (tAdd (tAdd knownHalf knownHalf) knownBit))).
  {
    exact (BProv_eq_congr_add_left Ax_s G _ _ knownBit hknownMul).
  }
  assert (hknownDecomp : BProv Ax_s G
      (pEq curKnown (tAdd (tMul knownHalf two) knownBit))).
  {
    exact (BProv_eqTrans Ax_s G _ _ _ hknownEq
      (BProv_eqSym Ax_s G _ _ hknownShape)).
  }
  assert (hknownAtHidden : BProv Ax_s G
      (pEq curHidden (tAdd (tMul knownHalf two) knownBit))).
  { exact (BProv_eqTrans Ax_s G _ _ _ hcurEq hknownDecomp). }
  exact
    (BProv_Ax_s_eq_of_bounded_remainder_decomposition_quotients_terms
      G curHidden two knownHalf nextHidden knownBit bitHidden
      hknownLt hhiddenLt hknownAtHidden hhiddenDecomp).
Qed.

(** Package a fully term-parametric beta entry in the legacy term-index
    wrapper. *)
Lemma BProv_Ax_s_betaTermAtTermIdx_of_betaTermTermAt :
  forall G out code step idxTerm,
  BProv Ax_s G
    (betaTermTermAt out (tVar code) (tVar step) idxTerm) ->
  BProv Ax_s G (betaTermAtTermIdx out code step idxTerm).
Proof.
  intros G out code step idxTerm hbeta.
  set (body := pAnd
    (pEq (tVar 0) (Term.rename S idxTerm))
    (betaTermAt (Term.rename S out) (S code) (S step) 0)).
  assert (hidx : BProv Ax_s G
      (subst (instTerm idxTerm)
        (pEq (tVar 0) (Term.rename S idxTerm)))).
  {
    simpl. rewrite term_subst_instTerm_rename_succ.
    apply BProv_eqRefl.
  }
  assert (hbetaBody : BProv Ax_s G
      (subst (instTerm idxTerm)
        (betaTermAt (Term.rename S out) (S code) (S step) 0))).
  {
    replace (subst (instTerm idxTerm)
        (betaTermAt (Term.rename S out) (S code) (S step) 0))
      with (betaTermTermAt out (tVar code) (tVar step) idxTerm).
    - exact hbeta.
    - unfold betaTermAt, betaTermTermAt, remTermAt, remTermTermAt,
        ltTermAt, betaModTerm, betaModTermTerm.
      simpl.
      normalize_subst_rename.
      reflexivity.
  }
  assert (hbody : BProv Ax_s G (subst (instTerm idxTerm) body)).
  { unfold body. exact (BProv_andI Ax_s G _ _ hidx hbetaBody). }
  unfold betaTermAtTermIdx, body.
  exact (BProv_exI Ax_s G
    (pAnd
      (pEq (tVar 0) (Term.rename S idxTerm))
      (betaTermAt (Term.rename S out) (S code) (S step) 0))
    idxTerm hbody).
Qed.

(** Propagate an explicit binary-halving quotient through a term-indexed beta
    step.  Quotient uniqueness avoids a separate even/odd case split. *)
Lemma
    BProv_Ax_s_betaDiv2StepWitnessAtTermIdx_next_termIdx_of_current_div2StepAt :
  forall G code step cur knownHalf knownBit idxTerm,
  BProv Ax_s G
    (betaTermAtTermIdx (tVar cur) code step idxTerm) ->
  BProv Ax_s G (div2StepAt cur knownHalf knownBit) ->
  BProv Ax_s G
    (betaDiv2StepWitnessAtTermIdx code step idxTerm) ->
  BProv Ax_s G
    (betaTermAtTermIdx (tVar knownHalf) code step (tSucc idxTerm)).
Proof.
  intros G code step cur knownHalf knownBit idxTerm
    hcurTerm hstep hwitness.
  assert (hcurFull : BProv Ax_s G
      (betaTermTermAt (tVar cur) (tVar code) (tVar step) idxTerm)).
  {
    exact (BProv_Ax_s_betaTermTermAt_of_betaTermAtTermIdx
      G (tVar cur) idxTerm code step hcurTerm).
  }
  assert (hwitnessFull : BProv Ax_s G
      (betaDiv2StepWitnessTermAt (tVar code) (tVar step) idxTerm)).
  {
    exact (BProv_Ax_s_betaDiv2StepWitnessAtTermIdx_to_termAt
      G code step idxTerm hwitness).
  }
  set (target := betaTermAtTermIdx
    (tVar knownHalf) code step (tSucc idxTerm)).
  set (body := pAnd
    (betaTermTermAt (tVar 2)
      (Term.rename S (Term.rename S (Term.rename S (tVar code))))
      (Term.rename S (Term.rename S (Term.rename S (tVar step))))
      (Term.rename S (Term.rename S (Term.rename S idxTerm))))
    (pAnd
      (betaTermTermAt (tVar 1)
        (Term.rename S (Term.rename S (Term.rename S (tVar code))))
        (Term.rename S (Term.rename S (Term.rename S (tVar step))))
        (tSucc (Term.rename S (Term.rename S (Term.rename S idxTerm)))))
      (div2StepTermAt (tVar 2) (tVar 1) (tVar 0)))).
  assert (hwit : BProv Ax_s G (pEx (pEx (pEx body)))).
  {
    unfold betaDiv2StepWitnessTermAt in hwitnessFull.
    unfold body.
    repeat rewrite (term_rename_add_eq_iterTermRenameSucc 3) in hwitnessFull.
    exact hwitnessFull.
  }
  apply (BProv_three_exE_of_sentences
    Ax_s sentence_ax_s G body target hwit).
  set (C := body :: map (rename S)
    (pEx body :: map (rename S)
      (pEx (pEx body) :: map (rename S) G))).
  change (BProv Ax_s C (rename S (rename S (rename S target)))).
        set (idx3 := Term.rename S (Term.rename S (Term.rename S idxTerm))).
        assert (hbody : BProv Ax_s C body).
        { apply BProv_ass. unfold C. simpl. left. reflexivity. }
        assert (hcurHidden : BProv Ax_s C
            (betaTermTermAt (tVar 2)
              (tVar (S (S (S code)))) (tVar (S (S (S step))))
              idx3)).
        {
          pose proof (BProv_andE1 Ax_s C _ _ hbody) as hcur.
          unfold body, idx3 in *.
          simpl in *.
          exact hcur.
        }
        assert (htailBody : BProv Ax_s C
            (pAnd
              (betaTermTermAt (tVar 1)
                (tVar (S (S (S code)))) (tVar (S (S (S step))))
                (tSucc idx3))
              (div2StepTermAt (tVar 2) (tVar 1) (tVar 0)))).
        {
          pose proof (BProv_andE2 Ax_s C _ _ hbody) as htail.
          unfold body, idx3 in *.
          simpl in *.
          exact htail.
        }
        assert (hnextHidden : BProv Ax_s C
            (betaTermTermAt (tVar 1)
              (tVar (S (S (S code)))) (tVar (S (S (S step))))
              (tSucc idx3))).
        { exact (BProv_andE1 Ax_s C _ _ htailBody). }
        assert (hdivHidden : BProv Ax_s C
            (div2StepTermAt (tVar 2) (tVar 1) (tVar 0))).
        { exact (BProv_andE2 Ax_s C _ _ htailBody). }
        pose proof (BProv_lift_three_contexts_of_sentences
          Ax_s sentence_ax_s G
          (pEx (pEx body)) (pEx body) body _ hcurFull) as hcurCtx.
        repeat rewrite rename_S_betaTermTermAt in hcurCtx.
        simpl in hcurCtx.
        assert (hcurKnown : BProv Ax_s C
            (betaTermTermAt (tVar (S (S (S cur))))
              (tVar (S (S (S code)))) (tVar (S (S (S step))))
              idx3)).
        {
          unfold C, idx3.
          exact hcurCtx.
        }
        assert (hcurEq : BProv Ax_s C
            (pEq (tVar 2) (tVar (S (S (S cur)))))).
        {
          exact
            (BProv_Ax_s_eq_of_betaTermTermAt_betaTermTermAt_same_index
              C (tVar (S (S (S cur)))) (tVar 2)
              (tVar (S (S (S code)))) (tVar (S (S (S step)))) idx3
              hcurKnown hcurHidden).
        }
        pose proof (BProv_lift_three_contexts_of_sentences
          Ax_s sentence_ax_s G
          (pEx (pEx body)) (pEx body) body _ hstep) as hstepCtx.
        repeat rewrite rename_S_div2StepAt in hstepCtx.
        assert (hdivKnown : BProv Ax_s C
            (div2StepTermAt
              (tVar (S (S (S cur))))
              (tVar (S (S (S knownHalf))))
              (tVar (S (S (S knownBit)))))).
        {
          unfold C.
          replace (div2StepTermAt
              (tVar (S (S (S cur))))
              (tVar (S (S (S knownHalf))))
              (tVar (S (S (S knownBit)))))
            with (div2StepAt (S (S (S cur)))
              (S (S (S knownHalf))) (S (S (S knownBit))))
            by reflexivity.
          exact hstepCtx.
        }
        assert (hnextEq : BProv Ax_s C
            (pEq (tVar 1) (tVar (S (S (S knownHalf)))))).
        {
          exact (BProv_Ax_s_eq_next_of_div2StepTermAt_pair C
            (tVar 2) (tVar (S (S (S cur))))
            (tVar 1) (tVar (S (S (S knownHalf))))
            (tVar 0) (tVar (S (S (S knownBit))))
            hcurEq hdivHidden hdivKnown).
        }
        assert (hnextKnown : BProv Ax_s C
            (betaTermTermAt (tVar (S (S (S knownHalf))))
              (tVar (S (S (S code)))) (tVar (S (S (S step))))
              (tSucc idx3))).
        {
          exact (BProv_Ax_s_betaTermTermAt_of_eq_output C
            (tVar 1) (tVar (S (S (S knownHalf))))
            (tVar (S (S (S code)))) (tVar (S (S (S step))))
            (tSucc idx3) hnextEq hnextHidden).
        }
        assert (hpacked : BProv Ax_s C
            (betaTermAtTermIdx (tVar (S (S (S knownHalf))))
              (S (S (S code))) (S (S (S step))) (tSucc idx3))).
        {
          exact (BProv_Ax_s_betaTermAtTermIdx_of_betaTermTermAt C
            (tVar (S (S (S knownHalf))))
            (S (S (S code))) (S (S (S step)))
            (tSucc idx3) hnextKnown).
        }
        unfold target.
        repeat rewrite rename_S_betaTermAtTermIdx.
        unfold C, idx3.
        simpl.
        exact hpacked.
Qed.

Lemma BProv_Ax_s_betaTermTermAt_of_subst_betaAt :
  forall G sigma out code step idx,
  BProv Ax_s G (subst sigma (betaAt out code step idx)) ->
  BProv Ax_s G
    (betaTermTermAt
      (Term.subst sigma (tVar out))
      (Term.subst sigma (tVar code))
      (Term.subst sigma (tVar step))
      (Term.subst sigma (tVar idx))).
Proof.
  intros G sigma out code step idx hbeta.
  replace (betaTermTermAt
      (Term.subst sigma (tVar out))
      (Term.subst sigma (tVar code))
      (Term.subst sigma (tVar step))
      (Term.subst sigma (tVar idx)))
    with (subst sigma (betaAt out code step idx)).
  - exact hbeta.
  - unfold betaTermTermAt, betaAt, remTermTermAt, remAt,
      ltTermAt, ltAt, betaModTermTerm, betaModTerm.
    simpl.
    repeat rewrite Term.subst_rename_succ_up.
    reflexivity.
Qed.

Lemma BProv_Ax_s_betaTermTermAt_succ_of_subst_betaAtSuccIdx :
  forall G sigma out code step idx,
  BProv Ax_s G (subst sigma (betaAtSuccIdx out code step idx)) ->
  BProv Ax_s G
    (betaTermTermAt
      (Term.subst sigma (tVar out))
      (Term.subst sigma (tVar code))
      (Term.subst sigma (tVar step))
      (tSucc (Term.subst sigma (tVar idx)))).
Proof.
  intros G sigma out code step idx hbeta.
  set (outTerm := Term.subst sigma (tVar out)).
  set (codeTerm := Term.subst sigma (tVar code)).
  set (stepTerm := Term.subst sigma (tVar step)).
  set (idxTerm := Term.subst sigma (tVar idx)).
  set (target := betaTermTermAt outTerm codeTerm stepTerm (tSucc idxTerm)).
  set (body := pAnd
    (pEq (tVar 0) (tSucc (Term.rename S idxTerm)))
    (betaTermTermAt (Term.rename S outTerm)
      (Term.rename S codeTerm) (Term.rename S stepTerm) (tVar 0))).
  assert (hbeta' : BProv Ax_s G (pEx body)).
  {
    replace (pEx body) with (subst sigma (betaAtSuccIdx out code step idx)).
    - exact hbeta.
    - unfold body, outTerm, codeTerm, stepTerm, idxTerm,
        betaAtSuccIdx, betaAt, betaTermTermAt, remTermTermAt,
        remAt, ltTermAt, ltAt, betaModTermTerm, betaModTerm.
      simpl.
      repeat rewrite Term.subst_rename_succ_up.
      repeat rewrite term_rename_up_succ_rename_succ.
      repeat rewrite Term.rename_comp.
      reflexivity.
  }
  assert (hopened : BProv Ax_s (body :: map (rename S) G)
      (rename S target)).
  {
    set (C := body :: map (rename S) G).
    assert (hbody : BProv Ax_s C body).
    { apply BProv_ass. unfold C. simpl. left. reflexivity. }
    assert (hidx : BProv Ax_s C
        (pEq (tVar 0) (tSucc (Term.rename S idxTerm)))).
    { exact (BProv_andE1 Ax_s C _ _ hbody). }
    assert (hraw : BProv Ax_s C
        (betaTermTermAt (Term.rename S outTerm)
          (Term.rename S codeTerm) (Term.rename S stepTerm) (tVar 0))).
    { exact (BProv_andE2 Ax_s C _ _ hbody). }
    assert (htarget : BProv Ax_s C
        (betaTermTermAt (Term.rename S outTerm)
          (Term.rename S codeTerm) (Term.rename S stepTerm)
          (tSucc (Term.rename S idxTerm)))).
    {
      exact (BProv_Ax_s_betaTermTermAt_of_eq_index C
        (Term.rename S outTerm) (Term.rename S codeTerm)
        (Term.rename S stepTerm) (tVar 0)
        (tSucc (Term.rename S idxTerm)) hidx hraw).
    }
    unfold target.
    rewrite rename_S_betaTermTermAt.
    simpl.
    exact htarget.
  }
  unfold target.
  exact (BProv_exE_of_sentences Ax_s G body
    (betaTermTermAt outTerm codeTerm stepTerm (tSucc idxTerm))
    sentence_ax_s hbeta' hopened).
Qed.

(** Convert a substituted legacy beta-bit read to its fully term-parametric
    form. *)
Lemma BProv_Ax_s_betaDiv2BitTermAt_of_subst_betaDiv2BitAt :
  forall G sigma bit code step idx,
  BProv Ax_s G (subst sigma (betaDiv2BitAt bit code step idx)) ->
  BProv Ax_s G
    (betaDiv2BitTermAt
      (Term.subst sigma (tVar bit))
      (Term.subst sigma (tVar code))
      (Term.subst sigma (tVar step))
      (Term.subst sigma (tVar idx))).
Proof.
  intros G sigma bit code step idx hbit.
  set (bitTerm := Term.subst sigma (tVar bit)).
  set (codeTerm := Term.subst sigma (tVar code)).
  set (stepTerm := Term.subst sigma (tVar step)).
  set (idxTerm := Term.subst sigma (tVar idx)).
  set (target := betaDiv2BitTermAt bitTerm codeTerm stepTerm idxTerm).
  set (sigma2 := Term.upSubst (Term.upSubst sigma)).
  set (body := pAnd
    (subst sigma2
      (betaAt 1 (S (S code)) (S (S step)) (S (S idx))))
    (pAnd
      (subst sigma2
        (betaAtSuccIdx 0 (S (S code)) (S (S step)) (S (S idx))))
      (subst sigma2 (div2StepAt 1 0 (S (S bit)))))).
  assert (hbit' : BProv Ax_s G (pEx (pEx body))).
  {
    unfold betaDiv2BitAt in hbit.
    unfold body, sigma2.
    exact hbit.
  }
  apply (BProv_two_exE_of_sentences
    Ax_s sentence_ax_s G body target hbit').
  set (C := body :: map (rename S)
    (pEx body :: map (rename S) G)).
  change (BProv Ax_s C (rename S (rename S target))).
      set (bit2 := Term.subst sigma2 (tVar (S (S bit)))).
      set (code2 := Term.subst sigma2 (tVar (S (S code)))).
      set (step2 := Term.subst sigma2 (tVar (S (S step)))).
      set (idx2 := Term.subst sigma2 (tVar (S (S idx)))).
      assert (hbody : BProv Ax_s C body).
      { apply BProv_ass. unfold C. simpl. left. reflexivity. }
      assert (hcurSub : BProv Ax_s C
          (subst sigma2
            (betaAt 1 (S (S code)) (S (S step)) (S (S idx))))).
      { exact (BProv_andE1 Ax_s C _ _ hbody). }
      assert (htailSub : BProv Ax_s C
          (pAnd
            (subst sigma2
              (betaAtSuccIdx 0 (S (S code)) (S (S step)) (S (S idx))))
            (subst sigma2 (div2StepAt 1 0 (S (S bit)))))).
      { exact (BProv_andE2 Ax_s C _ _ hbody). }
      assert (hnextSub : BProv Ax_s C
          (subst sigma2
            (betaAtSuccIdx 0 (S (S code)) (S (S step)) (S (S idx))))).
      { exact (BProv_andE1 Ax_s C _ _ htailSub). }
      assert (hdivSub : BProv Ax_s C
          (subst sigma2 (div2StepAt 1 0 (S (S bit))))).
      { exact (BProv_andE2 Ax_s C _ _ htailSub). }
      assert (hcur : BProv Ax_s C
          (betaTermTermAt (tVar 1) code2 step2 idx2)).
      {
        pose proof (BProv_Ax_s_betaTermTermAt_of_subst_betaAt C
          sigma2 1 (S (S code)) (S (S step)) (S (S idx))
          hcurSub) as hc.
        unfold sigma2, code2, step2, idx2 in *.
        simpl in *.
        exact hc.
      }
      assert (hnext : BProv Ax_s C
          (betaTermTermAt (tVar 0) code2 step2 (tSucc idx2))).
      {
        pose proof
          (BProv_Ax_s_betaTermTermAt_succ_of_subst_betaAtSuccIdx C
            sigma2 0 (S (S code)) (S (S step)) (S (S idx))
            hnextSub) as hn.
        unfold sigma2, code2, step2, idx2 in *.
        simpl in *.
        exact hn.
      }
      assert (hdiv : BProv Ax_s C
          (div2StepTermAt (tVar 1) (tVar 0) bit2)).
      {
        replace (div2StepTermAt (tVar 1) (tVar 0) bit2)
          with (subst sigma2 (div2StepAt 1 0 (S (S bit)))).
        - exact hdivSub.
        - unfold sigma2, bit2, div2StepTermAt, div2StepAt,
            boolTermAt, boolAt, zeroAt, oneAt, eqConstAt.
          simpl.
          repeat rewrite Term.subst_rename_succ_up.
          repeat rewrite term_rename_up_succ_rename_succ.
          repeat rewrite Term.rename_comp.
          reflexivity.
      }
      pose proof (BProv_Ax_s_betaDiv2BitTermAt_of_components
        C bit2 code2 step2 idx2 (tVar 1) (tVar 0)
        hcur hnext hdiv) as hterm.
      unfold target.
      repeat rewrite rename_S_betaDiv2BitTermAt.
      unfold C, bit2, code2, step2, idx2,
        bitTerm, codeTerm, stepTerm, idxTerm, sigma2.
      simpl.
      exact hterm.
Qed.

Lemma BProv_Ax_s_betaDiv2BitOneTermExAt_of_subst_bitOneEx :
  forall G sigma code step idx,
  BProv Ax_s G
    (subst sigma
      (pEx
        (pAnd (oneAt 0)
          (betaDiv2BitAt 0 (S code) (S step) (S idx))))) ->
  BProv Ax_s G
    (betaDiv2BitOneTermExAt
      (sigma code) (sigma step) (sigma idx)).
Proof.
  intros G sigma code step idx hbitEx.
  set (code0 := sigma code).
  set (step0 := sigma step).
  set (idx0 := sigma idx).
  set (target := betaDiv2BitOneTermExAt code0 step0 idx0).
  set (body := subst (Term.upSubst sigma)
    (pAnd (oneAt 0)
      (betaDiv2BitAt 0 (S code) (S step) (S idx)))).
  assert (hbitEx' : BProv Ax_s G (pEx body)).
  {
    unfold body.
    exact hbitEx.
  }
  assert (hopened : BProv Ax_s (body :: map (rename S) G)
      (rename S target)).
  {
    set (C := body :: map (rename S) G).
    set (code1 := Term.rename S code0).
    set (step1 := Term.rename S step0).
    set (idx1 := Term.rename S idx0).
    assert (hbody : BProv Ax_s C body).
    { apply BProv_ass. unfold C. simpl. left. reflexivity. }
    assert (hone : BProv Ax_s C (oneAt 0)).
    {
      pose proof (BProv_andE1 Ax_s C _ _ hbody) as ho.
      unfold body, oneAt, zeroAt, eqConstAt in *.
      simpl in *.
      exact ho.
    }
    assert (hlegacy : BProv Ax_s C
        (subst (Term.upSubst sigma)
          (betaDiv2BitAt 0 (S code) (S step) (S idx)))).
    {
      unfold body in hbody.
      exact (BProv_andE2 Ax_s C _ _ hbody).
    }
    assert (hterm : BProv Ax_s C
        (betaDiv2BitTermAt (tVar 0) code1 step1 idx1)).
    {
      pose proof
        (BProv_Ax_s_betaDiv2BitTermAt_of_subst_betaDiv2BitAt C
          (Term.upSubst sigma) 0 (S code) (S step) (S idx)
          hlegacy) as ht.
      unfold code1, step1, idx1, code0, step0, idx0 in *.
      simpl in *.
      repeat rewrite Term.subst_rename_succ_up in *.
      exact ht.
    }
    assert (hnewBody : BProv Ax_s C
        (pAnd (oneAt 0)
          (betaDiv2BitTermAt (tVar 0) code1 step1 idx1))).
    { exact (BProv_andI Ax_s C _ _ hone hterm). }
    set (newBody := pAnd
      (oneAt 0)
      (betaDiv2BitTermAt (tVar 0)
        (Term.rename S code1) (Term.rename S step1)
        (Term.rename S idx1))).
    assert (hnewBodySubst : BProv Ax_s C
        (subst (instTerm (tVar 0)) newBody)).
    {
      replace (subst (instTerm (tVar 0)) newBody)
        with (pAnd (oneAt 0)
          (betaDiv2BitTermAt (tVar 0) code1 step1 idx1)).
      - exact hnewBody.
      - unfold newBody, betaDiv2BitTermAt, betaTermTermAt,
          remTermTermAt, div2StepTermAt, boolTermAt, ltTermAt,
          betaModTermTerm, oneAt, zeroAt, eqConstAt.
        simpl.
        assert (hrename3 : forall t,
            Term.rename (fun n => S n + 2) t =
            Term.rename (fun n => S (S (S n))) t).
        { intro t. apply Term.rename_ext. intro n. lia. }
        repeat rewrite Term.rename_comp.
        repeat rewrite hrename3.
        assert (hrename4 : forall t,
            Term.rename (fun n => S (S n + 2)) t =
            Term.rename (fun n => S (S (S (S n)))) t).
        { intro t. apply Term.rename_ext. intro n. lia. }
        repeat rewrite hrename4.
        assert (hrename5 : forall t,
            Term.rename (fun n => S (S (S n + 2))) t =
            Term.rename (fun n => S (S (S (S (S n))))) t).
        { intro t. apply Term.rename_ext. intro n. lia. }
        repeat rewrite hrename5.
        normalize_subst_rename_comp.
        reflexivity.
    }
    assert (hnewEx : BProv Ax_s C (pEx newBody)).
    { exact (BProv_exI Ax_s C newBody (tVar 0) hnewBodySubst). }
    unfold target.
    rewrite rename_S_betaDiv2BitOneTermExAt.
    unfold betaDiv2BitOneTermExAt, newBody,
      code1, step1, idx1, code0, step0, idx0.
    exact hnewEx.
  }
  unfold target.
  exact (BProv_exE_of_sentences Ax_s G body
    (betaDiv2BitOneTermExAt code0 step0 idx0)
    sentence_ax_s hbitEx' hopened).
Qed.

(** Complete the membership-tail argument from the one remaining generic
    arithmetic service: PA-internal existence of a freshly shifted beta
    tail.  Keeping this premise explicit makes the trace plumbing usable and
    checkable independently of the fixed-step CRT construction. *)
Lemma BProv_Ax_s_hfMemAt_tail_of_succ_mem_and_div2StepAt_using_shift :
  (forall G oldCode oldStep lastTerm,
    BProv Ax_s G
      (betaShiftTailExistsTermAt oldCode oldStep lastTerm)) ->
  forall G head tailCode headBit,
  BProv Ax_s G (div2StepAt head tailCode headBit) ->
  BProv Ax_s G
    (subst (instTerm (tSucc (tVar 0))) (hfMemAt 0 (S head))) ->
  BProv Ax_s G (hfMemAt 0 tailCode).
Proof.
  intros shiftExists G head tailCode headBit hheadDiv hsuccMem.
  set (sigma := instTerm (tSucc (tVar 0))).
  set (target := hfMemAt 0 tailCode).
  assert (hsuccTerm : BProv Ax_s G
      (subst sigma (hfMemTermAt 0 (tVar (S head))))).
  {
    unfold sigma.
    rewrite hfMemTermAt_var.
    exact hsuccMem.
  }
  apply (BProv_Ax_s_subst_hfMemTermAt_elim_opened_code_step
    G target 0 (tVar (S head)) sigma hsuccTerm).
  set (bitBody := pAnd (oneAt 0) (betaDiv2BitAt 0 2 1 3)).
  set (traceTail := pAnd (betaDiv2StepsThroughAt 1 0 2) (pEx bitBody)).
  set (body := pAnd
    (betaTermAtConstIdx
      (Term.rename S (Term.rename S (tVar (S head)))) 1 0 0)
    traceTail).
  set (stepEx := subst (Term.upSubst sigma) (pEx body)).
  set (openedBody := subst (Term.upSubst (Term.upSubst sigma)) body).
  set (D := openedBody :: map (rename S)
    (stepEx :: map (rename S) G)).
  change (BProv Ax_s D (rename S (rename S target))).
  assert (hopenedBody : BProv Ax_s D openedBody).
  { apply BProv_ass. unfold D. simpl. left. reflexivity. }
  assert (hentrySub : BProv Ax_s D
      (subst (Term.upSubst (Term.upSubst sigma))
        (betaTermAtConstIdx
          (Term.rename S (Term.rename S (tVar (S head)))) 1 0 0))).
  {
    unfold openedBody, body, traceTail, bitBody in hopenedBody.
    simpl in hopenedBody.
    exact (BProv_andE1 Ax_s D _ _ hopenedBody).
  }
  assert (hentryLegacy : BProv Ax_s D
      (betaAtConstIdx (head + 2) 1 0 0)).
  {
    replace (Term.rename S (Term.rename S (tVar (S head))))
      with (tVar (head + 3)) in hentrySub
      by (simpl; f_equal; lia).
    rewrite betaTermAtConstIdx_var in hentrySub.
    replace (head + 3) with (S (S (S head))) in hentrySub by lia.
    simpl in hentrySub.
    replace (head + 2) with (S (S head)) by lia.
    exact hentrySub.
  }
  assert (hentryTermLegacy : BProv Ax_s D
      (betaTermAtConstIdx (tVar (head + 2)) 1 0 0)).
  {
    rewrite betaTermAtConstIdx_var.
    exact hentryLegacy.
  }
  assert (hentryTerm : BProv Ax_s D
      (betaTermAtTermIdx (tVar (head + 2)) 1 0 tZero)).
  {
    pose proof (BProv_Ax_s_betaTermAtTermIdx_of_betaTermAtConstIdx
      D (tVar (head + 2)) 1 0 0 hentryTermLegacy) as h.
    simpl in h.
    exact h.
  }
  assert (htraceSub : BProv Ax_s D
      (subst (Term.upSubst (Term.upSubst sigma)) traceTail)).
  {
    unfold openedBody, body in hopenedBody.
    simpl in hopenedBody.
    exact (BProv_andE2 Ax_s D _ _ hopenedBody).
  }
  assert (hstepsSub : BProv Ax_s D
      (subst (Term.upSubst (Term.upSubst sigma))
        (betaDiv2StepsThroughAt 1 0 2))).
  {
    unfold traceTail, bitBody in htraceSub.
    simpl in htraceSub.
    exact (BProv_andE1 Ax_s D _ _ htraceSub).
  }
  assert (hstepsTerm : BProv Ax_s D
      (betaDiv2StepsThroughTermAt 1 0 (tSucc (tVar 2)))).
  {
    unfold sigma, betaDiv2StepsThroughTermAt,
      betaDiv2StepsThroughAt, leAt, leTermAt,
      betaDiv2StepWitnessAt, betaAtSuccIdx, betaAt, remAt,
      div2StepAt, boolAt, ltAt, betaModTerm, zeroAt, oneAt,
      eqConstAt in hstepsSub |-.
    simpl in hstepsSub |-.
    repeat rewrite Term.rename_comp in hstepsSub.
    repeat rewrite term_rename_up_succ_rename_succ in hstepsSub.
    exact hstepsSub.
  }
  assert (hbitSub : BProv Ax_s D
      (subst (Term.upSubst (Term.upSubst sigma))
        (pEx (pAnd (oneAt 0) (betaDiv2BitAt 0 2 1 3))))).
  {
    unfold traceTail, bitBody in htraceSub.
    simpl in htraceSub.
    exact (BProv_andE2 Ax_s D _ _ htraceSub).
  }
  pose proof
    (BProv_Ax_s_betaDiv2BitOneTermExAt_of_subst_bitOneEx
      D (Term.upSubst (Term.upSubst sigma)) 1 0 2 hbitSub)
    as hbitTermRaw.
  assert (hbitTerm : BProv Ax_s D
      (betaDiv2BitOneTermExAt (tVar 1) (tVar 0)
        (tSucc (tVar 2)))).
  {
    unfold sigma in hbitTermRaw.
    simpl in hbitTermRaw.
    exact hbitTermRaw.
  }
  assert (hheadDivD : BProv Ax_s D
      (div2StepAt (head + 2) (tailCode + 2) (headBit + 2))).
  {
    pose proof (BProv_lift_two_contexts_of_sentences
      Ax_s sentence_ax_s G stepEx openedBody _ hheadDiv) as h.
    repeat rewrite rename_S_div2StepAt in h.
    replace (head + 2) with (S (S head)) by lia.
    replace (tailCode + 2) with (S (S tailCode)) by lia.
    replace (headBit + 2) with (S (S headBit)) by lia.
    unfold D.
    simpl.
    exact h.
  }
  assert (hzeroLe : BProv Ax_s D
      (leTermAt tZero (tSucc (tVar 2)))).
  { exact (BProv_Ax_s_leTermAt_zero_left D (tSucc (tVar 2))). }
  assert (hstepZero : BProv Ax_s D
      (betaDiv2StepWitnessAtTermIdx 1 0 tZero)).
  {
    exact
      (BProv_Ax_s_betaDiv2StepsThroughTermAt_step_termIdx_of_leTerm
        D 1 0 tZero (tSucc (tVar 2)) hstepsTerm hzeroLe).
  }
  assert (htailEntry : BProv Ax_s D
      (betaTermAtTermIdx (tVar (tailCode + 2)) 1 0
        (tSucc tZero))).
  {
    exact
      (BProv_Ax_s_betaDiv2StepWitnessAtTermIdx_next_termIdx_of_current_div2StepAt
        D 1 0 (head + 2) (tailCode + 2) (headBit + 2) tZero
        hentryTerm hheadDivD hstepZero).
  }
  assert (hshiftEx : BProv Ax_s D
      (betaShiftTailExistsTermAt 1 0 (tSucc (tVar 2)))).
  { exact (shiftExists D 1 0 (tSucc (tVar 2))). }
  apply (BProv_Ax_s_betaShiftTailExistsTermAt_elim_opened
    D (rename S (rename S target)) 1 0 (tSucc (tVar 2)));
    [|exact hshiftEx].
  set (E := betaShiftTailExistsTermAtOpenedContext
    1 0 (tSucc (tVar 2)) D).
  change (BProv Ax_s E
    (rename S (rename S (rename S (rename S target))))).
  assert (hshift : BProv Ax_s E
      (betaShiftTailThroughTermAt 3 2 (tVar 1) (tVar 0)
        (tSucc (tVar 4)))).
  {
    assert (hraw : BProv Ax_s E
        (betaShiftTailExistsTermAtBody 1 0 (tSucc (tVar 2)))).
    {
      apply BProv_ass.
      unfold E, betaShiftTailExistsTermAtOpenedContext.
      simpl. left. reflexivity.
    }
    unfold betaShiftTailExistsTermAtBody in hraw.
    simpl in hraw.
    exact hraw.
  }
  assert (lift2 : forall f,
      BProv Ax_s D f ->
      BProv Ax_s E (rename S (rename S f))).
  {
    intros f hf.
    set (shiftBody := betaShiftTailExistsTermAtBody
      1 0 (tSucc (tVar 2))).
    set (shiftStepEx := betaShiftTailExistsTermAtStepEx
      1 0 (tSucc (tVar 2))).
    pose proof (BProv_lift_two_contexts_of_sentences
      Ax_s sentence_ax_s D shiftStepEx shiftBody f hf) as h.
    unfold E, betaShiftTailExistsTermAtOpenedContext,
      shiftBody, shiftStepEx.
    simpl.
    exact h.
  }
  assert (htailEntryE : BProv Ax_s E
      (betaTermAtTermIdx (tVar (tailCode + 4)) 3 2
        (tSucc tZero))).
  {
    pose proof (lift2 _ htailEntry) as h.
    repeat rewrite rename_S_betaTermAtTermIdx in h.
    simpl in h.
    replace (tailCode + 4) with (S (S (tailCode + 2))) by lia.
    exact h.
  }
  assert (hstepsE : BProv Ax_s E
      (betaDiv2StepsThroughTermAt 3 2 (tSucc (tVar 4)))).
  {
    pose proof (lift2 _ hstepsTerm) as h.
    repeat rewrite rename_S_betaDiv2StepsThroughTermAt in h.
    simpl in h.
    exact h.
  }
  assert (hbitE : BProv Ax_s E
      (betaDiv2BitOneTermExAt (tVar 3) (tVar 2)
        (tSucc (tVar 4)))).
  {
    pose proof (lift2 _ hbitTerm) as h.
    repeat rewrite rename_S_betaDiv2BitOneTermExAt in h.
    simpl in h.
    exact h.
  }
  assert (htailEntryRaw : BProv Ax_s E
      (betaTermTermAt (tVar (tailCode + 4))
        (tVar 3) (tVar 2) (tSucc tZero))).
  {
    exact (BProv_Ax_s_betaTermTermAt_of_betaTermAtTermIdx
      E (tVar (tailCode + 4)) (tSucc tZero) 3 2 htailEntryE).
  }
  assert (hnewEntry : BProv Ax_s E
      (betaTermTermAt (tVar (tailCode + 4))
        (tVar 1) (tVar 0) tZero)).
  {
    exact (BProv_Ax_s_betaShiftTailThroughTermAt_entry_of_leTerm
      E 3 2 (tVar 1) (tVar 0) (tSucc (tVar 4))
      tZero (tVar (tailCode + 4)) hshift
      (BProv_Ax_s_leTermAt_zero_left E (tSucc (tVar 4)))
      htailEntryRaw).
  }
  assert (hnewSteps : BProv Ax_s E
      (betaDiv2StepsThroughTermTermAt
        (tVar 1) (tVar 0) (tVar 4))).
  {
    exact
      (BProv_Ax_s_betaShiftTailThroughTermAt_stepsThrough_of_oldSteps
        E 3 2 (tVar 1) (tVar 0) (tVar 4) hshift hstepsE).
  }
  assert (hnewBit : BProv Ax_s E
      (betaDiv2BitOneTermExAt
        (tVar 1) (tVar 0) (tVar 4))).
  {
    exact
      (BProv_Ax_s_betaShiftTailThroughTermAt_bitOneEx_of_oldBitOneEx
        E 3 2 (tVar 1) (tVar 0) (tVar 4) (tVar 4)
        hshift (BProv_Ax_s_leTermAt_refl E (tVar 4)) hbitE).
  }
  assert (hentryComponent : BProv Ax_s E
      (subst (instTerm (tVar 0))
        (subst (Term.upSubst (instTerm (tVar 1)))
          (betaTermAtConstIdx
            (Term.rename (fun n => n + 2) (tVar (tailCode + 4)))
            1 0 0)))).
  {
    exact (BProv_Ax_s_hfMemTermAt_entry_of_betaTermTermAt_zero
      E (tailCode + 4) (tVar 1) (tVar 0) hnewEntry).
  }
  assert (hstepsComponent : BProv Ax_s E
      (subst (instTerm (tVar 0))
        (subst (Term.upSubst (instTerm (tVar 1)))
          (betaDiv2StepsThroughAt 1 0 (4 + 2))))).
  {
    exact (BProv_Ax_s_hfMemTermAt_slot4_steps_of_term_trace
      E (tVar 1) (tVar 0) hnewSteps).
  }
  assert (hbitComponent : BProv Ax_s E
      (subst (instTerm (tVar 0))
        (subst (Term.upSubst (instTerm (tVar 1)))
          (pEx (pAnd (oneAt 0)
            (betaDiv2BitAt 0 2 1 (4 + 3))))))).
  {
    exact
      (BProv_Ax_s_hfMemTermAt_slot4_bitEx_of_betaDiv2BitOneTermExAt
        E (tVar 1) (tVar 0) hnewBit).
  }
  assert (hpacked : BProv Ax_s E
      (hfMemTermAt 4 (tVar (tailCode + 4)))).
  {
    pose proof (BProv_Ax_s_subst_hfMemTermAt_of_components
      E 4 (tVar (tailCode + 4)) (tVar 1) (tVar 0)
      (fun n => tVar n)) as pack.
    repeat rewrite subst_id in pack.
    exact (pack hentryComponent hstepsComponent hbitComponent).
  }
  rewrite hfMemTermAt_var in hpacked.
  repeat rewrite rename_hfMemAt.
  unfold target.
  replace (tailCode + 4) with (S (S (S (S tailCode)))) in hpacked
    by lia.
  exact hpacked.
Qed.

Definition hfMembershipTailStep_of_shift
    (shiftExists : forall G oldCode oldStep lastTerm,
      BProv Ax_s G
        (betaShiftTailExistsTermAt oldCode oldStep lastTerm))
    : HFMembershipTailStep :=
  BProv_Ax_s_hfMemAt_tail_of_succ_mem_and_div2StepAt_using_shift
    shiftExists.

Lemma BProv_Ax_s_all_hfMembersBelowAt_using_shift :
  forall (shiftExists : forall G oldCode oldStep lastTerm,
    BProv Ax_s G
      (betaShiftTailExistsTermAt oldCode oldStep lastTerm)),
  BProv Ax_s [] (pAll (hfMembersBelowAt 0)).
Proof.
  intro shiftExists.
  exact (BProv_Ax_s_all_hfMembersBelowAt_of_tail
    (hfMembershipTailStep_of_shift shiftExists)).
Qed.

Lemma BProv_Ax_s_translated_HF_induction_using_shift :
  forall (shiftExists : forall G oldCode oldStep lastTerm,
      BProv Ax_s G
        (betaShiftTailExistsTermAt oldCode oldStep lastTerm)) phi,
  BProv Ax_s []
    (translateHFFormula (Fol.seal (HF_induction_form phi))).
Proof.
  intros shiftExists phi.
  exact (BProv_Ax_s_translated_HF_induction_of_tail
    (hfMembershipTailStep_of_shift shiftExists) phi).
Qed.

(** The CRT shifted-prefix construction discharges the sole premise of the
    conditional trace proof. *)
Lemma BProv_Ax_s_hfMemAt_tail_of_succ_mem_and_div2StepAt :
  forall G head tailCode headBit,
  BProv Ax_s G (div2StepAt head tailCode headBit) ->
  BProv Ax_s G
    (subst (instTerm (tSucc (tVar 0))) (hfMemAt 0 (S head))) ->
  BProv Ax_s G (hfMemAt 0 tailCode).
Proof.
  exact
    (BProv_Ax_s_hfMemAt_tail_of_succ_mem_and_div2StepAt_using_shift
      BProv_Ax_s_betaShiftTailExistsTermAt).
Qed.

Definition hfMembershipTailStep : HFMembershipTailStep :=
  BProv_Ax_s_hfMemAt_tail_of_succ_mem_and_div2StepAt.

Lemma BProv_Ax_s_all_hfMembersBelowAt :
  BProv Ax_s [] (pAll (hfMembersBelowAt 0)).
Proof.
  exact (BProv_Ax_s_all_hfMembersBelowAt_of_tail
    hfMembershipTailStep).
Qed.

Lemma BProv_Ax_s_translated_HF_induction :
  forall phi,
  BProv Ax_s []
    (translateHFFormula (Fol.seal (HF_induction_form phi))).
Proof.
  exact (BProv_Ax_s_translated_HF_induction_of_tail
    hfMembershipTailStep).
Qed.
