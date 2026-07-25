(* ===================================================================== *)
(*  PAHFMembershipBoundSucc.v                                            *)
(*                                                                       *)
(*  The hard successor-code arithmetic for Ackermann membership bounds.  *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List.
From PAHF Require Import PAHF PAHFTranslatedHFFin PAHFMembershipBound.

Import ListNotations.
Import PA PA.Term PA.Formula.

(** If a binary head is the successor of [pred], its extracted half is at
    most [pred].  This proof needs only the defining step equation: no parity
    split is required. *)
Lemma BProv_Ax_s_leTermAt_half_of_div2StepAt_eq_succ :
  forall G head half bit pred,
  BProv Ax_s G (div2StepAt head half bit) ->
  BProv Ax_s G (pEq (tVar head) (tSucc pred)) ->
  BProv Ax_s G (leTermAt (tVar half) pred).
Proof.
  intros G head half bit pred hstep hhead.
  set (halfTerm := tVar half).
  set (doubleHalf := tAdd halfTerm halfTerm).
  set (target := leTermAt halfTerm pred).
  assert (hcmp : BProv Ax_s G
      (pOr target (ltTermAt pred halfTerm))).
  {
    unfold target, halfTerm.
    exact (BProv_Ax_s_leTermAt_or_gtTermAt G (tVar half) pred).
  }
  assert (hleBranch : BProv Ax_s (target :: G) target).
  { apply BProv_ass_head. }
  assert (hgtBranch : BProv Ax_s (ltTermAt pred halfTerm :: G) target).
  {
    set (C := ltTermAt pred halfTerm :: G).
    assert (hlt : BProv Ax_s C (ltTermAt pred halfTerm)).
    { apply BProv_ass. unfold C. simpl. left. reflexivity. }
    assert (hsuccLe : BProv Ax_s C
        (leTermAt (tSucc pred) halfTerm)).
    {
      apply (BProv_Ax_s_leTermAt_of_ltTermAt_succ_right
        C (tSucc pred) halfTerm).
      exact (BProv_Ax_s_ltTermAt_succ_succ C pred halfTerm hlt).
    }
    assert (hstepC : BProv Ax_s C (div2StepAt head half bit)).
    { unfold C. apply BProv_context_cons. exact hstep. }
    assert (hheadC : BProv Ax_s C
        (pEq (tVar head) (tSucc pred))).
    { unfold C. apply BProv_context_cons. exact hhead. }
    assert (hstepEq : BProv Ax_s C
        (pEq (tVar head) (tAdd doubleHalf (tVar bit)))).
    {
      pose proof (BProv_andE2 Ax_s C _ _ hstepC) as heq.
      unfold div2StepAt in heq.
      unfold doubleHalf, halfTerm.
      exact heq.
    }
    assert (hhalfLeDouble : BProv Ax_s C
        (leTermAt halfTerm doubleHalf)).
    {
      apply (BProv_Ax_s_leTermAt_of_eq_add_right_terms
        C halfTerm doubleHalf halfTerm).
      unfold doubleHalf.
      apply BProv_eqRefl.
    }
    assert (hdoubleLeHead : BProv Ax_s C
        (leTermAt doubleHalf (tVar head))).
    {
      exact (BProv_Ax_s_leTermAt_of_eq_add_right_terms
        C doubleHalf (tVar head) (tVar bit) hstepEq).
    }
    assert (hhalfLeHead : BProv Ax_s C
        (leTermAt halfTerm (tVar head))).
    {
      exact (BProv_Ax_s_leTermAt_trans C halfTerm doubleHalf
        (tVar head) hhalfLeDouble hdoubleLeHead).
    }
    assert (hhalfLeSuccPred : BProv Ax_s C
        (leTermAt halfTerm (tSucc pred))).
    {
      exact (BProv_leTermAt_of_eq_right Ax_s C halfTerm
        (tVar head) (tSucc pred) hheadC hhalfLeHead).
    }
    assert (hhalfEq : BProv Ax_s C
        (pEq halfTerm (tSucc pred))).
    {
      exact (BProv_Ax_s_eq_of_leTermAt_leTermAt C
        halfTerm (tSucc pred) hhalfLeSuccPred hsuccLe).
    }
    assert (hsuccPredEq : BProv Ax_s C
        (pEq (tSucc pred) (tAdd doubleHalf (tVar bit)))).
    {
      exact (BProv_eqTrans Ax_s C _ _ _
        (BProv_eqSym Ax_s C _ _ hheadC) hstepEq).
    }
    assert (hhalfSum : BProv Ax_s C
        (pEq halfTerm (tAdd doubleHalf (tVar bit)))).
    {
      exact (BProv_eqTrans Ax_s C _ _ _ hhalfEq hsuccPredEq).
    }
    assert (hassoc : BProv Ax_s C
        (pEq (tAdd doubleHalf (tVar bit))
          (tAdd halfTerm (tAdd halfTerm (tVar bit))))).
    {
      unfold doubleHalf.
      exact (BProv_Ax_s_add_assoc_terms C
        halfTerm halfTerm (tVar bit)).
    }
    assert (hbadEq : BProv Ax_s C
        (pEq (tAdd halfTerm (tAdd halfTerm (tVar bit))) halfTerm)).
    {
      exact (BProv_eqTrans Ax_s C _ _ _
        (BProv_eqSym Ax_s C _ _ hassoc)
        (BProv_eqSym Ax_s C _ _ hhalfSum)).
    }
    assert (hbot : BProv Ax_s C pBot).
    {
      exact (BProv_Ax_s_add_successor_summand_ne_self_terms
        C halfTerm halfTerm (tVar bit) pred hhalfEq hbadEq).
    }
    exact (BProv_botE Ax_s C target hbot).
  }
  exact (BProv_orE Ax_s G target (ltTermAt pred halfTerm)
    target hcmp hleBranch hgtBranch).
Qed.

Lemma rename_hfMemTermAt_succ : forall elem setCode,
  rename S (hfMemTermAt elem setCode) =
  hfMemTermAt (S elem) (Term.rename S setCode).
Proof.
  intros elem setCode.
  unfold hfMemTermAt, betaTermAtConstIdx, betaTermAt, remTermAt,
    ltTermAt, betaAt, remAt, ltAt, leAt,
    betaDiv2StepsThroughAt, betaDiv2StepWitnessAt, betaDiv2BitAt,
    betaAtSuccIdx, div2StepAt, boolAt, zeroAt, oneAt, eqConstAt,
    betaModTerm.
  simpl.
  repeat rewrite Term.rename_comp.
  reflexivity.
Qed.

Lemma BProv_hfMemTermAt_of_hfMemTermAt_eq_term :
  forall (B : formula -> Prop) G elem oldCode newCode,
  BProv B G (hfMemTermAt elem oldCode) ->
  BProv B G (pEq oldCode newCode) ->
  BProv B G (hfMemTermAt elem newCode).
Proof.
  intros B G elem oldCode newCode hmem hset.
  assert (hmemSubst : BProv B G
      (subst (instTerm oldCode) (hfMemAt (S elem) 0))).
  {
    rewrite subst_instTerm_hfMemAt_succ_zero.
    exact hmem.
  }
  pose proof (BProv_eqElim B G oldCode newCode
    (hfMemAt (S elem) 0) hset hmemSubst) as htermSubst.
  rewrite subst_instTerm_hfMemAt_succ_zero in htermSubst.
  exact htermSubst.
Qed.

Lemma BProv_Ax_s_leTermAt_succ_left_of_ltTermAt :
  forall G lower upper,
  BProv Ax_s G (ltTermAt lower upper) ->
  BProv Ax_s G (leTermAt (tSucc lower) upper).
Proof.
  intros G lower upper hlt.
  set (target := leTermAt (tSucc lower) upper).
  apply (BProv_Ax_s_ltTermAt_elim_opened
    G lower upper target).
  - set (body := pEq
      (tAdd (Term.rename S lower) (tSucc (tVar 0)))
      (Term.rename S upper)).
    set (D := body :: map (rename S) G).
    set (lower1 := Term.rename S lower).
    set (upper1 := Term.rename S upper).
    assert (hopened : BProv Ax_s D
        (pEq (tAdd lower1 (tSucc (tVar 0))) upper1)).
    { apply BProv_ass. unfold D, body, lower1, upper1. simpl. left. reflexivity. }
    assert (hsuccAdd : BProv Ax_s D
        (pEq (tAdd (tSucc lower1) (tVar 0))
          (tSucc (tAdd lower1 (tVar 0))))).
    { exact (BProv_Ax_s_succ_add_terms D lower1 (tVar 0)). }
    assert (haddSucc : BProv Ax_s D
        (pEq (tAdd lower1 (tSucc (tVar 0)))
          (tSucc (tAdd lower1 (tVar 0))))).
    {
      exact (BProv_Ax_s_addSucc_terms D lower1 (tVar 0)).
    }
    assert (hleEq : BProv Ax_s D
        (pEq (tAdd (tSucc lower1) (tVar 0)) upper1)).
    {
      exact (BProv_eqTrans Ax_s D _ _ _ hsuccAdd
        (BProv_eqTrans Ax_s D _ _ _
          (BProv_eqSym Ax_s D _ _ haddSucc) hopened)).
    }
    assert (hsubst : BProv Ax_s D
        (subst (instTerm (tVar 0))
          (pEq
            (tAdd (Term.rename S (tSucc lower1)) (tVar 0))
            (Term.rename S upper1)))).
    {
      simpl.
      repeat rewrite term_subst_instTerm_rename_succ.
      exact hleEq.
    }
    assert (hle : BProv Ax_s D (leTermAt (tSucc lower1) upper1)).
    {
      exact (BProv_exI Ax_s D
        (pEq (tAdd (Term.rename S (tSucc lower1)) (tVar 0))
          (Term.rename S upper1)) (tVar 0) hsubst).
    }
    unfold target, D, body, lower1, upper1, leTermAt in *.
    simpl in *.
    repeat rewrite Term.rename_comp in *.
    exact hle.
  - exact hlt.
Qed.

(** The one remaining trace operation needed by the successor-code proof:
    membership of a successor descends across one binary head step. *)
Definition HFMembershipTailStep : Prop :=
  forall G head tailCode headBit,
  BProv Ax_s G (div2StepAt head tailCode headBit) ->
  BProv Ax_s G
    (subst (instTerm (tSucc (tVar 0))) (hfMemAt 0 (S head))) ->
  BProv Ax_s G (hfMemAt 0 tailCode).

(** The concrete successor bound, parametrized only by trace-tail transport. *)
Lemma BProv_Ax_s_hfMembersBelowTermAt_succ_of_through_zero_of_tail :
  HFMembershipTailStep ->
  BProv Ax_s [hfMembersBelowThroughAt 0]
    (hfMembersBelowTermAt (tSucc (tVar 0))).
Proof.
  intro htail.
  set (through := hfMembersBelowThroughAt 0).
  set (G0 := [through]).
  set (highCode := tSucc (tVar 1)).
  set (memHyp := hfMemTermAt 0 highCode).
  set (target := ltTermAt (tVar 0) highCode).
  assert (himp : BProv Ax_s (map (rename S) G0)
      (pImp memHyp target)).
  {
    set (C := memHyp :: map (rename S) G0).
    set (highEqBody := pEq (tVar 0) (Term.rename S highCode)).
    assert (hhighEqEx : BProv Ax_s C (pEx highEqBody)).
    {
      assert (hinst : BProv Ax_s C
          (subst (instTerm highCode) highEqBody)).
      {
        unfold highEqBody.
        simpl.
        apply BProv_eqRefl.
      }
      exact (BProv_exI Ax_s C highEqBody highCode hinst).
    }
    assert (htarget : BProv Ax_s C target).
    {
      apply (BProv_exE_of_sentences Ax_s C highEqBody target
        sentence_ax_s hhighEqEx).
      set (H := highEqBody :: map (rename S) C).
      set (targetH := rename S target).
      assert (htargetH : BProv Ax_s H targetH).
      {
        apply (BProv_Ax_s_of_div2TotalAt_opened_step
          H 0 targetH (BProv_Ax_s_div2TotalAt H 0)).
        set (J := div2TotalOpenedStepContext H 0).
        set (targetJ := rename S (rename S targetH)).
        assert (hcases : BProv Ax_s J (zeroOrSuccPredAt 3)).
        { exact (BProv_Ax_s_zeroOrSuccPredAt J 3). }
        assert (hzeroBranch : BProv Ax_s (zeroAt 3 :: J) targetJ).
        {
          set (Z := zeroAt 3 :: J).
          assert (hzero : BProv Ax_s Z (pEq (tVar 3) tZero)).
          {
            apply BProv_ass.
            unfold Z, zeroAt, eqConstAt. simpl. left. reflexivity.
          }
          assert (hzeroLe : BProv Ax_s Z
              (leTermAt tZero (tVar 4))).
          { exact (BProv_Ax_s_leTermAt_zero_left Z (tVar 4)). }
          assert (hzeroLt : BProv Ax_s Z
              (ltTermAt tZero (tSucc (tVar 4)))).
          {
            exact (BProv_Ax_s_ltTermAt_succ_right_of_leTermAt
              Z tZero (tVar 4) hzeroLe).
          }
          assert (hlt : BProv Ax_s Z
              (ltTermAt (tVar 3) (tSucc (tVar 4)))).
          {
            exact (BProv_ltTermAt_of_eq_left Ax_s Z
              tZero (tVar 3) (tSucc (tVar 4))
              (BProv_eqSym Ax_s Z _ _ hzero) hzeroLt).
          }
          unfold targetJ, targetH, target, highCode.
          unfold ltTermAt in *.
          simpl in *.
          repeat rewrite Term.rename_comp in *.
          exact hlt.
        }
        assert (hsuccBranch : BProv Ax_s (succPredAt 3 :: J) targetJ).
        {
          set (Sctx := succPredAt 3 :: J).
          set (predBody := pEq (tVar 4) (tSucc (tVar 0))).
          assert (hsucc : BProv Ax_s Sctx (succPredAt 3)).
          { apply BProv_ass. unfold Sctx. simpl. left. reflexivity. }
          apply (BProv_exE_of_sentences Ax_s Sctx predBody targetJ
            sentence_ax_s hsucc).
          set (P := predBody :: map (rename S) Sctx).
          assert (hstep : BProv Ax_s P (div2StepAt 3 2 1)).
          {
            apply BProv_ass.
            unfold P, Sctx, J, div2TotalOpenedStepContext.
            simpl.
            repeat rewrite rename_S_div2StepAt.
            right. right. left. reflexivity.
          }
          assert (hhighEq : BProv Ax_s P
              (pEq (tVar 3) (tSucc (tVar 5)))).
          {
            apply BProv_ass.
            unfold P, Sctx, J, H, C, highEqBody, highCode,
              div2TotalOpenedStepContext.
            simpl.
            right. right. right. right. left. reflexivity.
          }
          assert (helemEq : BProv Ax_s P
              (pEq (tVar 4) (tSucc (tVar 0)))).
          {
            apply BProv_ass.
            unfold P, predBody. simpl. left. reflexivity.
          }
          assert (hmemTerm : BProv Ax_s P
              (hfMemTermAt 4 (tSucc (tVar 5)))).
          {
            apply BProv_ass.
            unfold P, Sctx, J, H, C, memHyp, highCode,
              div2TotalOpenedStepContext.
            simpl.
            repeat rewrite rename_hfMemTermAt_succ.
            right. right. right. right. right. left. reflexivity.
          }
          assert (hmemNamedTerm : BProv Ax_s P
              (hfMemTermAt 4 (tVar 3))).
          {
            exact (BProv_hfMemTermAt_of_hfMemTermAt_eq_term
              Ax_s P 4 (tSucc (tVar 5)) (tVar 3) hmemTerm
              (BProv_eqSym Ax_s P _ _ hhighEq)).
          }
          assert (hmemNamed : BProv Ax_s P (hfMemAt 4 3)).
          { rewrite <- hfMemTermAt_var. exact hmemNamedTerm. }
          assert (hsuccMem : BProv Ax_s P
              (subst (instTerm (tSucc (tVar 0)))
                (hfMemAt 0 4))).
          {
            exact (BProv_hfMemAt_of_elem_eq_term
              Ax_s P 4 3 (tSucc (tVar 0)) hmemNamed helemEq).
          }
          assert (hhalfMem : BProv Ax_s P (hfMemAt 0 2)).
          { exact (htail P 3 2 1 hstep hsuccMem). }
          assert (hhalfLe : BProv Ax_s P
              (leTermAt (tVar 2) (tVar 5))).
          {
            exact (BProv_Ax_s_leTermAt_half_of_div2StepAt_eq_succ
              P 3 2 1 (tVar 5) hstep hhighEq).
          }
          assert (hthrough : BProv Ax_s P
              (hfMembersBelowThroughTermAt (tVar 5))).
          {
            apply BProv_ass.
            unfold P, Sctx, J, H, C, G0, through,
              div2TotalOpenedStepContext.
            simpl.
            repeat rewrite rename_hfMembersBelowThroughTermAt_succ.
            right. right. right. right. right. right. left. reflexivity.
          }
          assert (hallHalf : BProv Ax_s P (hfMembersBelowAt 2)).
          {
            exact (BProv_Ax_s_hfMembersBelowAt_of_throughTermAt
              P (tVar 5) 2 hthrough hhalfLe).
          }
          assert (hpredLtHalf : BProv Ax_s P (ltAt 0 2)).
          {
            exact (BProv_ltAt_of_hfMembersBelowAt
              Ax_s P 0 2 hallHalf hhalfMem).
          }
          assert (hpredLtHalfTerm : BProv Ax_s P
              (ltTermAt (tVar 0) (tVar 2))).
          { rewrite ltTermAt_var. exact hpredLtHalf. }
          assert (hsuccPredLeHalf : BProv Ax_s P
              (leTermAt (tSucc (tVar 0)) (tVar 2))).
          {
            exact (BProv_Ax_s_leTermAt_succ_left_of_ltTermAt
              P (tVar 0) (tVar 2) hpredLtHalfTerm).
          }
          assert (hsuccPredLeBound : BProv Ax_s P
              (leTermAt (tSucc (tVar 0)) (tVar 5))).
          {
            exact (BProv_Ax_s_leTermAt_trans P
              (tSucc (tVar 0)) (tVar 2) (tVar 5)
              hsuccPredLeHalf hhalfLe).
          }
          assert (hsuccPredLtSuccBound : BProv Ax_s P
              (ltTermAt (tSucc (tVar 0)) (tSucc (tVar 5)))).
          {
            exact (BProv_Ax_s_ltTermAt_succ_right_of_leTermAt P
              (tSucc (tVar 0)) (tVar 5) hsuccPredLeBound).
          }
          assert (hlt : BProv Ax_s P
              (ltTermAt (tVar 4) (tSucc (tVar 5)))).
          {
            exact (BProv_ltTermAt_of_eq_left Ax_s P
              (tSucc (tVar 0)) (tVar 4) (tSucc (tVar 5))
              (BProv_eqSym Ax_s P _ _ helemEq)
              hsuccPredLtSuccBound).
          }
          unfold targetJ, targetH, target, highCode.
          unfold P, Sctx, J, H, C, G0, predBody,
            div2TotalOpenedStepContext.
          unfold ltTermAt in *.
          simpl in *.
          repeat rewrite Term.rename_comp in *.
          exact hlt.
        }
        exact (BProv_orE Ax_s J (zeroAt 3) (succPredAt 3)
          targetJ hcases hzeroBranch hsuccBranch).
      }
      unfold H, C, targetH, target, highCode in htargetH.
      simpl in htargetH.
      repeat rewrite Term.rename_comp in htargetH.
      exact htargetH.
    }
    unfold C in htarget.
    exact (BProv_impI Ax_s (map (rename S) G0)
      memHyp target htarget).
  }
  assert (hall : BProv Ax_s G0 (pAll (pImp memHyp target))).
  {
    exact (BProv_allI_of_sentences Ax_s G0
      (pImp memHyp target) sentence_ax_s himp).
  }
  unfold G0, through, hfMembersBelowTermAt, highCode, memHyp, target.
  exact hall.
Qed.

Lemma BProv_Ax_s_all_hfMembersBelowAt_of_tail :
  HFMembershipTailStep ->
  BProv Ax_s [] (pAll (hfMembersBelowAt 0)).
Proof.
  intro htail.
  apply BProv_Ax_s_all_hfMembersBelowAt_of_successor_new.
  exact (BProv_Ax_s_hfMembersBelowTermAt_succ_of_through_zero_of_tail
    htail).
Qed.

Lemma BProv_Ax_s_translated_HF_induction_of_tail :
  HFMembershipTailStep ->
  forall phi,
  BProv Ax_s []
    (translateHFFormula (Fol.seal (HF_induction_form phi))).
Proof.
  intros htail phi.
  apply BProv_Ax_s_translated_HF_induction_of_all_hfMembersBelowAt.
  exact (BProv_Ax_s_all_hfMembersBelowAt_of_tail htail).
Qed.
