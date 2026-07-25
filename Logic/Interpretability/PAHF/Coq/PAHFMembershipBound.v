(* ===================================================================== *)
(*  PAHFMembershipBound.v                                                *)
(*                                                                       *)
(*  PA arithmetic for the uniform Ackermann membership bound.  This file *)
(*  extends the translated-induction shell without changing its stable   *)
(*  interface.                                                           *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List.
From PAHF Require Import PAHF PAHFProofCalculus PAHFTranslatedHFFin.

Import ListNotations.
Import PA PA.Term PA.Formula.

(** Every term admits a binary-halving step. *)
Definition div2TotalTermAt (value : term) : formula :=
  pEx (pEx
    (div2StepTermAt (Term.rename (fun n => S (S n)) value)
      (tVar 1) (tVar 0))).

Definition div2TotalAt (value : nat) : formula :=
  div2TotalTermAt (tVar value).

Lemma boolTermAt_var : forall a,
  boolTermAt (tVar a) = boolAt a.
Proof. intro a. reflexivity. Qed.

Lemma div2StepTermAt_var : forall value half bit,
  div2StepTermAt (tVar value) (tVar half) (tVar bit) =
  div2StepAt value half bit.
Proof. intros value half bit. reflexivity. Qed.

(** PA arithmetic for the odd binary carry. *)
Lemma BProv_Ax_s_succ_oddDoubleEqAt_eq_double_succ :
  forall G value half,
  BProv Ax_s G (oddDoubleEqAt value half) ->
  BProv Ax_s G
    (pEq (tSucc (tVar value))
      (tAdd (tSucc (tVar half)) (tSucc (tVar half)))).
Proof.
  intros G value half hodd.
  set (h := tVar half).
  set (double := tAdd h h).
  assert (hvalue : BProv Ax_s G
      (pEq (tVar value) (tSucc double))).
  { unfold oddDoubleEqAt, h, double in hodd. exact hodd. }
  assert (hsuccValue : BProv Ax_s G
      (pEq (tSucc (tVar value)) (tSucc (tSucc double)))).
  { exact (BProv_eq_congr_succ Ax_s G _ _ hvalue). }
  assert (hleft : BProv Ax_s G
      (pEq (tAdd (tSucc h) (tSucc h))
        (tSucc (tAdd h (tSucc h))))).
  { exact (BProv_Ax_s_succ_add_terms G h (tSucc h)). }
  assert (hrightStep : BProv Ax_s G
      (pEq (tAdd h (tSucc h)) (tSucc double))).
  {
    unfold double.
    exact (BProv_Ax_s_addSucc_terms G h h).
  }
  assert (hright : BProv Ax_s G
      (pEq (tSucc (tAdd h (tSucc h)))
        (tSucc (tSucc double)))).
  { exact (BProv_eq_congr_succ Ax_s G _ _ hrightStep). }
  assert (hdoubleSucc : BProv Ax_s G
      (pEq (tAdd (tSucc h) (tSucc h))
        (tSucc (tSucc double)))).
  { exact (BProv_eqTrans Ax_s G _ _ _ hleft hright). }
  unfold h, double in hdoubleSucc.
  exact (BProv_eqTrans Ax_s G _ _ _ hsuccValue
    (BProv_eqSym Ax_s G _ _ hdoubleSucc)).
Qed.

(** Even successor case for term-parametric binary halving. *)
Lemma BProv_Ax_s_div2StepTermAt_succ_of_doubleEqAt :
  forall G value half,
  BProv Ax_s G (doubleEqAt value half) ->
  BProv Ax_s G
    (div2StepTermAt
      (tSucc (tVar value)) (tVar half) (tSucc tZero)).
Proof.
  intros G value half hdouble.
  set (d := tAdd (tVar half) (tVar half)).
  assert (hbool : BProv Ax_s G (boolTermAt (tSucc tZero))).
  {
    unfold boolTermAt.
    apply BProv_orI2.
    apply BProv_eqRefl.
  }
  assert (hvalue : BProv Ax_s G (pEq (tVar value) d)).
  { unfold doubleEqAt, d in hdouble. exact hdouble. }
  assert (hsuccValue : BProv Ax_s G
      (pEq (tSucc (tVar value)) (tSucc d))).
  { exact (BProv_eq_congr_succ Ax_s G _ _ hvalue). }
  assert (haddSucc : BProv Ax_s G
      (pEq (tAdd d (tSucc tZero)) (tSucc (tAdd d tZero)))).
  { exact (BProv_Ax_s_addSucc_terms G d tZero). }
  assert (haddZero : BProv Ax_s G
      (pEq (tSucc (tAdd d tZero)) (tSucc d))).
  {
    exact (BProv_eq_congr_succ Ax_s G _ _
      (BProv_Ax_s_addZero_term G d)).
  }
  assert (hsum : BProv Ax_s G
      (pEq (tAdd d (tSucc tZero)) (tSucc d))).
  { exact (BProv_eqTrans Ax_s G _ _ _ haddSucc haddZero). }
  assert (heq : BProv Ax_s G
      (pEq (tSucc (tVar value)) (tAdd d (tSucc tZero)))).
  {
    exact (BProv_eqTrans Ax_s G _ _ _ hsuccValue
      (BProv_eqSym Ax_s G _ _ hsum)).
  }
  unfold div2StepTermAt, d.
  exact (BProv_andI Ax_s G _ _ hbool heq).
Qed.

(** Odd successor carry for term-parametric binary halving. *)
Lemma BProv_Ax_s_div2StepTermAt_succ_of_oddDoubleEqAt :
  forall G value half,
  BProv Ax_s G (oddDoubleEqAt value half) ->
  BProv Ax_s G
    (div2StepTermAt
      (tSucc (tVar value)) (tSucc (tVar half)) tZero).
Proof.
  intros G value half hodd.
  set (d := tAdd (tSucc (tVar half)) (tSucc (tVar half))).
  assert (hbool : BProv Ax_s G (boolTermAt tZero)).
  {
    unfold boolTermAt.
    apply BProv_orI1.
    apply BProv_eqRefl.
  }
  assert (hvalue : BProv Ax_s G
      (pEq (tSucc (tVar value)) d)).
  {
    unfold d.
    exact (BProv_Ax_s_succ_oddDoubleEqAt_eq_double_succ
      G value half hodd).
  }
  assert (haddZero : BProv Ax_s G (pEq (tAdd d tZero) d)).
  { exact (BProv_Ax_s_addZero_term G d). }
  assert (heq : BProv Ax_s G
      (pEq (tSucc (tVar value)) (tAdd d tZero))).
  {
    exact (BProv_eqTrans Ax_s G _ _ _ hvalue
      (BProv_eqSym Ax_s G _ _ haddZero)).
  }
  unfold div2StepTermAt, d.
  exact (BProv_andI Ax_s G _ _ hbool heq).
Qed.

(** Introduce total halving from explicit half and bit witnesses. *)
Lemma BProv_Ax_s_div2TotalTermAt_intro :
  forall G value half bit,
  BProv Ax_s G (div2StepTermAt value half bit) ->
  BProv Ax_s G (div2TotalTermAt value).
Proof.
  intros G value half bit hstep.
  set (body := div2StepTermAt
    (Term.rename (fun n => S (S n)) value) (tVar 1) (tVar 0)).
  assert (hbit : BProv Ax_s G
      (subst (instTerm bit)
        (subst (Term.upSubst (instTerm half)) body))).
  {
    unfold body, div2StepTermAt, boolTermAt.
    simpl.
    normalize_subst_rename_comp.
    exact hstep.
  }
  assert (hhalf : BProv Ax_s G (subst (instTerm half) (pEx body))).
  {
    exact (BProv_exI Ax_s G
      (subst (Term.upSubst (instTerm half)) body) bit hbit).
  }
  unfold div2TotalTermAt.
  exact (BProv_exI Ax_s G (pEx body) half hhalf).
Qed.

(** A halving step exposes even and odd forms of its input. *)
Lemma BProv_Ax_s_double_or_oddDoubleEqAt_of_div2StepAt :
  forall G value half bit,
  BProv Ax_s G (div2StepAt value half bit) ->
  BProv Ax_s G
    (pOr (doubleEqAt value half) (oddDoubleEqAt value half)).
Proof.
  intros G value half bit hstep.
  assert (hbool : BProv Ax_s G (boolAt bit)).
  { exact (BProv_andE1 Ax_s G _ _ hstep). }
  assert (hzero : BProv Ax_s (zeroAt bit :: G)
      (pOr (doubleEqAt value half) (oddDoubleEqAt value half))).
  {
    apply BProv_orI1.
    apply (BProv_Ax_s_doubleEqAt_of_div2StepAt_bit_zero
      (zeroAt bit :: G) value half bit).
    - apply BProv_ass_head.
    - apply BProv_context_cons. exact hstep.
  }
  assert (hone : BProv Ax_s (oneAt bit :: G)
      (pOr (doubleEqAt value half) (oddDoubleEqAt value half))).
  {
    apply BProv_orI2.
    apply (BProv_Ax_s_oddDoubleEqAt_of_div2StepAt_bit_one
      (oneAt bit :: G) value half bit).
    - apply BProv_ass_head.
    - apply BProv_context_cons. exact hstep.
  }
  exact (BProv_orE Ax_s G (zeroAt bit) (oneAt bit)
    (pOr (doubleEqAt value half) (oddDoubleEqAt value half))
    hbool hzero hone).
Qed.

Lemma BProv_Ax_s_of_div2StepAt_double_odd_cases :
  forall G value half bit target,
  BProv Ax_s G (div2StepAt value half bit) ->
  BProv Ax_s (doubleEqAt value half :: G) target ->
  BProv Ax_s (oddDoubleEqAt value half :: G) target ->
  BProv Ax_s G target.
Proof.
  intros G value half bit target hstep heven hodd.
  exact (BProv_orE Ax_s G (doubleEqAt value half)
    (oddDoubleEqAt value half) target
    (BProv_Ax_s_double_or_oddDoubleEqAt_of_div2StepAt
      G value half bit hstep) heven hodd).
Qed.

Lemma BProv_Ax_s_div2TotalTermAt_succ_of_div2StepAt :
  forall G value half bit,
  BProv Ax_s G (div2StepAt value half bit) ->
  BProv Ax_s G (div2TotalTermAt (tSucc (tVar value))).
Proof.
  intros G value half bit hstep.
  assert (heven : BProv Ax_s (doubleEqAt value half :: G)
      (div2TotalTermAt (tSucc (tVar value)))).
  {
    apply BProv_Ax_s_div2TotalTermAt_intro with
      (half := tVar half) (bit := tSucc tZero).
    apply BProv_Ax_s_div2StepTermAt_succ_of_doubleEqAt.
    apply BProv_ass_head.
  }
  assert (hodd : BProv Ax_s (oddDoubleEqAt value half :: G)
      (div2TotalTermAt (tSucc (tVar value)))).
  {
    apply BProv_Ax_s_div2TotalTermAt_intro with
      (half := tSucc (tVar half)) (bit := tZero).
    apply BProv_Ax_s_div2StepTermAt_succ_of_oddDoubleEqAt.
    apply BProv_ass_head.
  }
  exact (BProv_Ax_s_of_div2StepAt_double_odd_cases
    G value half bit (div2TotalTermAt (tSucc (tVar value)))
    hstep heven hodd).
Qed.

Lemma BProv_Ax_s_div2TotalTermAt_zero :
  BProv Ax_s [] (div2TotalTermAt tZero).
Proof.
  assert (hbool : BProv Ax_s [] (boolTermAt tZero)).
  {
    unfold boolTermAt.
    apply BProv_orI1.
    apply BProv_eqRefl.
  }
  assert (hzeroAdd : BProv Ax_s [] (pEq (tAdd tZero tZero) tZero)).
  { exact (BProv_Ax_s_addZero_term [] tZero). }
  assert (hsumZero : BProv Ax_s []
      (pEq (tAdd (tAdd tZero tZero) tZero) (tAdd tZero tZero))).
  { exact (BProv_Ax_s_addZero_term [] (tAdd tZero tZero)). }
  assert (hsum : BProv Ax_s []
      (pEq (tAdd (tAdd tZero tZero) tZero) tZero)).
  { exact (BProv_eqTrans Ax_s [] _ _ _ hsumZero hzeroAdd). }
  assert (hstep : BProv Ax_s []
      (div2StepTermAt tZero tZero tZero)).
  {
    unfold div2StepTermAt.
    exact (BProv_andI Ax_s [] _ _ hbool
      (BProv_eqSym Ax_s [] _ _ hsum)).
  }
  exact (BProv_Ax_s_div2TotalTermAt_intro [] tZero tZero tZero hstep).
Qed.

Lemma substZero_div2TotalAt_zero :
  subst substZero (div2TotalAt 0) = div2TotalTermAt tZero.
Proof. reflexivity. Qed.

Lemma substSuccVar_div2TotalAt_zero :
  subst substSuccVar (div2TotalAt 0) =
  div2TotalTermAt (tSucc (tVar 0)).
Proof. reflexivity. Qed.

(** PA proves universal totality of binary halving. *)
Lemma BProv_Ax_s_div2TotalAt_all :
  BProv Ax_s [] (pAll (div2TotalAt 0)).
Proof.
  set (phi := div2TotalAt 0).
  assert (hzero : BProv Ax_s [] (subst substZero phi)).
  {
    unfold phi.
    rewrite substZero_div2TotalAt_zero.
    exact BProv_Ax_s_div2TotalTermAt_zero.
  }
  assert (hsuccBody : BProv Ax_s [phi] (subst substSuccVar phi)).
  {
    set (step := div2StepAt 2 1 0).
    set (inner := pEx step).
    set (target := div2TotalTermAt (tSucc (tVar 0))).
    assert (hphi : BProv Ax_s [phi] (pEx inner)).
    {
      assert (hraw : BProv Ax_s [phi] phi).
      { apply BProv_ass_head. }
      unfold phi, div2TotalAt, div2TotalTermAt in hraw.
      change (BProv Ax_s [phi] (pEx (pEx (div2StepAt 2 1 0)))) in hraw.
      unfold step, inner.
      exact hraw.
    }
    assert (htarget : BProv Ax_s [phi] target).
    {
      apply (BProv_two_exE_of_sentences
        Ax_s sentence_ax_s [phi] step target hphi).
      set (D := step :: map (rename S)
        (pEx step :: map (rename S) [phi])).
      assert (hstep : BProv Ax_s D (div2StepAt 2 1 0)).
      { apply BProv_ass. unfold D, step. simpl. left. reflexivity. }
      assert (hsucc : BProv Ax_s D
          (div2TotalTermAt (tSucc (tVar 2)))).
      {
        exact (BProv_Ax_s_div2TotalTermAt_succ_of_div2StepAt
          D 2 1 0 hstep).
      }
      unfold D, target, div2TotalTermAt.
      simpl.
      repeat rewrite Term.rename_comp.
      exact hsucc.
    }
    unfold phi.
    rewrite substSuccVar_div2TotalAt_zero.
    unfold target in htarget.
    exact htarget.
  }
  assert (hsuccImp : BProv Ax_s []
      (pImp phi (subst substSuccVar phi))).
  { exact (BProv_impI Ax_s [] phi (subst substSuccVar phi) hsuccBody). }
  assert (hsucc : BProv Ax_s []
      (pAll (pImp phi (subst substSuccVar phi)))).
  {
    exact (BProv_allI_of_sentences Ax_s []
      (pImp phi (subst substSuccVar phi)) sentence_ax_s hsuccImp).
  }
  unfold phi.
  exact (BProv_Ax_s_induction_rule [] (div2TotalAt 0) hzero hsucc).
Qed.

Lemma subst_instTerm_var_div2TotalAt_zero : forall value,
  subst (instTerm (tVar value)) (div2TotalAt 0) = div2TotalAt value.
Proof. intro value. reflexivity. Qed.

Lemma BProv_Ax_s_div2TotalAt : forall G value,
  BProv Ax_s G (div2TotalAt value).
Proof.
  intros G value.
  pose proof (BProv_weaken_nil Ax_s G _ BProv_Ax_s_div2TotalAt_all) as hall.
  pose proof (BProv_allE Ax_s G (div2TotalAt 0) (tVar value) hall)
    as hinst.
  rewrite subst_instTerm_var_div2TotalAt_zero in hinst.
  exact hinst.
Qed.

(** Generic eliminator exposing the two witnesses of total halving. *)
Lemma BProv_Ax_s_of_div2TotalAt_opened_step :
  forall G value target,
  BProv Ax_s G (div2TotalAt value) ->
  BProv Ax_s (div2TotalOpenedStepContext G value)
    (rename S (rename S target)) ->
  BProv Ax_s G target.
Proof.
  intros G value target htotal hbody.
  set (step := div2StepAt (value + 2) 1 0).
  set (inner := pEx step).
  assert (htotal' : BProv Ax_s G (pEx inner)).
  {
    unfold div2TotalAt, div2TotalTermAt in htotal.
    change (BProv Ax_s G
      (pEx (pEx
        (div2StepTermAt (tVar (S (S value))) (tVar 1) (tVar 0)))))
      in htotal.
    rewrite div2StepTermAt_var in htotal.
    replace (S (S value)) with (value + 2) in htotal by lia.
    unfold inner, step.
    exact htotal.
  }
  apply (BProv_two_exE_of_sentences
    Ax_s sentence_ax_s G step target htotal').
  unfold div2TotalOpenedStepContext in hbody.
  unfold inner, step.
  exact hbody.
Qed.

(** Extend the cumulative membership-bound invariant by one code. *)
Lemma BProv_Ax_s_hfMembersBelowThroughTermAt_succ :
  forall G boundCode,
  BProv Ax_s G (hfMembersBelowThroughTermAt boundCode) ->
  BProv Ax_s G (hfMembersBelowTermAt (tSucc boundCode)) ->
  BProv Ax_s G
    (hfMembersBelowThroughTermAt (tSucc boundCode)).
Proof.
  intros G boundCode hthrough hnew.
  set (bound1 := Term.rename S boundCode).
  set (oldLimit := tSucc bound1).
  set (newLimit := tSucc oldLimit).
  set (antecedent := ltTermAt (tVar 0) newLimit).
  set (target := hfMembersBelowAt 0).
  assert (hbody : BProv Ax_s
      (antecedent :: map (rename S) G) target).
  {
    set (C := antecedent :: map (rename S) G).
    assert (hltNew : BProv Ax_s C
        (ltTermAt (tVar 0) (tSucc oldLimit))).
    {
      apply BProv_ass.
      unfold C, antecedent, newLimit.
      simpl. left. reflexivity.
    }
    assert (hcases : BProv Ax_s C
        (pOr (ltTermAt (tVar 0) oldLimit)
          (pEq (tVar 0) oldLimit))).
    {
      exact (BProv_Ax_s_ltTermAt_succ_right_cases C
        (tVar 0) oldLimit hltNew).
    }
    assert (hthroughC : BProv Ax_s C
        (hfMembersBelowThroughTermAt bound1)).
    {
      pose proof (BProv_rename_succ_context_cons_of_sentences
        Ax_s sentence_ax_s G antecedent _ hthrough) as hren.
      rewrite rename_hfMembersBelowThroughTermAt_succ in hren.
      unfold C, bound1.
      exact hren.
    }
    assert (hnewC : BProv Ax_s C
        (hfMembersBelowTermAt oldLimit)).
    {
      pose proof (BProv_rename_succ_context_cons_of_sentences
        Ax_s sentence_ax_s G antecedent _ hnew) as hren.
      rewrite rename_hfMembersBelowTermAt_succ in hren.
      unfold C, oldLimit, bound1.
      exact hren.
    }
    assert (hstrict : BProv Ax_s
        (ltTermAt (tVar 0) oldLimit :: C) target).
    {
      set (D := ltTermAt (tVar 0) oldLimit :: C).
      assert (hlt : BProv Ax_s D
          (ltTermAt (tVar 0) (tSucc bound1))).
      {
        apply BProv_ass.
        unfold D, oldLimit. simpl. left. reflexivity.
      }
      assert (hle : BProv Ax_s D
          (leTermAt (tVar 0) bound1)).
      {
        exact (BProv_Ax_s_leTermAt_of_ltTermAt_succ_right D
          (tVar 0) bound1 hlt).
      }
      assert (hthroughD : BProv Ax_s D
          (hfMembersBelowThroughTermAt bound1)).
      {
        unfold D.
        apply BProv_context_cons.
        exact hthroughC.
      }
      unfold target.
      exact (BProv_Ax_s_hfMembersBelowAt_of_throughTermAt
        D bound1 0 hthroughD hle).
    }
    assert (hequal : BProv Ax_s
        (pEq (tVar 0) oldLimit :: C) target).
    {
      set (D := pEq (tVar 0) oldLimit :: C).
      assert (heq : BProv Ax_s D (pEq oldLimit (tVar 0))).
      {
        apply BProv_eqSym.
        apply BProv_ass.
        unfold D. simpl. left. reflexivity.
      }
      assert (hnewD : BProv Ax_s D
          (hfMembersBelowTermAt oldLimit)).
      {
        unfold D.
        apply BProv_context_cons.
        exact hnewC.
      }
      pose proof (BProv_hfMembersBelowTermAt_of_set_eq_term
        Ax_s D oldLimit (tVar 0) hnewD heq) as htransport.
      rewrite hfMembersBelowTermAt_var in htransport.
      unfold target.
      exact htransport.
    }
    exact (BProv_orE Ax_s C
      (ltTermAt (tVar 0) oldLimit) (pEq (tVar 0) oldLimit)
      target hcases hstrict hequal).
  }
  assert (himp : BProv Ax_s (map (rename S) G)
      (pImp antecedent target)).
  {
    exact (BProv_impI Ax_s (map (rename S) G)
      antecedent target hbody).
  }
  assert (hall : BProv Ax_s G (pAll (pImp antecedent target))).
  {
    exact (BProv_allI_of_sentences Ax_s G
      (pImp antecedent target) sentence_ax_s himp).
  }
  unfold hfMembersBelowThroughTermAt.
  unfold antecedent, target, newLimit, oldLimit, bound1 in hall.
  simpl in hall.
  repeat rewrite Term.rename_comp in hall.
  exact hall.
Qed.

Lemma BProv_Ax_s_hfMembersBelowAt_of_eqConst_zero :
  forall G set,
  BProv Ax_s G (eqConstAt set 0) ->
  BProv Ax_s G (hfMembersBelowAt set).
Proof.
  intros G set hzero.
  set (memHyp := hfMemAt 0 (S set)).
  assert (hbody : BProv Ax_s (memHyp :: map (rename S) G)
      (ltAt 0 (S set))).
  {
    set (C := memHyp :: map (rename S) G).
    assert (hmem : BProv Ax_s C (hfMemAt 0 (S set))).
    { apply BProv_ass. unfold C, memHyp. simpl. left. reflexivity. }
    assert (hzeroC : BProv Ax_s C (eqConstAt (S set) 0)).
    {
      pose proof (BProv_rename_succ_context_cons_of_sentences
        Ax_s sentence_ax_s G memHyp _ hzero) as h.
      unfold C, eqConstAt in h.
      simpl in h.
      exact h.
    }
    apply (BProv_botE Ax_s C (ltAt 0 (S set))).
    exact (BProv_Ax_s_hfMemAt_bot_of_eqConst_zero
      C 0 (S set) hzeroC hmem).
  }
  assert (himp : BProv Ax_s (map (rename S) G)
      (pImp (hfMemAt 0 (S set)) (ltAt 0 (S set)))).
  {
    unfold memHyp in hbody.
    exact (BProv_impI Ax_s (map (rename S) G)
      (hfMemAt 0 (S set)) (ltAt 0 (S set)) hbody).
  }
  unfold hfMembersBelowAt.
  exact (BProv_allI_of_sentences Ax_s G
    (pImp (hfMemAt 0 (S set)) (ltAt 0 (S set)))
    sentence_ax_s himp).
Qed.

Lemma BProv_Ax_s_hfMembersBelowThroughTermAt_zero :
  BProv Ax_s [] (hfMembersBelowThroughTermAt tZero).
Proof.
  set (belowOne := ltTermAt (tVar 0) (tSucc tZero)).
  assert (hlt : BProv Ax_s [belowOne] belowOne).
  { apply BProv_ass_head. }
  assert (hleTerm : BProv Ax_s [belowOne]
      (leTermAt (tVar 0) tZero)).
  {
    exact (BProv_Ax_s_leTermAt_of_ltTermAt_succ_right
      [belowOne] (tVar 0) tZero hlt).
  }
  assert (hle : BProv Ax_s [belowOne] (leConstAt 0 0)).
  { exact hleTerm. }
  assert (hzero : BProv Ax_s [belowOne] (eqConstAt 0 0)).
  { exact (BProv_Ax_s_eqConstAt_zero_of_leConstAt_zero
      [belowOne] 0 hle). }
  assert (hprop : BProv Ax_s [belowOne] (hfMembersBelowAt 0)).
  { exact (BProv_Ax_s_hfMembersBelowAt_of_eqConst_zero
      [belowOne] 0 hzero). }
  assert (himp : BProv Ax_s []
      (pImp (ltTermAt (tVar 0) (tSucc tZero))
        (hfMembersBelowAt 0))).
  {
    unfold belowOne in hprop.
    exact (BProv_impI Ax_s []
      (ltTermAt (tVar 0) (tSucc tZero))
      (hfMembersBelowAt 0) hprop).
  }
  unfold hfMembersBelowThroughTermAt.
  exact (BProv_allI_of_sentences Ax_s []
    (pImp (ltTermAt (tVar 0) (tSucc tZero))
      (hfMembersBelowAt 0)) sentence_ax_s himp).
Qed.

Lemma substZero_hfMembersBelowThroughAt_zero :
  subst substZero (hfMembersBelowThroughAt 0) =
  hfMembersBelowThroughTermAt tZero.
Proof. reflexivity. Qed.

Lemma substSuccVar_hfMembersBelowThroughAt_zero :
  subst substSuccVar (hfMembersBelowThroughAt 0) =
  hfMembersBelowThroughTermAt (tSucc (tVar 0)).
Proof. reflexivity. Qed.

(** PA induction closes the cumulative invariant from its only hard
    successor-code obligation. *)
Lemma BProv_Ax_s_all_hfMembersBelowThroughAt_of_successor_new :
  BProv Ax_s [hfMembersBelowThroughAt 0]
    (hfMembersBelowTermAt (tSucc (tVar 0))) ->
  BProv Ax_s [] (pAll (hfMembersBelowThroughAt 0)).
Proof.
  intro hnew.
  set (phi := hfMembersBelowThroughAt 0).
  assert (hzero : BProv Ax_s [] (subst substZero phi)).
  {
    unfold phi.
    rewrite substZero_hfMembersBelowThroughAt_zero.
    exact BProv_Ax_s_hfMembersBelowThroughTermAt_zero.
  }
  assert (hthrough : BProv Ax_s [phi]
      (hfMembersBelowThroughTermAt (tVar 0))).
  {
    unfold phi, hfMembersBelowThroughAt.
    apply BProv_ass_head.
  }
  assert (hsuccTerm : BProv Ax_s [phi]
      (hfMembersBelowThroughTermAt (tSucc (tVar 0)))).
  {
    apply (BProv_Ax_s_hfMembersBelowThroughTermAt_succ
      [phi] (tVar 0) hthrough).
    unfold phi in hnew.
    exact hnew.
  }
  assert (hsuccBody : BProv Ax_s [phi] (subst substSuccVar phi)).
  {
    unfold phi.
    rewrite substSuccVar_hfMembersBelowThroughAt_zero.
    exact hsuccTerm.
  }
  assert (hsuccImp : BProv Ax_s []
      (pImp phi (subst substSuccVar phi))).
  { exact (BProv_impI Ax_s [] phi (subst substSuccVar phi) hsuccBody). }
  assert (hsuccAll : BProv Ax_s []
      (pAll (pImp phi (subst substSuccVar phi)))).
  {
    exact (BProv_allI_of_sentences Ax_s []
      (pImp phi (subst substSuccVar phi)) sentence_ax_s hsuccImp).
  }
  unfold phi.
  exact (BProv_Ax_s_induction_rule []
    (hfMembersBelowThroughAt 0) hzero hsuccAll).
Qed.

Lemma subst_instTerm_var_hfMembersBelowThroughAt_zero : forall bound,
  subst (instTerm (tVar bound)) (hfMembersBelowThroughAt 0) =
  hfMembersBelowThroughTermAt (tVar bound).
Proof. intro bound. reflexivity. Qed.

Lemma BProv_Ax_s_all_hfMembersBelowAt_of_all_through :
  BProv Ax_s [] (pAll (hfMembersBelowThroughAt 0)) ->
  BProv Ax_s [] (pAll (hfMembersBelowAt 0)).
Proof.
  intro hall.
  pose proof (BProv_allE Ax_s [] (hfMembersBelowThroughAt 0)
    (tVar 0) hall) as hthrough.
  rewrite subst_instTerm_var_hfMembersBelowThroughAt_zero in hthrough.
  assert (hself : BProv Ax_s [] (leTermAt (tVar 0) (tVar 0))).
  { exact (BProv_Ax_s_leTermAt_refl [] (tVar 0)). }
  assert (hpoint : BProv Ax_s [] (hfMembersBelowAt 0)).
  {
    exact (BProv_Ax_s_hfMembersBelowAt_of_throughTermAt
      [] (tVar 0) 0 hthrough hself).
  }
  exact (BProv_allI_of_sentences Ax_s []
    (hfMembersBelowAt 0) sentence_ax_s hpoint).
Qed.

Lemma BProv_Ax_s_all_hfMembersBelowAt_of_successor_new :
  BProv Ax_s [hfMembersBelowThroughAt 0]
    (hfMembersBelowTermAt (tSucc (tVar 0))) ->
  BProv Ax_s [] (pAll (hfMembersBelowAt 0)).
Proof.
  intro hnew.
  apply BProv_Ax_s_all_hfMembersBelowAt_of_all_through.
  exact (BProv_Ax_s_all_hfMembersBelowThroughAt_of_successor_new hnew).
Qed.

Lemma BProv_Ax_s_translated_HF_induction_of_successor_new :
  BProv Ax_s [hfMembersBelowThroughAt 0]
    (hfMembersBelowTermAt (tSucc (tVar 0))) ->
  forall phi,
  BProv Ax_s []
    (translateHFFormula (Fol.seal (HF_induction_form phi))).
Proof.
  intros hnew phi.
  apply BProv_Ax_s_translated_HF_induction_of_all_hfMembersBelowAt.
  exact (BProv_Ax_s_all_hfMembersBelowAt_of_successor_new hnew).
Qed.
