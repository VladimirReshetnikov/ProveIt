(* ===================================================================== *)
(*  PAHFTranslatedExtensionality.v                                      *)
(*                                                                       *)
(*  PA proof of extensionality for Ackermann-coded hereditary finite     *)
(*  sets.  The proof is organized around one cumulative binary           *)
(*  strong-induction invariant; this is the short route used by the      *)
(*  current Lean development, without the later case-by-case facade.     *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List.
From PAHF Require Import PAHF PAHFProofCalculus PAHFOrdinalCode PAHFOrdinalCodeTotalCapacity
  PAHFMembershipBound PAHFMembershipBoundSucc
  PAHFBetaShiftPrefix PAHFMembershipTail PAHFAdjoinTotal.

Import ListNotations.
Import PA PA.Term PA.Formula.

(** Every code at most [boundCode] satisfies the pointwise
    lower-code-distinguisher predicate. *)
Definition hfLtDistinguishesThroughTermAt (boundCode : term) : formula :=
  pAll (pImp
    (ltTermAt (tVar 0) (tSucc (Term.rename S boundCode)))
    (hfLtDistinguishesAt 0)).

Definition hfLtDistinguishesThroughAt (bound : nat) : formula :=
  hfLtDistinguishesThroughTermAt (tVar bound).

Lemma hfLtDistinguishesThroughTermAt_var : forall bound,
  hfLtDistinguishesThroughTermAt (tVar bound) =
    hfLtDistinguishesThroughAt bound.
Proof. reflexivity. Qed.

Lemma rename_hfLtDistinguishesTermAt_succ : forall highCode,
  rename S (hfLtDistinguishesTermAt highCode) =
    hfLtDistinguishesTermAt (Term.rename S highCode).
Proof.
  intro highCode.
  unfold hfLtDistinguishesTermAt, hfSomeDistinguishesTermAt,
    hfDistinguishesTermAt, hfMemTermAt, hfMemAt,
    betaTermAtConstIdx, betaTermAt, remTermAt, ltTermAt,
    betaDiv2BitAt, betaDiv2StepsThroughAt, betaDiv2StepWitnessAt,
    betaAtSuccIdx, betaAtConstIdx, betaAt, remAt, ltAt, leAt,
    div2StepAt, boolAt, zeroAt, oneAt, eqConstAt, betaModTerm.
  simpl.
  repeat rewrite Term.rename_comp.
  reflexivity.
Qed.

Lemma rename_hfLtDistinguishesAt_succ : forall high,
  rename S (hfLtDistinguishesAt high) =
    hfLtDistinguishesAt (S high).
Proof.
  intro high.
  change (rename S (hfLtDistinguishesTermAt (tVar high)) =
    hfLtDistinguishesTermAt (tVar (S high))).
  rewrite rename_hfLtDistinguishesTermAt_succ.
  reflexivity.
Qed.

Lemma rename_hfLtDistinguishesThroughTermAt_succ : forall boundCode,
  rename S (hfLtDistinguishesThroughTermAt boundCode) =
    hfLtDistinguishesThroughTermAt (Term.rename S boundCode).
Proof.
  intro boundCode.
  unfold hfLtDistinguishesThroughTermAt, hfLtDistinguishesAt,
    hfSomeDistinguishesAt, hfDistinguishesAt, hfMemAt,
    betaDiv2BitAt, betaDiv2StepsThroughAt, betaDiv2StepWitnessAt,
    betaAtSuccIdx, betaAtConstIdx, betaAt, remAt, ltAt, leAt,
    ltTermAt, div2StepAt, boolAt, zeroAt, oneAt, eqConstAt,
    betaModTerm.
  simpl.
  repeat rewrite Term.rename_comp.
  reflexivity.
Qed.

Lemma substZero_hfLtDistinguishesThroughAt_zero :
  subst substZero (hfLtDistinguishesThroughAt 0) =
    hfLtDistinguishesThroughTermAt tZero.
Proof. reflexivity. Qed.

Lemma substSuccVar_hfLtDistinguishesThroughAt_zero :
  subst substSuccVar (hfLtDistinguishesThroughAt 0) =
    hfLtDistinguishesThroughTermAt (tSucc (tVar 0)).
Proof. reflexivity. Qed.

(** Project a single point of the cumulative invariant. *)
Lemma BProv_Ax_s_hfLtDistinguishesAt_of_throughTermAt :
  forall G boundCode high,
  BProv Ax_s G (hfLtDistinguishesThroughTermAt boundCode) ->
  BProv Ax_s G (leTermAt (tVar high) boundCode) ->
  BProv Ax_s G (hfLtDistinguishesAt high).
Proof.
  intros G boundCode high hthrough hle.
  assert (hlt : BProv Ax_s G
      (ltTermAt (tVar high) (tSucc boundCode))).
  { exact (BProv_Ax_s_ltTermAt_succ_right_of_leTermAt
      G (tVar high) boundCode hle). }
  pose proof (BProv_allE Ax_s G _ (tVar high) hthrough) as himp.
  assert (himp' : BProv Ax_s G
      (pImp (ltTermAt (tVar high) (tSucc boundCode))
        (hfLtDistinguishesAt high))).
  {
    unfold hfLtDistinguishesThroughTermAt in himp.
    change (BProv Ax_s G
      (pImp
        (subst (instTerm (tVar high))
          (ltTermAt (tVar 0) (tSucc (Term.rename S boundCode))))
        (subst (instTerm (tVar high))
          (hfLtDistinguishesAt 0)))) in himp.
    rewrite subst_ltTermAt in himp.
    rewrite subst_instTerm_var_hfLtDistinguishesAt_zero in himp.
    simpl in himp.
    rewrite term_subst_instTerm_rename_succ in himp.
    exact himp.
  }
  exact (BProv_mp Ax_s G _ _ himp' hlt).
Qed.

Lemma BProv_Ax_s_hfLtDistinguishesThroughTermAt_zero :
  BProv Ax_s [] (hfLtDistinguishesThroughTermAt tZero).
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
  { unfold belowOne, leConstAt in *. simpl in *. exact hleTerm. }
  assert (hzero : BProv Ax_s [belowOne] (eqConstAt 0 0)).
  { exact (BProv_Ax_s_eqConstAt_zero_of_leConstAt_zero [belowOne] 0 hle). }
  assert (hprop : BProv Ax_s [belowOne] (hfLtDistinguishesAt 0)).
  { exact (BProv_Ax_s_hfLtDistinguishesAt_of_eqConst_high
      [belowOne] 0 0 hzero). }
  assert (himp : BProv Ax_s []
      (pImp (ltTermAt (tVar 0) (tSucc tZero))
        (hfLtDistinguishesAt 0))).
  { unfold belowOne in hprop. exact (BProv_impI Ax_s [] _ _ hprop). }
  unfold hfLtDistinguishesThroughTermAt.
  apply (BProv_allI_of_sentences Ax_s [] _ sentence_ax_s).
  exact himp.
Qed.

(** Extending a cumulative invariant only needs the genuinely new endpoint. *)
Lemma BProv_Ax_s_hfLtDistinguishesThroughTermAt_succ :
  forall G boundCode,
  BProv Ax_s G (hfLtDistinguishesThroughTermAt boundCode) ->
  BProv Ax_s G (hfLtDistinguishesTermAt (tSucc boundCode)) ->
  BProv Ax_s G
    (hfLtDistinguishesThroughTermAt (tSucc boundCode)).
Proof.
  intros G boundCode hthrough hnew.
  set (bound1 := Term.rename S boundCode).
  set (oldLimit := tSucc bound1).
  set (newLimit := tSucc oldLimit).
  set (antecedent := ltTermAt (tVar 0) newLimit).
  set (target := hfLtDistinguishesAt 0).
  set (C := antecedent :: map (rename S) G).
  assert (hltNew : BProv Ax_s C
      (ltTermAt (tVar 0) (tSucc oldLimit))).
  { apply BProv_ass. unfold C. simpl. left. reflexivity. }
  pose proof (BProv_Ax_s_ltTermAt_succ_right_cases C
    (tVar 0) oldLimit hltNew) as hcases.
  assert (hltBranch : BProv Ax_s
      (ltTermAt (tVar 0) oldLimit :: C) target).
  {
    set (D := ltTermAt (tVar 0) oldLimit :: C).
    assert (hlt : BProv Ax_s D
        (ltTermAt (tVar 0) (tSucc bound1))).
    { apply BProv_ass. unfold D. simpl. left. reflexivity. }
    assert (hle : BProv Ax_s D
        (leTermAt (tVar 0) bound1)).
    { exact (BProv_Ax_s_leTermAt_of_ltTermAt_succ_right
        D (tVar 0) bound1 hlt). }
    pose proof (BProv_rename_succ_context_cons_of_sentences
      Ax_s sentence_ax_s G antecedent _ hthrough) as hthroughC.
    rewrite rename_hfLtDistinguishesThroughTermAt_succ in hthroughC.
    assert (hthroughD : BProv Ax_s D
        (hfLtDistinguishesThroughTermAt bound1)).
    {
      unfold C, D.
      apply BProv_context_cons.
      exact hthroughC.
    }
    unfold target.
    exact (BProv_Ax_s_hfLtDistinguishesAt_of_throughTermAt
      D bound1 0 hthroughD hle).
  }
  assert (heqBranch : BProv Ax_s
      (pEq (tVar 0) oldLimit :: C) target).
  {
    set (D := pEq (tVar 0) oldLimit :: C).
    assert (heq : BProv Ax_s D (pEq oldLimit (tVar 0))).
    {
      apply BProv_eqSym.
      apply BProv_ass. unfold D. simpl. left. reflexivity.
    }
    pose proof (BProv_rename_succ_context_cons_of_sentences
      Ax_s sentence_ax_s G antecedent _ hnew) as hnewC.
    rewrite rename_hfLtDistinguishesTermAt_succ in hnewC.
    assert (hnewD : BProv Ax_s D
        (hfLtDistinguishesTermAt oldLimit)).
    {
      unfold C, D.
      apply BProv_context_cons.
      exact hnewC.
    }
    assert (htransport : BProv Ax_s D
        (hfLtDistinguishesTermAt (tVar 0))).
    {
      apply (BProv_eqElim Ax_s D
        oldLimit (tVar 0) (hfLtDistinguishesAt 0) heq).
      rewrite subst_instTerm_hfLtDistinguishesAt_zero_term.
      exact hnewD.
    }
    unfold target.
    rewrite hfLtDistinguishesTermAt_var in htransport.
    exact htransport.
  }
  assert (htarget : BProv Ax_s C target).
  { exact (BProv_orE Ax_s C _ _ target hcases hltBranch heqBranch). }
  assert (himp : BProv Ax_s (map (rename S) G)
      (pImp antecedent target)).
  { unfold C in htarget. exact (BProv_impI Ax_s _ _ _ htarget). }
  unfold hfLtDistinguishesThroughTermAt, antecedent, target,
    newLimit, oldLimit, bound1 in *.
  exact (BProv_allI_of_sentences Ax_s G _ sentence_ax_s himp).
Qed.

(** Ordinary PA induction packages a proof of the new endpoint into the
    universal cumulative invariant. *)
Lemma BProv_Ax_s_all_hfLtDistinguishesThroughAt_of_successor_new :
  BProv Ax_s [hfLtDistinguishesThroughAt 0]
    (hfLtDistinguishesTermAt (tSucc (tVar 0))) ->
  BProv Ax_s [] (pAll (hfLtDistinguishesThroughAt 0)).
Proof.
  intro hnew.
  set (phi := hfLtDistinguishesThroughAt 0).
  assert (hzero : BProv Ax_s [] (subst substZero phi)).
  {
    unfold phi.
    rewrite substZero_hfLtDistinguishesThroughAt_zero.
    exact BProv_Ax_s_hfLtDistinguishesThroughTermAt_zero.
  }
  assert (hthrough : BProv Ax_s [phi]
      (hfLtDistinguishesThroughTermAt (tVar 0))).
  {
    unfold phi, hfLtDistinguishesThroughAt.
    apply BProv_ass_head.
  }
  assert (hsuccTerm : BProv Ax_s [phi]
      (hfLtDistinguishesThroughTermAt (tSucc (tVar 0)))).
  {
    apply BProv_Ax_s_hfLtDistinguishesThroughTermAt_succ.
    - exact hthrough.
    - unfold phi in hnew. exact hnew.
  }
  assert (hsuccBody : BProv Ax_s [phi] (subst substSuccVar phi)).
  {
    unfold phi.
    rewrite substSuccVar_hfLtDistinguishesThroughAt_zero.
    exact hsuccTerm.
  }
  assert (hsuccImp : BProv Ax_s []
      (pImp phi (subst substSuccVar phi))).
  { exact (BProv_impI Ax_s [] _ _ hsuccBody). }
  assert (hsuccAll : BProv Ax_s []
      (pAll (pImp phi (subst substSuccVar phi)))).
  { exact (BProv_allI_of_sentences Ax_s [] _ sentence_ax_s hsuccImp). }
  exact (BProv_Ax_s_induction_rule [] phi hzero hsuccAll).
Qed.

Lemma BProv_Ax_s_all_hfLtDistinguishesAt_of_all_through :
  BProv Ax_s [] (pAll (hfLtDistinguishesThroughAt 0)) ->
  BProv Ax_s [] (pAll (hfLtDistinguishesAt 0)).
Proof.
  intro hall.
  pose proof (BProv_allE Ax_s [] _ (tVar 0) hall) as hthroughRaw.
  assert (hthrough : BProv Ax_s []
      (hfLtDistinguishesThroughTermAt (tVar 0))).
  {
    unfold hfLtDistinguishesThroughAt in hthroughRaw.
    change (BProv Ax_s []
      (subst (instTerm (tVar 0))
        (hfLtDistinguishesThroughTermAt (tVar 0)))) in hthroughRaw.
    change (BProv Ax_s []
      (subst (fun n => tVar n)
        (hfLtDistinguishesThroughTermAt (tVar 0)))) in hthroughRaw.
    rewrite subst_id in hthroughRaw.
    exact hthroughRaw.
  }
  assert (hself : BProv Ax_s []
      (leTermAt (tVar 0) (tVar 0))).
  { exact (BProv_Ax_s_leTermAt_refl [] (tVar 0)). }
  assert (hpoint : BProv Ax_s [] (hfLtDistinguishesAt 0)).
  { exact (BProv_Ax_s_hfLtDistinguishesAt_of_throughTermAt
      [] (tVar 0) 0 hthrough hself). }
  exact (BProv_allI_of_sentences Ax_s [] _ sentence_ax_s hpoint).
Qed.

Lemma BProv_Ax_s_translated_HF_extensionality_of_all_through :
  BProv Ax_s [] (pAll (hfLtDistinguishesThroughAt 0)) ->
  BProv Ax_s []
    (translateHFFormula (Fol.seal HF_extensionality_form)).
Proof.
  intro hall.
  exact (BProv_Ax_s_translated_HF_extensionality_of_all_hfLtDistinguishesAt
    (BProv_Ax_s_all_hfLtDistinguishesAt_of_all_through hall)).
Qed.

(* --------------------------------------------------------------------- *)
(* Binary-head order facts used by the one genuinely new induction step. *)

Lemma BProv_Ax_s_leTermAt_add_left :
  forall G a b c,
  BProv Ax_s G (leTermAt b c) ->
  BProv Ax_s G (leTermAt (tAdd a b) (tAdd a c)).
Proof.
  intros G a b c hbc.
  set (target := leTermAt (tAdd a b) (tAdd a c)).
  apply (BProv_Ax_s_leTermAt_elim_opened G b c target); [|exact hbc].
  set (body := pEq (tAdd (Term.rename S b) (tVar 0))
    (Term.rename S c)).
  set (D := body :: map (rename S) G).
  set (a1 := Term.rename S a).
  set (b1 := Term.rename S b).
  set (c1 := Term.rename S c).
  set (d := tVar 0).
  assert (hbcEq : BProv Ax_s D (pEq (tAdd b1 d) c1)).
  { apply BProv_ass. unfold D, body, b1, c1, d. simpl. left. reflexivity. }
  assert (hassoc : BProv Ax_s D
      (pEq (tAdd (tAdd a1 b1) d) (tAdd a1 (tAdd b1 d)))).
  { exact (BProv_Ax_s_add_assoc_terms D a1 b1 d). }
  assert (hcongr : BProv Ax_s D
      (pEq (tAdd a1 (tAdd b1 d)) (tAdd a1 c1))).
  { exact (BProv_eq_congr_add_right Ax_s D a1 _ _ hbcEq). }
  assert (hshape : BProv Ax_s D
      (pEq (tAdd (tAdd a1 b1) d) (tAdd a1 c1))).
  { exact (BProv_eqTrans Ax_s D _ _ _ hassoc hcongr). }
  assert (hle : BProv Ax_s D
      (leTermAt (tAdd a1 b1) (tAdd a1 c1))).
  {
    exact (BProv_Ax_s_leTermAt_of_eq_add_right_terms D
      (tAdd a1 b1) (tAdd a1 c1) d
      (BProv_eqSym Ax_s D _ _ hshape)).
  }
  unfold target.
  rewrite rename_leTermAt.
  unfold a1, b1, c1, d in hle.
  simpl.
  exact hle.
Qed.

Lemma BProv_Ax_s_leTermAt_add_right :
  forall G a b c,
  BProv Ax_s G (leTermAt b c) ->
  BProv Ax_s G (leTermAt (tAdd b a) (tAdd c a)).
Proof.
  intros G a b c hbc.
  pose proof (BProv_Ax_s_leTermAt_add_left G a b c hbc) as hleft.
  exact (BProv_leTermAt_of_eq_right Ax_s G
    (tAdd b a) (tAdd a c) (tAdd c a)
    (BProv_Ax_s_add_comm_terms G a c)
    (BProv_leTermAt_of_eq_left Ax_s G
      (tAdd a b) (tAdd b a) (tAdd a c)
      (BProv_Ax_s_add_comm_terms G a b) hleft)).
Qed.

Lemma BProv_Ax_s_succ_double_le_double_of_ltTermAt :
  forall G highHalf lowHalf,
  BProv Ax_s G (ltTermAt highHalf lowHalf) ->
  BProv Ax_s G
    (leTermAt (tSucc (tAdd highHalf highHalf))
      (tAdd lowHalf lowHalf)).
Proof.
  intros G highHalf lowHalf hlt.
  assert (hsuccLe : BProv Ax_s G
      (leTermAt (tSucc highHalf) lowHalf)).
  { exact (BProv_Ax_s_leTermAt_succ_left_of_ltTermAt
      G highHalf lowHalf hlt). }
  assert (hle : BProv Ax_s G (leTermAt highHalf lowHalf)).
  {
    exact (BProv_Ax_s_leTermAt_trans G highHalf (tSucc highHalf) lowHalf
      (BProv_Ax_s_leTermAt_self_succ G highHalf) hsuccLe).
  }
  assert (hfirst : BProv Ax_s G
      (leTermAt (tAdd highHalf (tSucc highHalf))
        (tAdd highHalf lowHalf))).
  { exact (BProv_Ax_s_leTermAt_add_left G highHalf _ _ hsuccLe). }
  assert (hsecond : BProv Ax_s G
      (leTermAt (tAdd highHalf lowHalf)
        (tAdd lowHalf lowHalf))).
  { exact (BProv_Ax_s_leTermAt_add_right G lowHalf _ _ hle). }
  assert (hsum : BProv Ax_s G
      (leTermAt (tAdd highHalf (tSucc highHalf))
        (tAdd lowHalf lowHalf))).
  { exact (BProv_Ax_s_leTermAt_trans G _ _ _ hfirst hsecond). }
  exact (BProv_leTermAt_of_eq_left Ax_s G
    (tAdd highHalf (tSucc highHalf))
    (tSucc (tAdd highHalf highHalf))
    (tAdd lowHalf lowHalf)
    (BProv_Ax_s_addSucc_terms G highHalf highHalf) hsum).
Qed.

Lemma BProv_Ax_s_leAt_of_half_lt_and_binary_head_bounds :
  forall G high highHalf low lowHalf,
  BProv Ax_s G (ltAt highHalf lowHalf) ->
  BProv Ax_s G
    (leTermAt (tVar high)
      (tSucc (tAdd (tVar highHalf) (tVar highHalf)))) ->
  BProv Ax_s G
    (leTermAt (tAdd (tVar lowHalf) (tVar lowHalf)) (tVar low)) ->
  BProv Ax_s G (leAt high low).
Proof.
  intros G high highHalf low lowHalf hhalfLt hhighUpper hlowLower.
  assert (hmiddle : BProv Ax_s G
      (leTermAt (tSucc (tAdd (tVar highHalf) (tVar highHalf)))
        (tAdd (tVar lowHalf) (tVar lowHalf)))).
  {
    apply BProv_Ax_s_succ_double_le_double_of_ltTermAt.
    rewrite ltTermAt_var.
    exact hhalfLt.
  }
  pose proof (BProv_Ax_s_leTermAt_trans G _ _ _ hhighUpper hmiddle) as h1.
  pose proof (BProv_Ax_s_leTermAt_trans G _ _ _ h1 hlowLower) as hle.
  change (BProv Ax_s G (leAt high low)) in hle.
  exact hle.
Qed.

Lemma BProv_Ax_s_le_succ_double_of_doubleEqAt :
  forall G value half,
  BProv Ax_s G (doubleEqAt value half) ->
  BProv Ax_s G
    (leTermAt (tVar value)
      (tSucc (tAdd (tVar half) (tVar half)))).
Proof.
  intros G value half hdouble.
  assert (heq : BProv Ax_s G
      (pEq (tVar value) (tAdd (tVar half) (tVar half)))).
  { unfold doubleEqAt in hdouble. exact hdouble. }
  exact (BProv_leTermAt_of_eq_left Ax_s G
    (tAdd (tVar half) (tVar half)) (tVar value)
    (tSucc (tAdd (tVar half) (tVar half)))
    (BProv_eqSym Ax_s G _ _ heq)
    (BProv_Ax_s_leTermAt_self_succ G
      (tAdd (tVar half) (tVar half)))).
Qed.

Lemma BProv_Ax_s_le_succ_double_of_oddDoubleEqAt :
  forall G value half,
  BProv Ax_s G (oddDoubleEqAt value half) ->
  BProv Ax_s G
    (leTermAt (tVar value)
      (tSucc (tAdd (tVar half) (tVar half)))).
Proof.
  intros G value half hodd.
  assert (heq : BProv Ax_s G
      (pEq (tVar value)
        (tSucc (tAdd (tVar half) (tVar half))))).
  { unfold oddDoubleEqAt in hodd. exact hodd. }
  exact (BProv_leTermAt_of_eq_left Ax_s G
    (tSucc (tAdd (tVar half) (tVar half))) (tVar value)
    (tSucc (tAdd (tVar half) (tVar half)))
    (BProv_eqSym Ax_s G _ _ heq)
    (BProv_Ax_s_leTermAt_refl G
      (tSucc (tAdd (tVar half) (tVar half))))).
Qed.

Lemma BProv_Ax_s_double_le_of_doubleEqAt :
  forall G value half,
  BProv Ax_s G (doubleEqAt value half) ->
  BProv Ax_s G
    (leTermAt (tAdd (tVar half) (tVar half)) (tVar value)).
Proof.
  intros G value half hdouble.
  assert (heq : BProv Ax_s G
      (pEq (tVar value) (tAdd (tVar half) (tVar half)))).
  { unfold doubleEqAt in hdouble. exact hdouble. }
  exact (BProv_leTermAt_of_eq_right Ax_s G
    (tAdd (tVar half) (tVar half))
    (tAdd (tVar half) (tVar half)) (tVar value)
    (BProv_eqSym Ax_s G _ _ heq)
    (BProv_Ax_s_leTermAt_refl G
      (tAdd (tVar half) (tVar half)))).
Qed.

Lemma BProv_Ax_s_double_le_of_oddDoubleEqAt :
  forall G value half,
  BProv Ax_s G (oddDoubleEqAt value half) ->
  BProv Ax_s G
    (leTermAt (tAdd (tVar half) (tVar half)) (tVar value)).
Proof.
  intros G value half hodd.
  assert (heq : BProv Ax_s G
      (pEq (tVar value)
        (tSucc (tAdd (tVar half) (tVar half))))).
  { unfold oddDoubleEqAt in hodd. exact hodd. }
  exact (BProv_leTermAt_of_eq_right Ax_s G
    (tAdd (tVar half) (tVar half))
    (tSucc (tAdd (tVar half) (tVar half))) (tVar value)
    (BProv_eqSym Ax_s G _ _ heq)
    (BProv_Ax_s_leTermAt_self_succ G
      (tAdd (tVar half) (tVar half)))).
Qed.

Lemma BProv_Ax_s_leAt_of_div2_steps_and_half_lt :
  forall G high highHalf highBit low lowHalf lowBit,
  BProv Ax_s G (div2StepAt high highHalf highBit) ->
  BProv Ax_s G (div2StepAt low lowHalf lowBit) ->
  BProv Ax_s G (ltAt highHalf lowHalf) ->
  BProv Ax_s G (leAt high low).
Proof.
  intros G high highHalf highBit low lowHalf lowBit
    hhighStep hlowStep hhalfLt.
  apply (BProv_Ax_s_of_div2StepAt_double_odd_cases
    G high highHalf highBit (leAt high low) hhighStep).
  - set (GH := doubleEqAt high highHalf :: G).
    assert (hlowStepH : BProv Ax_s GH
        (div2StepAt low lowHalf lowBit)).
    { apply BProv_context_cons. exact hlowStep. }
    apply (BProv_Ax_s_of_div2StepAt_double_odd_cases
      GH low lowHalf lowBit (leAt high low) hlowStepH).
    + set (C := doubleEqAt low lowHalf :: GH).
      apply BProv_Ax_s_leAt_of_half_lt_and_binary_head_bounds
        with (highHalf := highHalf) (lowHalf := lowHalf).
      * unfold C, GH.
        exact (BProv_context_prefix Ax_s
          [doubleEqAt low lowHalf; doubleEqAt high highHalf]
          G _ hhalfLt).
      * apply BProv_Ax_s_le_succ_double_of_doubleEqAt.
        apply BProv_context_cons. apply BProv_ass_head.
      * apply BProv_Ax_s_double_le_of_doubleEqAt.
        apply BProv_ass_head.
    + set (C := oddDoubleEqAt low lowHalf :: GH).
      apply BProv_Ax_s_leAt_of_half_lt_and_binary_head_bounds
        with (highHalf := highHalf) (lowHalf := lowHalf).
      * unfold C, GH.
        exact (BProv_context_prefix Ax_s
          [oddDoubleEqAt low lowHalf; doubleEqAt high highHalf]
          G _ hhalfLt).
      * apply BProv_Ax_s_le_succ_double_of_doubleEqAt.
        apply BProv_context_cons. apply BProv_ass_head.
      * apply BProv_Ax_s_double_le_of_oddDoubleEqAt.
        apply BProv_ass_head.
  - set (GH := oddDoubleEqAt high highHalf :: G).
    assert (hlowStepH : BProv Ax_s GH
        (div2StepAt low lowHalf lowBit)).
    { apply BProv_context_cons. exact hlowStep. }
    apply (BProv_Ax_s_of_div2StepAt_double_odd_cases
      GH low lowHalf lowBit (leAt high low) hlowStepH).
    + set (C := doubleEqAt low lowHalf :: GH).
      apply BProv_Ax_s_leAt_of_half_lt_and_binary_head_bounds
        with (highHalf := highHalf) (lowHalf := lowHalf).
      * unfold C, GH.
        exact (BProv_context_prefix Ax_s
          [doubleEqAt low lowHalf; oddDoubleEqAt high highHalf]
          G _ hhalfLt).
      * apply BProv_Ax_s_le_succ_double_of_oddDoubleEqAt.
        apply BProv_context_cons. apply BProv_ass_head.
      * apply BProv_Ax_s_double_le_of_doubleEqAt.
        apply BProv_ass_head.
    + set (C := oddDoubleEqAt low lowHalf :: GH).
      apply BProv_Ax_s_leAt_of_half_lt_and_binary_head_bounds
        with (highHalf := highHalf) (lowHalf := lowHalf).
      * unfold C, GH.
        exact (BProv_context_prefix Ax_s
          [oddDoubleEqAt low lowHalf; oddDoubleEqAt high highHalf]
          G _ hhalfLt).
      * apply BProv_Ax_s_le_succ_double_of_oddDoubleEqAt.
        apply BProv_context_cons. apply BProv_ass_head.
      * apply BProv_Ax_s_double_le_of_oddDoubleEqAt.
        apply BProv_ass_head.
Qed.

Lemma BProv_Ax_s_eqConstAt_one_of_oddDoubleEqAt_div2StepAt :
  forall G value half bit,
  BProv Ax_s G (oddDoubleEqAt value half) ->
  BProv Ax_s G (div2StepAt value half bit) ->
  BProv Ax_s G (eqConstAt bit 1).
Proof.
  intros G value half bit hodd hstep.
  set (d := tAdd (tVar half) (tVar half)).
  assert (hoddEq : BProv Ax_s G (pEq (tVar value) (tSucc d))).
  { unfold oddDoubleEqAt, d in hodd. exact hodd. }
  assert (hstepEq : BProv Ax_s G
      (pEq (tVar value) (tAdd d (tVar bit)))).
  { unfold div2StepAt, d in hstep. exact (BProv_andE2 Ax_s G _ _ hstep). }
  assert (hbitSucc : BProv Ax_s G
      (pEq (tAdd d (tVar bit)) (tSucc d))).
  { exact (BProv_eqTrans Ax_s G _ _ _
      (BProv_eqSym Ax_s G _ _ hstepEq) hoddEq). }
  assert (haddSucc : BProv Ax_s G
      (pEq (tAdd d (tSucc tZero)) (tSucc (tAdd d tZero)))).
  { exact (BProv_Ax_s_addSucc_terms G d tZero). }
  assert (haddZero : BProv Ax_s G
      (pEq (tSucc (tAdd d tZero)) (tSucc d))).
  { apply BProv_eq_congr_succ. exact (BProv_Ax_s_addZero_term G d). }
  assert (honeSucc : BProv Ax_s G
      (pEq (tAdd d (tSucc tZero)) (tSucc d))).
  { exact (BProv_eqTrans Ax_s G _ _ _ haddSucc haddZero). }
  assert (hsame : BProv Ax_s G
      (pEq (tAdd d (tVar bit)) (tAdd d (tSucc tZero)))).
  { exact (BProv_eqTrans Ax_s G _ _ _ hbitSucc
      (BProv_eqSym Ax_s G _ _ honeSucc)). }
  pose proof (BProv_Ax_s_add_cancel_left_terms G d (tVar bit)
    (tSucc tZero) hsame) as hbit.
  unfold eqConstAt. simpl. exact hbit.
Qed.

Lemma BProv_Ax_s_div2_bits_one_zero_of_lt_and_equal_halves :
  forall G high highHalf highBit low lowHalf lowBit,
  BProv Ax_s G (ltAt low high) ->
  BProv Ax_s G (div2StepAt high highHalf highBit) ->
  BProv Ax_s G (div2StepAt low lowHalf lowBit) ->
  BProv Ax_s G (pEq (tVar lowHalf) (tVar highHalf)) ->
  BProv Ax_s G
    (pAnd (eqConstAt highBit 1) (eqConstAt lowBit 0)).
Proof.
  intros G high highHalf highBit low lowHalf lowBit
    hlt hhighStep hlowStep hhalfEq.
  set (target := pAnd (eqConstAt highBit 1) (eqConstAt lowBit 0)).
  apply (BProv_Ax_s_of_div2StepAt_double_odd_cases
    G high highHalf highBit target hhighStep).
  - set (GH := doubleEqAt high highHalf :: G).
    assert (hlowStepH : BProv Ax_s GH (div2StepAt low lowHalf lowBit)).
    { apply BProv_context_cons. exact hlowStep. }
    apply (BProv_Ax_s_of_div2StepAt_double_odd_cases
      GH low lowHalf lowBit target hlowStepH).
    + set (C := doubleEqAt low lowHalf :: GH).
      assert (hhigh : BProv Ax_s C (doubleEqAt high highHalf)).
      { apply BProv_context_cons. apply BProv_ass_head. }
      assert (hlow : BProv Ax_s C (doubleEqAt low lowHalf)).
      { apply BProv_ass_head. }
      assert (hhalfEqC : BProv Ax_s C
          (pEq (tVar lowHalf) (tVar highHalf))).
      { unfold C, GH. exact (BProv_context_prefix Ax_s
          [doubleEqAt low lowHalf; doubleEqAt high highHalf]
          G _ hhalfEq). }
      assert (hltC : BProv Ax_s C (ltAt low high)).
      { unfold C, GH. exact (BProv_context_prefix Ax_s
          [doubleEqAt low lowHalf; doubleEqAt high highHalf]
          G _ hlt). }
      assert (hhalves : BProv Ax_s C
          (pEq (tAdd (tVar lowHalf) (tVar lowHalf))
            (tAdd (tVar highHalf) (tVar highHalf)))).
      { exact (BProv_eq_congr_add Ax_s C _ _ _ _ hhalfEqC hhalfEqC). }
      assert (hheads : BProv Ax_s C (pEq (tVar high) (tVar low))).
      {
        exact (BProv_eqTrans Ax_s C _ _ _ hhigh
          (BProv_eqTrans Ax_s C _ _ _
            (BProv_eqSym Ax_s C _ _ hhalves)
            (BProv_eqSym Ax_s C _ _ hlow))).
      }
      exact (BProv_botE Ax_s C target
        (BProv_Ax_s_ltAt_eq_bot C low high hltC hheads)).
    + set (C := oddDoubleEqAt low lowHalf :: GH).
      assert (hhigh : BProv Ax_s C (doubleEqAt high highHalf)).
      { apply BProv_context_cons. apply BProv_ass_head. }
      assert (hlow : BProv Ax_s C (oddDoubleEqAt low lowHalf)).
      { apply BProv_ass_head. }
      assert (hhalfEqC : BProv Ax_s C
          (pEq (tVar lowHalf) (tVar highHalf))).
      { unfold C, GH. exact (BProv_context_prefix Ax_s
          [oddDoubleEqAt low lowHalf; doubleEqAt high highHalf]
          G _ hhalfEq). }
      assert (hltC : BProv Ax_s C (ltAt low high)).
      { unfold C, GH. exact (BProv_context_prefix Ax_s
          [oddDoubleEqAt low lowHalf; doubleEqAt high highHalf]
          G _ hlt). }
      assert (hhalves : BProv Ax_s C
          (pEq (tAdd (tVar lowHalf) (tVar lowHalf))
            (tAdd (tVar highHalf) (tVar highHalf)))).
      { exact (BProv_eq_congr_add Ax_s C _ _ _ _ hhalfEqC hhalfEqC). }
      assert (hhighToLowDouble : BProv Ax_s C
          (pEq (tVar high) (tAdd (tVar lowHalf) (tVar lowHalf)))).
      { exact (BProv_eqTrans Ax_s C _ _ _ hhigh
          (BProv_eqSym Ax_s C _ _ hhalves)). }
      assert (hheadLeTerm : BProv Ax_s C
          (leTermAt (tVar high) (tVar low))).
      {
        apply (BProv_leTermAt_of_eq_right Ax_s C
          (tVar high)
          (tSucc (tAdd (tVar lowHalf) (tVar lowHalf))) (tVar low)).
        - exact (BProv_eqSym Ax_s C _ _ hlow).
        - apply (BProv_leTermAt_of_eq_left Ax_s C
            (tAdd (tVar lowHalf) (tVar lowHalf)) (tVar high)
            (tSucc (tAdd (tVar lowHalf) (tVar lowHalf)))).
          + exact (BProv_eqSym Ax_s C _ _ hhighToLowDouble).
          + apply BProv_Ax_s_leTermAt_self_succ.
      }
      change (BProv Ax_s C (leAt high low)) in hheadLeTerm.
      exact (BProv_botE Ax_s C target
        (BProv_Ax_s_ltAt_leAt_bot C low high hltC hheadLeTerm)).
  - set (GH := oddDoubleEqAt high highHalf :: G).
    assert (hlowStepH : BProv Ax_s GH (div2StepAt low lowHalf lowBit)).
    { apply BProv_context_cons. exact hlowStep. }
    apply (BProv_Ax_s_of_div2StepAt_double_odd_cases
      GH low lowHalf lowBit target hlowStepH).
    + set (C := doubleEqAt low lowHalf :: GH).
      assert (hhigh : BProv Ax_s C (oddDoubleEqAt high highHalf)).
      { apply BProv_context_cons. apply BProv_ass_head. }
      assert (hlow : BProv Ax_s C (doubleEqAt low lowHalf)).
      { apply BProv_ass_head. }
      assert (hhighStepC : BProv Ax_s C
          (div2StepAt high highHalf highBit)).
      { unfold C, GH. exact (BProv_context_prefix Ax_s
          [doubleEqAt low lowHalf; oddDoubleEqAt high highHalf]
          G _ hhighStep). }
      assert (hlowStepC : BProv Ax_s C
          (div2StepAt low lowHalf lowBit)).
      { unfold C, GH. exact (BProv_context_prefix Ax_s
          [doubleEqAt low lowHalf; oddDoubleEqAt high highHalf]
          G _ hlowStep). }
      exact (BProv_andI Ax_s C _ _
        (BProv_Ax_s_eqConstAt_one_of_oddDoubleEqAt_div2StepAt
          C high highHalf highBit hhigh hhighStepC)
        (BProv_Ax_s_eqConstAt_zero_of_div2StepAt_double
          C low lowHalf lowBit hlow hlowStepC)).
    + set (C := oddDoubleEqAt low lowHalf :: GH).
      assert (hhigh : BProv Ax_s C (oddDoubleEqAt high highHalf)).
      { apply BProv_context_cons. apply BProv_ass_head. }
      assert (hlow : BProv Ax_s C (oddDoubleEqAt low lowHalf)).
      { apply BProv_ass_head. }
      assert (hhalfEqC : BProv Ax_s C
          (pEq (tVar lowHalf) (tVar highHalf))).
      { unfold C, GH. exact (BProv_context_prefix Ax_s
          [oddDoubleEqAt low lowHalf; oddDoubleEqAt high highHalf]
          G _ hhalfEq). }
      assert (hltC : BProv Ax_s C (ltAt low high)).
      { unfold C, GH. exact (BProv_context_prefix Ax_s
          [oddDoubleEqAt low lowHalf; oddDoubleEqAt high highHalf]
          G _ hlt). }
      assert (hhalves : BProv Ax_s C
          (pEq (tSucc (tAdd (tVar lowHalf) (tVar lowHalf)))
            (tSucc (tAdd (tVar highHalf) (tVar highHalf))))).
      { apply BProv_eq_congr_succ.
        exact (BProv_eq_congr_add Ax_s C _ _ _ _ hhalfEqC hhalfEqC). }
      assert (hheads : BProv Ax_s C (pEq (tVar high) (tVar low))).
      {
        exact (BProv_eqTrans Ax_s C _ _ _ hhigh
          (BProv_eqTrans Ax_s C _ _ _
            (BProv_eqSym Ax_s C _ _ hhalves)
            (BProv_eqSym Ax_s C _ _ hlow))).
      }
      exact (BProv_botE Ax_s C target
        (BProv_Ax_s_ltAt_eq_bot C low high hltC hheads)).
Qed.

Lemma BProv_Ax_s_div2_order_cases :
  forall G high highHalf highBit low lowHalf lowBit,
  BProv Ax_s G (ltAt low high) ->
  BProv Ax_s G (div2StepAt high highHalf highBit) ->
  BProv Ax_s G (div2StepAt low lowHalf lowBit) ->
  BProv Ax_s G
    (pOr (ltAt lowHalf highHalf)
      (pAnd (pEq (tVar lowHalf) (tVar highHalf))
        (pAnd (eqConstAt highBit 1) (eqConstAt lowBit 0)))).
Proof.
  intros G high highHalf highBit low lowHalf lowBit
    hlt hhighStep hlowStep.
  set (target := pOr (ltAt lowHalf highHalf)
    (pAnd (pEq (tVar lowHalf) (tVar highHalf))
      (pAnd (eqConstAt highBit 1) (eqConstAt lowBit 0)))).
  pose proof (BProv_Ax_s_leAt_or_gtAt G lowHalf highHalf) as hcmp.
  assert (hleBranch : BProv Ax_s (leAt lowHalf highHalf :: G) target).
  {
    set (C := leAt lowHalf highHalf :: G).
    pose proof (BProv_Ax_s_leAt_or_gtAt C highHalf lowHalf) as hcmp'.
    assert (heqBranch : BProv Ax_s (leAt highHalf lowHalf :: C) target).
    {
      set (D := leAt highHalf lowHalf :: C).
      assert (hleLowHigh : BProv Ax_s D (leAt lowHalf highHalf)).
      { apply BProv_context_cons. apply BProv_ass_head. }
      assert (hleHighLow : BProv Ax_s D (leAt highHalf lowHalf)).
      { apply BProv_ass_head. }
      assert (hhalfEq : BProv Ax_s D
          (pEq (tVar lowHalf) (tVar highHalf))).
      { apply BProv_eqSym. exact (BProv_Ax_s_eq_of_leAt_leAt
          D highHalf lowHalf hleHighLow hleLowHigh). }
      assert (hltD : BProv Ax_s D (ltAt low high)).
      { unfold D, C. exact (BProv_context_prefix Ax_s
          [leAt highHalf lowHalf; leAt lowHalf highHalf]
          G _ hlt). }
      assert (hhighStepD : BProv Ax_s D
          (div2StepAt high highHalf highBit)).
      { unfold D, C. exact (BProv_context_prefix Ax_s
          [leAt highHalf lowHalf; leAt lowHalf highHalf]
          G _ hhighStep). }
      assert (hlowStepD : BProv Ax_s D
          (div2StepAt low lowHalf lowBit)).
      { unfold D, C. exact (BProv_context_prefix Ax_s
          [leAt highHalf lowHalf; leAt lowHalf highHalf]
          G _ hlowStep). }
      assert (hbits : BProv Ax_s D
          (pAnd (eqConstAt highBit 1) (eqConstAt lowBit 0))).
      { exact (BProv_Ax_s_div2_bits_one_zero_of_lt_and_equal_halves
          D high highHalf highBit low lowHalf lowBit
          hltD hhighStepD hlowStepD hhalfEq). }
      apply BProv_orI2.
      exact (BProv_andI Ax_s D _ _ hhalfEq hbits).
    }
    assert (hltBranch : BProv Ax_s (ltAt lowHalf highHalf :: C) target).
    { apply BProv_orI1. apply BProv_ass_head. }
    exact (BProv_orE Ax_s C _ _ target hcmp' heqBranch hltBranch).
  }
  assert (hgtBranch : BProv Ax_s (ltAt highHalf lowHalf :: G) target).
  {
    set (C := ltAt highHalf lowHalf :: G).
    assert (hhalfLt : BProv Ax_s C (ltAt highHalf lowHalf)).
    { apply BProv_ass_head. }
    assert (hhighStepC : BProv Ax_s C
        (div2StepAt high highHalf highBit)).
    { apply BProv_context_cons. exact hhighStep. }
    assert (hlowStepC : BProv Ax_s C
        (div2StepAt low lowHalf lowBit)).
    { apply BProv_context_cons. exact hlowStep. }
    assert (hheadLe : BProv Ax_s C (leAt high low)).
    { exact (BProv_Ax_s_leAt_of_div2_steps_and_half_lt
        C high highHalf highBit low lowHalf lowBit
        hhighStepC hlowStepC hhalfLt). }
    assert (hltC : BProv Ax_s C (ltAt low high)).
    { apply BProv_context_cons. exact hlt. }
    exact (BProv_botE Ax_s C target
      (BProv_Ax_s_ltAt_leAt_bot C low high hltC hheadLe)).
  }
  exact (BProv_orE Ax_s G _ _ target hcmp hleBranch hgtBranch).
Qed.

Lemma BProv_hfSomeDistinguishesAt_intro_term :
  forall B G high low elem,
  BProv B G
    (subst (instTerm elem)
      (hfDistinguishesAt 0 (S high) (S low))) ->
  BProv B G (hfSomeDistinguishesAt high low).
Proof.
  intros B G high low elem hdist.
  unfold hfSomeDistinguishesAt.
  exact (BProv_exI B G
    (hfDistinguishesAt 0 (S high) (S low)) elem hdist).
Qed.

Lemma BProv_hfSomeDistinguishesAt_elim :
  forall B,
  Sentences B ->
  forall G target high low,
  BProv B G (hfSomeDistinguishesAt high low) ->
  BProv B
    (hfDistinguishesAt 0 (S high) (S low) :: map (rename S) G)
    (rename S target) ->
  BProv B G target.
Proof.
  intros B hB G target high low hsome hbody.
  unfold hfSomeDistinguishesAt in hsome.
  exact (BProv_exE_of_sentences B G
    (hfDistinguishesAt 0 (S high) (S low)) target
    hB hsome hbody).
Qed.

Lemma BProv_hfDistinguishesTermAt_of_high_eq_term :
  forall B G elem low oldCode newCode,
  BProv B G (hfDistinguishesTermAt elem oldCode low) ->
  BProv B G (pEq oldCode newCode) ->
  BProv B G (hfDistinguishesTermAt elem newCode low).
Proof.
  intros B G elem low oldCode newCode hdist hhigh.
  unfold hfDistinguishesTermAt in hdist |-.
  pose proof (BProv_andE1 B G _ _ hdist) as hmem.
  pose proof (BProv_andE2 B G _ _ hdist) as hnot.
  exact (BProv_andI B G _ _
    (BProv_hfMemTermAt_of_hfMemTermAt_eq_term
      B G elem oldCode newCode hmem hhigh) hnot).
Qed.

Lemma BProv_hfSomeDistinguishesTermAt_of_high_eq_term :
  forall B,
  Sentences B ->
  forall G oldCode newCode low,
  BProv B G (hfSomeDistinguishesTermAt oldCode low) ->
  BProv B G (pEq oldCode newCode) ->
  BProv B G (hfSomeDistinguishesTermAt newCode low).
Proof.
  intros B hB G oldCode newCode low hsome hhigh.
  set (witness := hfDistinguishesTermAt 0
    (Term.rename S oldCode) (S low)).
  set (target := hfSomeDistinguishesTermAt newCode low).
  assert (hbody : BProv B (witness :: map (rename S) G)
      (rename S target)).
  {
    set (C := witness :: map (rename S) G).
    assert (hdist : BProv B C
        (hfDistinguishesTermAt 0 (Term.rename S oldCode) (S low))).
    { apply BProv_ass. unfold C, witness. simpl. left. reflexivity. }
    pose proof (BProv_rename_succ_context_cons_of_sentences
      B hB G witness (pEq oldCode newCode) hhigh) as hhighC.
    assert (hdistNew : BProv B C
        (hfDistinguishesTermAt 0 (Term.rename S newCode) (S low))).
    {
      apply (BProv_hfDistinguishesTermAt_of_high_eq_term
        B C 0 (S low) (Term.rename S oldCode) (Term.rename S newCode)
        hdist).
      unfold C, witness in hhighC.
      simpl in hhighC.
      exact hhighC.
    }
    pose proof (BProv_hfSomeDistinguishesTermAt_intro_var
      B C 0 (S low) (Term.rename S newCode) hdistNew) as hsomeNew.
    unfold target, C, witness.
    rewrite rename_hfSomeDistinguishesTermAt_succ.
    exact hsomeNew.
  }
  unfold hfSomeDistinguishesTermAt in hsome.
  unfold witness, target in *.
  exact (BProv_exE_of_sentences B G
    (hfDistinguishesTermAt 0 (Term.rename S oldCode) (S low))
    (hfSomeDistinguishesTermAt newCode low) hB hsome hbody).
Qed.

(** The two compact trace facts consumed by the binary induction step.
    They are proved by the prepend/shift trace modules; keeping these
    interfaces explicit lets the logical assembly remain independent of the
    internal CRT witness layout. *)
Definition HFMembershipSuccLift : Prop :=
  forall G head tailCode headBit,
  BProv Ax_s G (div2StepAt head tailCode headBit) ->
  BProv Ax_s G (hfMemAt 0 tailCode) ->
  BProv Ax_s G
    (subst (instTerm (tSucc (tVar 0))) (hfMemAt 0 (S head))).

Definition hfMembershipSuccLift : HFMembershipSuccLift.
Proof.
  intros G head tailCode headBit hstep hmem.
  assert (hstepTerm : BProv Ax_s G
      (div2StepTermAt (tVar head) (tVar tailCode) (tVar headBit))).
  { rewrite div2StepTermAt_var. exact hstep. }
  assert (hmemTerm : BProv Ax_s G (hfMemTermAt 0 (tVar tailCode))).
  { rewrite hfMemTermAt_var. exact hmem. }
  pose proof (BProv_Ax_s_hfMemTermAt_succ_of_div2StepTermAt
    G (tVar head) (tVar tailCode) (tVar headBit)
    hstepTerm hmemTerm) as h.
  change (BProv Ax_s G
    (subst (instTerm (tSucc (tVar 0)))
      (hfMemAt 0 (S head)))) in h.
  exact h.
Defined.

Definition HFMembershipZeroLift : Prop :=
  forall G elem head half bit,
  BProv Ax_s G (eqConstAt elem 0) ->
  BProv Ax_s G (eqConstAt bit 1) ->
  BProv Ax_s G (div2StepAt head half bit) ->
  BProv Ax_s G (hfMemAt elem head).

Definition hfMembershipZeroLift : HFMembershipZeroLift :=
  BProv_Ax_s_hfMemAt_of_eqConst_zero_and_div2StepAt_bit_one.

Definition HFMembershipZeroExclusion : Prop :=
  forall G elem head half,
  BProv Ax_s G (eqConstAt elem 0) ->
  BProv Ax_s G (doubleEqAt head half) ->
  BProv Ax_s G (hfMemAt elem head) ->
  BProv Ax_s G pBot.

Definition hfMembershipZeroExclusion : HFMembershipZeroExclusion :=
  BProv_Ax_s_hfMemAt_bot_of_eqConst_zero_elem_low_double.

Lemma BProv_Ax_s_hfSomeDistinguishesAt_of_div2_steps_and_half_distinguishes :
  HFMembershipSuccLift ->
  forall G high low highHalf lowHalf highBit lowBit,
  BProv Ax_s G (div2StepAt high highHalf highBit) ->
  BProv Ax_s G (div2StepAt low lowHalf lowBit) ->
  BProv Ax_s G (hfSomeDistinguishesAt highHalf lowHalf) ->
  BProv Ax_s G (hfSomeDistinguishesAt high low).
Proof.
  intros hlift G high low highHalf lowHalf highBit lowBit
    hhighStep hlowStep hhalf.
  set (target := hfSomeDistinguishesAt high low).
  apply (BProv_hfSomeDistinguishesAt_elim Ax_s sentence_ax_s
    G target highHalf lowHalf hhalf).
  set (witness := hfDistinguishesAt 0 (S highHalf) (S lowHalf)).
  set (C := witness :: map (rename S) G).
  assert (hwitness : BProv Ax_s C witness).
  { apply BProv_ass. unfold C. simpl. left. reflexivity. }
  assert (hhalfHigh : BProv Ax_s C (hfMemAt 0 (S highHalf))).
  { unfold witness, hfDistinguishesAt in hwitness.
    exact (BProv_andE1 Ax_s C _ _ hwitness). }
  pose proof (BProv_rename_succ_context_cons_of_sentences
    Ax_s sentence_ax_s G witness _ hhighStep) as hhighStepC.
  rewrite rename_S_div2StepAt in hhighStepC.
  assert (hhighMem : BProv Ax_s C
      (subst (instTerm (tSucc (tVar 0))) (hfMemAt 0 (S (S high))))).
  { exact (hlift C (S high) (S highHalf) (S highBit)
      hhighStepC hhalfHigh). }
  assert (hnotHalfLow : BProv Ax_s C
      (pImp (hfMemAt 0 (S lowHalf)) pBot)).
  { unfold witness, hfDistinguishesAt in hwitness.
    exact (BProv_andE2 Ax_s C _ _ hwitness). }
  set (lowSuccMem :=
    subst (instTerm (tSucc (tVar 0))) (hfMemAt 0 (S (S low)))).
  set (D := lowSuccMem :: C).
  pose proof (BProv_rename_succ_context_cons_of_sentences
    Ax_s sentence_ax_s G witness _ hlowStep) as hlowStepC.
  rewrite rename_S_div2StepAt in hlowStepC.
  assert (hlowStepD : BProv Ax_s D
      (div2StepAt (S low) (S lowHalf) (S lowBit))).
  { unfold D, C. apply BProv_context_cons. exact hlowStepC. }
  assert (hlowSuccMem : BProv Ax_s D
      (subst (instTerm (tSucc (tVar 0))) (hfMemAt 0 (S (S low))))).
  { apply BProv_ass. unfold D, lowSuccMem. simpl. left. reflexivity. }
  assert (hlowHalfMem : BProv Ax_s D (hfMemAt 0 (S lowHalf))).
  { exact (BProv_Ax_s_hfMemAt_tail_of_succ_mem_and_div2StepAt
      D (S low) (S lowHalf) (S lowBit) hlowStepD hlowSuccMem). }
  assert (hnotHalfLowD : BProv Ax_s D
      (pImp (hfMemAt 0 (S lowHalf)) pBot)).
  { unfold D. apply BProv_context_cons. exact hnotHalfLow. }
  assert (hlowBot : BProv Ax_s D pBot).
  { exact (BProv_mp Ax_s D _ _ hnotHalfLowD hlowHalfMem). }
  assert (hnotLow : BProv Ax_s C (pImp lowSuccMem pBot)).
  { unfold D in hlowBot. exact (BProv_impI Ax_s C _ _ hlowBot). }
  assert (hdist : BProv Ax_s C
      (subst (instTerm (tSucc (tVar 0)))
        (hfDistinguishesAt 0 (S (S high)) (S (S low))))).
  {
    unfold hfDistinguishesAt.
    simpl.
    exact (BProv_andI Ax_s C _ _ hhighMem hnotLow).
  }
  assert (hsome : BProv Ax_s C
      (hfSomeDistinguishesAt (S high) (S low))).
  { exact (BProv_hfSomeDistinguishesAt_intro_term
      Ax_s C (S high) (S low) (tSucc (tVar 0)) hdist). }
  unfold target, C, witness.
  rewrite rename_hfSomeDistinguishesAt_succ.
  exact hsome.
Qed.

Lemma BProv_Ax_s_hfSomeDistinguishesAt_of_div2_bits_one_zero :
  HFMembershipZeroLift ->
  HFMembershipZeroExclusion ->
  forall G high highHalf highBit low lowHalf lowBit,
  BProv Ax_s G (eqConstAt highBit 1) ->
  BProv Ax_s G (div2StepAt high highHalf highBit) ->
  BProv Ax_s G (eqConstAt lowBit 0) ->
  BProv Ax_s G (div2StepAt low lowHalf lowBit) ->
  BProv Ax_s G (hfSomeDistinguishesAt high low).
Proof.
  intros hzero hzeroNot G high highHalf highBit low lowHalf lowBit
    hhighBit hhighStep hlowBit hlowStep.
  assert (hlowDouble : BProv Ax_s G (doubleEqAt low lowHalf)).
  { exact (BProv_Ax_s_doubleEqAt_of_div2StepAt_bit_zero
      G low lowHalf lowBit hlowBit hlowStep). }
  set (zeroEq := eqConstAt 0 0).
  pose proof (BProv_exists_eqConstAt Ax_s G 0) as hex.
  apply (BProv_exE_of_sentences Ax_s G zeroEq
    (hfSomeDistinguishesAt high low) sentence_ax_s hex).
  set (C := zeroEq :: map (rename S) G).
  assert (hzeroEq : BProv Ax_s C (eqConstAt 0 0)).
  { apply BProv_ass. unfold C, zeroEq. simpl. left. reflexivity. }
  pose proof (BProv_rename_succ_context_cons_of_sentences
    Ax_s sentence_ax_s G zeroEq _ hhighBit) as hhighBitC.
  unfold eqConstAt in hhighBitC.
  simpl in hhighBitC.
  pose proof (BProv_rename_succ_context_cons_of_sentences
    Ax_s sentence_ax_s G zeroEq _ hhighStep) as hhighStepC.
  rewrite rename_S_div2StepAt in hhighStepC.
  assert (hhighMem : BProv Ax_s C (hfMemAt 0 (S high))).
  { exact (hzero C 0 (S high) (S highHalf) (S highBit)
      hzeroEq hhighBitC hhighStepC). }
  pose proof (BProv_rename_succ_context_cons_of_sentences
    Ax_s sentence_ax_s G zeroEq _ hlowDouble) as hlowDoubleC.
  assert (hnotLow : BProv Ax_s C
      (pImp (hfMemAt 0 (S low)) pBot)).
  {
    apply BProv_impI.
    set (D := hfMemAt 0 (S low) :: C).
    exact (hzeroNot D 0 (S low) (S lowHalf)
      (BProv_context_cons Ax_s C (hfMemAt 0 (S low)) _ hzeroEq)
      (BProv_context_cons Ax_s C (hfMemAt 0 (S low)) _ hlowDoubleC)
      (BProv_ass Ax_s D (hfMemAt 0 (S low)) (or_introl eq_refl))).
  }
  assert (hdist : BProv Ax_s C
      (hfDistinguishesAt 0 (S high) (S low))).
  { exact (BProv_hfDistinguishesAt_of_mem_and_not_mem
      Ax_s C 0 (S high) (S low) hhighMem hnotLow). }
  pose proof (BProv_hfSomeDistinguishesAt_intro_var
    Ax_s C 0 (S high) (S low) hdist) as hsome.
  unfold C, zeroEq.
  rewrite rename_hfSomeDistinguishesAt_succ.
  exact hsome.
Qed.

(** The one genuinely new code of the cumulative induction.  Both binary
    heads are opened once.  Strictly ordered halves use the cumulative
    hypothesis; equal halves are settled by their head bits. *)
Lemma BProv_Ax_s_hfLtDistinguishesTermAt_succ_of_through_zero_of_membership :
  HFMembershipSuccLift ->
  HFMembershipZeroLift ->
  HFMembershipZeroExclusion ->
  BProv Ax_s [hfLtDistinguishesThroughAt 0]
    (hfLtDistinguishesTermAt (tSucc (tVar 0))).
Proof.
  intros hlift hzero hzeroNot.
  set (through := hfLtDistinguishesThroughAt 0).
  set (G := [through]).
  set (highCode := tSucc (tVar 1)).
  set (lowLtHigh := ltTermAt (tVar 0) highCode).
  set (target := hfSomeDistinguishesTermAt highCode 0).
  assert (himp : BProv Ax_s (map (rename S) G)
      (pImp lowLtHigh target)).
  {
    set (C := lowLtHigh :: map (rename S) G).
    set (highEqBody := pEq (tVar 0) (Term.rename S highCode)).
    assert (hhighEqEx : BProv Ax_s C (pEx highEqBody)).
    {
      apply (BProv_exI Ax_s C highEqBody highCode).
      unfold highEqBody.
      simpl.
      apply BProv_eqRefl.
    }
    assert (htarget : BProv Ax_s C target).
    {
      apply (BProv_exE_of_sentences Ax_s C highEqBody target
        sentence_ax_s hhighEqEx).
      set (H := highEqBody :: map (rename S) C).
      set (slotTarget := hfSomeDistinguishesAt 0 1).
      assert (hslot : BProv Ax_s H slotTarget).
      {
        apply (BProv_Ax_s_of_div2TotalAt_opened_step
          H 0 slotTarget (BProv_Ax_s_div2TotalAt H 0)).
        set (HH := div2TotalOpenedStepContext H 0).
        set (target2 := rename S (rename S slotTarget)).
        apply (BProv_Ax_s_of_div2TotalAt_opened_step
          HH 3 target2 (BProv_Ax_s_div2TotalAt HH 3)).
        set (K := div2TotalOpenedStepContext HH 3).
      assert (hhighStep : BProv Ax_s K (div2StepAt 4 3 2)).
      { apply BProv_ass. unfold K, HH, H, C, G,
          div2TotalOpenedStepContext. simpl. right. right. left. reflexivity. }
      assert (hlowStep : BProv Ax_s K (div2StepAt 5 1 0)).
      { apply BProv_ass. unfold K, div2TotalOpenedStepContext.
        simpl. left. reflexivity. }
      assert (hhighEq : BProv Ax_s K
          (pEq (tVar 4) (tSucc (tVar 6)))).
      { apply BProv_ass. unfold K, HH, H, C, highEqBody, highCode,
          div2TotalOpenedStepContext. simpl.
        right. right. right. right. left. reflexivity. }
      assert (hltRaw : BProv Ax_s K
          (ltTermAt (tVar 5) (tSucc (tVar 6)))).
      { apply BProv_ass. unfold K, HH, H, C, lowLtHigh, highCode,
          div2TotalOpenedStepContext. simpl.
        right. right. right. right. right. left. reflexivity. }
      assert (hlt : BProv Ax_s K (ltAt 5 4)).
      {
        change (BProv Ax_s K
          (ltTermAt (tVar 5) (tVar 4))).
        exact (BProv_ltTermAt_of_eq_right Ax_s K
          (tVar 5) (tSucc (tVar 6)) (tVar 4)
          (BProv_eqSym Ax_s K _ _ hhighEq) hltRaw).
      }
      assert (hthrough : BProv Ax_s K
          (hfLtDistinguishesThroughTermAt (tVar 6))).
      {
        apply BProv_ass.
        unfold K, HH, H, C, G, through,
          div2TotalOpenedStepContext, hfLtDistinguishesThroughAt.
        simpl. right. right. right. right. right. right. left. reflexivity.
      }
      pose proof (BProv_Ax_s_div2_order_cases K
        4 3 2 5 1 0 hlt hhighStep hlowStep) as hcases.
      assert (hstrict : BProv Ax_s (ltAt 1 3 :: K)
          (hfSomeDistinguishesAt 4 5)).
      {
        set (Sctx := ltAt 1 3 :: K).
        assert (hhalfLt : BProv Ax_s Sctx (ltAt 1 3)).
        { apply BProv_ass. unfold Sctx. simpl. left. reflexivity. }
        assert (hhighStepS : BProv Ax_s Sctx (div2StepAt 4 3 2)).
        { apply BProv_context_cons. exact hhighStep. }
        assert (hlowStepS : BProv Ax_s Sctx (div2StepAt 5 1 0)).
        { apply BProv_context_cons. exact hlowStep. }
        assert (hhighEqS : BProv Ax_s Sctx
            (pEq (tVar 4) (tSucc (tVar 6)))).
        { apply BProv_context_cons. exact hhighEq. }
        assert (hhalfLe : BProv Ax_s Sctx
            (leTermAt (tVar 3) (tVar 6))).
        { exact (BProv_Ax_s_leTermAt_half_of_div2StepAt_eq_succ
            Sctx 4 3 2 (tVar 6) hhighStepS hhighEqS). }
        assert (hthroughS : BProv Ax_s Sctx
            (hfLtDistinguishesThroughTermAt (tVar 6))).
        { apply BProv_context_cons. exact hthrough. }
        assert (hallHalf : BProv Ax_s Sctx (hfLtDistinguishesAt 3)).
        { exact (BProv_Ax_s_hfLtDistinguishesAt_of_throughTermAt
            Sctx (tVar 6) 3 hthroughS hhalfLe). }
        assert (hhalfSome : BProv Ax_s Sctx
            (hfSomeDistinguishesAt 3 1)).
        { exact (BProv_hfSomeDistinguishesAt_of_hfLtDistinguishesAt
            Ax_s Sctx 1 3 hallHalf hhalfLt). }
        exact (BProv_Ax_s_hfSomeDistinguishesAt_of_div2_steps_and_half_distinguishes
          hlift Sctx 4 5 3 1 2 0
          hhighStepS hlowStepS hhalfSome).
      }
      assert (htie : BProv Ax_s
          (pAnd (pEq (tVar 1) (tVar 3))
            (pAnd (eqConstAt 2 1) (eqConstAt 0 0)) :: K)
          (hfSomeDistinguishesAt 4 5)).
      {
        set (tie := pAnd (pEq (tVar 1) (tVar 3))
          (pAnd (eqConstAt 2 1) (eqConstAt 0 0))).
        set (T := tie :: K).
        assert (htieAss : BProv Ax_s T tie).
        { apply BProv_ass. unfold T. simpl. left. reflexivity. }
        pose proof (BProv_andE2 Ax_s T _ _ htieAss) as hbits.
        pose proof (BProv_andE1 Ax_s T _ _ hbits) as hhighBit.
        pose proof (BProv_andE2 Ax_s T _ _ hbits) as hlowBit.
        exact (BProv_Ax_s_hfSomeDistinguishesAt_of_div2_bits_one_zero
          hzero hzeroNot T 4 3 2 5 1 0
          hhighBit
          (BProv_context_cons Ax_s K tie _ hhighStep)
          hlowBit
          (BProv_context_cons Ax_s K tie _ hlowStep)).
      }
      pose proof (BProv_orE Ax_s K _ _ (hfSomeDistinguishesAt 4 5)
        hcases hstrict htie) as hresult.
      unfold K, HH, H, C, G, through, highEqBody, highCode,
        lowLtHigh, target, slotTarget, target2,
        div2TotalOpenedStepContext in hresult |-.
      simpl in hresult |-.
        exact hresult.
      }
      assert (hslotTerm : BProv Ax_s H
          (hfSomeDistinguishesTermAt (tVar 0) 1)).
      { rewrite hfSomeDistinguishesTermAt_var. exact hslot. }
      assert (hhighEq : BProv Ax_s H
          (pEq (tVar 0) (Term.rename S highCode))).
      { apply BProv_ass. unfold H, highEqBody. simpl. left. reflexivity. }
      assert (htransport : BProv Ax_s H
          (hfSomeDistinguishesTermAt (Term.rename S highCode) 1)).
      { exact (BProv_hfSomeDistinguishesTermAt_of_high_eq_term
          Ax_s sentence_ax_s H (tVar 0) (Term.rename S highCode) 1
          hslotTerm hhighEq). }
      unfold target.
      rewrite rename_hfSomeDistinguishesTermAt_succ.
      exact htransport.
    }
    unfold C in htarget.
    exact (BProv_impI Ax_s (map (rename S) G) lowLtHigh target htarget).
  }
  assert (hall : BProv Ax_s G (pAll (pImp lowLtHigh target))).
  { exact (BProv_allI_of_sentences Ax_s G _ sentence_ax_s himp). }
  unfold G, through, hfLtDistinguishesTermAt, highCode,
    lowLtHigh, target in hall |-.
  exact hall.
Qed.

Lemma BProv_Ax_s_all_hfLtDistinguishesThroughAt_of_membership :
  HFMembershipSuccLift ->
  HFMembershipZeroLift ->
  HFMembershipZeroExclusion ->
  BProv Ax_s [] (pAll (hfLtDistinguishesThroughAt 0)).
Proof.
  intros hlift hzero hzeroNot.
  apply BProv_Ax_s_all_hfLtDistinguishesThroughAt_of_successor_new.
  exact (BProv_Ax_s_hfLtDistinguishesTermAt_succ_of_through_zero_of_membership
    hlift hzero hzeroNot).
Qed.

Lemma BProv_Ax_s_all_hfLtDistinguishesAt_of_membership :
  HFMembershipSuccLift ->
  HFMembershipZeroLift ->
  HFMembershipZeroExclusion ->
  BProv Ax_s [] (pAll (hfLtDistinguishesAt 0)).
Proof.
  intros hlift hzero hzeroNot.
  apply BProv_Ax_s_all_hfLtDistinguishesAt_of_all_through.
  exact (BProv_Ax_s_all_hfLtDistinguishesThroughAt_of_membership
    hlift hzero hzeroNot).
Qed.

Lemma BProv_Ax_s_membership_extensionality_of_all_hfLtDistinguishesAt :
  BProv Ax_s [] (pAll (hfLtDistinguishesAt 0)) ->
  BProv Ax_s
    [pAll (iffForm (hfMemAt 0 2) (hfMemAt 0 1))]
    (pEq (tVar 1) (tVar 0)).
Proof.
  intro hall.
  apply BProv_Ax_s_HF_extensionality_member_ext_of_lt_bots.
  - apply BProv_Ax_s_HF_extensionality_lt10_bot_of_distinguishing.
    set (C := [ltAt 1 0;
      pAll (iffForm (hfMemAt 0 2) (hfMemAt 0 1))]).
    apply (BProv_hfSomeDistinguishesAt_of_all_hfLtDistinguishesAt
      Ax_s C 1 0).
    + exact (BProv_weaken_nil Ax_s C _ hall).
    + apply BProv_ass. unfold C. simpl. left. reflexivity.
  - apply BProv_Ax_s_HF_extensionality_lt01_bot_of_distinguishing.
    set (C := [ltAt 0 1;
      pAll (iffForm (hfMemAt 0 2) (hfMemAt 0 1))]).
    apply (BProv_hfSomeDistinguishesAt_of_all_hfLtDistinguishesAt
      Ax_s C 0 1).
    + exact (BProv_weaken_nil Ax_s C _ hall).
    + apply BProv_ass. unfold C. simpl. left. reflexivity.
Qed.

Lemma BProv_Ax_s_membership_extensionality_of_membership :
  HFMembershipSuccLift ->
  HFMembershipZeroLift ->
  HFMembershipZeroExclusion ->
  BProv Ax_s
    [pAll (iffForm (hfMemAt 0 2) (hfMemAt 0 1))]
    (pEq (tVar 1) (tVar 0)).
Proof.
  intros hlift hzero hzeroNot.
  apply BProv_Ax_s_membership_extensionality_of_all_hfLtDistinguishesAt.
  exact (BProv_Ax_s_all_hfLtDistinguishesAt_of_membership
    hlift hzero hzeroNot).
Qed.

Lemma BProv_Ax_s_translated_HF_extensionality_of_membership :
  HFMembershipSuccLift ->
  HFMembershipZeroLift ->
  HFMembershipZeroExclusion ->
  BProv Ax_s []
    (translateHFFormula (Fol.seal HF_extensionality_form)).
Proof.
  intros hlift hzero hzeroNot.
  apply BProv_Ax_s_translated_HF_extensionality_of_all_through.
  exact (BProv_Ax_s_all_hfLtDistinguishesThroughAt_of_membership
    hlift hzero hzeroNot).
Qed.

(** Concrete certificate-facing endpoints. *)
Theorem BProv_Ax_s_all_hfLtDistinguishesThroughAt :
  BProv Ax_s [] (pAll (hfLtDistinguishesThroughAt 0)).
Proof.
  exact (BProv_Ax_s_all_hfLtDistinguishesThroughAt_of_membership
    hfMembershipSuccLift hfMembershipZeroLift
    hfMembershipZeroExclusion).
Qed.

Theorem BProv_Ax_s_all_hfLtDistinguishesAt :
  BProv Ax_s [] (pAll (hfLtDistinguishesAt 0)).
Proof.
  exact (BProv_Ax_s_all_hfLtDistinguishesAt_of_membership
    hfMembershipSuccLift hfMembershipZeroLift
    hfMembershipZeroExclusion).
Qed.

Theorem BProv_Ax_s_membership_extensionality :
  BProv Ax_s
    [pAll (iffForm (hfMemAt 0 2) (hfMemAt 0 1))]
    (pEq (tVar 1) (tVar 0)).
Proof.
  exact (BProv_Ax_s_membership_extensionality_of_membership
    hfMembershipSuccLift hfMembershipZeroLift
    hfMembershipZeroExclusion).
Qed.

Theorem BProv_Ax_s_translated_HF_extensionality :
  BProv Ax_s []
    (translateHFFormula (Fol.seal HF_extensionality_form)).
Proof.
  exact (BProv_Ax_s_translated_HF_extensionality_of_membership
    hfMembershipSuccLift hfMembershipZeroLift
    hfMembershipZeroExclusion).
Qed.
