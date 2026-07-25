(* ===================================================================== *)
(*  PAHFTranslatedFiniteInduction.v                                     *)
(*                                                                       *)
(*  PA proof of the Ackermann translation of finite-generation          *)
(*  induction.  The proof is organized around one reusable arithmetic   *)
(*  fact: every code is empty or is a one-point extension of a strictly *)
(*  smaller code.                                                        *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List.
From Stdlib Require Import Logic.FunctionalExtensionality.
From PAHF Require Import PAHF PAHFProofCalculus PAHFOrdinalCode PAHFOrdinalCodeInjective
  PAHFTranslatedHFFin
  PAHFMembershipBound PAHFMembershipBoundSucc PAHFMembershipTail
  PAHFTranslatedExtensionality PAHFAdjoinTotal.

Import ListNotations.
Import PA PA.Term PA.Formula.

Definition hfEmptyAt (setCode : nat) : formula :=
  hfEmptyTermAt (tVar setCode).

(** A private slot wrapper keeps this module independent of the public
    adjunction-totality packaging. *)
Definition hfFIAdjoinGraphAt
    (newCode oldCode elemCode : nat) : formula :=
  hfAdjoinGraphTermAt
    (tVar newCode) (tVar oldCode) (tVar elemCode).

(** The translated finite-generation hypotheses: the predicate holds of
    empty codes and is preserved by one-point adjunction. *)
Definition hfFiniteGenerationAt (psi : formula) : formula :=
  pAnd
    (pAll (pImp (hfEmptyAt 0) psi))
    (pAll (pAll (pAll
      (pImp
        (hfFIAdjoinGraphAt 0 2 1)
        (pImp
          (rename rAdjStepOld psi)
          (rename rAdjStepNew psi)))))).

Definition translatedHFFiniteInductionBody (psi : formula) : formula :=
  pImp (hfFiniteGenerationAt psi) (pAll psi).

Lemma hfFormulaAt_HF_emptyAt_zero :
  hfFormulaAt (fun n : nat => n) (HF_emptyAt 0) = hfEmptyAt 0.
Proof. reflexivity. Qed.

Lemma hfFormulaAt_HF_adjoinAt_zero_two_one :
  hfFormulaAt (fun n : nat => n) (HF_adjoinAt 0 2 1) =
    hfFIAdjoinGraphAt 0 2 1.
Proof. reflexivity. Qed.

Lemma hfFormulaAt_HF_finite_induction_form : forall phi,
  hfFormulaAt (fun n : nat => n) (HF_finite_induction_form phi) =
  translatedHFFiniteInductionBody
    (hfFormulaAt (fun n : nat => n) phi).
Proof.
  intro phi.
  unfold HF_finite_induction_form, translatedHFFiniteInductionBody,
    hfFiniteGenerationAt.
  simpl.
  repeat rewrite hfUpVarMap_id.
  repeat rewrite hfFormulaAt_id_rename.
  reflexivity.
Qed.

Lemma translateHFFormula_sealed_finite_induction : forall phi,
  translateHFFormula (Fol.seal (HF_finite_induction_form phi)) =
  PA.Formula.closeN (Fol.bound (HF_finite_induction_form phi))
    (translatedHFFiniteInductionBody
      (hfFormulaAt (fun n : nat => n) phi)).
Proof.
  intro phi.
  unfold translateHFFormula, Fol.seal.
  rewrite hfFormulaAt_closeN_id.
  rewrite hfFormulaAt_HF_finite_induction_form.
  reflexivity.
Qed.

Lemma BProv_Ax_s_translated_HF_finite_induction_of_body : forall phi,
  BProv Ax_s []
    (translatedHFFiniteInductionBody
      (hfFormulaAt (fun n : nat => n) phi)) ->
  BProv Ax_s []
    (translateHFFormula (Fol.seal (HF_finite_induction_form phi))).
Proof.
  intros phi hbody.
  rewrite translateHFFormula_sealed_finite_induction.
  exact (BProv_closeN_nil_of_sentences Ax_s sentence_ax_s
    (Fol.bound (HF_finite_induction_form phi))
    (translatedHFFiniteInductionBody
      (hfFormulaAt (fun n : nat => n) phi)) hbody).
Qed.

(** A code is either empty or obtained by adjoining one element to a
    strictly smaller code.  The existential order is old code, then
    element. *)
Definition hfStrictPredAdjoinExistsTermAt (current : term) : formula :=
  pEx (pEx
    (pAnd
      (ltTermAt (tVar 1) (Term.rename (fun n => n + 2) current))
      (hfAdjoinGraphTermAt
        (Term.rename (fun n => n + 2) current)
        (tVar 1) (tVar 0)))).

Definition hfEmptyOrStrictPredAdjoinTermAt (current : term) : formula :=
  pOr
    (hfEmptyTermAt current)
    (hfStrictPredAdjoinExistsTermAt current).

Definition hfEmptyOrStrictPredAdjoinAt (current : nat) : formula :=
  hfEmptyOrStrictPredAdjoinTermAt (tVar current).

(** Cumulative invariant used with ordinary PA induction. *)
Definition hfEmptyOrStrictPredAdjoinThroughTermAt
    (boundCode : term) : formula :=
  pAll
    (pImp
      (ltTermAt (tVar 0) (tSucc (Term.rename S boundCode)))
      (hfEmptyOrStrictPredAdjoinAt 0)).

Definition hfEmptyOrStrictPredAdjoinThroughAt (bound : nat) : formula :=
  hfEmptyOrStrictPredAdjoinThroughTermAt (tVar bound).

Lemma subst_hfStrictPredAdjoinExistsTermAt : forall sigma code,
  subst sigma (hfStrictPredAdjoinExistsTermAt code) =
  hfStrictPredAdjoinExistsTermAt (Term.subst sigma code).
Proof.
  intros sigma code.
  unfold hfStrictPredAdjoinExistsTermAt.
  cbn [subst].
  rewrite subst_ltTermAt, subst_hfAdjoinGraphTermAt.
  rewrite term_subst_up_up_rename_add_two.
  reflexivity.
Qed.

Lemma subst_hfEmptyOrStrictPredAdjoinTermAt : forall sigma code,
  subst sigma (hfEmptyOrStrictPredAdjoinTermAt code) =
  hfEmptyOrStrictPredAdjoinTermAt (Term.subst sigma code).
Proof.
  intros sigma code.
  unfold hfEmptyOrStrictPredAdjoinTermAt.
  change
    (pOr
      (subst sigma (hfEmptyTermAt code))
      (subst sigma (hfStrictPredAdjoinExistsTermAt code)) =
     pOr
      (hfEmptyTermAt (Term.subst sigma code))
      (hfStrictPredAdjoinExistsTermAt (Term.subst sigma code))).
  rewrite subst_hfEmptyTermAt.
  rewrite subst_hfStrictPredAdjoinExistsTermAt.
  reflexivity.
Qed.

Lemma rename_hfEmptyTermAt : forall r code,
  rename r (hfEmptyTermAt code) =
  hfEmptyTermAt (Term.rename r code).
Proof.
  intros r code.
  rewrite <- subst_var_rename.
  rewrite subst_hfEmptyTermAt.
  rewrite term_subst_var_rename.
  reflexivity.
Qed.

Lemma rename_hfEmptyOrStrictPredAdjoinTermAt : forall r code,
  rename r (hfEmptyOrStrictPredAdjoinTermAt code) =
  hfEmptyOrStrictPredAdjoinTermAt (Term.rename r code).
Proof.
  intros r code.
  rewrite <- subst_var_rename.
  rewrite subst_hfEmptyOrStrictPredAdjoinTermAt.
  rewrite term_subst_var_rename.
  reflexivity.
Qed.

(** The decomposition proof consumes exactly three binary-head facts from
    adjunction totality.  Keeping them in one interface makes the genuinely
    independent numerical strong-induction shell below reusable. *)
Record HFAdjoinHeadProofs := {
  hfahp_zero_member_even_bot :
    forall G elem low lowHalf,
    BProv Ax_s G (eqConstAt elem 0) ->
    BProv Ax_s G (doubleEqAt low lowHalf) ->
    BProv Ax_s G (hfMemAt elem low) ->
    BProv Ax_s G pBot;

  hfahp_zero_of_shared_tail :
    forall G newHead oldHead tail newBit oldBit,
    BProv Ax_s G (eqConstAt newBit 1) ->
    BProv Ax_s G (div2StepAt newHead tail newBit) ->
    BProv Ax_s G (div2StepAt oldHead tail oldBit) ->
    BProv Ax_s G
      (hfAdjoinGraphTermAt
        (tVar newHead) (tVar oldHead) tZero);

  hfahp_heads_of_same_bit :
    forall G newHead newTail oldHead oldTail bit elem,
    BProv Ax_s G (div2StepAt newHead newTail bit) ->
    BProv Ax_s G (div2StepAt oldHead oldTail bit) ->
    BProv Ax_s G (hfFIAdjoinGraphAt newTail oldTail elem) ->
    BProv Ax_s G
      (hfAdjoinGraphTermAt
        (tVar newHead) (tVar oldHead) (tSucc (tVar elem)))
}.

(** An even equation plus a named zero bit gives a binary-halving step. *)
Lemma BProv_Ax_s_div2StepAt_of_doubleEqAt_bit_zero_FI :
  forall G value half bit,
  BProv Ax_s G (doubleEqAt value half) ->
  BProv Ax_s G (eqConstAt bit 0) ->
  BProv Ax_s G (div2StepAt value half bit).
Proof.
  intros G value half bit hdouble hbit.
  set (d := tAdd (tVar half) (tVar half)).
  assert (hbool : BProv Ax_s G (boolAt bit)).
  {
    unfold boolAt, zeroAt, oneAt.
    exact (BProv_orI1 Ax_s G (eqConstAt bit 0)
      (eqConstAt bit 1) hbit).
  }
  assert (hvalue : BProv Ax_s G (pEq (tVar value) d)).
  { unfold doubleEqAt, d in *. exact hdouble. }
  assert (hbit' : BProv Ax_s G (pEq (tVar bit) tZero)).
  { unfold eqConstAt in hbit. exact hbit. }
  assert (haddBit : BProv Ax_s G
    (pEq (tAdd d (tVar bit)) (tAdd d tZero))).
  { exact (BProv_eq_congr_add_right Ax_s G d _ _ hbit'). }
  assert (haddZero : BProv Ax_s G (pEq (tAdd d tZero) d)).
  { exact (BProv_Ax_s_addZero_term G d). }
  assert (hsum : BProv Ax_s G (pEq (tAdd d (tVar bit)) d)).
  { exact (BProv_eqTrans Ax_s G _ _ _ haddBit haddZero). }
  assert (heq : BProv Ax_s G
    (pEq (tVar value) (tAdd d (tVar bit)))).
  {
    exact (BProv_eqTrans Ax_s G _ _ _ hvalue
      (BProv_eqSym Ax_s G _ _ hsum)).
  }
  unfold div2StepAt, d.
  exact (BProv_andI Ax_s G _ _ hbool heq).
Qed.

(** Odd heads have the direct predecessor obtained by clearing bit zero;
    the adjoined element is zero. *)
Lemma BProv_Ax_s_hfEmptyOrStrictPredAdjoinAt_of_odd_step_using_pack :
  forall (P : HFAdjoinHeadProofs),
  (forall B G code oldCode elemCode,
    BProv B G (ltTermAt oldCode code) ->
    BProv B G (hfAdjoinGraphTermAt code oldCode elemCode) ->
    BProv B G (hfEmptyOrStrictPredAdjoinTermAt code)) ->
  forall G current half bit,
  BProv Ax_s G (div2StepAt current half bit) ->
  BProv Ax_s G (eqConstAt bit 1) ->
  BProv Ax_s G (hfEmptyOrStrictPredAdjoinAt current).
Proof.
  intros P pack G current half bit hstep hbitOne.
  set (oldTerm := tAdd (tVar half) (tVar half)).
  set (nameBody := pEq (tVar 0) (Term.rename S oldTerm)).
  set (target := hfEmptyOrStrictPredAdjoinAt current).
  assert (hnameEx : BProv Ax_s G (pEx nameBody)).
  {
    unfold nameBody.
    exact (BProv_exists_eq_term Ax_s G oldTerm).
  }
  apply (BProv_exE_of_sentences Ax_s G nameBody target
    sentence_ax_s hnameEx).
  set (H := nameBody :: map (rename S) G).
  set (zeroBit := eqConstAt 0 0).
  assert (hzeroEx : BProv Ax_s H (pEx zeroBit)).
  { exact (BProv_exists_eqConstAt Ax_s H 0). }
  apply (BProv_exE_of_sentences Ax_s H zeroBit
    (rename S target) sentence_ax_s hzeroEx).
  set (K := zeroBit :: map (rename S) H).
  assert (hzero : BProv Ax_s K (eqConstAt 0 0)).
  {
    unfold K, zeroBit.
    apply BProv_ass.
    simpl; auto.
  }
  assert (hname : BProv Ax_s K
    (pEq (tVar 1)
      (tAdd (tVar (S (S half))) (tVar (S (S half)))))).
  {
    unfold K, H, nameBody, oldTerm.
    apply BProv_ass.
    simpl; auto.
  }
  assert (holdDouble : BProv Ax_s K (doubleEqAt 1 (S (S half)))).
  { unfold doubleEqAt. exact hname. }
  assert (holdStep : BProv Ax_s K (div2StepAt 1 (S (S half)) 0)).
  {
    exact (BProv_Ax_s_div2StepAt_of_doubleEqAt_bit_zero_FI
      K 1 (S (S half)) 0 holdDouble hzero).
  }
  assert (hstepKRaw : BProv Ax_s K
    (rename S (rename S (div2StepAt current half bit)))).
  {
    pose proof (BProv_lift_two_contexts_of_sentences
      Ax_s sentence_ax_s G nameBody zeroBit _ hstep) as h.
    unfold K, H.
    exact h.
  }
  assert (hnewStep : BProv Ax_s K
    (div2StepAt (S (S current)) (S (S half)) (S (S bit)))).
  {
    repeat rewrite rename_S_div2StepAt in hstepKRaw.
    exact hstepKRaw.
  }
  assert (hbitKRaw : BProv Ax_s K
    (rename S (rename S (eqConstAt bit 1)))).
  {
    pose proof (BProv_lift_two_contexts_of_sentences
      Ax_s sentence_ax_s G nameBody zeroBit _ hbitOne) as h.
    unfold K, H.
    exact h.
  }
  assert (hnewBitOne : BProv Ax_s K (eqConstAt (S (S bit)) 1)).
  {
    unfold eqConstAt in *.
    simpl in hbitKRaw.
    exact hbitKRaw.
  }
  assert (hnewOdd : BProv Ax_s K
    (oddDoubleEqAt (S (S current)) (S (S half)))).
  {
    exact (BProv_Ax_s_oddDoubleEqAt_of_div2StepAt_bit_one
      K (S (S current)) (S (S half)) (S (S bit))
      hnewBitOne hnewStep).
  }
  assert (hcurrentEq : BProv Ax_s K
    (pEq (tVar (S (S current)))
      (tSucc (tAdd (tVar (S (S half))) (tVar (S (S half))))))).
  { unfold oddDoubleEqAt in hnewOdd. exact hnewOdd. }
  assert (hsuccOldEq : BProv Ax_s K
    (pEq (tSucc (tVar 1))
      (tSucc (tAdd (tVar (S (S half))) (tVar (S (S half))))))).
  { exact (BProv_eq_congr_succ Ax_s K _ _ hname). }
  assert (hsuccLe : BProv Ax_s K
    (leTermAt (tSucc (tVar 1)) (tVar (S (S current))))).
  {
    apply (BProv_leTermAt_of_eq_right Ax_s K
      (tSucc (tVar 1))
      (tSucc (tAdd (tVar (S (S half))) (tVar (S (S half)))))
      (tVar (S (S current)))).
    - exact (BProv_eqSym Ax_s K _ _ hcurrentEq).
    - apply (BProv_leTermAt_of_eq_left Ax_s K
        (tSucc (tAdd (tVar (S (S half))) (tVar (S (S half)))))
        (tSucc (tVar 1))
        (tSucc (tAdd (tVar (S (S half))) (tVar (S (S half)))))).
      + exact (BProv_eqSym Ax_s K _ _ hsuccOldEq).
      + exact (BProv_Ax_s_leTermAt_refl K
          (tSucc (tAdd (tVar (S (S half))) (tVar (S (S half)))))).
  }
  assert (hlt : BProv Ax_s K
    (ltTermAt (tVar 1) (tVar (S (S current))))).
  {
    exact (BProv_Ax_s_ltTermAt_of_succ_leTermAt
      K (tVar 1) (tVar (S (S current))) hsuccLe).
  }
  assert (hgraph : BProv Ax_s K
    (hfAdjoinGraphTermAt
      (tVar (S (S current))) (tVar 1) tZero)).
  {
    exact (hfahp_zero_of_shared_tail P K
      (S (S current)) 1 (S (S half)) (S (S bit)) 0
      hnewBitOne hnewStep holdStep).
  }
  assert (hproper : BProv Ax_s K
    (hfEmptyOrStrictPredAdjoinTermAt (tVar (S (S current))))).
  {
    exact (pack
      Ax_s K (tVar (S (S current))) (tVar 1) tZero hlt hgraph).
  }
  unfold target, hfEmptyOrStrictPredAdjoinAt.
  repeat rewrite rename_hfEmptyOrStrictPredAdjoinTermAt.
  simpl.
  exact hproper.
Qed.

(** Package concrete witnesses into the two existential binders. *)
Lemma BProv_hfStrictPredAdjoinExistsTermAt_of_terms :
  forall B G code oldCode elemCode,
  BProv B G (ltTermAt oldCode code) ->
  BProv B G (hfAdjoinGraphTermAt code oldCode elemCode) ->
  BProv B G (hfStrictPredAdjoinExistsTermAt code).
Proof.
  intros B G code oldCode elemCode hlt hgraph.
  set (body :=
    pAnd
      (ltTermAt (tVar 1) (Term.rename (fun n => n + 2) code))
      (hfAdjoinGraphTermAt
        (Term.rename (fun n => n + 2) code)
        (tVar 1) (tVar 0))).
  set (tau := fun n =>
    Term.subst (instTerm elemCode)
      (Term.upSubst (instTerm oldCode) n)).
  assert (htau2 : forall n, tau (n + 2) = tVar n).
  {
    intro n.
    replace (n + 2) with (S (S n)) by lia.
    unfold tau, Term.upSubst.
    change
      (Term.subst (instTerm elemCode) (Term.rename S (tVar n)) =
       tVar n).
    apply term_subst_instTerm_rename_succ.
  }
  assert (htau0 : tau 0 = elemCode).
  { unfold tau, instTerm, Term.upSubst. reflexivity. }
  assert (htau1 : tau 1 = oldCode).
  {
    unfold tau, Term.upSubst.
    change
      (Term.subst (instTerm elemCode) (Term.rename S oldCode) =
       oldCode).
    apply term_subst_instTerm_rename_succ.
  }
  assert (hcode :
    Term.subst tau (Term.rename (fun n => n + 2) code) = code).
  {
    rewrite Term.subst_rename.
    transitivity (Term.subst (fun n => tVar n) code).
    - apply Term.subst_ext.
      exact htau2.
    - apply Term.subst_id.
  }
  assert (hnorm :
    subst (instTerm elemCode)
      (subst (Term.upSubst (instTerm oldCode)) body) =
    pAnd (ltTermAt oldCode code)
      (hfAdjoinGraphTermAt code oldCode elemCode)).
  {
    rewrite subst_comp.
    change
      (subst tau body =
       pAnd (ltTermAt oldCode code)
         (hfAdjoinGraphTermAt code oldCode elemCode)).
    unfold body.
    change
      (pAnd
        (subst tau
          (ltTermAt (tVar 1)
            (Term.rename (fun n => n + 2) code)))
        (subst tau
          (hfAdjoinGraphTermAt
            (Term.rename (fun n => n + 2) code)
            (tVar 1) (tVar 0))) =
       pAnd (ltTermAt oldCode code)
         (hfAdjoinGraphTermAt code oldCode elemCode)).
    rewrite subst_ltTermAt, subst_hfAdjoinGraphTermAt.
    rewrite hcode.
    change
      (pAnd (ltTermAt (tau 1) code)
        (hfAdjoinGraphTermAt code (tau 1) (tau 0)) =
       pAnd (ltTermAt oldCode code)
        (hfAdjoinGraphTermAt code oldCode elemCode)).
    rewrite htau0, htau1.
    reflexivity.
  }
  unfold hfStrictPredAdjoinExistsTermAt.
  fold body.
  apply (BProv_exI B G (pEx body) oldCode).
  apply (BProv_exI B G
    (subst (Term.upSubst (instTerm oldCode)) body) elemCode).
  rewrite hnorm.
  exact (BProv_andI B G _ _ hlt hgraph).
Qed.

Lemma BProv_hfEmptyOrStrictPredAdjoinTermAt_of_terms :
  forall B G code oldCode elemCode,
  BProv B G (ltTermAt oldCode code) ->
  BProv B G (hfAdjoinGraphTermAt code oldCode elemCode) ->
  BProv B G (hfEmptyOrStrictPredAdjoinTermAt code).
Proof.
  intros B G code oldCode elemCode hlt hgraph.
  unfold hfEmptyOrStrictPredAdjoinTermAt.
  apply BProv_orI2.
  exact (BProv_hfStrictPredAdjoinExistsTermAt_of_terms
    B G code oldCode elemCode hlt hgraph).
Qed.

Lemma BProv_Ax_s_hfEmptyOrStrictPredAdjoinAt_of_odd_step :
  forall (P : HFAdjoinHeadProofs) G current half bit,
  BProv Ax_s G (div2StepAt current half bit) ->
  BProv Ax_s G (eqConstAt bit 1) ->
  BProv Ax_s G (hfEmptyOrStrictPredAdjoinAt current).
Proof.
  intros P G current half bit hstep hbit.
  exact
    (BProv_Ax_s_hfEmptyOrStrictPredAdjoinAt_of_odd_step_using_pack
      P BProv_hfEmptyOrStrictPredAdjoinTermAt_of_terms
      G current half bit hstep hbit).
Qed.

(** An even head over an empty tail is empty. *)
Lemma BProv_Ax_s_hfEmptyTermAt_of_even_step_tail_empty :
  forall (P : HFAdjoinHeadProofs) G current half bit,
  BProv Ax_s G (div2StepAt current half bit) ->
  BProv Ax_s G (eqConstAt bit 0) ->
  BProv Ax_s G (hfEmptyTermAt (tVar half)) ->
  BProv Ax_s G (hfEmptyTermAt (tVar current)).
Proof.
  intros P G current half bit hstep hbitZero htailEmpty.
  set (mem := hfMemTermAt 0 (tVar (S current))).
  set (Q := map (rename S) G).
  assert (hstepRenRaw : BProv Ax_s Q
    (rename S (div2StepAt current half bit))).
  {
    unfold Q.
    exact (BProv_rename_of_sentences Ax_s sentence_ax_s G
      (div2StepAt current half bit) hstep S).
  }
  assert (hstepRen : BProv Ax_s Q
    (div2StepAt (S current) (S half) (S bit))).
  { rewrite rename_S_div2StepAt in hstepRenRaw. exact hstepRenRaw. }
  assert (hbitRenRaw : BProv Ax_s Q
    (rename S (eqConstAt bit 0))).
  {
    unfold Q.
    exact (BProv_rename_of_sentences Ax_s sentence_ax_s G
      (eqConstAt bit 0) hbitZero S).
  }
  assert (hbitRen : BProv Ax_s Q (eqConstAt (S bit) 0)).
  { unfold eqConstAt in *. simpl in hbitRenRaw. exact hbitRenRaw. }
  assert (hdouble : BProv Ax_s Q (doubleEqAt (S current) (S half))).
  {
    exact (BProv_Ax_s_doubleEqAt_of_div2StepAt_bit_zero
      Q (S current) (S half) (S bit) hbitRen hstepRen).
  }
  assert (himp : BProv Ax_s Q (pImp mem pBot)).
  {
    set (C := mem :: Q).
    assert (hmem : BProv Ax_s C mem).
    {
      unfold C.
      apply BProv_ass.
      simpl; auto.
    }
    assert (hcases : BProv Ax_s C (zeroOrSuccPredAt 0)).
    { exact (BProv_Ax_s_zeroOrSuccPredAt C 0). }
    assert (hzeroBranch : BProv Ax_s (zeroAt 0 :: C) pBot).
    {
      set (Z := zeroAt 0 :: C).
      assert (hzero : BProv Ax_s Z (eqConstAt 0 0)).
      {
        unfold Z, zeroAt.
        apply BProv_ass.
        simpl; auto.
      }
      assert (hdoubleZ : BProv Ax_s Z
        (doubleEqAt (S current) (S half))).
      {
        unfold Z, C.
        exact (BProv_context_prefix Ax_s
          [zeroAt 0; mem] Q _ hdouble).
      }
      assert (hmemZ : BProv Ax_s Z (hfMemAt 0 (S current))).
      {
        unfold Z.
        apply BProv_context_cons.
        unfold mem in hmem.
        rewrite hfMemTermAt_var in hmem.
        exact hmem.
      }
      exact (hfahp_zero_member_even_bot P Z 0
        (S current) (S half) hzero hdoubleZ hmemZ).
    }
    assert (hsuccBranch : BProv Ax_s (succPredAt 0 :: C) pBot).
    {
      set (Sctx := succPredAt 0 :: C).
      assert (hsucc : BProv Ax_s Sctx (succPredAt 0)).
      {
        unfold Sctx.
        apply BProv_ass.
        simpl; auto.
      }
      set (succBody := pEq (tVar 1) (tSucc (tVar 0))).
      assert (hsuccEx : BProv Ax_s Sctx (pEx succBody)).
      { unfold succPredAt in hsucc. unfold succBody. exact hsucc. }
      apply (BProv_exE_of_sentences Ax_s Sctx succBody pBot
        sentence_ax_s hsuccEx).
      set (D := succBody :: map (rename S) Sctx).
      assert (lift2ToD : forall phi,
          BProv Ax_s G phi ->
          BProv Ax_s D (rename S (rename S phi))).
      {
        intros phi hphi.
        unfold D, Sctx, C, Q.
        cbn [map].
        apply BProv_context_cons.
        exact (BProv_lift_two_contexts_of_sentences
          Ax_s sentence_ax_s G mem
          (rename S (succPredAt 0)) phi hphi).
      }
      assert (heq : BProv Ax_s D
        (pEq (tVar 1) (tSucc (tVar 0)))).
      {
        unfold D, succBody.
        apply BProv_ass.
        simpl; auto.
      }
      assert (hmemRenRaw : BProv Ax_s (map (rename S) C)
        (rename S mem)).
      {
        unfold C in hmem.
        exact (BProv_rename_of_sentences Ax_s sentence_ax_s C
          mem hmem S).
      }
      assert (hmemD : BProv Ax_s D (hfMemAt 1 (S (S current)))).
      {
        assert (hraw : BProv Ax_s D (rename S mem)).
        {
          unfold D, Sctx.
          exact (BProv_context_prefix Ax_s
            [succBody; rename S (succPredAt 0)]
            (map (rename S) C) _ hmemRenRaw).
        }
        unfold mem in hraw.
        rewrite hfMemTermAt_var in hraw.
        rewrite rename_hfMemAt in hraw.
        exact hraw.
      }
      assert (hmemVar : BProv Ax_s D
        (subst (instTerm (tVar 1))
          (hfMemAt 0 (S (S (S current)))))).
      {
        rewrite subst_instTerm_var_hfMemAt_zero_succ.
        exact hmemD.
      }
      assert (hsuccMem : BProv Ax_s D
        (subst (instTerm (tSucc (tVar 0)))
          (hfMemAt 0 (S (S (S current)))))).
      {
        exact (BProv_eqElim Ax_s D (tVar 1) (tSucc (tVar 0))
          (hfMemAt 0 (S (S (S current)))) heq hmemVar).
      }
      pose proof (lift2ToD _ hstep) as hstepDRaw.
      assert (hstepD : BProv Ax_s D
        (div2StepAt (S (S current)) (S (S half)) (S (S bit)))).
      {
        repeat rewrite rename_S_div2StepAt in hstepDRaw.
        exact hstepDRaw.
      }
      assert (htailMem : BProv Ax_s D (hfMemAt 0 (S (S half)))).
      {
        exact (BProv_Ax_s_hfMemAt_tail_of_succ_mem_and_div2StepAt
          D (S (S current)) (S (S half)) (S (S bit))
          hstepD hsuccMem).
      }
      pose proof (lift2ToD _ htailEmpty) as htailDRaw.
      assert (htailD : BProv Ax_s D
        (hfEmptyTermAt (tVar (S (S half))))).
      {
        repeat rewrite rename_hfEmptyTermAt in htailDRaw.
        cbn [Term.rename] in htailDRaw.
        exact htailDRaw.
      }
      pose proof (BProv_allE Ax_s D
        (pImp
          (hfMemTermAt 0
            (Term.rename S (tVar (S (S half)))))
          pBot)
        (tVar 0) htailD) as hnotTailRaw.
      assert (hnotTail : BProv Ax_s D
        (pImp (hfMemAt 0 (S (S half))) pBot)).
      {
        change (BProv Ax_s D
          (pImp
            (subst (instTerm (tVar 0))
              (hfMemTermAt 0
                (Term.rename S (tVar (S (S half))))))
            pBot)) in hnotTailRaw.
        rewrite subst_instTerm_var_hfMemTermAt_zero_rename_succ
          in hnotTailRaw.
        rewrite hfMemTermAt_var in hnotTailRaw.
        exact hnotTailRaw.
      }
      exact (BProv_mp Ax_s D (hfMemAt 0 (S (S half))) pBot
        hnotTail htailMem).
    }
    assert (hbot : BProv Ax_s C pBot).
    {
      unfold zeroOrSuccPredAt in hcases.
      exact (BProv_orE Ax_s C (zeroAt 0) (succPredAt 0) pBot
        hcases hzeroBranch hsuccBranch).
    }
    unfold C in hbot.
    exact (BProv_impI Ax_s Q mem pBot hbot).
  }
  assert (hall : BProv Ax_s G (pAll (pImp mem pBot))).
  {
    exact (BProv_allI_of_sentences Ax_s G
      (pImp mem pBot) sentence_ax_s himp).
  }
  unfold hfEmptyTermAt, mem in *.
  exact hall.
Qed.

Lemma rename_S_hfFIAdjoinGraphAt : forall newCode oldCode elemCode,
  rename S (hfFIAdjoinGraphAt newCode oldCode elemCode) =
  hfFIAdjoinGraphAt (S newCode) (S oldCode) (S elemCode).
Proof.
  intros newCode oldCode elemCode.
  unfold hfFIAdjoinGraphAt.
  rewrite rename_hfAdjoinGraphTermAt.
  reflexivity.
Qed.

(** A strict predecessor of an even tail lifts through the shared zero bit. *)
Lemma BProv_Ax_s_hfEmptyOrStrictPredAdjoinAt_of_even_step_tail_pred :
  forall (P : HFAdjoinHeadProofs) G current half bit oldTail elem,
  BProv Ax_s G (div2StepAt current half bit) ->
  BProv Ax_s G (eqConstAt bit 0) ->
  BProv Ax_s G (ltAt oldTail half) ->
  BProv Ax_s G (hfFIAdjoinGraphAt half oldTail elem) ->
  BProv Ax_s G (hfEmptyOrStrictPredAdjoinAt current).
Proof.
  intros P G current half bit oldTail elem
    hstep hbitZero hltTail htailGraph.
  set (oldHeadTerm :=
    tAdd (tAdd (tVar oldTail) (tVar oldTail)) (tVar bit)).
  set (nameBody := pEq (tVar 0) (Term.rename S oldHeadTerm)).
  set (target := hfEmptyOrStrictPredAdjoinAt current).
  assert (hnameEx : BProv Ax_s G (pEx nameBody)).
  {
    unfold nameBody.
    exact (BProv_exists_eq_term Ax_s G oldHeadTerm).
  }
  apply (BProv_exE_of_sentences Ax_s G nameBody target
    sentence_ax_s hnameEx).
  set (H := nameBody :: map (rename S) G).
  assert (hname : BProv Ax_s H
    (pEq (tVar 0)
      (tAdd
        (tAdd (tVar (S oldTail)) (tVar (S oldTail)))
        (tVar (S bit))))).
  {
    unfold H, nameBody, oldHeadTerm.
    apply BProv_ass.
    simpl; auto.
  }
  assert (hstepRenRaw : BProv Ax_s H
    (rename S (div2StepAt current half bit))).
  {
    unfold H.
    exact (BProv_rename_succ_context_cons_of_sentences
      Ax_s sentence_ax_s G nameBody
      (div2StepAt current half bit) hstep).
  }
  assert (hnewStep : BProv Ax_s H
    (div2StepAt (S current) (S half) (S bit))).
  { rewrite rename_S_div2StepAt in hstepRenRaw. exact hstepRenRaw. }
  assert (holdStep : BProv Ax_s H
    (div2StepAt 0 (S oldTail) (S bit))).
  {
    exact (BProv_Ax_s_div2StepAt_of_named_head_and_old_step
      H 0 (S oldTail) (S current) (S half) (S bit)
      hname hnewStep).
  }
  assert (hbitRenRaw : BProv Ax_s H
    (rename S (eqConstAt bit 0))).
  {
    unfold H.
    exact (BProv_rename_succ_context_cons_of_sentences
      Ax_s sentence_ax_s G nameBody (eqConstAt bit 0) hbitZero).
  }
  assert (hbitH : BProv Ax_s H (eqConstAt (S bit) 0)).
  { unfold eqConstAt in *. simpl in hbitRenRaw. exact hbitRenRaw. }
  assert (hnewDouble : BProv Ax_s H
    (doubleEqAt (S current) (S half))).
  {
    exact (BProv_Ax_s_doubleEqAt_of_div2StepAt_bit_zero
      H (S current) (S half) (S bit) hbitH hnewStep).
  }
  assert (holdDouble : BProv Ax_s H (doubleEqAt 0 (S oldTail))).
  {
    exact (BProv_Ax_s_doubleEqAt_of_div2StepAt_bit_zero
      H 0 (S oldTail) (S bit) hbitH holdStep).
  }
  assert (hltRenRaw : BProv Ax_s H (rename S (ltAt oldTail half))).
  {
    unfold H.
    exact (BProv_rename_succ_context_cons_of_sentences
      Ax_s sentence_ax_s G nameBody (ltAt oldTail half) hltTail).
  }
  assert (hltH : BProv Ax_s H
    (ltTermAt (tVar (S oldTail)) (tVar (S half)))).
  {
    change (BProv Ax_s H
      (rename S (ltTermAt (tVar oldTail) (tVar half)))) in hltRenRaw.
    rewrite rename_ltTermAt in hltRenRaw.
    exact hltRenRaw.
  }
  assert (hmiddle : BProv Ax_s H
    (leTermAt
      (tSucc (tAdd (tVar (S oldTail)) (tVar (S oldTail))))
      (tAdd (tVar (S half)) (tVar (S half))))).
  {
    exact (BProv_Ax_s_succ_double_le_double_of_ltTermAt
      H (tVar (S oldTail)) (tVar (S half)) hltH).
  }
  assert (holdEq : BProv Ax_s H
    (pEq (tVar 0)
      (tAdd (tVar (S oldTail)) (tVar (S oldTail))))).
  { unfold doubleEqAt in holdDouble. exact holdDouble. }
  assert (hnewEq : BProv Ax_s H
    (pEq (tVar (S current))
      (tAdd (tVar (S half)) (tVar (S half))))).
  { unfold doubleEqAt in hnewDouble. exact hnewDouble. }
  assert (hsuccOldEq : BProv Ax_s H
    (pEq (tSucc (tVar 0))
      (tSucc (tAdd (tVar (S oldTail)) (tVar (S oldTail)))))).
  { exact (BProv_eq_congr_succ Ax_s H _ _ holdEq). }
  assert (hsuccLe : BProv Ax_s H
    (leTermAt (tSucc (tVar 0)) (tVar (S current)))).
  {
    apply (BProv_leTermAt_of_eq_right Ax_s H
      (tSucc (tVar 0))
      (tAdd (tVar (S half)) (tVar (S half)))
      (tVar (S current))).
    - exact (BProv_eqSym Ax_s H _ _ hnewEq).
    - apply (BProv_leTermAt_of_eq_left Ax_s H
        (tSucc (tAdd (tVar (S oldTail)) (tVar (S oldTail))))
        (tSucc (tVar 0))
        (tAdd (tVar (S half)) (tVar (S half)))).
      + exact (BProv_eqSym Ax_s H _ _ hsuccOldEq).
      + exact hmiddle.
  }
  assert (hltHead : BProv Ax_s H
    (ltTermAt (tVar 0) (tVar (S current)))).
  {
    exact (BProv_Ax_s_ltTermAt_of_succ_leTermAt
      H (tVar 0) (tVar (S current)) hsuccLe).
  }
  assert (htailRenRaw : BProv Ax_s H
    (rename S (hfFIAdjoinGraphAt half oldTail elem))).
  {
    unfold H.
    exact (BProv_rename_succ_context_cons_of_sentences
      Ax_s sentence_ax_s G nameBody
      (hfFIAdjoinGraphAt half oldTail elem) htailGraph).
  }
  assert (htailH : BProv Ax_s H
    (hfFIAdjoinGraphAt (S half) (S oldTail) (S elem))).
  { rewrite rename_S_hfFIAdjoinGraphAt in htailRenRaw. exact htailRenRaw. }
  assert (hgraph : BProv Ax_s H
    (hfAdjoinGraphTermAt
      (tVar (S current)) (tVar 0) (tSucc (tVar (S elem))))).
  {
    exact (hfahp_heads_of_same_bit P H
      (S current) (S half) 0 (S oldTail) (S bit) (S elem)
      hnewStep holdStep htailH).
  }
  assert (hproper : BProv Ax_s H
    (hfEmptyOrStrictPredAdjoinTermAt (tVar (S current)))).
  {
    exact (BProv_hfEmptyOrStrictPredAdjoinTermAt_of_terms
      Ax_s H (tVar (S current)) (tVar 0) (tSucc (tVar (S elem)))
      hltHead hgraph).
  }
  unfold target, hfEmptyOrStrictPredAdjoinAt.
  rewrite rename_hfEmptyOrStrictPredAdjoinTermAt.
  exact hproper.
Qed.

(** One binary step propagates the empty-or-strict-predecessor decomposition
    from its tail to its head. *)
Lemma BProv_Ax_s_hfEmptyOrStrictPredAdjoinAt_of_step_and_tail :
  forall (P : HFAdjoinHeadProofs) G current half bit,
  BProv Ax_s G (div2StepAt current half bit) ->
  BProv Ax_s G (hfEmptyOrStrictPredAdjoinAt half) ->
  BProv Ax_s G (hfEmptyOrStrictPredAdjoinAt current).
Proof.
  intros P G current half bit hstep htail.
  set (target := hfEmptyOrStrictPredAdjoinAt current).
  assert (hbool : BProv Ax_s G (boolAt bit)).
  { unfold div2StepAt in hstep. exact (BProv_andE1 Ax_s G _ _ hstep). }
  assert (heven : BProv Ax_s (zeroAt bit :: G) target).
  {
    set (C := zeroAt bit :: G).
    assert (hbitZero : BProv Ax_s C (eqConstAt bit 0)).
    {
      unfold C, zeroAt.
      apply BProv_ass.
      simpl; auto.
    }
    assert (hstepC : BProv Ax_s C (div2StepAt current half bit)).
    { unfold C. exact (BProv_context_cons Ax_s G _ _ hstep). }
    assert (htailC : BProv Ax_s C
      (hfEmptyOrStrictPredAdjoinAt half)).
    { unfold C. exact (BProv_context_cons Ax_s G _ _ htail). }
    set (tailEmpty := hfEmptyTermAt (tVar half)).
    set (predBody :=
      pAnd
        (ltTermAt (tVar 1) (tVar (S (S half))))
        (hfAdjoinGraphTermAt
          (tVar (S (S half))) (tVar 1) (tVar 0))).
    set (predInner := pEx predBody).
    set (predEx := pEx predInner).
    assert (hcases : BProv Ax_s C (pOr tailEmpty predEx)).
    {
      unfold hfEmptyOrStrictPredAdjoinAt,
        hfEmptyOrStrictPredAdjoinTermAt,
        hfStrictPredAdjoinExistsTermAt in htailC.
      change (BProv Ax_s C
        (pOr (hfEmptyTermAt (tVar half))
          (pEx (pEx
            (pAnd
              (ltTermAt (tVar 1) (tVar (half + 2)))
              (hfAdjoinGraphTermAt
                (tVar (half + 2)) (tVar 1) (tVar 0)))))))
        in htailC.
      replace (half + 2) with (S (S half)) in htailC by lia.
      unfold tailEmpty, predEx, predInner, predBody.
      exact htailC.
    }
    assert (hempty : BProv Ax_s (tailEmpty :: C) target).
    {
      set (E := tailEmpty :: C).
      assert (hemptyTail : BProv Ax_s E
        (hfEmptyTermAt (tVar half))).
      {
        unfold E, tailEmpty.
        apply BProv_ass.
        simpl; auto.
      }
      assert (hheadEmpty : BProv Ax_s E
        (hfEmptyTermAt (tVar current))).
      {
        exact (BProv_Ax_s_hfEmptyTermAt_of_even_step_tail_empty
          P E current half bit
          (BProv_context_cons Ax_s C tailEmpty _ hstepC)
          (BProv_context_cons Ax_s C tailEmpty _ hbitZero)
          hemptyTail).
      }
      unfold target, hfEmptyOrStrictPredAdjoinAt,
        hfEmptyOrStrictPredAdjoinTermAt.
      exact (BProv_orI1 Ax_s E _ _ hheadEmpty).
    }
    assert (hpred : BProv Ax_s (predEx :: C) target).
    {
      set (Pctx := predEx :: C).
      assert (hpredEx : BProv Ax_s Pctx (pEx (pEx predBody))).
      {
        unfold Pctx, predEx, predInner.
        apply BProv_ass.
        simpl; auto.
      }
      apply (BProv_two_exE_of_sentences
        Ax_s sentence_ax_s Pctx predBody target hpredEx).
      set (H := predBody :: map (rename S)
        (pEx predBody :: map (rename S) Pctx)).
      change (BProv Ax_s H (rename S (rename S target))).
      assert (hbody : BProv Ax_s H predBody).
      {
        unfold H.
        apply BProv_ass.
        simpl; auto.
      }
      assert (hlt : BProv Ax_s H (ltAt 1 (S (S half)))).
      {
        unfold predBody in hbody.
        change (BProv Ax_s H
          (ltTermAt (tVar 1) (tVar (S (S half))))).
        exact (BProv_andE1 Ax_s H _ _ hbody).
      }
      assert (hgraph : BProv Ax_s H
        (hfFIAdjoinGraphAt (S (S half)) 1 0)).
      {
        unfold predBody in hbody.
        change (BProv Ax_s H
          (hfAdjoinGraphTermAt
            (tVar (S (S half))) (tVar 1) (tVar 0))).
        exact (BProv_andE2 Ax_s H _ _ hbody).
      }
      assert (hstepP : BProv Ax_s Pctx
        (div2StepAt current half bit)).
      { unfold Pctx. exact (BProv_context_cons Ax_s C _ _ hstepC). }
      assert (hstepHRaw : BProv Ax_s H
        (rename S (rename S (div2StepAt current half bit)))).
      {
        pose proof (BProv_lift_two_opened_of_sentences
          Ax_s sentence_ax_s Pctx predBody _ hstepP) as h.
        unfold H.
        exact h.
      }
      assert (hstepH : BProv Ax_s H
        (div2StepAt (S (S current)) (S (S half)) (S (S bit)))).
      {
        repeat rewrite rename_S_div2StepAt in hstepHRaw.
        exact hstepHRaw.
      }
      assert (hbitP : BProv Ax_s Pctx (eqConstAt bit 0)).
      { unfold Pctx. exact (BProv_context_cons Ax_s C _ _ hbitZero). }
      assert (hbitHRaw : BProv Ax_s H
        (rename S (rename S (eqConstAt bit 0)))).
      {
        pose proof (BProv_lift_two_opened_of_sentences
          Ax_s sentence_ax_s Pctx predBody _ hbitP) as h.
        unfold H.
        exact h.
      }
      assert (hbitH : BProv Ax_s H (eqConstAt (S (S bit)) 0)).
      { unfold eqConstAt in *. simpl in hbitHRaw. exact hbitHRaw. }
      pose proof
        (BProv_Ax_s_hfEmptyOrStrictPredAdjoinAt_of_even_step_tail_pred
          P H (S (S current)) (S (S half)) (S (S bit))
          1 0 hstepH hbitH hlt hgraph) as hresult.
      unfold target, hfEmptyOrStrictPredAdjoinAt.
      repeat rewrite rename_hfEmptyOrStrictPredAdjoinTermAt.
      exact hresult.
    }
    exact (BProv_orE Ax_s C tailEmpty predEx target
      hcases hempty hpred).
  }
  assert (hodd : BProv Ax_s (oneAt bit :: G) target).
  {
    set (O := oneAt bit :: G).
    assert (hbitOne : BProv Ax_s O (eqConstAt bit 1)).
    {
      unfold O, oneAt.
      apply BProv_ass.
      simpl; auto.
    }
    unfold target.
    exact (BProv_Ax_s_hfEmptyOrStrictPredAdjoinAt_of_odd_step
      P O current half bit
      (BProv_context_cons Ax_s G (oneAt bit) _ hstep) hbitOne).
  }
  unfold boolAt in hbool.
  exact (BProv_orE Ax_s G (zeroAt bit) (oneAt bit) target
    hbool heven hodd).
Qed.

(** The local successor-code decomposition needed by cumulative PA
    induction. *)
Lemma BProv_Ax_s_hfEmptyOrStrictPredAdjoin_successor_new_using_project :
  forall (P : HFAdjoinHeadProofs),
  (forall G boundCode current,
    BProv Ax_s G
      (hfEmptyOrStrictPredAdjoinThroughTermAt boundCode) ->
    BProv Ax_s G (leTermAt (tVar current) boundCode) ->
    BProv Ax_s G (hfEmptyOrStrictPredAdjoinAt current)) ->
  (forall B G oldCode newCode,
    BProv B G (hfEmptyOrStrictPredAdjoinTermAt oldCode) ->
    BProv B G (pEq oldCode newCode) ->
    BProv B G (hfEmptyOrStrictPredAdjoinTermAt newCode)) ->
  BProv Ax_s [hfEmptyOrStrictPredAdjoinThroughAt 0]
    (hfEmptyOrStrictPredAdjoinTermAt (tSucc (tVar 0))).
Proof.
  intros P project transport.
  set (through := hfEmptyOrStrictPredAdjoinThroughAt 0).
  set (currentTerm := tSucc (tVar 0)).
  set (target := hfEmptyOrStrictPredAdjoinTermAt currentTerm).
  set (nameBody := pEq (tVar 0) (Term.rename S currentTerm)).
  assert (hnameEx : BProv Ax_s [through] (pEx nameBody)).
  {
    unfold nameBody.
    exact (BProv_exists_eq_term Ax_s [through] currentTerm).
  }
  apply (BProv_exE_of_sentences Ax_s [through] nameBody target
    sentence_ax_s hnameEx).
  set (H := nameBody :: map (rename S) [through]).
  assert (htotal : BProv Ax_s H (div2TotalAt 0)).
  { exact (BProv_Ax_s_div2TotalAt H 0). }
  apply (BProv_Ax_s_of_div2TotalAt_opened_step
    H 0 (rename S target) htotal).
  set (J := div2TotalOpenedStepContext H 0).
  assert (hstep : BProv Ax_s J (div2StepAt 2 1 0)).
  {
    unfold J, div2TotalOpenedStepContext.
    apply BProv_ass.
    simpl; auto.
  }
  assert (hheadEq : BProv Ax_s J
    (pEq (tVar 2) (tSucc (tVar 3)))).
  {
    unfold J, H, div2TotalOpenedStepContext,
      nameBody, currentTerm, through.
    apply BProv_ass.
    simpl; auto.
  }
  assert (hthrough : BProv Ax_s J
    (hfEmptyOrStrictPredAdjoinThroughTermAt (tVar 3))).
  {
    unfold J, H, through, div2TotalOpenedStepContext,
      hfEmptyOrStrictPredAdjoinThroughAt.
    repeat rewrite rename_hfEmptyOrStrictPredAdjoinThroughTermAt.
    apply BProv_ass.
    simpl; auto.
  }
  assert (hhalfLe : BProv Ax_s J
    (leTermAt (tVar 1) (tVar 3))).
  {
    exact (BProv_Ax_s_leTermAt_half_of_div2StepAt_eq_succ
      J 2 1 0 (tVar 3) hstep hheadEq).
  }
  assert (htail : BProv Ax_s J
    (hfEmptyOrStrictPredAdjoinAt 1)).
  {
    exact (project J (tVar 3) 1 hthrough hhalfLe).
  }
  assert (hnamed : BProv Ax_s J
    (hfEmptyOrStrictPredAdjoinAt 2)).
  {
    exact (BProv_Ax_s_hfEmptyOrStrictPredAdjoinAt_of_step_and_tail
      P J 2 1 0 hstep htail).
  }
  assert (htransport : BProv Ax_s J
    (hfEmptyOrStrictPredAdjoinTermAt (tSucc (tVar 3)))).
  {
    apply (transport Ax_s J (tVar 2) (tSucc (tVar 3))).
    - unfold hfEmptyOrStrictPredAdjoinAt in hnamed.
      exact hnamed.
    - exact hheadEq.
  }
  unfold target, currentTerm.
  repeat rewrite rename_hfEmptyOrStrictPredAdjoinTermAt.
  exact htransport.
Qed.

Lemma subst_hfEmptyOrStrictPredAdjoinThroughTermAt : forall sigma boundCode,
  subst sigma (hfEmptyOrStrictPredAdjoinThroughTermAt boundCode) =
  hfEmptyOrStrictPredAdjoinThroughTermAt
    (Term.subst sigma boundCode).
Proof.
  intros sigma boundCode.
  unfold hfEmptyOrStrictPredAdjoinThroughTermAt,
    hfEmptyOrStrictPredAdjoinAt.
  change
    (pAll
      (pImp
        (subst (Term.upSubst sigma)
          (ltTermAt (tVar 0)
            (tSucc (Term.rename S boundCode))))
        (subst (Term.upSubst sigma)
          (hfEmptyOrStrictPredAdjoinTermAt (tVar 0)))) =
     pAll
      (pImp
        (ltTermAt (tVar 0)
          (tSucc
            (Term.rename S (Term.subst sigma boundCode))))
        (hfEmptyOrStrictPredAdjoinTermAt (tVar 0)))).
  rewrite subst_ltTermAt.
  rewrite subst_hfEmptyOrStrictPredAdjoinTermAt.
  simpl.
  rewrite Term.subst_rename_succ_up.
  reflexivity.
Qed.

Lemma rename_hfEmptyOrStrictPredAdjoinThroughTermAt : forall r boundCode,
  rename r (hfEmptyOrStrictPredAdjoinThroughTermAt boundCode) =
  hfEmptyOrStrictPredAdjoinThroughTermAt (Term.rename r boundCode).
Proof.
  intros r boundCode.
  rewrite <- subst_var_rename.
  rewrite subst_hfEmptyOrStrictPredAdjoinThroughTermAt.
  rewrite term_subst_var_rename.
  reflexivity.
Qed.

Lemma substZero_hfEmptyOrStrictPredAdjoinThroughAt_zero :
  subst substZero (hfEmptyOrStrictPredAdjoinThroughAt 0) =
  hfEmptyOrStrictPredAdjoinThroughTermAt tZero.
Proof.
  unfold hfEmptyOrStrictPredAdjoinThroughAt.
  rewrite subst_hfEmptyOrStrictPredAdjoinThroughTermAt.
  reflexivity.
Qed.

Lemma substSuccVar_hfEmptyOrStrictPredAdjoinThroughAt_zero :
  subst substSuccVar (hfEmptyOrStrictPredAdjoinThroughAt 0) =
  hfEmptyOrStrictPredAdjoinThroughTermAt (tSucc (tVar 0)).
Proof.
  unfold hfEmptyOrStrictPredAdjoinThroughAt.
  rewrite subst_hfEmptyOrStrictPredAdjoinThroughTermAt.
  reflexivity.
Qed.

(** Equality transports the decomposition predicate between arbitrary code
    terms. *)
Lemma BProv_hfEmptyOrStrictPredAdjoinTermAt_of_eq_term :
  forall B G oldCode newCode,
  BProv B G (hfEmptyOrStrictPredAdjoinTermAt oldCode) ->
  BProv B G (pEq oldCode newCode) ->
  BProv B G (hfEmptyOrStrictPredAdjoinTermAt newCode).
Proof.
  intros B G oldCode newCode hprop heq.
  assert (hprop' : BProv B G
    (subst (instTerm oldCode)
      (hfEmptyOrStrictPredAdjoinTermAt (tVar 0)))).
  {
    rewrite subst_hfEmptyOrStrictPredAdjoinTermAt.
    exact hprop.
  }
  pose proof (BProv_eqElim B G oldCode newCode
    (hfEmptyOrStrictPredAdjoinTermAt (tVar 0)) heq hprop')
    as htransport.
  rewrite subst_hfEmptyOrStrictPredAdjoinTermAt in htransport.
  exact htransport.
Qed.

(** Project one code from the cumulative invariant. *)
Lemma BProv_Ax_s_hfEmptyOrStrictPredAdjoinAt_of_throughTermAt :
  forall G boundCode current,
  BProv Ax_s G
    (hfEmptyOrStrictPredAdjoinThroughTermAt boundCode) ->
  BProv Ax_s G (leTermAt (tVar current) boundCode) ->
  BProv Ax_s G (hfEmptyOrStrictPredAdjoinAt current).
Proof.
  intros G boundCode current hthrough hle.
  assert (hlt : BProv Ax_s G
    (ltTermAt (tVar current) (tSucc boundCode))).
  {
    exact (BProv_Ax_s_ltTermAt_succ_right_of_leTermAt
      G (tVar current) boundCode hle).
  }
  pose proof (BProv_allE Ax_s G
    (pImp
      (ltTermAt (tVar 0) (tSucc (Term.rename S boundCode)))
      (hfEmptyOrStrictPredAdjoinAt 0))
    (tVar current) hthrough) as himp.
  assert (hnorm :
    subst (instTerm (tVar current))
      (pImp
        (ltTermAt (tVar 0) (tSucc (Term.rename S boundCode)))
        (hfEmptyOrStrictPredAdjoinAt 0)) =
    pImp
      (ltTermAt (tVar current) (tSucc boundCode))
      (hfEmptyOrStrictPredAdjoinAt current)).
  {
    change
      (pImp
        (subst (instTerm (tVar current))
          (ltTermAt (tVar 0)
            (tSucc (Term.rename S boundCode))))
        (subst (instTerm (tVar current))
          (hfEmptyOrStrictPredAdjoinTermAt (tVar 0))) =
       pImp
        (ltTermAt (tVar current) (tSucc boundCode))
        (hfEmptyOrStrictPredAdjoinTermAt (tVar current))).
    rewrite subst_ltTermAt.
    rewrite subst_hfEmptyOrStrictPredAdjoinTermAt.
    simpl.
    rewrite term_subst_instTerm_rename_succ.
    reflexivity.
  }
  rewrite hnorm in himp.
  exact (BProv_mp Ax_s G _ _ himp hlt).
Qed.

(** A variable equal to zero codes the empty HF set. *)
Lemma BProv_Ax_s_hfEmptyAt_of_eqConst_zero : forall G setCode,
  BProv Ax_s G (eqConstAt setCode 0) ->
  BProv Ax_s G (hfEmptyAt setCode).
Proof.
  intros G setCode hzero.
  set (Q := map (rename S) G).
  assert (hzeroRen : BProv Ax_s Q
    (rename S (eqConstAt setCode 0))).
  {
    unfold Q.
    exact (BProv_rename_of_sentences Ax_s sentence_ax_s G
      (eqConstAt setCode 0) hzero S).
  }
  assert (hzeroQ : BProv Ax_s Q (eqConstAt (S setCode) 0)).
  {
    unfold Q in hzeroRen.
    unfold eqConstAt in *.
    simpl in hzeroRen.
    exact hzeroRen.
  }
  set (mem := hfMemAt 0 (S setCode)).
  set (C := mem :: Q).
  assert (hmem : BProv Ax_s C (hfMemAt 0 (S setCode))).
  {
    unfold C, mem.
    apply BProv_ass.
    simpl; auto.
  }
  assert (hzeroC : BProv Ax_s C (eqConstAt (S setCode) 0)).
  {
    unfold C.
    exact (BProv_context_cons Ax_s Q mem _ hzeroQ).
  }
  assert (hbot : BProv Ax_s C pBot).
  {
    exact (BProv_Ax_s_hfMemAt_bot_of_eqConst_zero
      C 0 (S setCode) hzeroC hmem).
  }
  assert (himp : BProv Ax_s Q (pImp mem pBot)).
  {
    unfold C in hbot.
    exact (BProv_impI Ax_s Q mem pBot hbot).
  }
  assert (hall : BProv Ax_s G (pAll (pImp mem pBot))).
  {
    exact (BProv_allI_of_sentences Ax_s G (pImp mem pBot)
      sentence_ax_s himp).
  }
  unfold hfEmptyAt, hfEmptyTermAt.
  unfold mem in hall.
  exact hall.
Qed.

(** Base case of the cumulative predecessor invariant. *)
Lemma BProv_Ax_s_hfEmptyOrStrictPredAdjoinThroughTermAt_zero :
  BProv Ax_s []
    (hfEmptyOrStrictPredAdjoinThroughTermAt tZero).
Proof.
  set (belowOne := ltTermAt (tVar 0) (tSucc tZero)).
  set (C := [belowOne]).
  assert (hlt : BProv Ax_s C belowOne).
  {
    unfold C.
    apply BProv_ass.
    simpl; auto.
  }
  assert (hleTerm : BProv Ax_s C (leTermAt (tVar 0) tZero)).
  {
    apply BProv_Ax_s_leTermAt_of_ltTermAt_succ_right.
    unfold belowOne in hlt.
    exact hlt.
  }
  assert (hle : BProv Ax_s C (leConstAt 0 0)).
  {
    unfold leConstAt, leTermAt.
    simpl.
    exact hleTerm.
  }
  assert (hzero : BProv Ax_s C (eqConstAt 0 0)).
  { exact (BProv_Ax_s_eqConstAt_zero_of_leConstAt_zero C 0 hle). }
  assert (hempty : BProv Ax_s C (hfEmptyAt 0)).
  { exact (BProv_Ax_s_hfEmptyAt_of_eqConst_zero C 0 hzero). }
  assert (hdecomp : BProv Ax_s C
    (hfEmptyOrStrictPredAdjoinAt 0)).
  {
    unfold hfEmptyOrStrictPredAdjoinAt,
      hfEmptyOrStrictPredAdjoinTermAt, hfEmptyAt.
    exact (BProv_orI1 Ax_s C _ _ hempty).
  }
  assert (himp : BProv Ax_s []
    (pImp belowOne (hfEmptyOrStrictPredAdjoinAt 0))).
  {
    unfold C in hdecomp.
    exact (BProv_impI Ax_s [] belowOne
      (hfEmptyOrStrictPredAdjoinAt 0) hdecomp).
  }
  unfold hfEmptyOrStrictPredAdjoinThroughTermAt.
  fold belowOne.
  exact (BProv_allI_of_sentences Ax_s []
    (pImp belowOne (hfEmptyOrStrictPredAdjoinAt 0))
    sentence_ax_s himp).
Qed.

(** Extend the cumulative invariant by one newly decomposed code. *)
Lemma BProv_Ax_s_hfEmptyOrStrictPredAdjoinThroughTermAt_succ :
  forall G boundCode,
  BProv Ax_s G
    (hfEmptyOrStrictPredAdjoinThroughTermAt boundCode) ->
  BProv Ax_s G
    (hfEmptyOrStrictPredAdjoinTermAt (tSucc boundCode)) ->
  BProv Ax_s G
    (hfEmptyOrStrictPredAdjoinThroughTermAt (tSucc boundCode)).
Proof.
  intros G boundCode hthrough hnew.
  set (bound1 := Term.rename S boundCode).
  set (oldLimit := tSucc bound1).
  set (newLimit := tSucc oldLimit).
  set (antecedent := ltTermAt (tVar 0) newLimit).
  set (target := hfEmptyOrStrictPredAdjoinAt 0).
  assert (hbody : BProv Ax_s
    (antecedent :: map (rename S) G) target).
  {
    set (C := antecedent :: map (rename S) G).
    assert (hltNew : BProv Ax_s C
      (ltTermAt (tVar 0) (tSucc oldLimit))).
    {
      unfold C, antecedent, newLimit.
      apply BProv_ass.
      simpl; auto.
    }
    assert (hcases : BProv Ax_s C
      (pOr
        (ltTermAt (tVar 0) oldLimit)
        (pEq (tVar 0) oldLimit))).
    {
      exact (BProv_Ax_s_ltTermAt_succ_right_cases
        C (tVar 0) oldLimit hltNew).
    }
    assert (hthroughC : BProv Ax_s C
      (hfEmptyOrStrictPredAdjoinThroughTermAt bound1)).
    {
      pose proof (BProv_rename_succ_context_cons_of_sentences
        Ax_s sentence_ax_s G antecedent _ hthrough) as hren.
      rewrite rename_hfEmptyOrStrictPredAdjoinThroughTermAt in hren.
      unfold C, bound1.
      exact hren.
    }
    assert (hnewC : BProv Ax_s C
      (hfEmptyOrStrictPredAdjoinTermAt oldLimit)).
    {
      pose proof (BProv_rename_succ_context_cons_of_sentences
        Ax_s sentence_ax_s G antecedent _ hnew) as hren.
      rewrite rename_hfEmptyOrStrictPredAdjoinTermAt in hren.
      unfold C, oldLimit, bound1.
      simpl in hren.
      exact hren.
    }
    assert (hstrict : BProv Ax_s
      (ltTermAt (tVar 0) oldLimit :: C) target).
    {
      set (D := ltTermAt (tVar 0) oldLimit :: C).
      assert (hlt : BProv Ax_s D
        (ltTermAt (tVar 0) (tSucc bound1))).
      {
        unfold D, oldLimit.
        apply BProv_ass.
        simpl; auto.
      }
      assert (hle : BProv Ax_s D
        (leTermAt (tVar 0) bound1)).
      {
        exact (BProv_Ax_s_leTermAt_of_ltTermAt_succ_right
          D (tVar 0) bound1 hlt).
      }
      assert (hthroughD : BProv Ax_s D
        (hfEmptyOrStrictPredAdjoinThroughTermAt bound1)).
      {
        unfold D.
        apply BProv_context_cons.
        exact hthroughC.
      }
      unfold target.
      exact (BProv_Ax_s_hfEmptyOrStrictPredAdjoinAt_of_throughTermAt
        D bound1 0 hthroughD hle).
    }
    assert (hequal : BProv Ax_s
      (pEq (tVar 0) oldLimit :: C) target).
    {
      set (D := pEq (tVar 0) oldLimit :: C).
      assert (heq : BProv Ax_s D (pEq oldLimit (tVar 0))).
      {
        apply BProv_eqSym.
        unfold D.
        apply BProv_ass.
        simpl; auto.
      }
      assert (hnewD : BProv Ax_s D
        (hfEmptyOrStrictPredAdjoinTermAt oldLimit)).
      {
        unfold D.
        apply BProv_context_cons.
        exact hnewC.
      }
      pose proof
        (BProv_hfEmptyOrStrictPredAdjoinTermAt_of_eq_term
          Ax_s D oldLimit (tVar 0) hnewD heq) as htransport.
      unfold target, hfEmptyOrStrictPredAdjoinAt.
      exact htransport.
    }
    exact (BProv_orE Ax_s C
      (ltTermAt (tVar 0) oldLimit)
      (pEq (tVar 0) oldLimit) target
      hcases hstrict hequal).
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
  unfold hfEmptyOrStrictPredAdjoinThroughTermAt.
  unfold antecedent, target, newLimit, oldLimit, bound1 in hall.
  simpl in hall.
  exact hall.
Qed.

(** Ordinary PA induction closes the cumulative invariant once the new
    successor code can be decomposed from the cumulative hypothesis. *)
Lemma BProv_Ax_s_all_hfEmptyOrStrictPredAdjoinThroughAt_of_successor_new :
  BProv Ax_s [hfEmptyOrStrictPredAdjoinThroughAt 0]
    (hfEmptyOrStrictPredAdjoinTermAt (tSucc (tVar 0))) ->
  BProv Ax_s []
    (pAll (hfEmptyOrStrictPredAdjoinThroughAt 0)).
Proof.
  intro hnew.
  set (phi := hfEmptyOrStrictPredAdjoinThroughAt 0).
  assert (hzero : BProv Ax_s [] (subst substZero phi)).
  {
    unfold phi.
    rewrite substZero_hfEmptyOrStrictPredAdjoinThroughAt_zero.
    exact BProv_Ax_s_hfEmptyOrStrictPredAdjoinThroughTermAt_zero.
  }
  assert (hthrough : BProv Ax_s [phi]
    (hfEmptyOrStrictPredAdjoinThroughTermAt (tVar 0))).
  {
    unfold phi, hfEmptyOrStrictPredAdjoinThroughAt.
    apply BProv_ass.
    simpl; auto.
  }
  assert (hsuccTerm : BProv Ax_s [phi]
    (hfEmptyOrStrictPredAdjoinThroughTermAt (tSucc (tVar 0)))).
  {
    apply (BProv_Ax_s_hfEmptyOrStrictPredAdjoinThroughTermAt_succ
      [phi] (tVar 0) hthrough).
    unfold phi in hnew.
    exact hnew.
  }
  assert (hsuccBody : BProv Ax_s [phi]
    (subst substSuccVar phi)).
  {
    unfold phi.
    rewrite substSuccVar_hfEmptyOrStrictPredAdjoinThroughAt_zero.
    exact hsuccTerm.
  }
  assert (hsuccImp : BProv Ax_s []
    (pImp phi (subst substSuccVar phi))).
  {
    exact (BProv_impI Ax_s [] phi (subst substSuccVar phi) hsuccBody).
  }
  assert (hsuccAll : BProv Ax_s []
    (pAll (pImp phi (subst substSuccVar phi)))).
  {
    exact (BProv_allI_of_sentences Ax_s []
      (pImp phi (subst substSuccVar phi)) sentence_ax_s hsuccImp).
  }
  exact (BProv_Ax_s_induction_rule [] phi hzero hsuccAll).
Qed.

(** Project the pointwise decomposition from the closed cumulative theorem. *)
Lemma BProv_Ax_s_all_hfEmptyOrStrictPredAdjoinAt_of_all_through :
  BProv Ax_s []
    (pAll (hfEmptyOrStrictPredAdjoinThroughAt 0)) ->
  BProv Ax_s [] (pAll (hfEmptyOrStrictPredAdjoinAt 0)).
Proof.
  intro hall.
  pose proof (BProv_allE Ax_s []
    (hfEmptyOrStrictPredAdjoinThroughAt 0)
    (tVar 0) hall) as hthroughRaw.
  assert (hthrough : BProv Ax_s []
    (hfEmptyOrStrictPredAdjoinThroughTermAt (tVar 0))).
  {
    unfold hfEmptyOrStrictPredAdjoinThroughAt in hthroughRaw.
    rewrite subst_hfEmptyOrStrictPredAdjoinThroughTermAt in hthroughRaw.
    exact hthroughRaw.
  }
  assert (hself : BProv Ax_s []
    (leTermAt (tVar 0) (tVar 0))).
  { exact (BProv_Ax_s_leTermAt_refl [] (tVar 0)). }
  assert (hpoint : BProv Ax_s []
    (hfEmptyOrStrictPredAdjoinAt 0)).
  {
    exact (BProv_Ax_s_hfEmptyOrStrictPredAdjoinAt_of_throughTermAt
      [] (tVar 0) 0 hthrough hself).
  }
  exact (BProv_allI_of_sentences Ax_s []
    (hfEmptyOrStrictPredAdjoinAt 0) sentence_ax_s hpoint).
Qed.

Lemma BProv_Ax_s_all_hfEmptyOrStrictPredAdjoinAt_of_cumulative_successor_new :
  BProv Ax_s [hfEmptyOrStrictPredAdjoinThroughAt 0]
    (hfEmptyOrStrictPredAdjoinTermAt (tSucc (tVar 0))) ->
  BProv Ax_s [] (pAll (hfEmptyOrStrictPredAdjoinAt 0)).
Proof.
  intro hnew.
  apply BProv_Ax_s_all_hfEmptyOrStrictPredAdjoinAt_of_all_through.
  exact
    (BProv_Ax_s_all_hfEmptyOrStrictPredAdjoinThroughAt_of_successor_new
      hnew).
Qed.

(** In the opened predecessor context ([elem], [old], [current], ...), read
    the strong-induction predicate at [old]. *)
Definition rPredOld (n : nat) : nat :=
  match n with
  | 0 => 1
  | S k => k + 3
  end.

Lemma BProv_hfStrongBelowAt_old_of_opened_pred : forall G psi,
  BProv Ax_s G (rename S (rename S (hfStrongBelowAt psi))) ->
  BProv Ax_s G
    (pImp (ltAt 1 2) (rename rPredOld psi)).
Proof.
  intros G psi hbelow.
  set (body := pImp (ltAt 0 1) (rename rSkipParam psi)).
  pose proof (BProv_allE Ax_s G
    (rename (Fol.up S) (rename (Fol.up S) body))
    (tVar 1) hbelow) as hraw.
  rewrite subst_instTerm_var in hraw.
  repeat rewrite rename_comp in hraw.
  set (R := fun n => Fol.inst 1 (Fol.up S (Fol.up S n))).
  assert (hraw' : BProv Ax_s G (rename R body)).
  {
    unfold R.
    exact hraw.
  }
  assert (hlt : rename R (ltAt 0 1) = ltAt 1 2).
  {
    unfold R, ltAt, leAt, Fol.up, Fol.inst.
    simpl.
    reflexivity.
  }
  assert (hpsi :
    rename R (rename rSkipParam psi) = rename rPredOld psi).
  {
    rewrite rename_comp.
    apply rename_ext.
    intros [|n].
    - reflexivity.
    - unfold R, rSkipParam, rPredOld, Fol.up, Fol.inst.
      simpl. lia.
  }
  unfold body in hraw'.
  change (BProv Ax_s G
    (pImp
      (rename R (ltAt 0 1))
      (rename R (rename rSkipParam psi)))) in hraw'.
  rewrite hlt, hpsi in hraw'.
  exact hraw'.
Qed.

(** Map the local [new,old,elem] slots of the generation rule to the opened
    predecessor context [elem,old,current]. *)
Definition rPredInstantiate (n : nat) : nat :=
  match n with
  | 0 => 2
  | 1 => 0
  | 2 => 1
  | S (S (S k)) => S (S (S k))
  end.

Lemma BProv_hfFiniteGenerationAt_step_of_opened_pred : forall G psi,
  BProv Ax_s G
    (rename S (rename S (rename S (hfFiniteGenerationAt psi)))) ->
  BProv Ax_s G
    (pImp
      (hfFIAdjoinGraphAt 2 1 0)
      (pImp
        (rename rPredOld psi)
        (rename rAdjStepOld psi))).
Proof.
  intros G psi hgeneration.
  set (body :=
    pImp
      (hfFIAdjoinGraphAt 0 2 1)
      (pImp
        (rename rAdjStepOld psi)
        (rename rAdjStepNew psi))).
  set (A := fun n => n + 3).
  set (R1 := fun n => Fol.inst 1 (Fol.up A n)).
  set (R2 := fun n => Fol.inst 0 (Fol.up R1 n)).
  set (R3 := fun n => Fol.inst 2 (Fol.up R2 n)).
  assert (hgenerationA : BProv Ax_s G
    (rename A (hfFiniteGenerationAt psi))).
  {
    unfold A.
    repeat rewrite rename_comp in hgeneration.
    replace (fun n : nat => S (S (S n))) with (fun n : nat => n + 3)
      in hgeneration by (apply functional_extensionality; intro n; lia).
    exact hgeneration.
  }
  assert (hstepAll : BProv Ax_s G
    (rename A (pAll (pAll (pAll body))))).
  {
    unfold hfFiniteGenerationAt in hgenerationA.
    unfold body.
    exact (BProv_andE2 Ax_s G _ _ hgenerationA).
  }
  pose proof (BProv_allE Ax_s G
    (rename (Fol.up A) (pAll (pAll body)))
    (tVar 1) hstepAll) as ha.
  rewrite subst_instTerm_var in ha.
  rewrite rename_comp in ha.
  assert (ha' : BProv Ax_s G (rename R1 (pAll (pAll body)))).
  { unfold R1. exact ha. }
  pose proof (BProv_allE Ax_s G
    (rename (Fol.up R1) (pAll body))
    (tVar 0) ha') as hb.
  rewrite subst_instTerm_var in hb.
  rewrite rename_comp in hb.
  assert (hb' : BProv Ax_s G (rename R2 (pAll body))).
  { unfold R2. exact hb. }
  pose proof (BProv_allE Ax_s G
    (rename (Fol.up R2) body)
    (tVar 2) hb') as hc.
  rewrite subst_instTerm_var in hc.
  rewrite rename_comp in hc.
  assert (hcR3 : BProv Ax_s G (rename R3 body)).
  { unfold R3. exact hc. }
  assert (hR3 : R3 = rPredInstantiate).
  {
    apply functional_extensionality.
    intros [|[|[|n]]];
      unfold R3, R2, R1, A, rPredInstantiate, Fol.up, Fol.inst;
      simpl; try reflexivity; lia.
  }
  rewrite hR3 in hcR3.
  assert (hgraph :
    rename rPredInstantiate (hfFIAdjoinGraphAt 0 2 1) =
    hfFIAdjoinGraphAt 2 1 0).
  {
    unfold hfFIAdjoinGraphAt.
    rewrite rename_hfAdjoinGraphTermAt.
    reflexivity.
  }
  assert (hold :
    rename rPredInstantiate (rename rAdjStepOld psi) =
    rename rPredOld psi).
  {
    rewrite rename_comp.
    apply rename_ext.
    intros [|n].
    - reflexivity.
    - unfold rPredInstantiate, rAdjStepOld, rPredOld.
      simpl. lia.
  }
  assert (hnew :
    rename rPredInstantiate (rename rAdjStepNew psi) =
    rename rAdjStepOld psi).
  {
    rewrite rename_comp.
    apply rename_ext.
    intros [|n].
    - reflexivity.
    - unfold rPredInstantiate, rAdjStepNew, rAdjStepOld.
      reflexivity.
  }
  unfold body in hcR3.
  change (BProv Ax_s G
    (pImp
      (rename rPredInstantiate (hfFIAdjoinGraphAt 0 2 1))
      (pImp
        (rename rPredInstantiate (rename rAdjStepOld psi))
        (rename rPredInstantiate (rename rAdjStepNew psi))))) in hcR3.
  rewrite hgraph, hold, hnew in hcR3.
  exact hcR3.
Qed.

Lemma hfEmptyOrStrictPredAdjoinAt_zero_unfold :
  hfEmptyOrStrictPredAdjoinAt 0 =
  pOr
    (hfEmptyAt 0)
    (pEx (pEx
      (pAnd (ltAt 1 2) (hfFIAdjoinGraphAt 2 1 0)))).
Proof. reflexivity. Qed.

Lemma BProv_hfFiniteGenerationAt_empty_of_current : forall G psi,
  BProv Ax_s G (rename S (hfFiniteGenerationAt psi)) ->
  BProv Ax_s G (pImp (hfEmptyAt 0) psi).
Proof.
  intros G psi hgeneration.
  assert (hbase : BProv Ax_s G
    (rename S (pAll (pImp (hfEmptyAt 0) psi)))).
  {
    unfold hfFiniteGenerationAt in hgeneration.
    exact (BProv_andE1 Ax_s G _ _ hgeneration).
  }
  exact (BProv_allE_current_of_renamed G
    (pImp (hfEmptyAt 0) psi) hbase).
Qed.

(** The local strong-induction step follows from the empty-or-proper-adjoin
    decomposition of the current code. *)
Lemma BProv_Ax_s_finiteGeneration_current_of_decomposition : forall G psi,
  BProv Ax_s G (hfEmptyOrStrictPredAdjoinAt 0) ->
  BProv Ax_s G (rename S (hfFiniteGenerationAt psi)) ->
  BProv Ax_s G (hfStrongBelowAt psi) ->
  BProv Ax_s G psi.
Proof.
  intros G psi hdecomp hgeneration hbelow.
  set (predBody := pAnd (ltAt 1 2) (hfFIAdjoinGraphAt 2 1 0)).
  set (predInner := pEx predBody).
  set (predEx := pEx predInner).
  assert (hcases : BProv Ax_s G (pOr (hfEmptyAt 0) predEx)).
  {
    rewrite hfEmptyOrStrictPredAdjoinAt_zero_unfold in hdecomp.
    unfold predEx, predInner, predBody.
    exact hdecomp.
  }
  assert (hempty : BProv Ax_s (hfEmptyAt 0 :: G) psi).
  {
    set (C := hfEmptyAt 0 :: G).
    assert (hemptyC : BProv Ax_s C (hfEmptyAt 0)).
    {
      unfold C.
      apply BProv_ass.
      simpl; auto.
    }
    assert (hgenerationC : BProv Ax_s C
      (rename S (hfFiniteGenerationAt psi))).
    { unfold C. exact (BProv_context_cons Ax_s G _ _ hgeneration). }
    pose proof (BProv_hfFiniteGenerationAt_empty_of_current
      C psi hgenerationC) as hbase.
    exact (BProv_mp Ax_s C (hfEmptyAt 0) psi hbase hemptyC).
  }
  assert (hpred : BProv Ax_s (predEx :: G) psi).
  {
    set (C := predEx :: G).
    assert (hpredEx : BProv Ax_s C (pEx (pEx predBody))).
    {
      unfold C, predEx, predInner.
      apply BProv_ass.
      simpl; auto.
    }
    apply (BProv_two_exE_of_sentences
      Ax_s sentence_ax_s C predBody psi hpredEx).
    set (H := predBody :: map (rename S)
      (pEx predBody :: map (rename S) C)).
    change (BProv Ax_s H (rename S (rename S psi))).
    assert (hpredBody : BProv Ax_s H predBody).
    {
      unfold H.
      apply BProv_ass.
      simpl; auto.
    }
    assert (hlt : BProv Ax_s H (ltAt 1 2)).
    {
      unfold predBody in hpredBody.
      exact (BProv_andE1 Ax_s H _ _ hpredBody).
    }
    assert (hgraph : BProv Ax_s H (hfFIAdjoinGraphAt 2 1 0)).
    {
      unfold predBody in hpredBody.
      exact (BProv_andE2 Ax_s H _ _ hpredBody).
    }
    assert (hbelowC : BProv Ax_s C (hfStrongBelowAt psi)).
    { unfold C. exact (BProv_context_cons Ax_s G _ _ hbelow). }
    assert (hbelowH : BProv Ax_s H
      (rename S (rename S (hfStrongBelowAt psi)))).
    {
      pose proof (BProv_lift_two_opened_of_sentences
        Ax_s sentence_ax_s C predBody _ hbelowC) as h.
      unfold H.
      exact h.
    }
    pose proof (BProv_hfStrongBelowAt_old_of_opened_pred
      H psi hbelowH) as holdImp.
    assert (hold : BProv Ax_s H (rename rPredOld psi)).
    {
      exact (BProv_mp Ax_s H (ltAt 1 2)
        (rename rPredOld psi) holdImp hlt).
    }
    assert (hgenerationC : BProv Ax_s C
      (rename S (hfFiniteGenerationAt psi))).
    { unfold C. exact (BProv_context_cons Ax_s G _ _ hgeneration). }
    assert (hgenerationH : BProv Ax_s H
      (rename S (rename S (rename S
        (hfFiniteGenerationAt psi))))).
    {
      pose proof (BProv_lift_two_opened_of_sentences
        Ax_s sentence_ax_s C predBody _ hgenerationC) as h.
      unfold H.
      exact h.
    }
    pose proof (BProv_hfFiniteGenerationAt_step_of_opened_pred
      H psi hgenerationH) as hstep.
    assert (hstepOld : BProv Ax_s H
      (pImp (rename rPredOld psi) (rename rAdjStepOld psi))).
    {
      exact (BProv_mp Ax_s H (hfFIAdjoinGraphAt 2 1 0) _
        hstep hgraph).
    }
    assert (hcurrent : BProv Ax_s H (rename rAdjStepOld psi)).
    {
      exact (BProv_mp Ax_s H (rename rPredOld psi) _
        hstepOld hold).
    }
    replace (rename rAdjStepOld psi)
      with (rename S (rename S psi)) in hcurrent.
    - exact hcurrent.
    - rewrite rename_comp.
      apply rename_ext.
      intros [|n]; reflexivity.
  }
  exact (BProv_orE Ax_s G (hfEmptyAt 0) predEx psi
    hcases hempty hpred).
Qed.

(** Generic numerical strong-induction shell.  Arithmetic enters only via
    the supplied local current-code rule. *)
Lemma BProv_Ax_s_translatedHFFiniteInductionBody_of_current : forall psi,
  (forall G,
    BProv Ax_s G (rename S (hfFiniteGenerationAt psi)) ->
    BProv Ax_s G (hfStrongBelowAt psi) ->
    BProv Ax_s G psi) ->
  BProv Ax_s [] (translatedHFFiniteInductionBody psi).
Proof.
  intros psi hcurrent.
  set (generation := hfFiniteGenerationAt psi).
  assert (hallPsi : BProv Ax_s [generation] (pAll psi)).
  {
    apply (BProv_Ax_s_all_of_strongStep_under [generation] psi).
    intros G hpremises hbelow.
    apply (hcurrent G).
    - exact (hpremises generation (or_introl eq_refl)).
    - exact hbelow.
  }
  unfold translatedHFFiniteInductionBody.
  unfold generation in hallPsi.
  exact (BProv_impI Ax_s []
    (hfFiniteGenerationAt psi) (pAll psi) hallPsi).
Qed.

Lemma BProv_Ax_s_translatedHFFiniteInductionBody_of_all_decomposition :
  BProv Ax_s [] (pAll (hfEmptyOrStrictPredAdjoinAt 0)) ->
  forall psi,
  BProv Ax_s [] (translatedHFFiniteInductionBody psi).
Proof.
  intros hall psi.
  apply BProv_Ax_s_translatedHFFiniteInductionBody_of_current.
  intros G hgeneration hbelow.
  pose proof (BProv_allE Ax_s []
    (hfEmptyOrStrictPredAdjoinAt 0) (tVar 0) hall) as hraw.
  assert (hdecomp0 : BProv Ax_s []
    (hfEmptyOrStrictPredAdjoinAt 0)).
  {
    unfold hfEmptyOrStrictPredAdjoinAt in *.
    rewrite subst_hfEmptyOrStrictPredAdjoinTermAt in hraw.
    exact hraw.
  }
  apply (BProv_Ax_s_finiteGeneration_current_of_decomposition
    G psi).
  - exact (BProv_weaken_nil Ax_s G _ hdecomp0).
  - exact hgeneration.
  - exact hbelow.
Qed.

Lemma BProv_Ax_s_translated_HF_finite_induction_of_all_decomposition :
  BProv Ax_s [] (pAll (hfEmptyOrStrictPredAdjoinAt 0)) ->
  forall phi,
  BProv Ax_s []
    (translateHFFormula (Fol.seal (HF_finite_induction_form phi))).
Proof.
  intros hall phi.
  apply BProv_Ax_s_translated_HF_finite_induction_of_body.
  exact
    (BProv_Ax_s_translatedHFFiniteInductionBody_of_all_decomposition
      hall (hfFormulaAt (fun n : nat => n) phi)).
Qed.

Lemma BProv_Ax_s_hfEmptyOrStrictPredAdjoin_successor_new_of_head_proofs :
  forall P : HFAdjoinHeadProofs,
  BProv Ax_s [hfEmptyOrStrictPredAdjoinThroughAt 0]
    (hfEmptyOrStrictPredAdjoinTermAt (tSucc (tVar 0))).
Proof.
  intro P.
  exact
    (BProv_Ax_s_hfEmptyOrStrictPredAdjoin_successor_new_using_project
      P BProv_Ax_s_hfEmptyOrStrictPredAdjoinAt_of_throughTermAt
      BProv_hfEmptyOrStrictPredAdjoinTermAt_of_eq_term).
Qed.

Lemma BProv_Ax_s_all_hfEmptyOrStrictPredAdjoinAt_of_head_proofs :
  forall P : HFAdjoinHeadProofs,
  BProv Ax_s [] (pAll (hfEmptyOrStrictPredAdjoinAt 0)).
Proof.
  intro P.
  apply
    BProv_Ax_s_all_hfEmptyOrStrictPredAdjoinAt_of_cumulative_successor_new.
  exact
    (BProv_Ax_s_hfEmptyOrStrictPredAdjoin_successor_new_of_head_proofs P).
Qed.

Lemma BProv_Ax_s_translated_HF_finite_induction_of_head_proofs :
  forall (P : HFAdjoinHeadProofs) phi,
  BProv Ax_s []
    (translateHFFormula (Fol.seal (HF_finite_induction_form phi))).
Proof.
  intros P phi.
  exact
    (BProv_Ax_s_translated_HF_finite_induction_of_all_decomposition
      (BProv_Ax_s_all_hfEmptyOrStrictPredAdjoinAt_of_head_proofs P)
      phi).
Qed.

(** The arithmetic adjunction development supplies the three binary-head
    facts isolated by [HFAdjoinHeadProofs]. *)
Definition HFAdjoinHeadProofs_total : HFAdjoinHeadProofs.
Proof.
  refine
    {| hfahp_zero_member_even_bot :=
         BProv_Ax_s_hfMemAt_bot_of_eqConst_zero_elem_low_double;
       hfahp_zero_of_shared_tail :=
         BProv_Ax_s_hfAdjoinGraph_zero_of_shared_tail |}.
  intros G newHead newTail oldHead oldTail bit elem
    hnewStep holdStep htail.
  apply (BProv_Ax_s_hfAdjoinGraph_heads_of_same_bit
    G newHead newTail oldHead oldTail bit elem
    hnewStep holdStep).
  unfold hfFIAdjoinGraphAt in htail.
  unfold hfAdjoinGraphAt.
  exact htail.
Defined.

Theorem BProv_Ax_s_all_hfEmptyOrStrictPredAdjoinAt :
  BProv Ax_s [] (pAll (hfEmptyOrStrictPredAdjoinAt 0)).
Proof.
  exact
    (BProv_Ax_s_all_hfEmptyOrStrictPredAdjoinAt_of_head_proofs
      HFAdjoinHeadProofs_total).
Qed.

(** The Ackermann translation of every finite-generation induction axiom is
    provable in PA. *)
Theorem BProv_Ax_s_translated_HF_finite_induction :
  forall phi,
  BProv Ax_s []
    (translateHFFormula (Fol.seal (HF_finite_induction_form phi))).
Proof.
  exact
    (BProv_Ax_s_translated_HF_finite_induction_of_head_proofs
      HFAdjoinHeadProofs_total).
Qed.
