(* ===================================================================== *)
(*  PAHFOrdinalCodeFunctional.v                                         *)
(*                                                                       *)
(*  Functionality of the PA-internal finite-ordinal code graph.          *)
(*                                                                       *)
(*  Two beta traces for the same raw ordinal agree pointwise: both start *)
(*  at zero, and their recurrence edges are the same Ackermann           *)
(*  self-adjunction.  The only structural input is extensionality of     *)
(*  Ackermann membership codes, exposed by                              *)
(*  [PAHFMembershipExtensionalityProof].                                 *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List.
From Stdlib Require Import Logic.FunctionalExtensionality.
From FirstOrder Require Import Fol Calculus.
From PAHF Require Import PAHF PAHFProofCalculus PAHFOrdinalCode PAHFOrdinalCodeTotal
  PAHFOrdinalCodeTotalCapacity PAHFOrdinalCodeTotalInduction
  PAHFCompositeArithmetic PAHFOrdinalCodeTermCompatibility.

Import ListNotations.
Import PA PA.Term PA.Formula.

(** Term-parametric point specialization of the Ackermann-adjoin graph. *)
Lemma BProv_hfAdjoinGraphTermAt_point_functional : forall
    (B : formula -> Prop) G query newCode oldCode elemCode,
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

(** The exact operation-facing fact used by one trace-agreement step. *)
Definition PAHFAdjoinGraphFunctionalProof : Prop :=
  forall (G : list formula)
    (newCode1 newCode2 oldCode elemCode : term),
    BProv Ax_s G
      (hfAdjoinGraphTermAt newCode1 oldCode elemCode) ->
    BProv Ax_s G
      (hfAdjoinGraphTermAt newCode2 oldCode elemCode) ->
    BProv Ax_s G (pEq newCode1 newCode2).

(** Instantiate the raw PA membership-extensionality residual at arbitrary
    output terms. *)
Lemma BProv_Ax_s_eq_of_hfSameMembersTermAt_of_extensionality : forall
    (hext : PAHFMembershipExtensionalityProof)
    G left right,
  BProv Ax_s G
    (pAll
      (iffForm
        (hfMemTermAt 0 (Term.rename S left))
        (hfMemTermAt 0 (Term.rename S right)))) ->
  BProv Ax_s G (pEq left right).
Proof.
  intros hext G left right hsame.
  unfold PAHFMembershipExtensionalityProof in hext.
  set (sigma := fun n =>
    match n with
    | 0 => right
    | 1 => left
    | _ => tZero
    end).
  pose proof (BProv_subst_of_sentences Ax_s sentence_ax_s
    [PAHFCompositeSameMembers] (pEq (tVar 1) (tVar 0))
    hext sigma) as hsub.
  assert (hleftSub :
      subst (Term.upSubst sigma) (hfMemAt 0 2) =
        hfMemTermAt 0 (Term.rename S left)).
  {
    change (subst (Term.upSubst sigma)
      (hfMemTermAt 0 (Term.rename S (tVar 1))) =
      hfMemTermAt 0 (Term.rename S left)).
    rewrite subst_up_hfMemTermAt_zero_rename_succ.
    unfold sigma. simpl. reflexivity.
  }
  assert (hrightSub :
      subst (Term.upSubst sigma) (hfMemAt 0 1) =
        hfMemTermAt 0 (Term.rename S right)).
  {
    change (subst (Term.upSubst sigma)
      (hfMemTermAt 0 (Term.rename S (tVar 0))) =
      hfMemTermAt 0 (Term.rename S right)).
    rewrite subst_up_hfMemTermAt_zero_rename_succ.
    unfold sigma. simpl. reflexivity.
  }
  assert (hsameSub : subst sigma PAHFCompositeSameMembers =
      pAll
        (iffForm
          (hfMemTermAt 0 (Term.rename S left))
          (hfMemTermAt 0 (Term.rename S right)))).
  {
    unfold PAHFCompositeSameMembers, iffForm.
    cbn [subst].
    rewrite hleftSub, hrightSub.
    reflexivity.
  }
  change (BProv Ax_s [subst sigma PAHFCompositeSameMembers]
    (pEq left right)) in hsub.
  rewrite hsameSub in hsub.
  apply (BProv_cut Ax_s
    [pAll
      (iffForm
        (hfMemTermAt 0 (Term.rename S left))
        (hfMemTermAt 0 (Term.rename S right)))]
    G (pEq left right) hsub).
  intros f hf.
  simpl in hf.
  destruct hf as [<- | []].
  exact hsame.
Qed.

(** Extensionality makes the translated Ackermann-adjoin graph functional
    in its output. *)
Theorem PAHFAdjoinGraphFunctionalProof_of_extensionality :
  PAHFMembershipExtensionalityProof ->
  PAHFAdjoinGraphFunctionalProof.
Proof.
  intros hext G newCode1 newCode2 oldCode elemCode hgraph1 hgraph2.
  set (C := map (rename S) G).
  set (leftMem := hfMemTermAt 0 (Term.rename S newCode1)).
  set (rightMem := hfMemTermAt 0 (Term.rename S newCode2)).
  set (rhs := pOr
    (hfMemTermAt 0 (Term.rename S oldCode))
    (pEq (tVar 0) (Term.rename S elemCode))).
  pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s
    G _ hgraph1 S) as hgraph1Raw.
  assert (hgraph1C : BProv Ax_s C
      (hfAdjoinGraphTermAt
        (Term.rename S newCode1)
        (Term.rename S oldCode)
        (Term.rename S elemCode))).
  {
    unfold C.
    rewrite rename_hfAdjoinGraphTermAt in hgraph1Raw.
    exact hgraph1Raw.
  }
  pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s
    G _ hgraph2 S) as hgraph2Raw.
  assert (hgraph2C : BProv Ax_s C
      (hfAdjoinGraphTermAt
        (Term.rename S newCode2)
        (Term.rename S oldCode)
        (Term.rename S elemCode))).
  {
    unfold C.
    rewrite rename_hfAdjoinGraphTermAt in hgraph2Raw.
    exact hgraph2Raw.
  }
  assert (hpoint1 : BProv Ax_s C (iffForm leftMem rhs)).
  {
    unfold leftMem, rhs.
    exact (BProv_hfAdjoinGraphTermAt_point_functional
      Ax_s C 0
      (Term.rename S newCode1)
      (Term.rename S oldCode)
      (Term.rename S elemCode) hgraph1C).
  }
  assert (hpoint2 : BProv Ax_s C (iffForm rightMem rhs)).
  {
    unfold rightMem, rhs.
    exact (BProv_hfAdjoinGraphTermAt_point_functional
      Ax_s C 0
      (Term.rename S newCode2)
      (Term.rename S oldCode)
      (Term.rename S elemCode) hgraph2C).
  }
  assert (hforward : BProv Ax_s C (pImp leftMem rightMem)).
  {
    set (D := leftMem :: C).
    assert (hleft : BProv Ax_s D leftMem).
    { apply BProv_ass. unfold D. simpl. now left. }
    assert (hpoint1D : BProv Ax_s D (iffForm leftMem rhs)).
    { exact (BProv_context_cons Ax_s C leftMem _ hpoint1). }
    assert (hpoint2D : BProv Ax_s D (iffForm rightMem rhs)).
    { exact (BProv_context_cons Ax_s C leftMem _ hpoint2). }
    assert (hrhs : BProv Ax_s D rhs).
    { exact (BProv_mp Ax_s D _ _
        (BProv_andE1 Ax_s D _ _ hpoint1D) hleft). }
    assert (hright : BProv Ax_s D rightMem).
    { exact (BProv_mp Ax_s D _ _
        (BProv_andE2 Ax_s D _ _ hpoint2D) hrhs). }
    unfold D in hright.
    exact (BProv_impI Ax_s C _ _ hright).
  }
  assert (hreverse : BProv Ax_s C (pImp rightMem leftMem)).
  {
    set (D := rightMem :: C).
    assert (hright : BProv Ax_s D rightMem).
    { apply BProv_ass. unfold D. simpl. now left. }
    assert (hpoint1D : BProv Ax_s D (iffForm leftMem rhs)).
    { exact (BProv_context_cons Ax_s C rightMem _ hpoint1). }
    assert (hpoint2D : BProv Ax_s D (iffForm rightMem rhs)).
    { exact (BProv_context_cons Ax_s C rightMem _ hpoint2). }
    assert (hrhs : BProv Ax_s D rhs).
    { exact (BProv_mp Ax_s D _ _
        (BProv_andE1 Ax_s D _ _ hpoint2D) hright). }
    assert (hleft : BProv Ax_s D leftMem).
    { exact (BProv_mp Ax_s D _ _
        (BProv_andE2 Ax_s D _ _ hpoint1D) hrhs). }
    unfold D in hleft.
    exact (BProv_impI Ax_s C _ _ hleft).
  }
  assert (hsame : BProv Ax_s G
      (pAll (iffForm leftMem rightMem))).
  {
    apply (BProv_allI_of_sentences Ax_s G _ sentence_ax_s).
    exact (PAHFProofCalculus.BProv_PA_iffForm_intro Ax_s C _ _ hforward hreverse).
  }
  unfold leftMem, rightMem in hsame.
  exact (BProv_Ax_s_eq_of_hfSameMembersTermAt_of_extensionality
    hext G newCode1 newCode2 hsame).
Qed.

(* --------------------------------------------------------------------- *)
(* Opening the two graph witnesses.                                      *)

(** Eliminate the two beta-sequence witnesses while retaining the fully
    opened graph body in the local context. *)
Lemma BProv_Ax_s_ordinalCodeGraphTermAt_elim_opened_functional : forall
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

(** Two explicit graph bodies with a common raw endpoint have equal
    advertised output codes. *)
Definition PAOrdinalCodeGraphBodyFunctionalProof : Prop :=
  forall (G : list formula)
    (sequenceCode1 sequenceStep1 sequenceCode2 sequenceStep2
      raw coded1 coded2 : term),
    BProv Ax_s G
      (ordinalCodeGraphBodyTermAt
        sequenceCode1 sequenceStep1 raw coded1) ->
    BProv Ax_s G
      (ordinalCodeGraphBodyTermAt
        sequenceCode2 sequenceStep2 raw coded2) ->
    BProv Ax_s G (pEq coded1 coded2).

(** Opened-body functionality lifts through both graph witnesses. *)
Lemma BProv_Ax_s_ordinalCodeGraphTermAt_functional_of_body_functional :
  PAOrdinalCodeGraphBodyFunctionalProof ->
  forall G raw coded1 coded2,
    BProv Ax_s G (ordinalCodeGraphTermAt raw coded1) ->
    BProv Ax_s G (ordinalCodeGraphTermAt raw coded2) ->
    BProv Ax_s G (pEq coded1 coded2).
Proof.
  intros hbodyFunctional G raw coded1 coded2 hgraph1 hgraph2.
  set (body1 := ordinalCodeGraphBodyTermAt
    (tVar 1) (tVar 0)
    (Term.rename (fun n => n + 2) raw)
    (Term.rename (fun n => n + 2) coded1)).
  set (inner1 := pEx body1).
  apply (BProv_Ax_s_ordinalCodeGraphTermAt_elim_opened_functional
    G raw coded1 (pEq coded1 coded2) hgraph1).
  set (A := body1 :: map (rename S) (inner1 :: map (rename S) G)).
  assert (hbody1A : BProv Ax_s A body1).
  { apply BProv_ass. unfold A. simpl. now left. }
  pose proof (BProv_lift_two_opened_of_sentences
    Ax_s sentence_ax_s G body1 _ hgraph2) as hgraph2Ctx2.
  assert (hgraph2A : BProv Ax_s A
      (ordinalCodeGraphTermAt
        (Term.rename (fun n => n + 2) raw)
        (Term.rename (fun n => n + 2) coded2))).
  {
    unfold A.
    rewrite !rename_ordinalCodeGraphTermAt in hgraph2Ctx2.
    rewrite !Term.rename_comp in hgraph2Ctx2.
    replace (fun x : nat => S (S x)) with
      (fun x => x + 2) in hgraph2Ctx2
      by (apply functional_extensionality; intro x; lia).
    exact hgraph2Ctx2.
  }
  set (raw2 := Term.rename (fun n => n + 2) raw).
  set (coded12 := Term.rename (fun n => n + 2) coded1).
  set (coded22 := Term.rename (fun n => n + 2) coded2).
  set (body2 := ordinalCodeGraphBodyTermAt
    (tVar 1) (tVar 0)
    (Term.rename (fun n => n + 2) raw2)
    (Term.rename (fun n => n + 2) coded22)).
  set (inner2 := pEx body2).
  assert (hnested : BProv Ax_s A (pEq coded12 coded22)).
  {
    apply (BProv_Ax_s_ordinalCodeGraphTermAt_elim_opened_functional
      A raw2 coded22 (pEq coded12 coded22)).
    - unfold raw2, coded22. exact hgraph2A.
    - set (B := body2 :: map (rename S) (inner2 :: map (rename S) A)).
      assert (hbody2B : BProv Ax_s B body2).
      { apply BProv_ass. unfold B. simpl. now left. }
      pose proof (BProv_lift_two_opened_of_sentences
        Ax_s sentence_ax_s A body2 _ hbody1A) as hbody1Ctx2.
      set (raw4 := Term.rename (fun n => n + 4) raw).
      set (coded14 := Term.rename (fun n => n + 4) coded1).
      set (coded24 := Term.rename (fun n => n + 4) coded2).
      assert (hbody1B : BProv Ax_s B
          (ordinalCodeGraphBodyTermAt
            (tVar 3) (tVar 2) raw4 coded14)).
      {
        unfold B, A in *.
        unfold body1 in hbody1Ctx2.
        rewrite !rename_ordinalCodeGraphBodyTermAt in hbody1Ctx2.
        rewrite !Term.rename_comp in hbody1Ctx2.
        replace (fun x : nat => S (S (x + 2))) with
          (fun x => x + 4) in hbody1Ctx2
          by (apply functional_extensionality; intro x; lia).
        unfold raw4, coded14.
        exact hbody1Ctx2.
      }
      assert (hbody2B' : BProv Ax_s B
          (ordinalCodeGraphBodyTermAt
            (tVar 1) (tVar 0) raw4 coded24)).
      {
        unfold body2, raw2, coded22, raw4, coded24 in *.
        rewrite !Term.rename_comp in hbody2B.
        replace (fun x : nat => x + 2 + 2) with
          (fun x => x + 4) in hbody2B
          by (apply functional_extensionality; intro x; lia).
        exact hbody2B.
      }
      pose proof (hbodyFunctional B
        (tVar 3) (tVar 2) (tVar 1) (tVar 0)
        raw4 coded14 coded24 hbody1B hbody2B') as heq.
      replace (rename S (rename S (pEq coded12 coded22))) with
        (pEq coded14 coded24).
      2: {
        unfold coded12, coded22, coded14, coded24.
        cbn [rename].
        rewrite !Term.rename_comp.
        replace (fun x : nat => S (S (x + 2))) with
          (fun x => x + 4)
          by (apply functional_extensionality; intro x; lia).
        reflexivity.
      }
      exact heq.
  }
  replace (rename S (rename S (pEq coded1 coded2))) with
    (pEq coded12 coded22).
  2: {
    unfold coded12, coded22.
    cbn [rename].
    rewrite !Term.rename_comp.
    replace (fun x : nat => S (S x)) with
      (fun x => x + 2)
      by (apply functional_extensionality; intro x; lia).
    reflexivity.
  }
  exact hnested.
Qed.

Theorem PAOrdinalCodeGraphFunctionalProof_of_body :
  PAOrdinalCodeGraphBodyFunctionalProof ->
  PAOrdinalCodeGraphFunctionalProof.
Proof.
  intros hbody G raw coded1 coded2 hgraph1 hgraph2.
  exact (BProv_Ax_s_ordinalCodeGraphTermAt_functional_of_body_functional
    hbody G raw coded1 coded2 hgraph1 hgraph2).
Qed.

(* --------------------------------------------------------------------- *)
(* Pointwise trace agreement.                                            *)

(** Two beta traces agree at [index], with both current values explicitly
    named by the existential witnesses. *)
Definition ordinalCodeTraceAgreementAt
    (sequenceCode1 sequenceStep1 sequenceCode2 sequenceStep2
      index : term) : formula :=
  pEx (pEx
    (pAnd
      (betaTermTermAt (tVar 1)
        (Term.rename (fun n => n + 2) sequenceCode1)
        (Term.rename (fun n => n + 2) sequenceStep1)
        (Term.rename (fun n => n + 2) index))
      (pAnd
        (betaTermTermAt (tVar 0)
          (Term.rename (fun n => n + 2) sequenceCode2)
          (Term.rename (fun n => n + 2) sequenceStep2)
          (Term.rename (fun n => n + 2) index))
        (pEq (tVar 1) (tVar 0))))).

Lemma subst_ordinalCodeTraceAgreementAt : forall sigma
    sequenceCode1 sequenceStep1 sequenceCode2 sequenceStep2 index,
  subst sigma
      (ordinalCodeTraceAgreementAt
        sequenceCode1 sequenceStep1 sequenceCode2 sequenceStep2 index) =
    ordinalCodeTraceAgreementAt
      (Term.subst sigma sequenceCode1)
      (Term.subst sigma sequenceStep1)
      (Term.subst sigma sequenceCode2)
      (Term.subst sigma sequenceStep2)
      (Term.subst sigma index).
Proof.
  intros sigma sequenceCode1 sequenceStep1 sequenceCode2 sequenceStep2
    index.
  unfold ordinalCodeTraceAgreementAt.
  cbn [subst].
  rewrite !subst_betaTermTermAt.
  repeat rewrite term_subst_up_up_rename_add_two.
  reflexivity.
Qed.

Lemma rename_ordinalCodeTraceAgreementAt : forall r
    sequenceCode1 sequenceStep1 sequenceCode2 sequenceStep2 index,
  rename r
      (ordinalCodeTraceAgreementAt
        sequenceCode1 sequenceStep1 sequenceCode2 sequenceStep2 index) =
    ordinalCodeTraceAgreementAt
      (Term.rename r sequenceCode1)
      (Term.rename r sequenceStep1)
      (Term.rename r sequenceCode2)
      (Term.rename r sequenceStep2)
      (Term.rename r index).
Proof.
  intros r sequenceCode1 sequenceStep1 sequenceCode2 sequenceStep2 index.
  rename_from_subst subst_ordinalCodeTraceAgreementAt.
Qed.

(** Package two named beta values and their equality. *)
Lemma BProv_ordinalCodeTraceAgreementAt_of_components : forall
    (B : formula -> Prop) G
    sequenceCode1 sequenceStep1 sequenceCode2 sequenceStep2
    index value1 value2,
  BProv B G
    (betaTermTermAt value1 sequenceCode1 sequenceStep1 index) ->
  BProv B G
    (betaTermTermAt value2 sequenceCode2 sequenceStep2 index) ->
  BProv B G (pEq value1 value2) ->
  BProv B G
    (ordinalCodeTraceAgreementAt
      sequenceCode1 sequenceStep1 sequenceCode2 sequenceStep2 index).
Proof.
  intros B G sequenceCode1 sequenceStep1 sequenceCode2 sequenceStep2
    index value1 value2 hvalue1 hvalue2 heq.
  assert (hcomponents : BProv B G
      (pAnd
        (betaTermTermAt value1 sequenceCode1 sequenceStep1 index)
        (pAnd
          (betaTermTermAt value2 sequenceCode2 sequenceStep2 index)
          (pEq value1 value2)))).
  { exact (BProv_andI B G _ _ hvalue1
      (BProv_andI B G _ _ hvalue2 heq)). }
  apply (BProv_exI B G _ value1).
  apply (BProv_exI B G _ value2).
  unfold ordinalCodeTraceAgreementAt.
  cbn [subst].
  rewrite !subst_betaTermTermAt.
  repeat rewrite term_subst_upSubst_instTerm_rename_add_two.
  repeat rewrite term_subst_instTerm_rename_succ.
  cbn [Term.subst Term.upSubst instTerm].
  repeat rewrite term_subst_instTerm_rename_succ.
  exact hcomponents.
Qed.

(** The explicit zero entries establish agreement at zero. *)
Lemma BProv_Ax_s_ordinalCodeTraceAgreementAt_zero : forall G
    sequenceCode1 sequenceStep1 sequenceCode2 sequenceStep2,
  BProv Ax_s G
    (betaTermTermAt tZero sequenceCode1 sequenceStep1 tZero) ->
  BProv Ax_s G
    (betaTermTermAt tZero sequenceCode2 sequenceStep2 tZero) ->
  BProv Ax_s G
    (ordinalCodeTraceAgreementAt
      sequenceCode1 sequenceStep1 sequenceCode2 sequenceStep2 tZero).
Proof.
  intros G sequenceCode1 sequenceStep1 sequenceCode2 sequenceStep2
    hzero1 hzero2.
  exact (BProv_ordinalCodeTraceAgreementAt_of_components
    Ax_s G sequenceCode1 sequenceStep1 sequenceCode2 sequenceStep2
    tZero tZero tZero hzero1 hzero2
    (BProv_eqRefl Ax_s G tZero)).
Qed.

(** Endpoint agreement plus each trace's endpoint beta entry forces equality
    of the advertised output codes. *)
Lemma BProv_Ax_s_eq_of_ordinalCodeTraceAgreementAt : forall G
    sequenceCode1 sequenceStep1 sequenceCode2 sequenceStep2
    raw coded1 coded2,
  BProv Ax_s G
    (betaTermTermAt coded1 sequenceCode1 sequenceStep1 raw) ->
  BProv Ax_s G
    (betaTermTermAt coded2 sequenceCode2 sequenceStep2 raw) ->
  BProv Ax_s G
    (ordinalCodeTraceAgreementAt
      sequenceCode1 sequenceStep1 sequenceCode2 sequenceStep2 raw) ->
  BProv Ax_s G (pEq coded1 coded2).
Proof.
  intros G sequenceCode1 sequenceStep1 sequenceCode2 sequenceStep2
    raw coded1 coded2 hendpoint1 hendpoint2 hagreement.
  set (body := pAnd
    (betaTermTermAt (tVar 1)
      (Term.rename (fun n => n + 2) sequenceCode1)
      (Term.rename (fun n => n + 2) sequenceStep1)
      (Term.rename (fun n => n + 2) raw))
    (pAnd
      (betaTermTermAt (tVar 0)
        (Term.rename (fun n => n + 2) sequenceCode2)
        (Term.rename (fun n => n + 2) sequenceStep2)
        (Term.rename (fun n => n + 2) raw))
      (pEq (tVar 1) (tVar 0)))).
  assert (houter : BProv Ax_s G (pEx (pEx body))).
  {
    unfold ordinalCodeTraceAgreementAt in hagreement.
    unfold body.
    exact hagreement.
  }
  apply (BProv_two_exE_of_sentences
    Ax_s sentence_ax_s G body (pEq coded1 coded2) houter).
  set (D := body :: map (rename S) (pEx body :: map (rename S) G)).
  assert (hbody : BProv Ax_s D body).
  { apply BProv_ass. unfold D. simpl. now left. }
  assert (hcurrent1 : BProv Ax_s D
      (betaTermTermAt (tVar 1)
        (Term.rename (fun n => n + 2) sequenceCode1)
        (Term.rename (fun n => n + 2) sequenceStep1)
        (Term.rename (fun n => n + 2) raw))).
  { unfold body in hbody. exact (BProv_andE1 Ax_s D _ _ hbody). }
  pose proof (BProv_andE2 Ax_s D _ _ hbody) as htail.
  assert (hcurrent2 : BProv Ax_s D
      (betaTermTermAt (tVar 0)
        (Term.rename (fun n => n + 2) sequenceCode2)
        (Term.rename (fun n => n + 2) sequenceStep2)
        (Term.rename (fun n => n + 2) raw))).
  { unfold body in htail. exact (BProv_andE1 Ax_s D _ _ htail). }
  assert (hcurrentEq : BProv Ax_s D (pEq (tVar 1) (tVar 0))).
  { unfold body in htail. exact (BProv_andE2 Ax_s D _ _ htail). }
  pose proof (BProv_lift_two_opened_of_sentences Ax_s sentence_ax_s
    G body _ hendpoint1) as hendpoint1Raw.
  assert (hendpoint1D : BProv Ax_s D
      (betaTermTermAt
        (Term.rename (fun n => n + 2) coded1)
        (Term.rename (fun n => n + 2) sequenceCode1)
        (Term.rename (fun n => n + 2) sequenceStep1)
        (Term.rename (fun n => n + 2) raw))).
  {
    unfold D.
    rewrite !rename_betaTermTermAt in hendpoint1Raw.
    rewrite !Term.rename_comp in hendpoint1Raw.
    replace (fun x : nat => S (S x)) with
      (fun x => x + 2) in hendpoint1Raw
      by (apply functional_extensionality; intro x; lia).
    exact hendpoint1Raw.
  }
  pose proof (BProv_lift_two_opened_of_sentences Ax_s sentence_ax_s
    G body _ hendpoint2) as hendpoint2Raw.
  assert (hendpoint2D : BProv Ax_s D
      (betaTermTermAt
        (Term.rename (fun n => n + 2) coded2)
        (Term.rename (fun n => n + 2) sequenceCode2)
        (Term.rename (fun n => n + 2) sequenceStep2)
        (Term.rename (fun n => n + 2) raw))).
  {
    unfold D.
    rewrite !rename_betaTermTermAt in hendpoint2Raw.
    rewrite !Term.rename_comp in hendpoint2Raw.
    replace (fun x : nat => S (S x)) with
      (fun x => x + 2) in hendpoint2Raw
      by (apply functional_extensionality; intro x; lia).
    exact hendpoint2Raw.
  }
  pose proof
    (BProv_Ax_s_eq_of_betaTermTermAt_betaTermTermAt_same_index
      D (Term.rename (fun n => n + 2) coded1) (tVar 1)
      (Term.rename (fun n => n + 2) sequenceCode1)
      (Term.rename (fun n => n + 2) sequenceStep1)
      (Term.rename (fun n => n + 2) raw)
      hendpoint1D hcurrent1) as hcurrent1ToEndpoint.
  pose proof
    (BProv_Ax_s_eq_of_betaTermTermAt_betaTermTermAt_same_index
      D (Term.rename (fun n => n + 2) coded2) (tVar 0)
      (Term.rename (fun n => n + 2) sequenceCode2)
      (Term.rename (fun n => n + 2) sequenceStep2)
      (Term.rename (fun n => n + 2) raw)
      hendpoint2D hcurrent2) as hcurrent2ToEndpoint.
  assert (heq : BProv Ax_s D
      (pEq
        (Term.rename (fun n => n + 2) coded1)
        (Term.rename (fun n => n + 2) coded2))).
  {
    exact (BProv_eqTrans Ax_s D _ _ _
      (BProv_eqSym Ax_s D _ _ hcurrent1ToEndpoint)
      (BProv_eqTrans Ax_s D _ _ _ hcurrentEq hcurrent2ToEndpoint)).
  }
  replace (rename S (rename S (pEq coded1 coded2))) with
    (pEq
      (Term.rename (fun n => n + 2) coded1)
      (Term.rename (fun n => n + 2) coded2)).
  2: {
    cbn [rename]. rewrite !Term.rename_comp.
    replace (fun x : nat => S (S x)) with
      (fun x => x + 2)
      by (apply functional_extensionality; intro x; lia).
    reflexivity.
  }
  unfold D in heq.
  exact heq.
Qed.

(* --------------------------------------------------------------------- *)
(* Public trace-agreement reduction.                                     *)

(** Exact recurrence-induction frontier: two explicit graph bodies agree
    at their common raw endpoint. *)
Definition OrdinalCodeTraceAgreementProof : Prop :=
  forall (G : list formula)
    (sequenceCode1 sequenceStep1 sequenceCode2 sequenceStep2
      raw coded1 coded2 : term),
    BProv Ax_s G
      (ordinalCodeGraphBodyTermAt
        sequenceCode1 sequenceStep1 raw coded1) ->
    BProv Ax_s G
      (ordinalCodeGraphBodyTermAt
        sequenceCode2 sequenceStep2 raw coded2) ->
    BProv Ax_s G
      (ordinalCodeTraceAgreementAt
        sequenceCode1 sequenceStep1 sequenceCode2 sequenceStep2 raw).

(** Endpoint trace agreement supplies opened-body functionality. *)
Theorem OrdinalCodeGraphBodyFunctional_of_traceAgreement :
  OrdinalCodeTraceAgreementProof ->
  PAOrdinalCodeGraphBodyFunctionalProof.
Proof.
  intros hagreement G sequenceCode1 sequenceStep1
    sequenceCode2 sequenceStep2 raw coded1 coded2 hbody1 hbody2.
  assert (htail1 : BProv Ax_s G
      (pAnd
        (betaTermTermAt coded1 sequenceCode1 sequenceStep1 raw)
        (ordinalCodeStepsTermAt sequenceCode1 sequenceStep1 raw))).
  {
    unfold ordinalCodeGraphBodyTermAt in hbody1.
    exact (BProv_andE2 Ax_s G _ _ hbody1).
  }
  assert (htail2 : BProv Ax_s G
      (pAnd
        (betaTermTermAt coded2 sequenceCode2 sequenceStep2 raw)
        (ordinalCodeStepsTermAt sequenceCode2 sequenceStep2 raw))).
  {
    unfold ordinalCodeGraphBodyTermAt in hbody2.
    exact (BProv_andE2 Ax_s G _ _ hbody2).
  }
  exact (BProv_Ax_s_eq_of_ordinalCodeTraceAgreementAt
    G sequenceCode1 sequenceStep1 sequenceCode2 sequenceStep2
    raw coded1 coded2
    (BProv_andE1 Ax_s G _ _ htail1)
    (BProv_andE1 Ax_s G _ _ htail2)
    (hagreement G sequenceCode1 sequenceStep1 sequenceCode2 sequenceStep2
      raw coded1 coded2 hbody1 hbody2)).
Qed.

(** End-to-end graph functionality from the sole trace-agreement frontier. *)
Theorem BProv_Ax_s_ordinalCodeGraphTermAt_functional_of_traceAgreement :
  OrdinalCodeTraceAgreementProof ->
  forall G raw coded1 coded2,
    BProv Ax_s G (ordinalCodeGraphTermAt raw coded1) ->
    BProv Ax_s G (ordinalCodeGraphTermAt raw coded2) ->
    BProv Ax_s G (pEq coded1 coded2).
Proof.
  intros hagreement G raw coded1 coded2 hgraph1 hgraph2.
  exact (BProv_Ax_s_ordinalCodeGraphTermAt_functional_of_body_functional
    (OrdinalCodeGraphBodyFunctional_of_traceAgreement hagreement)
    G raw coded1 coded2 hgraph1 hgraph2).
Qed.

(** Lean-compatible operation-facing alias. *)
Definition OrdinalCodeGraphFunctional : Prop :=
  PAOrdinalCodeGraphFunctionalProof.

Theorem OrdinalCodeGraphFunctional_of_traceAgreement :
  OrdinalCodeTraceAgreementProof ->
  OrdinalCodeGraphFunctional.
Proof.
  intros hagreement G raw coded1 coded2 hgraph1 hgraph2.
  exact (BProv_Ax_s_ordinalCodeGraphTermAt_functional_of_traceAgreement
    hagreement G raw coded1 coded2 hgraph1 hgraph2).
Qed.

(* --------------------------------------------------------------------- *)
(* Concrete recurrence step.                                             *)

Definition ordinalCodeStepBodyTermAt_functional
    (current next sequenceCode sequenceStep index : term) : formula :=
  pAnd
    (betaTermTermAt current sequenceCode sequenceStep index)
    (pAnd
      (betaTermTermAt next sequenceCode sequenceStep (tSucc index))
      (hfAdjoinGraphTermAt next current current)).

(** Pointwise agreement is preserved by one common self-adjoin recurrence
    edge.  Output functionality of that concrete edge is the only input. *)
Lemma BProv_Ax_s_ordinalCodeTraceAgreementAt_succ_of_adjoin_functional :
  PAHFAdjoinGraphFunctionalProof ->
  forall G sequenceCode1 sequenceStep1 sequenceCode2 sequenceStep2 index,
    BProv Ax_s G
      (ordinalCodeTraceAgreementAt
        sequenceCode1 sequenceStep1 sequenceCode2 sequenceStep2 index) ->
    BProv Ax_s G
      (ordinalCodeStepWitnessTermAt
        sequenceCode1 sequenceStep1 index) ->
    BProv Ax_s G
      (ordinalCodeStepWitnessTermAt
        sequenceCode2 sequenceStep2 index) ->
    BProv Ax_s G
      (ordinalCodeTraceAgreementAt
        sequenceCode1 sequenceStep1 sequenceCode2 sequenceStep2
        (tSucc index)).
Proof.
  intros hadjoinFunctional G sequenceCode1 sequenceStep1
    sequenceCode2 sequenceStep2 index hagreement hstep1 hstep2.
  set (target := ordinalCodeTraceAgreementAt
    sequenceCode1 sequenceStep1 sequenceCode2 sequenceStep2
    (tSucc index)).
  set (sequenceCode1A := Term.rename (fun n => n + 2) sequenceCode1).
  set (sequenceStep1A := Term.rename (fun n => n + 2) sequenceStep1).
  set (sequenceCode2A := Term.rename (fun n => n + 2) sequenceCode2).
  set (sequenceStep2A := Term.rename (fun n => n + 2) sequenceStep2).
  set (indexA := Term.rename (fun n => n + 2) index).
  set (body1 := ordinalCodeStepBodyTermAt_functional
    (tVar 1) (tVar 0) sequenceCode1A sequenceStep1A indexA).
  assert (hstep1Ex : BProv Ax_s G (pEx (pEx body1))).
  {
    unfold ordinalCodeStepWitnessTermAt in hstep1.
    unfold body1, ordinalCodeStepBodyTermAt_functional,
      sequenceCode1A, sequenceStep1A, indexA.
    exact hstep1.
  }
  apply (BProv_two_exE_of_sentences
    Ax_s sentence_ax_s G body1 target hstep1Ex).
  set (A := body1 :: map (rename S) (pEx body1 :: map (rename S) G)).
  assert (hbody1A : BProv Ax_s A body1).
  { apply BProv_ass. unfold A. simpl. now left. }
  pose proof (BProv_lift_two_opened_of_sentences Ax_s sentence_ax_s
    G body1 _ hstep2) as hstep2ARaw.
  assert (hstep2A : BProv Ax_s A
      (ordinalCodeStepWitnessTermAt sequenceCode2A sequenceStep2A indexA)).
  {
    unfold A.
    rewrite !rename_ordinalCodeStepWitnessTermAt in hstep2ARaw.
    rewrite !Term.rename_comp in hstep2ARaw.
    replace (fun x : nat => S (S x)) with
      (fun x => x + 2) in hstep2ARaw
      by (apply functional_extensionality; intro x; lia).
    unfold sequenceCode2A, sequenceStep2A, indexA.
    exact hstep2ARaw.
  }
  pose proof (BProv_lift_two_opened_of_sentences Ax_s sentence_ax_s
    G body1 _ hagreement) as hagreementARaw.
  assert (hagreementA : BProv Ax_s A
      (ordinalCodeTraceAgreementAt
        sequenceCode1A sequenceStep1A sequenceCode2A sequenceStep2A
        indexA)).
  {
    unfold A.
    rewrite !rename_ordinalCodeTraceAgreementAt in hagreementARaw.
    rewrite !Term.rename_comp in hagreementARaw.
    replace (fun x : nat => S (S x)) with
      (fun x => x + 2) in hagreementARaw
      by (apply functional_extensionality; intro x; lia).
    unfold sequenceCode1A, sequenceStep1A,
      sequenceCode2A, sequenceStep2A, indexA.
    exact hagreementARaw.
  }
  set (sequenceCode1D := Term.rename (fun n => n + 4) sequenceCode1).
  set (sequenceStep1D := Term.rename (fun n => n + 4) sequenceStep1).
  set (sequenceCode2D := Term.rename (fun n => n + 4) sequenceCode2).
  set (sequenceStep2D := Term.rename (fun n => n + 4) sequenceStep2).
  set (indexD := Term.rename (fun n => n + 4) index).
  set (body2 := ordinalCodeStepBodyTermAt_functional
    (tVar 1) (tVar 0) sequenceCode2D sequenceStep2D indexD).
  assert (hstep2Ex : BProv Ax_s A (pEx (pEx body2))).
  {
    unfold ordinalCodeStepWitnessTermAt in hstep2A.
    unfold body2, ordinalCodeStepBodyTermAt_functional,
      sequenceCode2A, sequenceStep2A, indexA,
      sequenceCode2D, sequenceStep2D, indexD in *.
    rewrite !Term.rename_comp in hstep2A.
    replace (fun x : nat => x + 2 + 2) with
      (fun x => x + 4) in hstep2A
      by (apply functional_extensionality; intro x; lia).
    exact hstep2A.
  }
  apply (BProv_two_exE_of_sentences
    Ax_s sentence_ax_s A body2 (rename S (rename S target)) hstep2Ex).
  set (D := body2 :: map (rename S) (pEx body2 :: map (rename S) A)).
  assert (hbody2D : BProv Ax_s D body2).
  { apply BProv_ass. unfold D. simpl. now left. }
  assert (hcurrent1A : BProv Ax_s A
      (betaTermTermAt (tVar 1)
        sequenceCode1A sequenceStep1A indexA)).
  {
    unfold body1, ordinalCodeStepBodyTermAt_functional in hbody1A.
    exact (BProv_andE1 Ax_s A _ _ hbody1A).
  }
  pose proof (BProv_andE2 Ax_s A _ _ hbody1A) as htail1A.
  assert (hnext1A : BProv Ax_s A
      (betaTermTermAt (tVar 0)
        sequenceCode1A sequenceStep1A (tSucc indexA))).
  {
    unfold body1, ordinalCodeStepBodyTermAt_functional in htail1A.
    exact (BProv_andE1 Ax_s A _ _ htail1A).
  }
  assert (hgraph1A : BProv Ax_s A
      (hfAdjoinGraphTermAt (tVar 0) (tVar 1) (tVar 1))).
  {
    unfold body1, ordinalCodeStepBodyTermAt_functional in htail1A.
    exact (BProv_andE2 Ax_s A _ _ htail1A).
  }
  pose proof (BProv_lift_two_opened_of_sentences Ax_s sentence_ax_s
    A body2 _ hcurrent1A) as hcurrent1DRaw.
  assert (hcurrent1D : BProv Ax_s D
      (betaTermTermAt (tVar 3)
        sequenceCode1D sequenceStep1D indexD)).
  {
    unfold D.
    unfold sequenceCode1A, sequenceStep1A, indexA,
      sequenceCode1D, sequenceStep1D, indexD in *.
    rewrite !rename_betaTermTermAt in hcurrent1DRaw.
    rewrite !Term.rename_comp in hcurrent1DRaw.
    replace (fun x : nat => S (S (x + 2))) with
      (fun x => x + 4) in hcurrent1DRaw
      by (apply functional_extensionality; intro x; lia).
    cbn [Term.rename] in hcurrent1DRaw.
    exact hcurrent1DRaw.
  }
  pose proof (BProv_lift_two_opened_of_sentences Ax_s sentence_ax_s
    A body2 _ hnext1A) as hnext1DRaw.
  assert (hnext1D : BProv Ax_s D
      (betaTermTermAt (tVar 2)
        sequenceCode1D sequenceStep1D (tSucc indexD))).
  {
    unfold D.
    unfold sequenceCode1A, sequenceStep1A, indexA,
      sequenceCode1D, sequenceStep1D, indexD in *.
    rewrite !rename_betaTermTermAt in hnext1DRaw.
    rewrite !Term.rename_comp in hnext1DRaw.
    replace (fun x : nat => S (S (x + 2))) with
      (fun x => x + 4) in hnext1DRaw
      by (apply functional_extensionality; intro x; lia).
    cbn [Term.rename] in hnext1DRaw.
    rewrite !Term.rename_comp in hnext1DRaw.
    replace (fun x : nat => S (S (x + 2))) with
      (fun x => x + 4) in hnext1DRaw
      by (apply functional_extensionality; intro x; lia).
    exact hnext1DRaw.
  }
  pose proof (BProv_lift_two_opened_of_sentences Ax_s sentence_ax_s
    A body2 _ hgraph1A) as hgraph1DRaw.
  assert (hgraph1D : BProv Ax_s D
      (hfAdjoinGraphTermAt (tVar 2) (tVar 3) (tVar 3))).
  {
    unfold D.
    rewrite !rename_hfAdjoinGraphTermAt in hgraph1DRaw.
    simpl in hgraph1DRaw.
    exact hgraph1DRaw.
  }
  pose proof (BProv_lift_two_opened_of_sentences Ax_s sentence_ax_s
    A body2 _ hagreementA) as hagreementDRaw.
  assert (hagreementD : BProv Ax_s D
      (ordinalCodeTraceAgreementAt
        sequenceCode1D sequenceStep1D sequenceCode2D sequenceStep2D
        indexD)).
  {
    unfold D.
    unfold sequenceCode1A, sequenceStep1A,
      sequenceCode2A, sequenceStep2A, indexA,
      sequenceCode1D, sequenceStep1D,
      sequenceCode2D, sequenceStep2D, indexD in *.
    rewrite !rename_ordinalCodeTraceAgreementAt in hagreementDRaw.
    rewrite !Term.rename_comp in hagreementDRaw.
    replace (fun x : nat => S (S (x + 2))) with
      (fun x => x + 4) in hagreementDRaw
      by (apply functional_extensionality; intro x; lia).
    exact hagreementDRaw.
  }
  assert (hcurrent2D : BProv Ax_s D
      (betaTermTermAt (tVar 1)
        sequenceCode2D sequenceStep2D indexD)).
  {
    unfold body2, ordinalCodeStepBodyTermAt_functional in hbody2D.
    exact (BProv_andE1 Ax_s D _ _ hbody2D).
  }
  pose proof (BProv_andE2 Ax_s D _ _ hbody2D) as htail2D.
  assert (hnext2D : BProv Ax_s D
      (betaTermTermAt (tVar 0)
        sequenceCode2D sequenceStep2D (tSucc indexD))).
  {
    unfold body2, ordinalCodeStepBodyTermAt_functional in htail2D.
    exact (BProv_andE1 Ax_s D _ _ htail2D).
  }
  assert (hgraph2D : BProv Ax_s D
      (hfAdjoinGraphTermAt (tVar 0) (tVar 1) (tVar 1))).
  {
    unfold body2, ordinalCodeStepBodyTermAt_functional in htail2D.
    exact (BProv_andE2 Ax_s D _ _ htail2D).
  }
  assert (hcurrentEq : BProv Ax_s D (pEq (tVar 3) (tVar 1))).
  {
    exact (BProv_Ax_s_eq_of_ordinalCodeTraceAgreementAt
      D sequenceCode1D sequenceStep1D sequenceCode2D sequenceStep2D
      indexD (tVar 3) (tVar 1)
      hcurrent1D hcurrent2D hagreementD).
  }
  assert (hgraph2D' : BProv Ax_s D
      (hfAdjoinGraphTermAt (tVar 0) (tVar 3) (tVar 3))).
  {
    exact (BProv_hfAdjoinGraphTermAt_congr_inputs
      Ax_s D (tVar 0) (tVar 1) (tVar 3) (tVar 1) (tVar 3)
      (BProv_eqSym Ax_s D _ _ hcurrentEq)
      (BProv_eqSym Ax_s D _ _ hcurrentEq) hgraph2D).
  }
  assert (hnextEq : BProv Ax_s D (pEq (tVar 2) (tVar 0))).
  {
    exact (hadjoinFunctional D
      (tVar 2) (tVar 0) (tVar 3) (tVar 3)
      hgraph1D hgraph2D').
  }
  assert (hresult : BProv Ax_s D
      (ordinalCodeTraceAgreementAt
        sequenceCode1D sequenceStep1D sequenceCode2D sequenceStep2D
        (tSucc indexD))).
  {
    exact (BProv_ordinalCodeTraceAgreementAt_of_components
      Ax_s D sequenceCode1D sequenceStep1D sequenceCode2D sequenceStep2D
      (tSucc indexD) (tVar 2) (tVar 0)
      hnext1D hnext2D hnextEq).
  }
  unfold target.
  rewrite !rename_ordinalCodeTraceAgreementAt.
  rewrite !Term.rename_comp.
  replace (fun x : nat => S (S (S (S x)))) with
    (fun x => x + 4)
    by (apply functional_extensionality; intro x; lia).
  unfold sequenceCode1D, sequenceStep1D,
    sequenceCode2D, sequenceStep2D, indexD in hresult.
  exact hresult.
Qed.

(** Bounded PA induction turns the concrete successor step into endpoint
    agreement for any two complete ordinal-code traces. *)
Theorem ordinalCodeTraceAgreementProof_of_adjoin_functional :
  PAHFAdjoinGraphFunctionalProof ->
  OrdinalCodeTraceAgreementProof.
Proof.
  intros hadjoinFunctional G
    sequenceCode1 sequenceStep1 sequenceCode2 sequenceStep2
    raw coded1 coded2 hbody1 hbody2.
  assert (hzero1 : BProv Ax_s G
      (betaTermTermAt tZero sequenceCode1 sequenceStep1 tZero)).
  {
    unfold ordinalCodeGraphBodyTermAt in hbody1.
    exact (BProv_andE1 Ax_s G _ _ hbody1).
  }
  pose proof (BProv_andE2 Ax_s G _ _ hbody1) as htail1.
  assert (hsteps1 : BProv Ax_s G
      (ordinalCodeStepsTermAt sequenceCode1 sequenceStep1 raw)).
  {
    unfold ordinalCodeGraphBodyTermAt in htail1.
    exact (BProv_andE2 Ax_s G _ _ htail1).
  }
  assert (hzero2 : BProv Ax_s G
      (betaTermTermAt tZero sequenceCode2 sequenceStep2 tZero)).
  {
    unfold ordinalCodeGraphBodyTermAt in hbody2.
    exact (BProv_andE1 Ax_s G _ _ hbody2).
  }
  pose proof (BProv_andE2 Ax_s G _ _ hbody2) as htail2.
  assert (hsteps2 : BProv Ax_s G
      (ordinalCodeStepsTermAt sequenceCode2 sequenceStep2 raw)).
  {
    unfold ordinalCodeGraphBodyTermAt in htail2.
    exact (BProv_andE2 Ax_s G _ _ htail2).
  }
  set (agreementZero := ordinalCodeTraceAgreementAt
    sequenceCode1 sequenceStep1 sequenceCode2 sequenceStep2 tZero).
  assert (hagreementZero : BProv Ax_s G agreementZero).
  {
    unfold agreementZero.
    exact (BProv_Ax_s_ordinalCodeTraceAgreementAt_zero
      G sequenceCode1 sequenceStep1 sequenceCode2 sequenceStep2
      hzero1 hzero2).
  }
  set (phi := pImp
    (leTermAt (tVar 0) (Term.rename S raw))
    (ordinalCodeTraceAgreementAt
      (Term.rename S sequenceCode1)
      (Term.rename S sequenceStep1)
      (Term.rename S sequenceCode2)
      (Term.rename S sequenceStep2)
      (tVar 0))).
  assert (hzeroImp : BProv Ax_s G
      (pImp (leTermAt tZero raw) agreementZero)).
  {
    apply (BProv_impI Ax_s G (leTermAt tZero raw) agreementZero).
    exact (BProv_context_cons Ax_s G (leTermAt tZero raw)
      _ hagreementZero).
  }
  assert (hzero : BProv Ax_s G (subst substZero phi)).
  {
    unfold phi.
    cbn [subst].
    rewrite subst_leTermAt.
    rewrite subst_ordinalCodeTraceAgreementAt.
    simpl.
    repeat rewrite term_substZero_rename_succ.
    unfold agreementZero in hzeroImp.
    exact hzeroImp.
  }
  set (R := map (rename S) G).
  pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
    hsteps1 S) as hsteps1RRaw.
  pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
    hsteps2 S) as hsteps2RRaw.
  set (sequenceCode1R := Term.rename S sequenceCode1).
  set (sequenceStep1R := Term.rename S sequenceStep1).
  set (sequenceCode2R := Term.rename S sequenceCode2).
  set (sequenceStep2R := Term.rename S sequenceStep2).
  set (rawR := Term.rename S raw).
  assert (hsteps1R : BProv Ax_s R
      (ordinalCodeStepsTermAt sequenceCode1R sequenceStep1R rawR)).
  {
    unfold R.
    rewrite rename_ordinalCodeStepsTermAt in hsteps1RRaw.
    unfold sequenceCode1R, sequenceStep1R, rawR.
    exact hsteps1RRaw.
  }
  assert (hsteps2R : BProv Ax_s R
      (ordinalCodeStepsTermAt sequenceCode2R sequenceStep2R rawR)).
  {
    unfold R.
    rewrite rename_ordinalCodeStepsTermAt in hsteps2RRaw.
    unfold sequenceCode2R, sequenceStep2R, rawR.
    exact hsteps2RRaw.
  }
  set (C := phi :: R).
  set (agreementCurrent := ordinalCodeTraceAgreementAt
    sequenceCode1R sequenceStep1R sequenceCode2R sequenceStep2R
    (tVar 0)).
  set (agreementNext := ordinalCodeTraceAgreementAt
    sequenceCode1R sequenceStep1R sequenceCode2R sequenceStep2R
    (tSucc (tVar 0))).
  set (leCurrent := leTermAt (tVar 0) rawR).
  set (leNext := leTermAt (tSucc (tVar 0)) rawR).
  assert (hsuccBody : BProv Ax_s C (subst substSuccVar phi)).
  {
    set (D := leNext :: C).
    assert (hleNext : BProv Ax_s D leNext).
    { apply BProv_ass. unfold D. simpl. now left. }
    assert (hleCurrent : BProv Ax_s D leCurrent).
    {
      unfold leCurrent, leNext.
      exact (BProv_Ax_s_leTermAt_pred_of_succ_le
        D (tVar 0) rawR hleNext).
    }
    assert (hphiC : BProv Ax_s C phi).
    { apply BProv_ass. unfold C. simpl. now left. }
    assert (hphiD : BProv Ax_s D phi).
    { exact (BProv_context_cons Ax_s C leNext _ hphiC). }
    assert (hih : BProv Ax_s D
        (pImp leCurrent agreementCurrent)).
    {
      unfold phi, leCurrent, agreementCurrent,
        sequenceCode1R, sequenceStep1R,
        sequenceCode2R, sequenceStep2R, rawR in hphiD.
      exact hphiD.
    }
    assert (hagreementCurrent : BProv Ax_s D agreementCurrent).
    { exact (BProv_mp Ax_s D _ _ hih hleCurrent). }
    assert (hlt : BProv Ax_s D (ltTermAt (tVar 0) rawR)).
    {
      unfold leNext in hleNext.
      exact (BProv_Ax_s_ltTermAt_of_succ_leTermAt
        D (tVar 0) rawR hleNext).
    }
    assert (hsteps1D : BProv Ax_s D
        (ordinalCodeStepsTermAt sequenceCode1R sequenceStep1R rawR)).
    {
      exact (BProv_context_two Ax_s R leNext phi _ hsteps1R).
    }
    assert (hsteps2D : BProv Ax_s D
        (ordinalCodeStepsTermAt sequenceCode2R sequenceStep2R rawR)).
    {
      exact (BProv_context_two Ax_s R leNext phi _ hsteps2R).
    }
    assert (hstep1D : BProv Ax_s D
        (ordinalCodeStepWitnessTermAt
          sequenceCode1R sequenceStep1R (tVar 0))).
    {
      exact (BProv_Ax_s_ordinalCodeStepsTermAt_step_of_ltTerm
        D sequenceCode1R sequenceStep1R rawR (tVar 0)
        hsteps1D hlt).
    }
    assert (hstep2D : BProv Ax_s D
        (ordinalCodeStepWitnessTermAt
          sequenceCode2R sequenceStep2R (tVar 0))).
    {
      exact (BProv_Ax_s_ordinalCodeStepsTermAt_step_of_ltTerm
        D sequenceCode2R sequenceStep2R rawR (tVar 0)
        hsteps2D hlt).
    }
    assert (hagreementNext : BProv Ax_s D agreementNext).
    {
      unfold agreementCurrent in hagreementCurrent.
      unfold agreementNext.
      exact
        (BProv_Ax_s_ordinalCodeTraceAgreementAt_succ_of_adjoin_functional
          hadjoinFunctional D
          sequenceCode1R sequenceStep1R sequenceCode2R sequenceStep2R
          (tVar 0) hagreementCurrent hstep1D hstep2D).
    }
    assert (hnextImp : BProv Ax_s C (pImp leNext agreementNext)).
    {
      unfold D in hagreementNext.
      exact (BProv_impI Ax_s C leNext agreementNext hagreementNext).
    }
    unfold phi.
    cbn [subst].
    rewrite subst_leTermAt.
    rewrite subst_ordinalCodeTraceAgreementAt.
    simpl.
    repeat rewrite term_substSuccVar_rename_succ.
    unfold leNext, agreementNext,
      sequenceCode1R, sequenceStep1R,
      sequenceCode2R, sequenceStep2R, rawR in hnextImp.
    exact hnextImp.
  }
  assert (hsuccImp : BProv Ax_s R
      (pImp phi (subst substSuccVar phi))).
  {
    unfold C in hsuccBody.
    exact (BProv_impI Ax_s R phi (subst substSuccVar phi) hsuccBody).
  }
  assert (hsuccAll : BProv Ax_s G
      (pAll (pImp phi (subst substSuccVar phi)))).
  {
    exact (BProv_allI_of_sentences Ax_s G _ sentence_ax_s hsuccImp).
  }
  pose proof (BProv_Ax_s_induction_rule G phi hzero hsuccAll) as hall.
  pose proof (BProv_allE Ax_s G phi raw hall) as hrawRaw.
  assert (hraw : BProv Ax_s G
      (pImp
        (leTermAt raw raw)
        (ordinalCodeTraceAgreementAt
          sequenceCode1 sequenceStep1 sequenceCode2 sequenceStep2 raw))).
  {
    unfold phi in hrawRaw.
    cbn [subst] in hrawRaw.
    rewrite subst_leTermAt in hrawRaw.
    rewrite subst_ordinalCodeTraceAgreementAt in hrawRaw.
    simpl in hrawRaw.
    repeat rewrite term_subst_instTerm_rename_succ in hrawRaw.
    exact hrawRaw.
  }
  exact (BProv_mp Ax_s G _ _ hraw
    (BProv_Ax_s_leTermAt_refl G raw)).
Qed.

(** The full coded-output functionality residual is discharged once raw PA
    membership extensionality is supplied. *)
Theorem PAOrdinalCodeGraphFunctionalProof_of_extensionality :
  PAHFMembershipExtensionalityProof ->
  PAOrdinalCodeGraphFunctionalProof.
Proof.
  intro hext.
  apply OrdinalCodeGraphFunctional_of_traceAgreement.
  apply ordinalCodeTraceAgreementProof_of_adjoin_functional.
  exact (PAHFAdjoinGraphFunctionalProof_of_extensionality hext).
Qed.

Theorem OrdinalCodeTraceAgreementProof_of_extensionality :
  PAHFMembershipExtensionalityProof ->
  OrdinalCodeTraceAgreementProof.
Proof.
  intro hext.
  apply ordinalCodeTraceAgreementProof_of_adjoin_functional.
  exact (PAHFAdjoinGraphFunctionalProof_of_extensionality hext).
Qed.

Theorem BProv_Ax_s_ordinalCodeGraphTermAt_functional_of_extensionality :
  PAHFMembershipExtensionalityProof ->
  forall G raw coded1 coded2,
    BProv Ax_s G (ordinalCodeGraphTermAt raw coded1) ->
    BProv Ax_s G (ordinalCodeGraphTermAt raw coded2) ->
    BProv Ax_s G (pEq coded1 coded2).
Proof.
  intros hext G raw coded1 coded2 hgraph1 hgraph2.
  exact (PAOrdinalCodeGraphFunctionalProof_of_extensionality
    hext G raw coded1 coded2 hgraph1 hgraph2).
Qed.

Theorem ordinalCodeGraphFunctional_of_extensionality :
  PAHFMembershipExtensionalityProof ->
  OrdinalCodeGraphFunctional.
Proof.
  exact PAOrdinalCodeGraphFunctionalProof_of_extensionality.
Qed.
