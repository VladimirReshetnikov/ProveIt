(* ===================================================================== *)
(*  PAHFOrdinalCodeAddCore.v                                            *)
(*                                                                       *)
(*  Arithmetic core for reverse-translated HF addition.                 *)
(*                                                                       *)
(*  Closed HFFin operation laws are instantiated at arbitrary PA terms;  *)
(*  subsequent ordinal induction is kept behind explicit graph-law       *)
(*  interfaces so it composes with the independently proved graph tower. *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List Logic.FunctionalExtensionality.
From FirstOrder Require Import Fol Calculus.
From PAHF Require Import PAHF PAHFOrdinalCode
  PAHFOrdinalCodeTotalInduction PAHFRoundTripArithmetic
  PAHFOrdinalCodeTermCompatibility
  PAHFOrdinalCodeInjective PAHFOrdinalCodeRange PAHFTranslatedOperations
  PAHFOrdinalCodeTermOperations.

Import ListNotations.
Import PA PA.Term PA.Formula.

(** Exact successor edge used by the addition recursion.  The term-base
    module supplies this from graph successor closure, output functionality,
    and Ackermann-adjoin totality. *)
Definition PAOrdinalCodeSuccAdjoinCompatibility : Prop :=
  forall (G : list formula) (raw pred out : term),
    BProv Ax_s G (ordinalCodeGraphTermAt raw pred) ->
    BProv Ax_s G
      (iffForm
        (hfAdjoinGraphTermAt out pred pred)
        (ordinalCodeGraphTermAt (tSucc raw) out)).

Definition addTermSubst (out left right : term) (n : nat) : term :=
  match n with
  | 0 => right
  | 1 => left
  | 2 => out
  | S (S (S k)) => tVar (k + 3)
  end.

Definition hfAddGraphTermAt
    (out left right : term) : formula :=
  subst (addTermSubst out left right) (hfAddGraphAt 2 1 0).

Lemma hfAddGraphAt_eq_termAt : forall out left right,
  hfAddGraphAt out left right =
    hfAddGraphTermAt (tVar out) (tVar left) (tVar right).
Proof.
  intros out left right.
  set (r := fun n =>
    match n with
    | 0 => right
    | 1 => left
    | 2 => out
    | S (S (S k)) => k + 3
    end).
  assert (hsubst :
      addTermSubst (tVar out) (tVar left) (tVar right) =
      fun n => tVar (r n)).
  {
    apply functional_extensionality.
    intros [|[|[|n]]]; reflexivity.
  }
  assert (hsource : Fol.rename r (addGraphAt 2 1 0) =
      addGraphAt out left right).
  {
    rewrite rename_addGraphAt.
    unfold r.
    reflexivity.
  }
  unfold hfAddGraphTermAt, hfAddGraphAt.
  rewrite hsubst.
  rewrite subst_var_rename.
  rewrite <- hsource.
  apply hfFormulaAt_id_rename.
Qed.

Lemma subst_hfAddGraphTermAt : forall sigma out left right,
  subst sigma (hfAddGraphTermAt out left right) =
    hfAddGraphTermAt
      (Term.subst sigma out)
      (Term.subst sigma left)
      (Term.subst sigma right).
Proof.
  intros sigma out left right.
  unfold hfAddGraphTermAt.
  rewrite subst_comp.
  apply subst_ext_free.
  intros n hn.
  destruct (hfFormulaAt_free (addGraphAt 2 1 0)
    (fun n => n) n hn) as [m [hm ->]].
  destruct (addGraphAt_free m 2 1 0 hm) as [-> | [-> | ->]];
    reflexivity.
Qed.

Lemma rename_hfAddGraphTermAt : forall r out left right,
  rename r (hfAddGraphTermAt out left right) =
    hfAddGraphTermAt
      (Term.rename r out)
      (Term.rename r left)
      (Term.rename r right).
Proof.
  intros r out left right.
  rename_from_subst subst_hfAddGraphTermAt.
Qed.

Lemma compositeAddCoreAt_eq_termAt : forall codedOut,
  compositeAddCoreAt codedOut =
    hfAddGraphTermAt
      (tVar (codedOut + 2)) (tVar 1) (tVar 0).
Proof.
  intro codedOut.
  rewrite <- hfAddGraphAt_eq_termAt.
  unfold compositeAddCoreAt, hfAddGraphAt.
  set (r := compositeAddCoreSlotMap codedOut).
  assert (hsource : Fol.rename r (addGraphAt 2 1 0) =
      addGraphAt (codedOut + 2) 1 0).
  {
    rewrite rename_addGraphAt.
    unfold r, compositeAddCoreSlotMap.
    replace (codedOut + 0 + 2) with (codedOut + 2) by lia.
    reflexivity.
  }
  rewrite <- hsource.
  rewrite hfFormulaAt_source_rename.
  apply hfFormulaAt_ext.
  intro n; reflexivity.
Qed.

Lemma hfEmptyCodeAt_eq_termAt : forall slot,
  hfEmptyCodeAt slot = hfEmptyTermAt (tVar slot).
Proof.
  intro slot.
  unfold hfEmptyCodeAt, hfEmptyTermAt, HF_emptyAt.
  cbn [hfFormulaAt hfUpVarMap Term.rename].
  rewrite hfMemTermAt_var.
  reflexivity.
Qed.

Lemma addHFOrdinalLikeAt_eq_domainTermAt : forall slot,
  addHFOrdinalLikeAt slot =
    subst (instTerm (tVar slot)) codedOrdinalDomain.
Proof.
  intro slot.
  assert (hsource :
      Fol.rename (Fol.inst slot) domainForm = HF_ordinalLikeAt slot).
  {
    unfold domainForm, HF_ordinalLikeAt, HF_transitiveAt,
      HF_memTotalOnAt.
    cbn [Fol.rename Fol.up Fol.inst].
    reflexivity.
  }
  unfold addHFOrdinalLikeAt, codedOrdinalDomain, translateHFFormula.
  rewrite subst_instTerm_var.
  rewrite <- hsource.
  apply hfFormulaAt_id_rename.
Qed.

Lemma subst_domainTermAt : forall sigma coded,
  subst sigma (subst (instTerm coded) codedOrdinalDomain) =
    subst (instTerm (Term.subst sigma coded)) codedOrdinalDomain.
Proof.
  intros sigma coded.
  rewrite subst_comp.
  apply subst_ext_free.
  intros n hn.
  pose proof (codedOrdinalDomain_free n hn) as ->.
  reflexivity.
Qed.

Lemma BProv_Ax_s_hfAddGraphTermAt_zero_right : forall
    (P : TranslatedHFFinAxiomProofs) G out left right,
  BProv Ax_s G (hfEmptyTermAt right) ->
  BProv Ax_s G (pEq out left) ->
  BProv Ax_s G (hfAddGraphTermAt out left right).
Proof.
  intros P G out left right hright hout.
  assert (hall : BProv Ax_s G
      (pAll (pAll (pAll
        (pImp
          (hfEmptyTermAt (tVar 1))
          (pImp
            (pEq (tVar 0) (tVar 2))
            (hfAddGraphTermAt (tVar 0) (tVar 2) (tVar 1)))))))).
  {
    pose proof (BProv_weaken_nil Ax_s G _
      (BProv_Ax_s_addZeroRightSentence P)) as h.
    repeat rewrite hfEmptyCodeAt_eq_termAt in h.
    repeat rewrite hfAddGraphAt_eq_termAt in h.
    exact h.
  }
  pose proof (BProv_allE Ax_s G _ left hall) as hleft.
  pose proof (BProv_allE Ax_s G _ right hleft) as hright0.
  pose proof (BProv_allE Ax_s G _ out hright0) as hout0.
  assert (himp : BProv Ax_s G
      (pImp (hfEmptyTermAt right)
        (pImp (pEq out left)
          (hfAddGraphTermAt out left right)))).
  {
    cbn [subst instTerm Term.subst Term.upSubst] in hout0.
    repeat rewrite subst_hfEmptyTermAt in hout0.
    repeat rewrite subst_hfAddGraphTermAt in hout0.
    repeat rewrite Term.subst_rename_succ_up in hout0.
    repeat rewrite term_subst_instTerm_rename_succ in hout0.
    cbn [Term.subst Term.upSubst instTerm] in hout0.
    repeat rewrite Term.subst_rename_succ_up in hout0.
    repeat rewrite term_subst_instTerm_rename_succ in hout0.
    exact hout0.
  }
  exact (BProv_mp Ax_s G _ _
    (BProv_mp Ax_s G _ _ himp hright) hout).
Qed.

Lemma BProv_Ax_s_hfAddGraphTermAt_succ_right : forall
    (P : TranslatedHFFinAxiomProofs) G
    outSucc out left rightSucc right,
  BProv Ax_s G (subst (instTerm right) codedOrdinalDomain) ->
  BProv Ax_s G (hfAdjoinGraphTermAt rightSucc right right) ->
  BProv Ax_s G (hfAdjoinGraphTermAt outSucc out out) ->
  BProv Ax_s G (hfAddGraphTermAt out left right) ->
  BProv Ax_s G (hfAddGraphTermAt outSucc left rightSucc).
Proof.
  intros P G outSucc out left rightSucc right
    hrightDomain hrightSucc houtSucc hadd.
  assert (hall : BProv Ax_s G
      (pAll (pAll (pAll (pAll (pAll
        (pImp
          (subst (instTerm (tVar 3)) codedOrdinalDomain)
          (pImp
            (hfAdjoinGraphTermAt (tVar 2) (tVar 3) (tVar 3))
            (pImp
              (hfAdjoinGraphTermAt (tVar 0) (tVar 1) (tVar 1))
              (pImp
                (hfAddGraphTermAt (tVar 1) (tVar 4) (tVar 3))
                (hfAddGraphTermAt (tVar 0) (tVar 4) (tVar 2)))))))))))).
  {
    pose proof (BProv_weaken_nil Ax_s G _
      (BProv_Ax_s_addSuccRightSentence P)) as h.
    rewrite addHFOrdinalLikeAt_eq_domainTermAt in h.
    repeat rewrite hfAddGraphAt_eq_termAt in h.
    exact h.
  }
  pose proof (BProv_allE Ax_s G _ left hall) as hleft.
  pose proof (BProv_allE Ax_s G _ right hleft) as hright0.
  pose proof (BProv_allE Ax_s G _ rightSucc hright0) as hrightSucc0.
  pose proof (BProv_allE Ax_s G _ out hrightSucc0) as hout0.
  pose proof (BProv_allE Ax_s G _ outSucc hout0) as houtSucc0.
  assert (himp : BProv Ax_s G
      (pImp (subst (instTerm right) codedOrdinalDomain)
        (pImp (hfAdjoinGraphTermAt rightSucc right right)
          (pImp (hfAdjoinGraphTermAt outSucc out out)
            (pImp (hfAddGraphTermAt out left right)
              (hfAddGraphTermAt outSucc left rightSucc)))))).
  {
    cbn [subst instTerm Term.subst Term.upSubst] in houtSucc0.
    repeat rewrite subst_domainTermAt in houtSucc0.
    repeat rewrite subst_hfAdjoinGraphTermAt in houtSucc0.
    repeat rewrite subst_hfAddGraphTermAt in houtSucc0.
    repeat rewrite Term.subst_rename_succ_up in houtSucc0.
    repeat rewrite term_subst_instTerm_rename_succ in houtSucc0.
    cbn [Term.subst Term.upSubst instTerm] in houtSucc0.
    repeat rewrite subst_domainTermAt in houtSucc0.
    repeat rewrite subst_hfAdjoinGraphTermAt in houtSucc0.
    repeat rewrite subst_hfAddGraphTermAt in houtSucc0.
    repeat rewrite Term.subst_rename_succ_up in houtSucc0.
    repeat rewrite term_subst_instTerm_rename_succ in houtSucc0.
    exact houtSucc0.
  }
  exact (BProv_mp Ax_s G _ _
    (BProv_mp Ax_s G _ _
      (BProv_mp Ax_s G _ _
        (BProv_mp Ax_s G _ _ himp hrightDomain)
        hrightSucc) houtSucc) hadd).
Qed.

Lemma BProv_Ax_s_hfAddGraphTermAt_functional : forall
    (P : TranslatedHFFinAxiomProofs) G out1 out2 left right,
  BProv Ax_s G (subst (instTerm right) codedOrdinalDomain) ->
  BProv Ax_s G (hfAddGraphTermAt out1 left right) ->
  BProv Ax_s G (hfAddGraphTermAt out2 left right) ->
  BProv Ax_s G (pEq out1 out2).
Proof.
  intros P G out1 out2 left right hrightDomain hadd1 hadd2.
  assert (hall : BProv Ax_s G
      (pAll (pAll (pAll (pAll
        (pImp
          (subst (instTerm (tVar 2)) codedOrdinalDomain)
          (pImp
            (hfAddGraphTermAt (tVar 1) (tVar 3) (tVar 2))
            (pImp
              (hfAddGraphTermAt (tVar 0) (tVar 3) (tVar 2))
              (pEq (tVar 1) (tVar 0)))))))))).
  {
    pose proof (BProv_weaken_nil Ax_s G _
      (BProv_Ax_s_addFunctionalSentence P)) as h.
    rewrite addHFOrdinalLikeAt_eq_domainTermAt in h.
    repeat rewrite hfAddGraphAt_eq_termAt in h.
    exact h.
  }
  pose proof (BProv_allE Ax_s G _ left hall) as hleft.
  pose proof (BProv_allE Ax_s G _ right hleft) as hright0.
  pose proof (BProv_allE Ax_s G _ out1 hright0) as hout1.
  pose proof (BProv_allE Ax_s G _ out2 hout1) as hout2.
  assert (himp : BProv Ax_s G
      (pImp (subst (instTerm right) codedOrdinalDomain)
        (pImp (hfAddGraphTermAt out1 left right)
          (pImp (hfAddGraphTermAt out2 left right)
            (pEq out1 out2))))).
  {
    cbn [subst instTerm Term.subst Term.upSubst] in hout2.
    repeat rewrite subst_domainTermAt in hout2.
    repeat rewrite subst_hfAddGraphTermAt in hout2.
    repeat rewrite Term.subst_rename_succ_up in hout2.
    repeat rewrite term_subst_instTerm_rename_succ in hout2.
    cbn [Term.subst Term.upSubst instTerm] in hout2.
    repeat rewrite subst_domainTermAt in hout2.
    repeat rewrite subst_hfAddGraphTermAt in hout2.
    repeat rewrite Term.subst_rename_succ_up in hout2.
    repeat rewrite term_subst_instTerm_rename_succ in hout2.
    exact hout2.
  }
  exact (BProv_mp Ax_s G _ _
    (BProv_mp Ax_s G _ _
      (BProv_mp Ax_s G _ _ himp hrightDomain) hadd1) hadd2).
Qed.

Lemma BProv_Ax_s_codedOrdinalDomain_of_graph : forall
    (hcodomain : PAOrdinalCodeGraphCodomainProof)
    G raw coded,
  BProv Ax_s G (ordinalCodeGraphTermAt raw coded) ->
  BProv Ax_s G (subst (instTerm coded) codedOrdinalDomain).
Proof.
  intros hcodomain G raw coded hgraph.
  apply (hcodomain G coded).
  unfold ordinalCodeGraphRangeExistsTermAt.
  apply (BProv_exI Ax_s G _ raw).
  rewrite subst_ordinalCodeGraphTermAt.
  cbn [instTerm Term.subst].
  rewrite term_subst_instTerm_rename_succ.
  exact hgraph.
Qed.

Lemma BProv_Ax_s_hfEmptyTermAt_of_eq_zero : forall G t,
  BProv Ax_s G (pEq t tZero) ->
  BProv Ax_s G (hfEmptyTermAt t).
Proof.
  intros G t heq.
  set (context := hfEmptyTermAt (tVar 0)).
  assert (hzero : BProv Ax_s G
      (subst (instTerm tZero) context)).
  {
    unfold context.
    rewrite subst_hfEmptyTermAt.
    cbn [instTerm Term.subst].
    exact (BProv_weaken_nil Ax_s G _ BProv_Ax_s_hfEmptyTermAt_zero).
  }
  pose proof (BProv_eqElim Ax_s G tZero t context
    (BProv_eqSym Ax_s G _ _ heq) hzero) as htransport.
  unfold context in htransport.
  repeat rewrite subst_hfEmptyTermAt in htransport.
  cbn [instTerm Term.subst] in htransport.
  repeat rewrite term_subst_instTerm_rename_succ in htransport.
  exact htransport.
Qed.

(** Base case of ordinal-code addition.  The only HF fact needed here is
    addition by the empty code; output uniqueness on both graph sides turns
    that canonical witness into an equivalence for an arbitrary output. *)
Lemma BProv_Ax_s_ordinalCodeAddCore_zero : forall
    (P : TranslatedHFFinAxiomProofs)
    (hcodomain : PAOrdinalCodeGraphCodomainProof)
    (hfunctional : PAOrdinalCodeGraphFunctionalProof)
    G leftRaw leftCode rightCode out,
  BProv Ax_s G (ordinalCodeGraphTermAt leftRaw leftCode) ->
  BProv Ax_s G (ordinalCodeGraphTermAt tZero rightCode) ->
  BProv Ax_s G
    (iffForm
      (hfAddGraphTermAt out leftCode rightCode)
      (ordinalCodeGraphTermAt (tAdd leftRaw tZero) out)).
Proof.
  intros P hcodomain hfunctional G leftRaw leftCode rightCode out
    hleft hright.
  pose proof
    (BProv_Ax_s_eq_zero_of_ordinalCodeGraphTermAt_zero
      G rightCode hright) as hrightEq.
  pose proof
    (BProv_Ax_s_hfEmptyTermAt_of_eq_zero G rightCode hrightEq)
    as hrightEmpty.
  pose proof
    (BProv_Ax_s_codedOrdinalDomain_of_graph
      hcodomain G tZero rightCode hright) as hrightDomain.
  assert (hbase : BProv Ax_s G
      (hfAddGraphTermAt leftCode leftCode rightCode)).
  {
    exact (BProv_Ax_s_hfAddGraphTermAt_zero_right
      P G leftCode leftCode rightCode hrightEmpty
      (BProv_eqRefl Ax_s G leftCode)).
  }
  pose proof (BProv_Ax_s_addZero_term G leftRaw) as haddZero.
  assert (hforward : BProv Ax_s G
      (pImp
        (hfAddGraphTermAt out leftCode rightCode)
        (ordinalCodeGraphTermAt (tAdd leftRaw tZero) out))).
  {
    apply BProv_impI.
    set (C := hfAddGraphTermAt out leftCode rightCode :: G).
    assert (hadd : BProv Ax_s C
        (hfAddGraphTermAt out leftCode rightCode)).
    { apply BProv_ass. unfold C. simpl. now left. }
    assert (houtEq : BProv Ax_s C (pEq out leftCode)).
    {
      exact (BProv_Ax_s_hfAddGraphTermAt_functional
        P C out leftCode leftCode rightCode
        (BProv_context_cons Ax_s G
          (hfAddGraphTermAt out leftCode rightCode) _ hrightDomain)
        hadd
        (BProv_context_cons Ax_s G
          (hfAddGraphTermAt out leftCode rightCode) _ hbase)).
    }
    exact (BProv_ordinalCodeGraphTermAt_congr
      Ax_s C leftRaw (tAdd leftRaw tZero) leftCode out
      (BProv_eqSym Ax_s C _ _
        (BProv_context_cons Ax_s G
          (hfAddGraphTermAt out leftCode rightCode) _ haddZero))
      (BProv_eqSym Ax_s C _ _ houtEq)
      (BProv_context_cons Ax_s G
        (hfAddGraphTermAt out leftCode rightCode) _ hleft)).
  }
  assert (hreverse : BProv Ax_s G
      (pImp
        (ordinalCodeGraphTermAt (tAdd leftRaw tZero) out)
        (hfAddGraphTermAt out leftCode rightCode))).
  {
    apply BProv_impI.
    set (C := ordinalCodeGraphTermAt (tAdd leftRaw tZero) out :: G).
    assert (htarget : BProv Ax_s C
        (ordinalCodeGraphTermAt (tAdd leftRaw tZero) out)).
    { apply BProv_ass. unfold C. simpl. now left. }
    assert (houtGraph : BProv Ax_s C
        (ordinalCodeGraphTermAt leftRaw out)).
    {
      exact (BProv_ordinalCodeGraphTermAt_congr_raw
        Ax_s C (tAdd leftRaw tZero) leftRaw out
        (BProv_context_cons Ax_s G
          (ordinalCodeGraphTermAt (tAdd leftRaw tZero) out) _ haddZero)
        htarget).
    }
    assert (houtEq : BProv Ax_s C (pEq out leftCode)).
    {
      exact (hfunctional C leftRaw out leftCode
        houtGraph
        (BProv_context_cons Ax_s G
          (ordinalCodeGraphTermAt (tAdd leftRaw tZero) out) _ hleft)).
    }
    exact (BProv_Ax_s_hfAddGraphTermAt_zero_right
      P C out leftCode rightCode
      (BProv_context_cons Ax_s G
        (ordinalCodeGraphTermAt (tAdd leftRaw tZero) out) _ hrightEmpty)
      houtEq).
  }
  exact (PAHFProofCalculus.BProv_PA_iffForm_intro Ax_s G _ _ hforward hreverse).
Qed.

(** The output predicate packages compatibility for every possible code of
    one fixed right-hand PA value. *)
Definition ordinalCodeAddOutputTermAt
    (leftRaw leftCode rightRaw rightCode : term) : formula :=
  pAll
    (iffForm
      (hfAddGraphTermAt
        (tVar 0)
        (Term.rename S leftCode)
        (Term.rename S rightCode))
      (ordinalCodeGraphTermAt
        (Term.rename S (tAdd leftRaw rightRaw))
        (tVar 0))).

Lemma subst_ordinalCodeAddOutputTermAt : forall sigma
    leftRaw leftCode rightRaw rightCode,
  subst sigma
      (ordinalCodeAddOutputTermAt
        leftRaw leftCode rightRaw rightCode) =
    ordinalCodeAddOutputTermAt
      (Term.subst sigma leftRaw)
      (Term.subst sigma leftCode)
      (Term.subst sigma rightRaw)
      (Term.subst sigma rightCode).
Proof.
  intros sigma leftRaw leftCode rightRaw rightCode.
  unfold ordinalCodeAddOutputTermAt, iffForm.
  cbn [subst].
  rewrite subst_hfAddGraphTermAt.
  rewrite subst_ordinalCodeGraphTermAt.
  cbn [Term.subst Term.upSubst].
  repeat rewrite Term.subst_rename_succ_up.
  reflexivity.
Qed.

Lemma rename_ordinalCodeAddOutputTermAt : forall r
    leftRaw leftCode rightRaw rightCode,
  rename r
      (ordinalCodeAddOutputTermAt
        leftRaw leftCode rightRaw rightCode) =
    ordinalCodeAddOutputTermAt
      (Term.rename r leftRaw)
      (Term.rename r leftCode)
      (Term.rename r rightRaw)
      (Term.rename r rightCode).
Proof.
  intros r leftRaw leftCode rightRaw rightCode.
  rename_from_subst subst_ordinalCodeAddOutputTermAt.
Qed.

Lemma BProv_Ax_s_ordinalCodeAddOutputTermAt_at : forall
    G leftRaw leftCode rightRaw rightCode out,
  BProv Ax_s G
    (ordinalCodeAddOutputTermAt
      leftRaw leftCode rightRaw rightCode) ->
  BProv Ax_s G
    (iffForm
      (hfAddGraphTermAt out leftCode rightCode)
      (ordinalCodeGraphTermAt (tAdd leftRaw rightRaw) out)).
Proof.
  intros G leftRaw leftCode rightRaw rightCode out hall.
  pose proof (BProv_allE Ax_s G _ out hall) as hraw.
  unfold ordinalCodeAddOutputTermAt, iffForm in hraw.
  cbn [subst instTerm Term.subst Term.upSubst] in hraw.
  repeat rewrite subst_hfAddGraphTermAt in hraw.
  repeat rewrite subst_ordinalCodeGraphTermAt in hraw.
  cbn [Term.subst Term.upSubst instTerm] in hraw.
  repeat rewrite Term.subst_rename_succ_up in hraw.
  repeat rewrite term_subst_instTerm_rename_succ in hraw.
  exact hraw.
Qed.

(** A point says that every graph output for one right-hand PA value satisfies
    the output predicate.  This form is deliberately stable under PA
    induction in [rightRaw]. *)
Definition ordinalCodeAddPointTermAt
    (leftRaw leftCode rightRaw : term) : formula :=
  pAll
    (pImp
      (ordinalCodeGraphTermAt
        (Term.rename S rightRaw) (tVar 0))
      (ordinalCodeAddOutputTermAt
        (Term.rename S leftRaw)
        (Term.rename S leftCode)
        (Term.rename S rightRaw)
        (tVar 0))).

Lemma subst_ordinalCodeAddPointTermAt : forall sigma
    leftRaw leftCode rightRaw,
  subst sigma
      (ordinalCodeAddPointTermAt leftRaw leftCode rightRaw) =
    ordinalCodeAddPointTermAt
      (Term.subst sigma leftRaw)
      (Term.subst sigma leftCode)
      (Term.subst sigma rightRaw).
Proof.
  intros sigma leftRaw leftCode rightRaw.
  unfold ordinalCodeAddPointTermAt.
  cbn [subst].
  rewrite subst_ordinalCodeGraphTermAt.
  rewrite subst_ordinalCodeAddOutputTermAt.
  cbn [Term.subst Term.upSubst].
  repeat rewrite Term.subst_rename_succ_up.
  reflexivity.
Qed.

Lemma rename_ordinalCodeAddPointTermAt : forall r
    leftRaw leftCode rightRaw,
  rename r
      (ordinalCodeAddPointTermAt leftRaw leftCode rightRaw) =
    ordinalCodeAddPointTermAt
      (Term.rename r leftRaw)
      (Term.rename r leftCode)
      (Term.rename r rightRaw).
Proof.
  intros r leftRaw leftCode rightRaw.
  rename_from_subst subst_ordinalCodeAddPointTermAt.
Qed.

(** Successor step at already selected predecessor outputs.  In the forward
    direction we deliberately use graph totality for the successor sum,
    instead of opening a second, unrelated HF-adjoin existence proof.  The
    exact successor/adjoin equivalence then makes that graph witness the
    canonical output of the translated addition recursion. *)
Lemma BProv_Ax_s_ordinalCodeAddCore_succ_of_pred : forall
    (P : TranslatedHFFinAxiomProofs)
    (hcodomain : PAOrdinalCodeGraphCodomainProof)
    (hsucc : PAOrdinalCodeSuccAdjoinCompatibility)
    (htotal : PAOrdinalCodeGraphTotalProof)
    G leftRaw leftCode rightRaw rightCode rightSuccCode predOut out,
  BProv Ax_s G (ordinalCodeGraphTermAt rightRaw rightCode) ->
  BProv Ax_s G
    (ordinalCodeGraphTermAt (tSucc rightRaw) rightSuccCode) ->
  BProv Ax_s G
    (ordinalCodeGraphTermAt (tAdd leftRaw rightRaw) predOut) ->
  BProv Ax_s G (hfAddGraphTermAt predOut leftCode rightCode) ->
  BProv Ax_s G
    (iffForm
      (hfAddGraphTermAt out leftCode rightSuccCode)
      (ordinalCodeGraphTermAt
        (tAdd leftRaw (tSucc rightRaw)) out)).
Proof.
  intros P hcodomain hsucc htotal G
    leftRaw leftCode rightRaw rightCode rightSuccCode predOut out
    hright hrightSucc hsumPred haddPred.
  pose proof (BProv_Ax_s_codedOrdinalDomain_of_graph
    hcodomain G rightRaw rightCode hright) as hrightDomain.
  pose proof (hsucc G rightRaw rightCode rightSuccCode hright)
    as hrightStep.
  assert (hrightAdjoin : BProv Ax_s G
      (hfAdjoinGraphTermAt rightSuccCode rightCode rightCode)).
  {
    pose proof (BProv_andE2 Ax_s G _ _ hrightStep) as himp.
    exact (BProv_mp Ax_s G _ _ himp hrightSucc).
  }
  pose proof (BProv_Ax_s_addSucc_terms G leftRaw rightRaw) as haddSucc.
  assert (hforward : BProv Ax_s G
      (pImp
        (hfAddGraphTermAt out leftCode rightSuccCode)
        (ordinalCodeGraphTermAt
          (tAdd leftRaw (tSucc rightRaw)) out))).
  {
    apply BProv_impI.
    set (antecedent := hfAddGraphTermAt out leftCode rightSuccCode).
    set (target := ordinalCodeGraphTermAt
      (tAdd leftRaw (tSucc rightRaw)) out).
    set (C := antecedent :: G).
    assert (haddOut : BProv Ax_s C antecedent).
    { apply BProv_ass. unfold C. simpl. now left. }
    set (sumSuccRaw := tSucc (tAdd leftRaw rightRaw)).
    set (body := ordinalCodeGraphTermAt
      (Term.rename S sumSuccRaw) (tVar 0)).
    pose proof (htotal C sumSuccRaw) as hex.
    set (D := body :: map (rename S) C).
    assert (hinner : BProv Ax_s D (rename S target)).
    {
      assert (hsumSuccD : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (tSucc (Term.rename S (tAdd leftRaw rightRaw)))
            (tVar 0))).
      {
        apply BProv_ass.
        unfold D, body, sumSuccRaw.
        cbn [Term.rename].
        now left.
      }
      assert (liftC : forall phi,
          BProv Ax_s C phi -> BProv Ax_s D (rename S phi)).
      {
        intros phi hphi.
        unfold D.
        exact (BProv_rename_succ_context_cons_of_sentences
          Ax_s sentence_ax_s C body phi hphi).
      }
      assert (liftG : forall phi,
          BProv Ax_s G phi -> BProv Ax_s D (rename S phi)).
      {
        intros phi hphi.
        apply liftC.
        exact (BProv_context_cons Ax_s G antecedent phi hphi).
      }
      assert (hrightD : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (Term.rename S rightRaw) (Term.rename S rightCode))).
      {
        pose proof (liftG _ hright) as h.
        rewrite rename_ordinalCodeGraphTermAt in h.
        exact h.
      }
      assert (hrightSuccD : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (tSucc (Term.rename S rightRaw))
            (Term.rename S rightSuccCode))).
      {
        pose proof (liftG _ hrightSucc) as h.
        rewrite rename_ordinalCodeGraphTermAt in h.
        cbn [Term.rename] in h.
        exact h.
      }
      pose proof (BProv_Ax_s_codedOrdinalDomain_of_graph
        hcodomain D (Term.rename S rightRaw)
        (Term.rename S rightCode) hrightD) as hrightDomainD.
      pose proof (BProv_Ax_s_codedOrdinalDomain_of_graph
        hcodomain D (tSucc (Term.rename S rightRaw))
        (Term.rename S rightSuccCode) hrightSuccD)
        as hrightSuccDomainD.
      assert (hrightAdjoinD : BProv Ax_s D
          (hfAdjoinGraphTermAt
            (Term.rename S rightSuccCode)
            (Term.rename S rightCode)
            (Term.rename S rightCode))).
      {
        pose proof (liftG _ hrightAdjoin) as h.
        rewrite rename_hfAdjoinGraphTermAt in h.
        exact h.
      }
      assert (hsumPredD : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (Term.rename S (tAdd leftRaw rightRaw))
            (Term.rename S predOut))).
      {
        pose proof (liftG _ hsumPred) as h.
        rewrite rename_ordinalCodeGraphTermAt in h.
        exact h.
      }
      assert (haddPredD : BProv Ax_s D
          (hfAddGraphTermAt
            (Term.rename S predOut)
            (Term.rename S leftCode)
            (Term.rename S rightCode))).
      {
        pose proof (liftG _ haddPred) as h.
        rewrite rename_hfAddGraphTermAt in h.
        exact h.
      }
      assert (haddOutD : BProv Ax_s D
          (hfAddGraphTermAt
            (Term.rename S out)
            (Term.rename S leftCode)
            (Term.rename S rightSuccCode))).
      {
        pose proof (liftC _ haddOut) as h.
        unfold antecedent in h.
        rewrite rename_hfAddGraphTermAt in h.
        exact h.
      }
      pose proof (hsucc D
        (Term.rename S (tAdd leftRaw rightRaw))
        (Term.rename S predOut) (tVar 0) hsumPredD) as hsumStep.
      assert (hsumAdjoinD : BProv Ax_s D
          (hfAdjoinGraphTermAt
            (tVar 0) (Term.rename S predOut) (Term.rename S predOut))).
      {
        pose proof (BProv_andE2 Ax_s D _ _ hsumStep) as himp.
        exact (BProv_mp Ax_s D _ _ himp hsumSuccD).
      }
      assert (haddKnown : BProv Ax_s D
          (hfAddGraphTermAt
            (tVar 0)
            (Term.rename S leftCode)
            (Term.rename S rightSuccCode))).
      {
        exact (BProv_Ax_s_hfAddGraphTermAt_succ_right
          P D (tVar 0) (Term.rename S predOut)
          (Term.rename S leftCode)
          (Term.rename S rightSuccCode) (Term.rename S rightCode)
          hrightDomainD hrightAdjoinD hsumAdjoinD haddPredD).
      }
      assert (houtEq : BProv Ax_s D
          (pEq (Term.rename S out) (tVar 0))).
      {
        exact (BProv_Ax_s_hfAddGraphTermAt_functional
          P D (Term.rename S out) (tVar 0)
          (Term.rename S leftCode) (Term.rename S rightSuccCode)
          hrightSuccDomainD haddOutD haddKnown).
      }
      pose proof (BProv_Ax_s_addSucc_terms D
          (Term.rename S leftRaw) (Term.rename S rightRaw))
        as haddSuccD.
      pose proof (BProv_ordinalCodeGraphTermAt_congr
        Ax_s D
        (tSucc (tAdd (Term.rename S leftRaw) (Term.rename S rightRaw)))
        (tAdd (Term.rename S leftRaw) (tSucc (Term.rename S rightRaw)))
        (tVar 0)
        (Term.rename S out)
        (BProv_eqSym Ax_s D _ _ haddSuccD)
        (BProv_eqSym Ax_s D _ _ houtEq)
        hsumSuccD) as hresult.
      unfold target.
      rewrite rename_ordinalCodeGraphTermAt.
      cbn [Term.rename].
      exact hresult.
    }
    unfold target, C in *.
    exact (BProv_exE_of_sentences
      Ax_s (antecedent :: G) body
      (ordinalCodeGraphTermAt (tAdd leftRaw (tSucc rightRaw)) out)
      sentence_ax_s hex hinner).
  }
  assert (hreverse : BProv Ax_s G
      (pImp
        (ordinalCodeGraphTermAt
          (tAdd leftRaw (tSucc rightRaw)) out)
        (hfAddGraphTermAt out leftCode rightSuccCode))).
  {
    apply BProv_impI.
    set (antecedent := ordinalCodeGraphTermAt
      (tAdd leftRaw (tSucc rightRaw)) out).
    set (C := antecedent :: G).
    assert (htarget : BProv Ax_s C antecedent).
    { apply BProv_ass. unfold C. simpl. now left. }
    assert (liftG : forall phi,
        BProv Ax_s G phi -> BProv Ax_s C phi).
    {
      intros phi hphi.
      exact (BProv_context_cons Ax_s G antecedent phi hphi).
    }
    assert (hsumSucc : BProv Ax_s C
        (ordinalCodeGraphTermAt
          (tSucc (tAdd leftRaw rightRaw)) out)).
    {
      exact (BProv_ordinalCodeGraphTermAt_congr_raw
        Ax_s C
        (tAdd leftRaw (tSucc rightRaw))
        (tSucc (tAdd leftRaw rightRaw)) out
        (liftG _ haddSucc) htarget).
    }
    pose proof (hsucc C (tAdd leftRaw rightRaw) predOut out
      (liftG _ hsumPred)) as hsumStep.
    assert (hsumAdjoin : BProv Ax_s C
        (hfAdjoinGraphTermAt out predOut predOut)).
    {
      pose proof (BProv_andE2 Ax_s C _ _ hsumStep) as himp.
      exact (BProv_mp Ax_s C _ _ himp hsumSucc).
    }
    exact (BProv_Ax_s_hfAddGraphTermAt_succ_right
      P C out predOut leftCode rightSuccCode rightCode
      (liftG _ hrightDomain)
      (liftG _ hrightAdjoin)
      hsumAdjoin
      (liftG _ haddPred)).
  }
  exact (PAHFProofCalculus.BProv_PA_iffForm_intro Ax_s G _ _ hforward hreverse).
Qed.

Lemma BProv_Ax_s_ordinalCodeAddPointTermAt_zero : forall
    (P : TranslatedHFFinAxiomProofs)
    (hcodomain : PAOrdinalCodeGraphCodomainProof)
    (hfunctional : PAOrdinalCodeGraphFunctionalProof)
    G leftRaw leftCode,
  BProv Ax_s G (ordinalCodeGraphTermAt leftRaw leftCode) ->
  BProv Ax_s G
    (ordinalCodeAddPointTermAt leftRaw leftCode tZero).
Proof.
  intros P hcodomain hfunctional G leftRaw leftCode hleft.
  set (rightGraph := ordinalCodeGraphTermAt tZero (tVar 0)).
  set (Q := map (rename S) G).
  assert (hbody : BProv Ax_s Q
      (pImp rightGraph
        (ordinalCodeAddOutputTermAt
          (Term.rename S leftRaw)
          (Term.rename S leftCode) tZero (tVar 0)))).
  {
    apply BProv_impI.
    set (C := rightGraph :: Q).
    assert (hright : BProv Ax_s C rightGraph).
    { apply BProv_ass. unfold C. simpl. now left. }
    set (D := map (rename S) C).
    assert (hleftD : BProv Ax_s D
        (ordinalCodeGraphTermAt
          (Term.rename S (Term.rename S leftRaw))
          (Term.rename S (Term.rename S leftCode)))).
    {
      pose proof (BProv_rename_of_sentences
        Ax_s sentence_ax_s G _ hleft S) as h1.
      pose proof (BProv_context_cons Ax_s Q rightGraph _ h1) as h2.
      pose proof (BProv_rename_of_sentences
        Ax_s sentence_ax_s C _ h2 S) as h3.
      unfold D, C, Q in h3 |- *.
      repeat rewrite rename_ordinalCodeGraphTermAt in h3.
      exact h3.
    }
    assert (hrightD : BProv Ax_s D
        (ordinalCodeGraphTermAt tZero (tVar 1))).
    {
      pose proof (BProv_rename_of_sentences
        Ax_s sentence_ax_s C _ hright S) as h.
      unfold D, rightGraph in h.
      rewrite rename_ordinalCodeGraphTermAt in h.
      cbn [Term.rename] in h.
      exact h.
    }
    pose proof (BProv_Ax_s_ordinalCodeAddCore_zero
      P hcodomain hfunctional D
      (Term.rename S (Term.rename S leftRaw))
      (Term.rename S (Term.rename S leftCode))
      (tVar 1) (tVar 0) hleftD hrightD) as hiff.
    pose proof (BProv_allI_of_sentences
      Ax_s C _ sentence_ax_s hiff) as hall.
    unfold ordinalCodeAddOutputTermAt.
    unfold D, C, Q, rightGraph in hall |- *.
    cbn [Term.rename] in hall |- *.
    exact hall.
  }
  pose proof (BProv_allI_of_sentences
    Ax_s G _ sentence_ax_s hbody) as hall.
  unfold ordinalCodeAddPointTermAt, rightGraph, Q in hall |- *.
  cbn [Term.rename] in hall |- *.
  exact hall.
Qed.

Lemma BProv_Ax_s_ordinalCodeAddOutputTermAt_succ : forall
    (P : TranslatedHFFinAxiomProofs)
    (hcodomain : PAOrdinalCodeGraphCodomainProof)
    (hsucc : PAOrdinalCodeSuccAdjoinCompatibility)
    (htotal : PAOrdinalCodeGraphTotalProof)
    G leftRaw leftCode rightRaw rightCode rightSuccCode,
  BProv Ax_s G (ordinalCodeGraphTermAt rightRaw rightCode) ->
  BProv Ax_s G
    (ordinalCodeGraphTermAt (tSucc rightRaw) rightSuccCode) ->
  BProv Ax_s G
    (ordinalCodeAddOutputTermAt
      leftRaw leftCode rightRaw rightCode) ->
  BProv Ax_s G
    (ordinalCodeAddOutputTermAt
      leftRaw leftCode (tSucc rightRaw) rightSuccCode).
Proof.
  intros P hcodomain hsucc htotal G
    leftRaw leftCode rightRaw rightCode rightSuccCode
    hright hrightSucc hih.
  set (sumRaw := tAdd leftRaw rightRaw).
  set (graphBody := ordinalCodeGraphTermAt
    (Term.rename S sumRaw) (tVar 0)).
  pose proof (htotal G sumRaw) as hex.
  set (target := ordinalCodeAddOutputTermAt
    leftRaw leftCode (tSucc rightRaw) rightSuccCode).
  set (C := graphBody :: map (rename S) G).
  assert (hinner : BProv Ax_s C (rename S target)).
  {
    assert (hsumPred : BProv Ax_s C graphBody).
    { apply BProv_ass. unfold C. simpl. now left. }
    assert (liftG : forall phi,
        BProv Ax_s G phi -> BProv Ax_s C (rename S phi)).
    {
      intros phi hphi.
      unfold C.
      exact (BProv_rename_succ_context_cons_of_sentences
        Ax_s sentence_ax_s G graphBody phi hphi).
    }
    assert (hrightC : BProv Ax_s C
        (ordinalCodeGraphTermAt
          (Term.rename S rightRaw) (Term.rename S rightCode))).
    {
      pose proof (liftG _ hright) as h.
      rewrite rename_ordinalCodeGraphTermAt in h.
      exact h.
    }
    assert (hrightSuccC : BProv Ax_s C
        (ordinalCodeGraphTermAt
          (tSucc (Term.rename S rightRaw))
          (Term.rename S rightSuccCode))).
    {
      pose proof (liftG _ hrightSucc) as h.
      rewrite rename_ordinalCodeGraphTermAt in h.
      cbn [Term.rename] in h.
      exact h.
    }
    assert (hihC : BProv Ax_s C
        (ordinalCodeAddOutputTermAt
          (Term.rename S leftRaw)
          (Term.rename S leftCode)
          (Term.rename S rightRaw)
          (Term.rename S rightCode))).
    {
      pose proof (liftG _ hih) as h.
      rewrite rename_ordinalCodeAddOutputTermAt in h.
      exact h.
    }
    pose proof (BProv_Ax_s_ordinalCodeAddOutputTermAt_at
      C (Term.rename S leftRaw) (Term.rename S leftCode)
      (Term.rename S rightRaw) (Term.rename S rightCode)
      (tVar 0) hihC) as hpoint.
    assert (haddPred : BProv Ax_s C
        (hfAddGraphTermAt
          (tVar 0) (Term.rename S leftCode) (Term.rename S rightCode))).
    {
      pose proof (BProv_andE2 Ax_s C _ _ hpoint) as himp.
      unfold graphBody, sumRaw in hsumPred.
      cbn [Term.rename] in hsumPred.
      exact (BProv_mp Ax_s C _ _ himp hsumPred).
    }
    set (D := map (rename S) C).
    assert (hrightD : BProv Ax_s D
        (ordinalCodeGraphTermAt
          (Term.rename S (Term.rename S rightRaw))
          (Term.rename S (Term.rename S rightCode)))).
    {
      pose proof (BProv_rename_of_sentences
        Ax_s sentence_ax_s C _ hrightC S) as h.
      unfold D in h.
      repeat rewrite rename_ordinalCodeGraphTermAt in h.
      exact h.
    }
    assert (hrightSuccD : BProv Ax_s D
        (ordinalCodeGraphTermAt
          (tSucc (Term.rename S (Term.rename S rightRaw)))
          (Term.rename S (Term.rename S rightSuccCode)))).
    {
      pose proof (BProv_rename_of_sentences
        Ax_s sentence_ax_s C _ hrightSuccC S) as h.
      unfold D in h.
      rewrite rename_ordinalCodeGraphTermAt in h.
      cbn [Term.rename] in h.
      exact h.
    }
    assert (hsumPredD : BProv Ax_s D
        (ordinalCodeGraphTermAt
          (tAdd
            (Term.rename S (Term.rename S leftRaw))
            (Term.rename S (Term.rename S rightRaw)))
          (tVar 1))).
    {
      pose proof (BProv_rename_of_sentences
        Ax_s sentence_ax_s C _ hsumPred S) as h.
      unfold D, graphBody, sumRaw in h.
      repeat rewrite rename_ordinalCodeGraphTermAt in h.
      cbn [Term.rename] in h.
      exact h.
    }
    assert (haddPredD : BProv Ax_s D
        (hfAddGraphTermAt
          (tVar 1)
          (Term.rename S (Term.rename S leftCode))
          (Term.rename S (Term.rename S rightCode)))).
    {
      pose proof (BProv_rename_of_sentences
        Ax_s sentence_ax_s C _ haddPred S) as h.
      unfold D in h.
      rewrite rename_hfAddGraphTermAt in h.
      cbn [Term.rename] in h.
      exact h.
    }
    pose proof (BProv_Ax_s_ordinalCodeAddCore_succ_of_pred
      P hcodomain hsucc htotal D
      (Term.rename S (Term.rename S leftRaw))
      (Term.rename S (Term.rename S leftCode))
      (Term.rename S (Term.rename S rightRaw))
      (Term.rename S (Term.rename S rightCode))
      (Term.rename S (Term.rename S rightSuccCode))
      (tVar 1) (tVar 0)
      hrightD hrightSuccD hsumPredD haddPredD) as hiff.
    pose proof (BProv_allI_of_sentences
      Ax_s C _ sentence_ax_s hiff) as hall.
    unfold D in hall.
    unfold target.
    rewrite rename_ordinalCodeAddOutputTermAt.
    cbn [Term.rename].
    exact hall.
  }
  unfold target, C in *.
  exact (BProv_exE_of_sentences
    Ax_s G graphBody
    (ordinalCodeAddOutputTermAt
      leftRaw leftCode (tSucc rightRaw) rightSuccCode)
    sentence_ax_s hex hinner).
Qed.

Lemma BProv_Ax_s_ordinalCodeAddPointTermAt_of_graph : forall
    G leftRaw leftCode rightRaw rightCode,
  BProv Ax_s G
    (ordinalCodeAddPointTermAt leftRaw leftCode rightRaw) ->
  BProv Ax_s G (ordinalCodeGraphTermAt rightRaw rightCode) ->
  BProv Ax_s G
    (ordinalCodeAddOutputTermAt
      leftRaw leftCode rightRaw rightCode).
Proof.
  intros G leftRaw leftCode rightRaw rightCode hpoint hgraph.
  pose proof (BProv_allE Ax_s G _ rightCode hpoint) as hraw.
  unfold ordinalCodeAddPointTermAt in hraw.
  cbn [subst instTerm Term.subst Term.upSubst] in hraw.
  rewrite subst_ordinalCodeGraphTermAt in hraw.
  rewrite subst_ordinalCodeAddOutputTermAt in hraw.
  cbn [Term.subst Term.upSubst instTerm] in hraw.
  repeat rewrite Term.subst_rename_succ_up in hraw.
  repeat rewrite term_subst_instTerm_rename_succ in hraw.
  exact (BProv_mp Ax_s G _ _ hraw hgraph).
Qed.

Lemma BProv_Ax_s_ordinalCodeAddPointTermAt_succ : forall
    (P : TranslatedHFFinAxiomProofs)
    (hcodomain : PAOrdinalCodeGraphCodomainProof)
    (hsucc : PAOrdinalCodeSuccAdjoinCompatibility)
    (htotal : PAOrdinalCodeGraphTotalProof)
    G leftRaw leftCode rightRaw,
  BProv Ax_s G
    (ordinalCodeAddPointTermAt leftRaw leftCode rightRaw) ->
  BProv Ax_s G
    (ordinalCodeAddPointTermAt leftRaw leftCode (tSucc rightRaw)).
Proof.
  intros P hcodomain hsucc htotal G leftRaw leftCode rightRaw hih.
  set (rightSuccGraph := ordinalCodeGraphTermAt
    (tSucc (Term.rename S rightRaw)) (tVar 0)).
  set (Q := map (rename S) G).
  assert (hbody : BProv Ax_s Q
      (pImp rightSuccGraph
        (ordinalCodeAddOutputTermAt
          (Term.rename S leftRaw)
          (Term.rename S leftCode)
          (tSucc (Term.rename S rightRaw))
          (tVar 0)))).
  {
    apply BProv_impI.
    set (C := rightSuccGraph :: Q).
    assert (hrightSucc : BProv Ax_s C rightSuccGraph).
    { apply BProv_ass. unfold C. simpl. now left. }
    set (predRaw := Term.rename S rightRaw).
    set (predBody := ordinalCodeGraphTermAt
      (Term.rename S predRaw) (tVar 0)).
    pose proof (htotal C predRaw) as hex.
    set (target := ordinalCodeAddOutputTermAt
      (Term.rename S leftRaw)
      (Term.rename S leftCode)
      (tSucc (Term.rename S rightRaw))
      (tVar 0)).
    set (D := predBody :: map (rename S) C).
    assert (hinner : BProv Ax_s D (rename S target)).
    {
      assert (hpred : BProv Ax_s D predBody).
      { apply BProv_ass. unfold D. simpl. now left. }
      assert (hrightSuccD : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (tSucc (Term.rename S (Term.rename S rightRaw)))
            (tVar 1))).
      {
        pose proof (BProv_rename_succ_context_cons_of_sentences
          Ax_s sentence_ax_s C predBody rightSuccGraph hrightSucc) as h.
        unfold D, rightSuccGraph in h.
        rewrite rename_ordinalCodeGraphTermAt in h.
        cbn [Term.rename] in h.
        exact h.
      }
      assert (hihQ : BProv Ax_s Q
          (ordinalCodeAddPointTermAt
            (Term.rename S leftRaw)
            (Term.rename S leftCode)
            (Term.rename S rightRaw))).
      {
        pose proof (BProv_rename_of_sentences
          Ax_s sentence_ax_s G _ hih S) as h.
        unfold Q in h.
        rewrite rename_ordinalCodeAddPointTermAt in h.
        exact h.
      }
      assert (hihC : BProv Ax_s C
          (ordinalCodeAddPointTermAt
            (Term.rename S leftRaw)
            (Term.rename S leftCode)
            (Term.rename S rightRaw))).
      {
        exact (BProv_context_cons Ax_s Q rightSuccGraph _ hihQ).
      }
      assert (hihD : BProv Ax_s D
          (ordinalCodeAddPointTermAt
            (Term.rename S (Term.rename S leftRaw))
            (Term.rename S (Term.rename S leftCode))
            (Term.rename S (Term.rename S rightRaw)))).
      {
        pose proof (BProv_rename_succ_context_cons_of_sentences
          Ax_s sentence_ax_s C predBody _ hihC) as h.
        unfold D in h.
        rewrite rename_ordinalCodeAddPointTermAt in h.
        exact h.
      }
      assert (hpredGraph : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (Term.rename S (Term.rename S rightRaw)) (tVar 0))).
      { unfold predBody, predRaw in hpred. exact hpred. }
      pose proof (BProv_Ax_s_ordinalCodeAddPointTermAt_of_graph
        D
        (Term.rename S (Term.rename S leftRaw))
        (Term.rename S (Term.rename S leftCode))
        (Term.rename S (Term.rename S rightRaw))
        (tVar 0) hihD hpredGraph) as houtputPred.
      pose proof (BProv_Ax_s_ordinalCodeAddOutputTermAt_succ
        P hcodomain hsucc htotal D
        (Term.rename S (Term.rename S leftRaw))
        (Term.rename S (Term.rename S leftCode))
        (Term.rename S (Term.rename S rightRaw))
        (tVar 0) (tVar 1)
        hpredGraph hrightSuccD houtputPred) as houtputSucc.
      unfold target.
      rewrite rename_ordinalCodeAddOutputTermAt.
      cbn [Term.rename].
      exact houtputSucc.
    }
    unfold target, C in *.
    exact (BProv_exE_of_sentences
      Ax_s (rightSuccGraph :: Q) predBody
      (ordinalCodeAddOutputTermAt
        (Term.rename S leftRaw)
        (Term.rename S leftCode)
        (tSucc (Term.rename S rightRaw))
        (tVar 0))
      sentence_ax_s hex hinner).
  }
  pose proof (BProv_allI_of_sentences
    Ax_s G _ sentence_ax_s hbody) as hall.
  unfold ordinalCodeAddPointTermAt, rightSuccGraph, Q in hall |- *.
  cbn [Term.rename] in hall |- *.
  exact hall.
Qed.

(** One ordinary PA induction now closes the point predicate for every raw
    right operand. *)
Lemma BProv_Ax_s_all_ordinalCodeAddPoint : forall
    (P : TranslatedHFFinAxiomProofs)
    (hcodomain : PAOrdinalCodeGraphCodomainProof)
    (hfunctional : PAOrdinalCodeGraphFunctionalProof)
    (hsucc : PAOrdinalCodeSuccAdjoinCompatibility)
    (htotal : PAOrdinalCodeGraphTotalProof)
    G leftRaw leftCode,
  BProv Ax_s G (ordinalCodeGraphTermAt leftRaw leftCode) ->
  BProv Ax_s G
    (pAll
      (ordinalCodeAddPointTermAt
        (Term.rename S leftRaw)
        (Term.rename S leftCode)
        (tVar 0))).
Proof.
  intros P hcodomain hfunctional hsucc htotal
    G leftRaw leftCode hleft.
  set (phi := ordinalCodeAddPointTermAt
    (Term.rename S leftRaw) (Term.rename S leftCode) (tVar 0)).
  assert (hzero : BProv Ax_s G (subst substZero phi)).
  {
    pose proof (BProv_Ax_s_ordinalCodeAddPointTermAt_zero
      P hcodomain hfunctional G leftRaw leftCode hleft) as hbase.
    unfold phi.
    rewrite subst_ordinalCodeAddPointTermAt.
    cbn [substZero Term.subst].
    repeat rewrite term_substZero_rename_succ.
    exact hbase.
  }
  set (Q := map (rename S) G).
  assert (hsuccImp : BProv Ax_s Q
      (pImp phi (subst substSuccVar phi))).
  {
    set (C := phi :: Q).
    assert (hih : BProv Ax_s C phi).
    { apply BProv_ass. unfold C. simpl. now left. }
    assert (hnext : BProv Ax_s C
        (ordinalCodeAddPointTermAt
          (Term.rename S leftRaw)
          (Term.rename S leftCode)
          (tSucc (tVar 0)))).
    {
      unfold phi in hih.
      exact (BProv_Ax_s_ordinalCodeAddPointTermAt_succ
        P hcodomain hsucc htotal C
        (Term.rename S leftRaw) (Term.rename S leftCode)
        (tVar 0) hih).
    }
    assert (hnextSub : BProv Ax_s C (subst substSuccVar phi)).
    {
      unfold phi.
      rewrite subst_ordinalCodeAddPointTermAt.
      cbn [substSuccVar Term.subst].
      repeat rewrite term_substSuccVar_rename_succ.
      exact hnext.
    }
    unfold C in hnextSub.
    exact (BProv_impI Ax_s Q phi _ hnextSub).
  }
  assert (hsuccAll : BProv Ax_s G
      (pAll (pImp phi (subst substSuccVar phi)))).
  {
    exact (BProv_allI_of_sentences
      Ax_s G _ sentence_ax_s hsuccImp).
  }
  unfold phi.
  exact (BProv_Ax_s_induction_rule G
    (ordinalCodeAddPointTermAt
      (Term.rename S leftRaw) (Term.rename S leftCode) (tVar 0))
    hzero hsuccAll).
Qed.

Lemma BProv_Ax_s_ordinalCodeAddPointTermAt : forall
    (P : TranslatedHFFinAxiomProofs)
    (hcodomain : PAOrdinalCodeGraphCodomainProof)
    (hfunctional : PAOrdinalCodeGraphFunctionalProof)
    (hsucc : PAOrdinalCodeSuccAdjoinCompatibility)
    (htotal : PAOrdinalCodeGraphTotalProof)
    G leftRaw leftCode rightRaw,
  BProv Ax_s G (ordinalCodeGraphTermAt leftRaw leftCode) ->
  BProv Ax_s G
    (ordinalCodeAddPointTermAt leftRaw leftCode rightRaw).
Proof.
  intros P hcodomain hfunctional hsucc htotal
    G leftRaw leftCode rightRaw hleft.
  pose proof (BProv_Ax_s_all_ordinalCodeAddPoint
    P hcodomain hfunctional hsucc htotal
    G leftRaw leftCode hleft) as hall.
  pose proof (BProv_allE Ax_s G _ rightRaw hall) as hraw.
  rewrite subst_ordinalCodeAddPointTermAt in hraw.
  cbn [instTerm Term.subst] in hraw.
  repeat rewrite term_subst_instTerm_rename_succ in hraw.
  exact hraw.
Qed.

Lemma BProv_Ax_s_ordinalCodeAddTermAt : forall
    (P : TranslatedHFFinAxiomProofs)
    (hcodomain : PAOrdinalCodeGraphCodomainProof)
    (hfunctional : PAOrdinalCodeGraphFunctionalProof)
    (hsucc : PAOrdinalCodeSuccAdjoinCompatibility)
    (htotal : PAOrdinalCodeGraphTotalProof)
    G leftRaw leftCode rightRaw rightCode out,
  BProv Ax_s G (ordinalCodeGraphTermAt leftRaw leftCode) ->
  BProv Ax_s G (ordinalCodeGraphTermAt rightRaw rightCode) ->
  BProv Ax_s G
    (iffForm
      (hfAddGraphTermAt out leftCode rightCode)
      (ordinalCodeGraphTermAt (tAdd leftRaw rightRaw) out)).
Proof.
  intros P hcodomain hfunctional hsucc htotal G
    leftRaw leftCode rightRaw rightCode out hleft hright.
  pose proof (BProv_Ax_s_ordinalCodeAddPointTermAt
    P hcodomain hfunctional hsucc htotal
    G leftRaw leftCode rightRaw hleft) as hpoint.
  pose proof (BProv_Ax_s_ordinalCodeAddPointTermAt_of_graph
    G leftRaw leftCode rightRaw rightCode hpoint hright) as houtput.
  exact (BProv_Ax_s_ordinalCodeAddOutputTermAt_at
    G leftRaw leftCode rightRaw rightCode out houtput).
Qed.

(** Concrete addition-core certificate consumed by the structural term lift. *)
Theorem PAOrdinalCodeAddCoreCompatibility_of_interfaces :
  TranslatedHFFinAxiomProofs ->
  PAOrdinalCodeGraphCodomainProof ->
  PAOrdinalCodeGraphFunctionalProof ->
  PAOrdinalCodeSuccAdjoinCompatibility ->
  PAOrdinalCodeGraphTotalProof ->
  PAOrdinalCodeAddCoreCompatibility.
Proof.
  intros P hcodomain hfunctional hsucc htotal
    G leftRaw rightRaw codedOut hleft hright.
  pose proof (BProv_Ax_s_ordinalCodeAddTermAt
    P hcodomain hfunctional hsucc htotal
    G leftRaw (tVar 1) rightRaw (tVar 0)
    (tVar (codedOut + 2)) hleft hright) as hiff.
  rewrite compositeAddCoreAt_eq_termAt.
  exact hiff.
Qed.
