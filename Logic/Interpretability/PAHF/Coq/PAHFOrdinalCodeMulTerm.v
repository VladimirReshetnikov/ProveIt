(* ===================================================================== *)
(*  PAHFOrdinalCodeMulTerm.v                                            *)
(*                                                                       *)
(*  Arithmetic multiplication kernel for ordinal-code term graphs.      *)
(*                                                                       *)
(*  This module ports the term-parametric part of the Lean multiplication *)
(*  induction.  Its hypotheses are the already isolated graph, successor, *)
(*  and addition interfaces; no semantic or proof-theoretic assumption is *)
(*  hidden in the construction.                                          *)
(* ===================================================================== *)

From Stdlib Require Import List.
From FirstOrder Require Import Fol Calculus.
From PAHF Require Import PAHF PAHFOrdinalCode
  PAHFTranslatedOperations PAHFOrdinalCodeMulCore
  PAHFOrdinalCodeAddCore
  PAHFOrdinalCodeTotal PAHFOrdinalCodeInjective PAHFOrdinalCodeRange
  PAHFOrdinalCodeRangeArithmetic PAHFOrdinalCodeFunctional
  PAHFOrdinalCodeTermCompatibility
  PAHFRoundTripArithmetic.

Import ListNotations.
Import PA PA.Term PA.Formula.

(* --------------------------------------------------------------------- *)
(* The addition bridge consumed by multiplication.                       *)

(** Keep the three term-parametric graph predicates atomic during the many
    substitution rewrites below.  Unfolding their large recursive formulas
    during failed rewrite matching otherwise dominates compilation time. *)
Local Opaque hfAddGraphTermAt hfMulGraphTermAt_core
  hfAdjoinGraphTermAt.

Definition PAOrdinalCodeAddTermCompatibility_mul : Prop :=
  forall (G : list formula)
    (leftRaw leftCode rightRaw rightCode out : term),
    BProv Ax_s G (ordinalCodeGraphTermAt leftRaw leftCode) ->
    BProv Ax_s G (ordinalCodeGraphTermAt rightRaw rightCode) ->
    BProv Ax_s G
      (iffForm
        (hfAddGraphTermAt out leftCode rightCode)
        (ordinalCodeGraphTermAt (tAdd leftRaw rightRaw) out)).

Definition PAOrdinalCodeAddTermCompatibility_mul_of_interfaces
    (P : TranslatedHFFinAxiomProofs)
    (hcodomain : PAOrdinalCodeGraphCodomainProof)
    (hfunctional : PAOrdinalCodeGraphFunctionalProof)
    (hsucc : PAOrdinalCodeSuccAdjoinCompatibility)
    (htotal : PAOrdinalCodeGraphTotalProof) :
  PAOrdinalCodeAddTermCompatibility_mul :=
  BProv_Ax_s_ordinalCodeAddTermAt
    P hcodomain hfunctional hsucc htotal.

(* --------------------------------------------------------------------- *)
(* Arbitrary-term instances of the three translated multiplication laws. *)

Lemma BProv_Ax_s_hfMulGraphTermAt_zero_right_mul : forall
    (P : TranslatedHFFinAxiomProofs) G out left right,
  BProv Ax_s G (hfEmptyTermAt right) ->
  BProv Ax_s G (hfEmptyTermAt out) ->
  BProv Ax_s G (hfMulGraphTermAt_core out left right).
Proof.
  intros P G out left right hright hout.
  assert (hall : BProv Ax_s G
      (pAll (pAll (pAll
        (pImp
          (hfEmptyTermAt (tVar 1))
          (pImp
            (hfEmptyTermAt (tVar 0))
            (hfMulGraphTermAt_core
              (tVar 0) (tVar 2) (tVar 1)))))))).
  {
    pose proof (BProv_weaken_nil Ax_s G _
      (BProv_Ax_s_mulZeroRightSentence P)) as h.
    repeat rewrite hfEmptyCodeAt_eq_termAt in h.
    repeat rewrite hfMulGraphAt_eq_termAt_core in h.
    exact h.
  }
  pose proof (BProv_allE Ax_s G _ left hall) as hleft.
  pose proof (BProv_allE Ax_s G _ right hleft) as hright0.
  pose proof (BProv_allE Ax_s G _ out hright0) as hout0.
  assert (himp : BProv Ax_s G
      (pImp
        (hfEmptyTermAt right)
        (pImp
          (hfEmptyTermAt out)
          (hfMulGraphTermAt_core out left right)))).
  {
    cbn [subst instTerm Term.subst Term.upSubst] in hout0.
    repeat rewrite subst_hfEmptyTermAt in hout0.
    repeat rewrite subst_hfMulGraphTermAt_core in hout0.
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

(** Instantiate the closed multiplication-successor law at arbitrary terms.

    Directly eliminating the five universal binders at those terms makes Rocq
    repeatedly normalize the large HF graph macros.  Instead we first open
    them at fresh variables and apply one simultaneous substitution.  The two
    [match type of] blocks below normalize only the implication leaves needed
    by modus ponens; keeping the graph predicates opaque makes this proof both
    clearer about its binder map and dramatically faster to check. *)
Lemma BProv_Ax_s_hfMulGraphTermAt_succ_right_mul : forall
    (P : TranslatedHFFinAxiomProofs) G
    out previous left rightSucc right,
  BProv Ax_s G (subst (instTerm right) codedOrdinalDomain) ->
  BProv Ax_s G (hfAdjoinGraphTermAt rightSucc right right) ->
  BProv Ax_s G (hfMulGraphTermAt_core previous left right) ->
  BProv Ax_s G (hfAddGraphTermAt out previous left) ->
  BProv Ax_s G (hfMulGraphTermAt_core out left rightSucc).
Proof.
  intros P G out previous left rightSucc right
    hrightDomain hrightSucc hmul hadd.
  assert (hall : BProv Ax_s []
      (pAll (pAll (pAll (pAll (pAll
        (pImp
          (subst (instTerm (tVar 3)) codedOrdinalDomain)
          (pImp
            (hfAdjoinGraphTermAt (tVar 2) (tVar 3) (tVar 3))
            (pImp
              (hfMulGraphTermAt_core (tVar 1) (tVar 4) (tVar 3))
              (pImp
                (hfAddGraphTermAt (tVar 0) (tVar 1) (tVar 4))
                (hfMulGraphTermAt_core
                  (tVar 0) (tVar 4) (tVar 2)))))))))))).
  {
    pose proof (BProv_Ax_s_mulSuccRightSentence P) as h.
    rewrite addHFOrdinalLikeAt_eq_domainTermAt in h.
    repeat rewrite hfMulGraphAt_eq_termAt_core in h.
    repeat rewrite hfAddGraphAt_eq_termAt_mul in h.
    exact h.
  }
  pose proof (BProv_allE Ax_s [] _ (tVar 4) hall) as hleft.
  pose proof (BProv_allE Ax_s [] _ (tVar 3) hleft) as hright0.
  pose proof (BProv_allE Ax_s [] _ (tVar 2) hright0) as hrightSucc0.
  pose proof (BProv_allE Ax_s [] _ (tVar 1) hrightSucc0) as hprevious0.
  pose proof (BProv_allE Ax_s [] _ (tVar 0) hprevious0) as hopen0.
  set (sigma := fun n =>
    match n with
    | 0 => out
    | 1 => previous
    | 2 => rightSucc
    | 3 => right
    | 4 => left
    | _ => tZero
    end).
  pose proof (BProv_subst_of_sentences Ax_s sentence_ax_s [] _
    hopen0 sigma) as hsub.
  cbn [map] in hsub.
  rewrite subst_comp in hsub.
  rewrite subst_comp in hsub.
  rewrite subst_comp in hsub.
  rewrite subst_comp in hsub.
  cbn [subst] in hsub.
  rewrite subst_domainTermAt in hsub.
  rewrite subst_hfAdjoinGraphTermAt in hsub.
  unfold sigma in hsub.
  cbn [Term.subst Term.upSubst instTerm] in hsub.
  pose proof (BProv_weaken_nil Ax_s G _ hsub) as hsubG.
  pose proof (BProv_mp Ax_s G
    (subst (instTerm right) codedOrdinalDomain) _
    hsubG hrightDomain) as hrightStep.
  pose proof (BProv_mp Ax_s G
    (hfAdjoinGraphTermAt rightSucc right right) _
    hrightStep hrightSucc) as hmulStep.
  match type of hmulStep with
  | BProv _ _ (pImp ?a _) =>
      assert (ha : a = hfMulGraphTermAt_core previous left right);
      [ repeat rewrite subst_comp;
        rewrite subst_hfMulGraphTermAt_core;
        cbn [Term.subst Term.upSubst instTerm];
        reflexivity
      | rewrite ha in hmulStep ]
  end.
  pose proof (BProv_mp Ax_s G
    (hfMulGraphTermAt_core previous left right) _
    hmulStep hmul) as haddStep.
  match type of haddStep with
  | BProv _ _ (pImp ?a ?b) =>
      assert (haddAntecedentEq :
        a = hfAddGraphTermAt out previous left);
      [ repeat rewrite subst_comp;
        rewrite subst_hfAddGraphTermAt;
        cbn [Term.subst Term.upSubst instTerm];
        reflexivity
      | assert (hmulResultEq :
          b = hfMulGraphTermAt_core out left rightSucc);
        [ repeat rewrite subst_comp;
          rewrite subst_hfMulGraphTermAt_core;
          cbn [Term.subst Term.upSubst instTerm];
          reflexivity
        | rewrite haddAntecedentEq, hmulResultEq in haddStep ] ]
  end.
  exact (BProv_mp Ax_s G
    (hfAddGraphTermAt out previous left) _ haddStep hadd).
Qed.

Lemma BProv_Ax_s_hfMulGraphTermAt_functional_mul : forall
    (P : TranslatedHFFinAxiomProofs) G out1 out2 left right,
  BProv Ax_s G (subst (instTerm left) codedOrdinalDomain) ->
  BProv Ax_s G (subst (instTerm right) codedOrdinalDomain) ->
  BProv Ax_s G (hfMulGraphTermAt_core out1 left right) ->
  BProv Ax_s G (hfMulGraphTermAt_core out2 left right) ->
  BProv Ax_s G (pEq out1 out2).
Proof.
  intros P G out1 out2 left right
    hleftDomain hrightDomain hmul1 hmul2.
  assert (hall : BProv Ax_s G
      (pAll (pAll (pAll (pAll
        (pImp
          (subst (instTerm (tVar 3)) codedOrdinalDomain)
          (pImp
            (subst (instTerm (tVar 2)) codedOrdinalDomain)
            (pImp
              (hfMulGraphTermAt_core (tVar 1) (tVar 3) (tVar 2))
              (pImp
                (hfMulGraphTermAt_core (tVar 0) (tVar 3) (tVar 2))
                (pEq (tVar 1) (tVar 0))))))))))).
  {
    pose proof (BProv_weaken_nil Ax_s G _
      (BProv_Ax_s_mulFunctionalSentence P)) as h.
    repeat rewrite addHFOrdinalLikeAt_eq_domainTermAt in h.
    repeat rewrite hfMulGraphAt_eq_termAt_core in h.
    exact h.
  }
  pose proof (BProv_allE Ax_s G _ left hall) as hleft.
  pose proof (BProv_allE Ax_s G _ right hleft) as hright0.
  pose proof (BProv_allE Ax_s G _ out1 hright0) as hout1.
  pose proof (BProv_allE Ax_s G _ out2 hout1) as hout2.
  assert (himp : BProv Ax_s G
      (pImp
        (subst (instTerm left) codedOrdinalDomain)
        (pImp
          (subst (instTerm right) codedOrdinalDomain)
          (pImp
            (hfMulGraphTermAt_core out1 left right)
            (pImp
              (hfMulGraphTermAt_core out2 left right)
              (pEq out1 out2)))))).
  {
    cbn [subst instTerm Term.subst Term.upSubst] in hout2.
    repeat rewrite subst_domainTermAt in hout2.
    repeat rewrite subst_hfMulGraphTermAt_core in hout2.
    repeat rewrite Term.subst_rename_succ_up in hout2.
    repeat rewrite term_subst_instTerm_rename_succ in hout2.
    cbn [Term.subst Term.upSubst instTerm] in hout2.
    repeat rewrite subst_domainTermAt in hout2.
    repeat rewrite subst_hfMulGraphTermAt_core in hout2.
    repeat rewrite Term.subst_rename_succ_up in hout2.
    repeat rewrite term_subst_instTerm_rename_succ in hout2.
    exact hout2.
  }
  exact (BProv_mp Ax_s G _ _
    (BProv_mp Ax_s G _ _
      (BProv_mp Ax_s G _ _
        (BProv_mp Ax_s G _ _ himp hleftDomain)
        hrightDomain) hmul1) hmul2).
Qed.

(* --------------------------------------------------------------------- *)
(* Fixed-predecessor multiplication base case.                           *)

Lemma BProv_Ax_s_ordinalCodeMulCore_zero_mul : forall
    (P : TranslatedHFFinAxiomProofs)
    (hcodomain : PAOrdinalCodeGraphCodomainProof)
    (hfunctional : PAOrdinalCodeGraphFunctionalProof)
    G leftRaw leftCode rightCode out,
  BProv Ax_s G (ordinalCodeGraphTermAt leftRaw leftCode) ->
  BProv Ax_s G (ordinalCodeGraphTermAt tZero rightCode) ->
  BProv Ax_s G
    (iffForm
      (hfMulGraphTermAt_core out leftCode rightCode)
      (ordinalCodeGraphTermAt (tMul leftRaw tZero) out)).
Proof.
  intros P hcodomain hfunctional G
    leftRaw leftCode rightCode out hleft hright.
  pose proof (BProv_Ax_s_codedOrdinalDomain_of_graph
    hcodomain G leftRaw leftCode hleft) as hleftDomain.
  pose proof (BProv_Ax_s_codedOrdinalDomain_of_graph
    hcodomain G tZero rightCode hright) as hrightDomain.
  pose proof (BProv_Ax_s_eq_zero_of_ordinalCodeGraphTermAt_zero
    G rightCode hright) as hrightEq.
  pose proof (BProv_Ax_s_hfEmptyTermAt_of_eq_zero
    G rightCode hrightEq) as hrightEmpty.
  assert (hzeroEmpty : BProv Ax_s G (hfEmptyTermAt tZero)).
  { exact (BProv_weaken_nil Ax_s G _ BProv_Ax_s_hfEmptyTermAt_zero). }
  assert (hbase : BProv Ax_s G
      (hfMulGraphTermAt_core tZero leftCode rightCode)).
  {
    exact (BProv_Ax_s_hfMulGraphTermAt_zero_right_mul
      P G tZero leftCode rightCode hrightEmpty hzeroEmpty).
  }
  assert (hmulZero : BProv Ax_s G
      (pEq (tMul leftRaw tZero) tZero)).
  {
    exact (BProv_Ax_s_mulZero_term G leftRaw).
  }
  assert (hzeroGraph : BProv Ax_s G
      (ordinalCodeGraphTermAt tZero tZero)).
  { exact (BProv_Ax_s_ordinalCodeGraphTermAt_zero G). }
  assert (hforward : BProv Ax_s G
      (pImp
        (hfMulGraphTermAt_core out leftCode rightCode)
        (ordinalCodeGraphTermAt (tMul leftRaw tZero) out))).
  {
    set (antecedent := hfMulGraphTermAt_core out leftCode rightCode).
    set (C := antecedent :: G).
    assert (hmul : BProv Ax_s C antecedent).
    { apply BProv_ass. unfold C. simpl. now left. }
    assert (houtEq : BProv Ax_s C (pEq out tZero)).
    {
      exact (BProv_Ax_s_hfMulGraphTermAt_functional_mul
        P C out tZero leftCode rightCode
        (BProv_context_cons Ax_s G antecedent _ hleftDomain)
        (BProv_context_cons Ax_s G antecedent _ hrightDomain)
        hmul
        (BProv_context_cons Ax_s G antecedent _ hbase)).
    }
    assert (hresult : BProv Ax_s C
        (ordinalCodeGraphTermAt (tMul leftRaw tZero) out)).
    {
      exact (BProv_ordinalCodeGraphTermAt_congr
        Ax_s C tZero (tMul leftRaw tZero) tZero out
        (BProv_eqSym Ax_s C _ _
          (BProv_context_cons Ax_s G antecedent _ hmulZero))
        (BProv_eqSym Ax_s C _ _ houtEq)
        (BProv_context_cons Ax_s G antecedent _ hzeroGraph)).
    }
    unfold C in hresult.
    exact (BProv_impI Ax_s G antecedent _ hresult).
  }
  assert (hreverse : BProv Ax_s G
      (pImp
        (ordinalCodeGraphTermAt (tMul leftRaw tZero) out)
        (hfMulGraphTermAt_core out leftCode rightCode))).
  {
    set (antecedent := ordinalCodeGraphTermAt
      (tMul leftRaw tZero) out).
    set (C := antecedent :: G).
    assert (htarget : BProv Ax_s C antecedent).
    { apply BProv_ass. unfold C. simpl. now left. }
    assert (houtGraph : BProv Ax_s C
        (ordinalCodeGraphTermAt tZero out)).
    {
      exact (BProv_ordinalCodeGraphTermAt_congr_raw
        Ax_s C (tMul leftRaw tZero) tZero out
        (BProv_context_cons Ax_s G antecedent _ hmulZero) htarget).
    }
    assert (houtEq : BProv Ax_s C (pEq out tZero)).
    {
      exact (hfunctional C tZero out tZero houtGraph
        (BProv_context_cons Ax_s G antecedent _ hzeroGraph)).
    }
    assert (houtEmpty : BProv Ax_s C (hfEmptyTermAt out)).
    { exact (BProv_Ax_s_hfEmptyTermAt_of_eq_zero C out houtEq). }
    assert (hresult : BProv Ax_s C
        (hfMulGraphTermAt_core out leftCode rightCode)).
    {
      exact (BProv_Ax_s_hfMulGraphTermAt_zero_right_mul
        P C out leftCode rightCode
        (BProv_context_cons Ax_s G antecedent _ hrightEmpty)
        houtEmpty).
    }
    unfold C, antecedent in hresult.
    exact (BProv_impI Ax_s G _ _ hresult).
  }
  exact (PAHFProofCalculus.BProv_PA_iffForm_intro Ax_s G _ _ hforward hreverse).
Qed.

(* --------------------------------------------------------------------- *)
(* Fixed-predecessor multiplication successor recurrence.                *)

Lemma BProv_Ax_s_ordinalCodeMulCore_succ_of_pred_mul : forall
    (P : TranslatedHFFinAxiomProofs)
    (hcodomain : PAOrdinalCodeGraphCodomainProof)
    (hsucc : PAOrdinalCodeSuccAdjoinCompatibility)
    (htotal : PAOrdinalCodeGraphTotalProof)
    (hadd : PAOrdinalCodeAddTermCompatibility_mul)
    G leftRaw leftCode rightRaw rightCode rightSuccCode predOut out,
  BProv Ax_s G (ordinalCodeGraphTermAt leftRaw leftCode) ->
  BProv Ax_s G (ordinalCodeGraphTermAt rightRaw rightCode) ->
  BProv Ax_s G
    (ordinalCodeGraphTermAt (tSucc rightRaw) rightSuccCode) ->
  BProv Ax_s G
    (ordinalCodeGraphTermAt (tMul leftRaw rightRaw) predOut) ->
  BProv Ax_s G
    (hfMulGraphTermAt_core predOut leftCode rightCode) ->
  BProv Ax_s G
    (iffForm
      (hfMulGraphTermAt_core out leftCode rightSuccCode)
      (ordinalCodeGraphTermAt
        (tMul leftRaw (tSucc rightRaw)) out)).
Proof.
  intros P hcodomain hsucc htotal hadd G
    leftRaw leftCode rightRaw rightCode rightSuccCode predOut out
    hleft hright hrightSucc hprodPred hmulPred.
  set (sumRaw := tAdd (tMul leftRaw rightRaw) leftRaw).
  set (targetRaw := tMul leftRaw (tSucc rightRaw)).
  pose proof (BProv_Ax_s_codedOrdinalDomain_of_graph
    hcodomain G rightRaw rightCode hright) as hrightDomain.
  pose proof (hsucc G rightRaw rightCode rightSuccCode hright)
    as hrightStep.
  assert (hrightAdjoin : BProv Ax_s G
      (hfAdjoinGraphTermAt rightSuccCode rightCode rightCode)).
  {
    unfold iffForm in hrightStep.
    pose proof (BProv_andE2 Ax_s G _ _ hrightStep) as himp.
    exact (BProv_mp Ax_s G _ _ himp hrightSucc).
  }
  assert (hmulSucc : BProv Ax_s G (pEq targetRaw sumRaw)).
  {
    unfold targetRaw, sumRaw.
    exact (BProv_Ax_s_mulSucc_terms G leftRaw rightRaw).
  }
  assert (hforward : BProv Ax_s G
      (pImp
        (hfMulGraphTermAt_core out leftCode rightSuccCode)
        (ordinalCodeGraphTermAt targetRaw out))).
  {
    apply BProv_impI.
    set (antecedent :=
      hfMulGraphTermAt_core out leftCode rightSuccCode).
    set (C := antecedent :: G).
    assert (hmulOut : BProv Ax_s C antecedent).
    { apply BProv_ass. unfold C. simpl. now left. }
    set (graphBody := ordinalCodeGraphTermAt
      (Term.rename S sumRaw) (tVar 0)).
    pose proof (htotal C sumRaw) as htotalSum.
    set (D := graphBody :: map (rename S) C).
    assert (hinner : BProv Ax_s D
        (rename S (ordinalCodeGraphTermAt targetRaw out))).
    {
      assert (hsum : BProv Ax_s D graphBody).
      { apply BProv_ass. unfold D. simpl. now left. }
      assert (liftC : forall phi,
          BProv Ax_s C phi -> BProv Ax_s D (rename S phi)).
      {
        intros phi hphi.
        unfold D.
        exact (BProv_rename_succ_context_cons_of_sentences
          Ax_s sentence_ax_s C graphBody phi hphi).
      }
      assert (liftG : forall phi,
          BProv Ax_s G phi -> BProv Ax_s D (rename S phi)).
      {
        intros phi hphi.
        apply liftC.
        exact (BProv_context_cons Ax_s G antecedent phi hphi).
      }
      assert (hleftD : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (Term.rename S leftRaw) (Term.rename S leftCode))).
      {
        pose proof (liftG _ hleft) as h.
        rewrite rename_ordinalCodeGraphTermAt in h.
        exact h.
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
      assert (hprodPredD : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (tMul (Term.rename S leftRaw) (Term.rename S rightRaw))
            (Term.rename S predOut))).
      {
        pose proof (liftG _ hprodPred) as h.
        rewrite rename_ordinalCodeGraphTermAt in h.
        cbn [Term.rename] in h.
        exact h.
      }
      assert (hmulPredD : BProv Ax_s D
          (hfMulGraphTermAt_core
            (Term.rename S predOut)
            (Term.rename S leftCode)
            (Term.rename S rightCode))).
      {
        pose proof (liftG _ hmulPred) as h.
        rewrite rename_hfMulGraphTermAt_core in h.
        exact h.
      }
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
      pose proof (BProv_Ax_s_codedOrdinalDomain_of_graph
        hcodomain D (Term.rename S leftRaw)
        (Term.rename S leftCode) hleftD) as hleftDomainD.
      pose proof (BProv_Ax_s_codedOrdinalDomain_of_graph
        hcodomain D (Term.rename S rightRaw)
        (Term.rename S rightCode) hrightD) as hrightDomainD.
      pose proof (BProv_Ax_s_codedOrdinalDomain_of_graph
        hcodomain D (tSucc (Term.rename S rightRaw))
        (Term.rename S rightSuccCode) hrightSuccD)
        as hrightSuccDomainD.
      assert (hmulOutD : BProv Ax_s D
          (hfMulGraphTermAt_core
            (Term.rename S out)
            (Term.rename S leftCode)
            (Term.rename S rightSuccCode))).
      {
        pose proof (liftC _ hmulOut) as h.
        unfold antecedent in h.
        rewrite rename_hfMulGraphTermAt_core in h.
        exact h.
      }
      assert (haddIff : BProv Ax_s D
          (iffForm
            (hfAddGraphTermAt
              (tVar 0) (Term.rename S predOut) (Term.rename S leftCode))
            graphBody)).
      {
        pose proof (hadd D
          (tMul (Term.rename S leftRaw) (Term.rename S rightRaw))
          (Term.rename S predOut)
          (Term.rename S leftRaw) (Term.rename S leftCode)
          (tVar 0) hprodPredD hleftD) as hraw.
        unfold graphBody, sumRaw.
        cbn [Term.rename].
        exact hraw.
      }
      assert (haddOut : BProv Ax_s D
          (hfAddGraphTermAt
            (tVar 0) (Term.rename S predOut) (Term.rename S leftCode))).
      {
        unfold iffForm in haddIff.
        pose proof (BProv_andE2 Ax_s D _ _ haddIff) as himp.
        exact (BProv_mp Ax_s D _ _ himp hsum).
      }
      assert (hmulKnown : BProv Ax_s D
          (hfMulGraphTermAt_core
            (tVar 0) (Term.rename S leftCode)
            (Term.rename S rightSuccCode))).
      {
        exact (BProv_Ax_s_hfMulGraphTermAt_succ_right_mul
          P D (tVar 0) (Term.rename S predOut)
          (Term.rename S leftCode) (Term.rename S rightSuccCode)
          (Term.rename S rightCode)
          hrightDomainD hrightAdjoinD hmulPredD haddOut).
      }
      assert (houtEq : BProv Ax_s D
          (pEq (Term.rename S out) (tVar 0))).
      {
        exact (BProv_Ax_s_hfMulGraphTermAt_functional_mul
          P D (Term.rename S out) (tVar 0)
          (Term.rename S leftCode) (Term.rename S rightSuccCode)
          hleftDomainD hrightSuccDomainD hmulOutD hmulKnown).
      }
      assert (hmulSuccD : BProv Ax_s D
          (pEq
            (Term.rename S targetRaw)
            (Term.rename S sumRaw))).
      {
        unfold targetRaw, sumRaw.
        cbn [Term.rename].
        exact (BProv_Ax_s_mulSucc_terms D
            (Term.rename S leftRaw) (Term.rename S rightRaw)).
      }
      unfold graphBody in hsum.
      pose proof (BProv_ordinalCodeGraphTermAt_congr
        Ax_s D (Term.rename S sumRaw) (Term.rename S targetRaw)
        (tVar 0)
        (Term.rename S out)
        (BProv_eqSym Ax_s D _ _ hmulSuccD)
        (BProv_eqSym Ax_s D _ _ houtEq)
        hsum) as hresult.
      rewrite rename_ordinalCodeGraphTermAt.
      exact hresult.
    }
    unfold C, antecedent.
    apply (BProv_exE_of_sentences Ax_s
      (hfMulGraphTermAt_core out leftCode rightSuccCode :: G)
      graphBody (ordinalCodeGraphTermAt targetRaw out)
      sentence_ax_s htotalSum).
    unfold D.
    exact hinner.
  }
  assert (hreverse : BProv Ax_s G
      (pImp
        (ordinalCodeGraphTermAt targetRaw out)
        (hfMulGraphTermAt_core out leftCode rightSuccCode))).
  {
    apply BProv_impI.
    set (antecedent := ordinalCodeGraphTermAt targetRaw out).
    set (C := antecedent :: G).
    assert (htarget : BProv Ax_s C antecedent).
    { apply BProv_ass. unfold C. simpl. now left. }
    assert (liftG : forall phi,
        BProv Ax_s G phi -> BProv Ax_s C phi).
    {
      intros phi hphi.
      exact (BProv_context_cons Ax_s G antecedent phi hphi).
    }
    assert (hsum : BProv Ax_s C
        (ordinalCodeGraphTermAt sumRaw out)).
    {
      exact (BProv_ordinalCodeGraphTermAt_congr_raw
        Ax_s C targetRaw sumRaw out (liftG _ hmulSucc) htarget).
    }
    assert (haddIff : BProv Ax_s C
        (iffForm
          (hfAddGraphTermAt out predOut leftCode)
          (ordinalCodeGraphTermAt sumRaw out))).
    {
      pose proof (hadd C
        (tMul leftRaw rightRaw) predOut leftRaw leftCode out
        (liftG _ hprodPred) (liftG _ hleft)) as hraw.
      unfold sumRaw.
      exact hraw.
    }
    assert (haddOut : BProv Ax_s C
        (hfAddGraphTermAt out predOut leftCode)).
    {
      unfold iffForm in haddIff.
      pose proof (BProv_andE2 Ax_s C _ _ haddIff) as himp.
      exact (BProv_mp Ax_s C _ _ himp hsum).
    }
    assert (hresult : BProv Ax_s C
        (hfMulGraphTermAt_core out leftCode rightSuccCode)).
    {
      exact (BProv_Ax_s_hfMulGraphTermAt_succ_right_mul
        P C out predOut leftCode rightSuccCode rightCode
        (liftG _ hrightDomain) (liftG _ hrightAdjoin)
        (liftG _ hmulPred) haddOut).
    }
    unfold C, antecedent in hresult.
    exact hresult.
  }
  exact (PAHFProofCalculus.BProv_PA_iffForm_intro Ax_s G _ _ hforward hreverse).
Qed.

(* --------------------------------------------------------------------- *)
(* Stable output and induction-point predicates.                         *)

(** Every possible code of one product satisfies the exact translated
    multiplication/ordinal-graph equivalence. *)
Definition ordinalCodeMulOutputTermAt
    (leftRaw leftCode rightRaw rightCode : term) : formula :=
  pAll
    (iffForm
      (hfMulGraphTermAt_core
        (tVar 0)
        (Term.rename S leftCode)
        (Term.rename S rightCode))
      (ordinalCodeGraphTermAt
        (Term.rename S (tMul leftRaw rightRaw))
        (tVar 0))).

Lemma subst_ordinalCodeMulOutputTermAt : forall sigma
    leftRaw leftCode rightRaw rightCode,
  subst sigma
      (ordinalCodeMulOutputTermAt
        leftRaw leftCode rightRaw rightCode) =
    ordinalCodeMulOutputTermAt
      (Term.subst sigma leftRaw)
      (Term.subst sigma leftCode)
      (Term.subst sigma rightRaw)
      (Term.subst sigma rightCode).
Proof.
  intros sigma leftRaw leftCode rightRaw rightCode.
  unfold ordinalCodeMulOutputTermAt, iffForm.
  cbn [subst].
  rewrite subst_hfMulGraphTermAt_core.
  rewrite subst_ordinalCodeGraphTermAt.
  cbn [Term.subst Term.upSubst].
  repeat rewrite Term.subst_rename_succ_up.
  reflexivity.
Qed.

Lemma rename_ordinalCodeMulOutputTermAt : forall r
    leftRaw leftCode rightRaw rightCode,
  rename r
      (ordinalCodeMulOutputTermAt
        leftRaw leftCode rightRaw rightCode) =
    ordinalCodeMulOutputTermAt
      (Term.rename r leftRaw)
      (Term.rename r leftCode)
      (Term.rename r rightRaw)
      (Term.rename r rightCode).
Proof.
  intros r leftRaw leftCode rightRaw rightCode.
  rename_from_subst subst_ordinalCodeMulOutputTermAt.
Qed.

Lemma BProv_Ax_s_ordinalCodeMulOutputTermAt_at : forall
    G leftRaw leftCode rightRaw rightCode out,
  BProv Ax_s G
    (ordinalCodeMulOutputTermAt
      leftRaw leftCode rightRaw rightCode) ->
  BProv Ax_s G
    (iffForm
      (hfMulGraphTermAt_core out leftCode rightCode)
      (ordinalCodeGraphTermAt (tMul leftRaw rightRaw) out)).
Proof.
  intros G leftRaw leftCode rightRaw rightCode out hall.
  pose proof (BProv_allE Ax_s G _ out hall) as hraw.
  unfold ordinalCodeMulOutputTermAt, iffForm in hraw.
  cbn [subst instTerm Term.subst Term.upSubst] in hraw.
  repeat rewrite subst_hfMulGraphTermAt_core in hraw.
  repeat rewrite subst_ordinalCodeGraphTermAt in hraw.
  cbn [Term.subst Term.upSubst instTerm] in hraw.
  repeat rewrite Term.subst_rename_succ_up in hraw.
  repeat rewrite term_subst_instTerm_rename_succ in hraw.
  exact hraw.
Qed.

(** A multiplication point quantifies over every code of one fixed raw
    right operand.  This is the formula used by the single PA induction. *)
Definition ordinalCodeMulPointTermAt
    (leftRaw leftCode rightRaw : term) : formula :=
  pAll
    (pImp
      (ordinalCodeGraphTermAt
        (Term.rename S rightRaw) (tVar 0))
      (ordinalCodeMulOutputTermAt
        (Term.rename S leftRaw)
        (Term.rename S leftCode)
        (Term.rename S rightRaw)
        (tVar 0))).

Lemma subst_ordinalCodeMulPointTermAt : forall sigma
    leftRaw leftCode rightRaw,
  subst sigma
      (ordinalCodeMulPointTermAt leftRaw leftCode rightRaw) =
    ordinalCodeMulPointTermAt
      (Term.subst sigma leftRaw)
      (Term.subst sigma leftCode)
      (Term.subst sigma rightRaw).
Proof.
  intros sigma leftRaw leftCode rightRaw.
  unfold ordinalCodeMulPointTermAt.
  cbn [subst].
  rewrite subst_ordinalCodeGraphTermAt.
  rewrite subst_ordinalCodeMulOutputTermAt.
  cbn [Term.subst Term.upSubst].
  repeat rewrite Term.subst_rename_succ_up.
  reflexivity.
Qed.

Lemma rename_ordinalCodeMulPointTermAt : forall r
    leftRaw leftCode rightRaw,
  rename r
      (ordinalCodeMulPointTermAt leftRaw leftCode rightRaw) =
    ordinalCodeMulPointTermAt
      (Term.rename r leftRaw)
      (Term.rename r leftCode)
      (Term.rename r rightRaw).
Proof.
  intros r leftRaw leftCode rightRaw.
  rename_from_subst subst_ordinalCodeMulPointTermAt.
Qed.


Lemma BProv_Ax_s_ordinalCodeMulPointTermAt_zero : forall
    (P : TranslatedHFFinAxiomProofs)
    (hcodomain : PAOrdinalCodeGraphCodomainProof)
    (hfunctional : PAOrdinalCodeGraphFunctionalProof)
    G leftRaw leftCode,
  BProv Ax_s G (ordinalCodeGraphTermAt leftRaw leftCode) ->
  BProv Ax_s G
    (ordinalCodeMulPointTermAt leftRaw leftCode tZero).
Proof.
  intros P hcodomain hfunctional G leftRaw leftCode hleft.
  set (rightGraph := ordinalCodeGraphTermAt tZero (tVar 0)).
  set (Q := map (rename S) G).
  assert (hbody : BProv Ax_s Q
      (pImp rightGraph
        (ordinalCodeMulOutputTermAt
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
    pose proof (BProv_Ax_s_ordinalCodeMulCore_zero_mul
      P hcodomain hfunctional D
      (Term.rename S (Term.rename S leftRaw))
      (Term.rename S (Term.rename S leftCode))
      (tVar 1) (tVar 0) hleftD hrightD) as hiff.
    pose proof (BProv_allI_of_sentences
      Ax_s C _ sentence_ax_s hiff) as hall.
    unfold ordinalCodeMulOutputTermAt.
    unfold D, C, Q, rightGraph in hall |- *.
    cbn [Term.rename] in hall |- *.
    exact hall.
  }
  pose proof (BProv_allI_of_sentences
    Ax_s G _ sentence_ax_s hbody) as hall.
  unfold ordinalCodeMulPointTermAt, rightGraph, Q in hall |- *.
  cbn [Term.rename] in hall |- *.
  exact hall.
Qed.

Lemma BProv_Ax_s_ordinalCodeMulOutputTermAt_succ : forall
    (P : TranslatedHFFinAxiomProofs)
    (hcodomain : PAOrdinalCodeGraphCodomainProof)
    (hsucc : PAOrdinalCodeSuccAdjoinCompatibility)
    (htotal : PAOrdinalCodeGraphTotalProof)
    (hadd : PAOrdinalCodeAddTermCompatibility_mul)
    G leftRaw leftCode rightRaw rightCode rightSuccCode,
  BProv Ax_s G (ordinalCodeGraphTermAt leftRaw leftCode) ->
  BProv Ax_s G (ordinalCodeGraphTermAt rightRaw rightCode) ->
  BProv Ax_s G
    (ordinalCodeGraphTermAt (tSucc rightRaw) rightSuccCode) ->
  BProv Ax_s G
    (ordinalCodeMulOutputTermAt
      leftRaw leftCode rightRaw rightCode) ->
  BProv Ax_s G
    (ordinalCodeMulOutputTermAt
      leftRaw leftCode (tSucc rightRaw) rightSuccCode).
Proof.
  intros P hcodomain hsucc htotal hadd G
    leftRaw leftCode rightRaw rightCode rightSuccCode
    hleft hright hrightSucc hih.
  set (productRaw := tMul leftRaw rightRaw).
  set (graphBody := ordinalCodeGraphTermAt
    (Term.rename S productRaw) (tVar 0)).
  pose proof (htotal G productRaw) as hex.
  set (target := ordinalCodeMulOutputTermAt
    leftRaw leftCode (tSucc rightRaw) rightSuccCode).
  set (C := graphBody :: map (rename S) G).
  assert (hinner : BProv Ax_s C (rename S target)).
  {
    assert (hproductPred : BProv Ax_s C graphBody).
    { apply BProv_ass. unfold C. simpl. now left. }
    assert (liftG : forall phi,
        BProv Ax_s G phi -> BProv Ax_s C (rename S phi)).
    {
      intros phi hphi.
      unfold C.
      exact (BProv_rename_succ_context_cons_of_sentences
        Ax_s sentence_ax_s G graphBody phi hphi).
    }
    assert (hleftC : BProv Ax_s C
        (ordinalCodeGraphTermAt
          (Term.rename S leftRaw) (Term.rename S leftCode))).
    {
      pose proof (liftG _ hleft) as h.
      rewrite rename_ordinalCodeGraphTermAt in h.
      exact h.
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
        (ordinalCodeMulOutputTermAt
          (Term.rename S leftRaw)
          (Term.rename S leftCode)
          (Term.rename S rightRaw)
          (Term.rename S rightCode))).
    {
      pose proof (liftG _ hih) as h.
      rewrite rename_ordinalCodeMulOutputTermAt in h.
      exact h.
    }
    pose proof (BProv_Ax_s_ordinalCodeMulOutputTermAt_at
      C (Term.rename S leftRaw) (Term.rename S leftCode)
      (Term.rename S rightRaw) (Term.rename S rightCode)
      (tVar 0) hihC) as hpoint.
    assert (hmulPred : BProv Ax_s C
        (hfMulGraphTermAt_core
          (tVar 0) (Term.rename S leftCode) (Term.rename S rightCode))).
    {
      pose proof (BProv_andE2 Ax_s C _ _ hpoint) as himp.
      unfold graphBody, productRaw in hproductPred.
      cbn [Term.rename] in hproductPred.
      exact (BProv_mp Ax_s C _ _ himp hproductPred).
    }
    set (D := map (rename S) C).
    assert (hleftD : BProv Ax_s D
        (ordinalCodeGraphTermAt
          (Term.rename S (Term.rename S leftRaw))
          (Term.rename S (Term.rename S leftCode)))).
    {
      pose proof (BProv_rename_of_sentences
        Ax_s sentence_ax_s C _ hleftC S) as h.
      unfold D in h.
      repeat rewrite rename_ordinalCodeGraphTermAt in h.
      exact h.
    }
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
    assert (hproductPredD : BProv Ax_s D
        (ordinalCodeGraphTermAt
          (tMul
            (Term.rename S (Term.rename S leftRaw))
            (Term.rename S (Term.rename S rightRaw)))
          (tVar 1))).
    {
      pose proof (BProv_rename_of_sentences
        Ax_s sentence_ax_s C _ hproductPred S) as h.
      unfold D, graphBody, productRaw in h.
      repeat rewrite rename_ordinalCodeGraphTermAt in h.
      cbn [Term.rename] in h.
      exact h.
    }
    assert (hmulPredD : BProv Ax_s D
        (hfMulGraphTermAt_core
          (tVar 1)
          (Term.rename S (Term.rename S leftCode))
          (Term.rename S (Term.rename S rightCode)))).
    {
      pose proof (BProv_rename_of_sentences
        Ax_s sentence_ax_s C _ hmulPred S) as h.
      unfold D in h.
      rewrite rename_hfMulGraphTermAt_core in h.
      cbn [Term.rename] in h.
      exact h.
    }
    pose proof (BProv_Ax_s_ordinalCodeMulCore_succ_of_pred_mul
      P hcodomain hsucc htotal hadd D
      (Term.rename S (Term.rename S leftRaw))
      (Term.rename S (Term.rename S leftCode))
      (Term.rename S (Term.rename S rightRaw))
      (Term.rename S (Term.rename S rightCode))
      (Term.rename S (Term.rename S rightSuccCode))
      (tVar 1) (tVar 0)
      hleftD hrightD hrightSuccD hproductPredD hmulPredD) as hiff.
    pose proof (BProv_allI_of_sentences
      Ax_s C _ sentence_ax_s hiff) as hall.
    unfold D in hall.
    unfold target.
    rewrite rename_ordinalCodeMulOutputTermAt.
    cbn [Term.rename].
    exact hall.
  }
  unfold target, C in *.
  exact (BProv_exE_of_sentences
    Ax_s G graphBody
    (ordinalCodeMulOutputTermAt
      leftRaw leftCode (tSucc rightRaw) rightSuccCode)
    sentence_ax_s hex hinner).
Qed.

Lemma BProv_Ax_s_ordinalCodeMulPointTermAt_of_graph : forall
    G leftRaw leftCode rightRaw rightCode,
  BProv Ax_s G
    (ordinalCodeMulPointTermAt leftRaw leftCode rightRaw) ->
  BProv Ax_s G (ordinalCodeGraphTermAt rightRaw rightCode) ->
  BProv Ax_s G
    (ordinalCodeMulOutputTermAt
      leftRaw leftCode rightRaw rightCode).
Proof.
  intros G leftRaw leftCode rightRaw rightCode hpoint hgraph.
  pose proof (BProv_allE Ax_s G _ rightCode hpoint) as hraw.
  unfold ordinalCodeMulPointTermAt in hraw.
  cbn [subst instTerm Term.subst Term.upSubst] in hraw.
  rewrite subst_ordinalCodeGraphTermAt in hraw.
  rewrite subst_ordinalCodeMulOutputTermAt in hraw.
  cbn [Term.subst Term.upSubst instTerm] in hraw.
  repeat rewrite Term.subst_rename_succ_up in hraw.
  repeat rewrite term_subst_instTerm_rename_succ in hraw.
  exact (BProv_mp Ax_s G _ _ hraw hgraph).
Qed.

Lemma BProv_Ax_s_ordinalCodeMulPointTermAt_succ : forall
    (P : TranslatedHFFinAxiomProofs)
    (hcodomain : PAOrdinalCodeGraphCodomainProof)
    (hsucc : PAOrdinalCodeSuccAdjoinCompatibility)
    (htotal : PAOrdinalCodeGraphTotalProof)
    (hadd : PAOrdinalCodeAddTermCompatibility_mul)
    G leftRaw leftCode rightRaw,
  BProv Ax_s G (ordinalCodeGraphTermAt leftRaw leftCode) ->
  BProv Ax_s G
    (ordinalCodeMulPointTermAt leftRaw leftCode rightRaw) ->
  BProv Ax_s G
    (ordinalCodeMulPointTermAt leftRaw leftCode (tSucc rightRaw)).
Proof.
  intros P hcodomain hsucc htotal hadd G
    leftRaw leftCode rightRaw hleft hih.
  set (rightSuccGraph := ordinalCodeGraphTermAt
    (tSucc (Term.rename S rightRaw)) (tVar 0)).
  set (Q := map (rename S) G).
  assert (hbody : BProv Ax_s Q
      (pImp rightSuccGraph
        (ordinalCodeMulOutputTermAt
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
    set (target := ordinalCodeMulOutputTermAt
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
      assert (hleftQ : BProv Ax_s Q
          (ordinalCodeGraphTermAt
            (Term.rename S leftRaw) (Term.rename S leftCode))).
      {
        pose proof (BProv_rename_of_sentences
          Ax_s sentence_ax_s G _ hleft S) as h.
        unfold Q in h.
        rewrite rename_ordinalCodeGraphTermAt in h.
        exact h.
      }
      assert (hleftC : BProv Ax_s C
          (ordinalCodeGraphTermAt
            (Term.rename S leftRaw) (Term.rename S leftCode))).
      { exact (BProv_context_cons Ax_s Q rightSuccGraph _ hleftQ). }
      assert (hleftD : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (Term.rename S (Term.rename S leftRaw))
            (Term.rename S (Term.rename S leftCode)))).
      {
        pose proof (BProv_rename_succ_context_cons_of_sentences
          Ax_s sentence_ax_s C predBody _ hleftC) as h.
        unfold D in h.
        rewrite rename_ordinalCodeGraphTermAt in h.
        exact h.
      }
      assert (hihQ : BProv Ax_s Q
          (ordinalCodeMulPointTermAt
            (Term.rename S leftRaw)
            (Term.rename S leftCode)
            (Term.rename S rightRaw))).
      {
        pose proof (BProv_rename_of_sentences
          Ax_s sentence_ax_s G _ hih S) as h.
        unfold Q in h.
        rewrite rename_ordinalCodeMulPointTermAt in h.
        exact h.
      }
      assert (hihC : BProv Ax_s C
          (ordinalCodeMulPointTermAt
            (Term.rename S leftRaw)
            (Term.rename S leftCode)
            (Term.rename S rightRaw))).
      { exact (BProv_context_cons Ax_s Q rightSuccGraph _ hihQ). }
      assert (hihD : BProv Ax_s D
          (ordinalCodeMulPointTermAt
            (Term.rename S (Term.rename S leftRaw))
            (Term.rename S (Term.rename S leftCode))
            (Term.rename S (Term.rename S rightRaw)))).
      {
        pose proof (BProv_rename_succ_context_cons_of_sentences
          Ax_s sentence_ax_s C predBody _ hihC) as h.
        unfold D in h.
        rewrite rename_ordinalCodeMulPointTermAt in h.
        exact h.
      }
      assert (hpredGraph : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (Term.rename S (Term.rename S rightRaw)) (tVar 0))).
      { unfold predBody, predRaw in hpred. exact hpred. }
      pose proof (BProv_Ax_s_ordinalCodeMulPointTermAt_of_graph
        D
        (Term.rename S (Term.rename S leftRaw))
        (Term.rename S (Term.rename S leftCode))
        (Term.rename S (Term.rename S rightRaw))
        (tVar 0) hihD hpredGraph) as houtputPred.
      pose proof (BProv_Ax_s_ordinalCodeMulOutputTermAt_succ
        P hcodomain hsucc htotal hadd D
        (Term.rename S (Term.rename S leftRaw))
        (Term.rename S (Term.rename S leftCode))
        (Term.rename S (Term.rename S rightRaw))
        (tVar 0) (tVar 1)
        hleftD hpredGraph hrightSuccD houtputPred) as houtputSucc.
      unfold target.
      rewrite rename_ordinalCodeMulOutputTermAt.
      cbn [Term.rename].
      exact houtputSucc.
    }
    unfold target, C in *.
    exact (BProv_exE_of_sentences
      Ax_s (rightSuccGraph :: Q) predBody
      (ordinalCodeMulOutputTermAt
        (Term.rename S leftRaw)
        (Term.rename S leftCode)
        (tSucc (Term.rename S rightRaw))
        (tVar 0))
      sentence_ax_s hex hinner).
  }
  pose proof (BProv_allI_of_sentences
    Ax_s G _ sentence_ax_s hbody) as hall.
  unfold ordinalCodeMulPointTermAt, rightSuccGraph, Q in hall |- *.
  cbn [Term.rename] in hall |- *.
  exact hall.
Qed.

(** One ordinary PA induction closes multiplication compatibility for every
    raw right operand. *)
Lemma BProv_Ax_s_all_ordinalCodeMulPoint : forall
    (P : TranslatedHFFinAxiomProofs)
    (hcodomain : PAOrdinalCodeGraphCodomainProof)
    (hfunctional : PAOrdinalCodeGraphFunctionalProof)
    (hsucc : PAOrdinalCodeSuccAdjoinCompatibility)
    (htotal : PAOrdinalCodeGraphTotalProof)
    (hadd : PAOrdinalCodeAddTermCompatibility_mul)
    G leftRaw leftCode,
  BProv Ax_s G (ordinalCodeGraphTermAt leftRaw leftCode) ->
  BProv Ax_s G
    (pAll
      (ordinalCodeMulPointTermAt
        (Term.rename S leftRaw)
        (Term.rename S leftCode)
        (tVar 0))).
Proof.
  intros P hcodomain hfunctional hsucc htotal hadd
    G leftRaw leftCode hleft.
  set (phi := ordinalCodeMulPointTermAt
    (Term.rename S leftRaw) (Term.rename S leftCode) (tVar 0)).
  assert (hzero : BProv Ax_s G (subst substZero phi)).
  {
    pose proof (BProv_Ax_s_ordinalCodeMulPointTermAt_zero
      P hcodomain hfunctional G leftRaw leftCode hleft) as hbase.
    unfold phi.
    rewrite subst_ordinalCodeMulPointTermAt.
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
    assert (hleftQ : BProv Ax_s Q
        (ordinalCodeGraphTermAt
          (Term.rename S leftRaw) (Term.rename S leftCode))).
    {
      pose proof (BProv_rename_of_sentences
        Ax_s sentence_ax_s G _ hleft S) as h.
      unfold Q in h.
      rewrite rename_ordinalCodeGraphTermAt in h.
      exact h.
    }
    assert (hleftC : BProv Ax_s C
        (ordinalCodeGraphTermAt
          (Term.rename S leftRaw) (Term.rename S leftCode))).
    { exact (BProv_context_cons Ax_s Q phi _ hleftQ). }
    assert (hnext : BProv Ax_s C
        (ordinalCodeMulPointTermAt
          (Term.rename S leftRaw)
          (Term.rename S leftCode)
          (tSucc (tVar 0)))).
    {
      unfold phi in hih.
      exact (BProv_Ax_s_ordinalCodeMulPointTermAt_succ
        P hcodomain hsucc htotal hadd C
        (Term.rename S leftRaw) (Term.rename S leftCode)
        (tVar 0) hleftC hih).
    }
    assert (hnextSub : BProv Ax_s C (subst substSuccVar phi)).
    {
      unfold phi.
      rewrite subst_ordinalCodeMulPointTermAt.
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
    (ordinalCodeMulPointTermAt
      (Term.rename S leftRaw) (Term.rename S leftCode) (tVar 0))
    hzero hsuccAll).
Qed.

Lemma BProv_Ax_s_ordinalCodeMulPointTermAt : forall
    (P : TranslatedHFFinAxiomProofs)
    (hcodomain : PAOrdinalCodeGraphCodomainProof)
    (hfunctional : PAOrdinalCodeGraphFunctionalProof)
    (hsucc : PAOrdinalCodeSuccAdjoinCompatibility)
    (htotal : PAOrdinalCodeGraphTotalProof)
    (hadd : PAOrdinalCodeAddTermCompatibility_mul)
    G leftRaw leftCode rightRaw,
  BProv Ax_s G (ordinalCodeGraphTermAt leftRaw leftCode) ->
  BProv Ax_s G
    (ordinalCodeMulPointTermAt leftRaw leftCode rightRaw).
Proof.
  intros P hcodomain hfunctional hsucc htotal hadd
    G leftRaw leftCode rightRaw hleft.
  pose proof (BProv_Ax_s_all_ordinalCodeMulPoint
    P hcodomain hfunctional hsucc htotal hadd
    G leftRaw leftCode hleft) as hall.
  pose proof (BProv_allE Ax_s G _ rightRaw hall) as hraw.
  rewrite subst_ordinalCodeMulPointTermAt in hraw.
  cbn [instTerm Term.subst] in hraw.
  repeat rewrite term_subst_instTerm_rename_succ in hraw.
  exact hraw.
Qed.

Theorem BProv_Ax_s_ordinalCodeMulTermAt : forall
    (P : TranslatedHFFinAxiomProofs)
    (hcodomain : PAOrdinalCodeGraphCodomainProof)
    (hfunctional : PAOrdinalCodeGraphFunctionalProof)
    (hsucc : PAOrdinalCodeSuccAdjoinCompatibility)
    (htotal : PAOrdinalCodeGraphTotalProof)
    (hadd : PAOrdinalCodeAddTermCompatibility_mul)
    G leftRaw leftCode rightRaw rightCode out,
  BProv Ax_s G (ordinalCodeGraphTermAt leftRaw leftCode) ->
  BProv Ax_s G (ordinalCodeGraphTermAt rightRaw rightCode) ->
  BProv Ax_s G
    (iffForm
      (hfMulGraphTermAt_core out leftCode rightCode)
      (ordinalCodeGraphTermAt (tMul leftRaw rightRaw) out)).
Proof.
  intros P hcodomain hfunctional hsucc htotal hadd G
    leftRaw leftCode rightRaw rightCode out hleft hright.
  pose proof (BProv_Ax_s_ordinalCodeMulPointTermAt
    P hcodomain hfunctional hsucc htotal hadd
    G leftRaw leftCode rightRaw hleft) as hpoint.
  pose proof (BProv_Ax_s_ordinalCodeMulPointTermAt_of_graph
    G leftRaw leftCode rightRaw rightCode hpoint hright) as houtput.
  exact (BProv_Ax_s_ordinalCodeMulOutputTermAt_at
    G leftRaw leftCode rightRaw rightCode out houtput).
Qed.

(** Abstract sound multiplication kernel.  This is the exact proposition
    consumed by [PAOrdinalCodeMulCoreProofsCorrected_of_term]. *)
Theorem PAOrdinalCodeMulTermCompatibility_of_term_interfaces :
  TranslatedHFFinAxiomProofs ->
  PAOrdinalCodeGraphCodomainProof ->
  PAOrdinalCodeGraphFunctionalProof ->
  PAOrdinalCodeSuccAdjoinCompatibility ->
  PAOrdinalCodeGraphTotalProof ->
  PAOrdinalCodeAddTermCompatibility_mul ->
  PAOrdinalCodeMulTermCompatibility.
Proof.
  intros P hcodomain hfunctional hsucc htotal hadd
    G leftRaw leftCode rightRaw rightCode out hleft hright.
  exact (BProv_Ax_s_ordinalCodeMulTermAt
    P hcodomain hfunctional hsucc htotal hadd
    G leftRaw leftCode rightRaw rightCode out hleft hright).
Qed.

(** Canonical public wrapper: addition and successor term interfaces are
    instantiated from the already proved AddCore compatibility machinery. *)
Theorem PAOrdinalCodeMulTermCompatibility_of_interfaces :
  TranslatedHFFinAxiomProofs ->
  PAOrdinalCodeGraphCodomainProof ->
  PAOrdinalCodeGraphFunctionalProof ->
  PAOrdinalCodeSuccAdjoinCompatibility ->
  PAOrdinalCodeGraphTotalProof ->
  PAOrdinalCodeMulTermCompatibility.
Proof.
  intros P hcodomain hfunctional hsucc htotal.
  exact (PAOrdinalCodeMulTermCompatibility_of_term_interfaces
    P hcodomain hfunctional hsucc
    htotal
    (PAOrdinalCodeAddTermCompatibility_mul_of_interfaces
      P hcodomain hfunctional hsucc htotal)).
Qed.
