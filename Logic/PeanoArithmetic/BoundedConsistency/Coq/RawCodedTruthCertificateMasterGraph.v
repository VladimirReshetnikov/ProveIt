(**
  A represented graph for the six-field truth-certificate master code.

  The final-projection module fixes the master certificate to a
  right-associated conjunction, but its constructor was previously exposed
  only as a meta-level operation on elements of a raw PA model.  The uniform
  selector needs the corresponding object-language graph: its induction
  invariant must say that one and the same carrier element is both the exact
  six-field formula code and the target of an ordinary PA proof certificate.

  Four hidden tail codes suffice.  Every constraint below is one of the
  already represented formula-code constructors, so the graph works for
  nonstandard field codes without decoding any syntax in Rocq.
*)

From Stdlib Require Import Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedPAProvability
  RawCodedTruthCertificateFinalProjection.

Module PABoundedRawCodedTruthCertificateMasterGraph.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedTruthCertificateFinalProjection.

(** Small right-associated wrappers keep the de Bruijn layout below visible. *)
Definition masterGraphAnd5
    (first second third fourth fifth : formula) : formula :=
  pAnd first (pAnd second (pAnd third (pAnd fourth fifth))).

Definition masterGraphEx4 (body : formula) : formula :=
  pEx (pEx (pEx (pEx body))).

(** Output-first graph.  From the outside in, the four witnesses are the
    conjunction tails beginning at fields 2, 3, 4, and 5 respectively. *)
Definition sixFieldMasterCodeTermAt
    (output field1 field2 field3 field4 field5 finalField : term) : formula :=
  masterGraphEx4
    (masterGraphAnd5
      (formulaAndCodeTermAt
        (liftTerm 4 output) (liftTerm 4 field1) (tVar 3))
      (formulaAndCodeTermAt
        (tVar 3) (liftTerm 4 field2) (tVar 2))
      (formulaAndCodeTermAt
        (tVar 2) (liftTerm 4 field3) (tVar 1))
      (formulaAndCodeTermAt
        (tVar 1) (liftTerm 4 field4) (tVar 0))
      (formulaAndCodeTermAt
        (tVar 0) (liftTerm 4 field5) (liftTerm 4 finalField))).

Definition RawSixFieldMasterCodeAt (M : RawPAModel)
    (output field1 field2 field3 field4 field5 finalField : M) : Prop :=
  output = rawSixFieldMasterCode M
    field1 field2 field3 field4 field5 finalField.

Arguments RawSixFieldMasterCodeAt
  M output field1 field2 field3 field4 field5 finalField : clear implicits.

Lemma raw_masterGraph_eval_liftTerm_four : forall
    (M : RawPAModel) a b c d (e : nat -> M) t,
  raw_term_eval M
    (scons M a (scons M b (scons M c (scons M d e))))
    (liftTerm 4 t) = raw_term_eval M e t.
Proof.
  intros M a b c d e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro i.
  replace (i + 4) with (S (S (S (S i)))) by lia.
  reflexivity.
Qed.

(** Exact arbitrary-model semantics of the represented constructor graph. *)
Lemma raw_sat_sixFieldMasterCodeTermAt_iff : forall
    (M : RawPAModel) e output
      field1 field2 field3 field4 field5 finalField,
  raw_formula_sat M e
    (sixFieldMasterCodeTermAt output
      field1 field2 field3 field4 field5 finalField) <->
  RawSixFieldMasterCodeAt M
    (raw_term_eval M e output)
    (raw_term_eval M e field1)
    (raw_term_eval M e field2)
    (raw_term_eval M e field3)
    (raw_term_eval M e field4)
    (raw_term_eval M e field5)
    (raw_term_eval M e finalField).
Proof.
  intros M e output field1 field2 field3 field4 field5 finalField.
  unfold sixFieldMasterCodeTermAt, masterGraphEx4, masterGraphAnd5,
    RawSixFieldMasterCodeAt.
  cbn [raw_formula_sat].
  unfold rawSixFieldMasterCode.
  split.
  - intros (tail1 & tail2 & tail3 & tail4 &
      hroot & htail1 & htail2 & htail3 & htail4).
    apply (proj1 (raw_sat_formulaAndCodeTermAt_iff M
      (scons M tail4 (scons M tail3 (scons M tail2 (scons M tail1 e))))
      (liftTerm 4 output) (liftTerm 4 field1) (tVar 3))) in hroot.
    apply (proj1 (raw_sat_formulaAndCodeTermAt_iff M
      (scons M tail4 (scons M tail3 (scons M tail2 (scons M tail1 e))))
      (tVar 3) (liftTerm 4 field2) (tVar 2))) in htail1.
    apply (proj1 (raw_sat_formulaAndCodeTermAt_iff M
      (scons M tail4 (scons M tail3 (scons M tail2 (scons M tail1 e))))
      (tVar 2) (liftTerm 4 field3) (tVar 1))) in htail2.
    apply (proj1 (raw_sat_formulaAndCodeTermAt_iff M
      (scons M tail4 (scons M tail3 (scons M tail2 (scons M tail1 e))))
      (tVar 1) (liftTerm 4 field4) (tVar 0))) in htail3.
    apply (proj1 (raw_sat_formulaAndCodeTermAt_iff M
      (scons M tail4 (scons M tail3 (scons M tail2 (scons M tail1 e))))
      (tVar 0) (liftTerm 4 field5) (liftTerm 4 finalField))) in htail4.
    repeat rewrite raw_masterGraph_eval_liftTerm_four in hroot.
    repeat rewrite raw_masterGraph_eval_liftTerm_four in htail1.
    repeat rewrite raw_masterGraph_eval_liftTerm_four in htail2.
    repeat rewrite raw_masterGraph_eval_liftTerm_four in htail3.
    repeat rewrite raw_masterGraph_eval_liftTerm_four in htail4.
    cbn [raw_term_eval scons] in hroot, htail1, htail2, htail3, htail4.
    rewrite htail4 in htail3.
    rewrite htail3 in htail2.
    rewrite htail2 in htail1.
    now rewrite htail1 in hroot.
  - intro hroot.
    set (tail4 := rawFormulaAndCode M
      (raw_term_eval M e field5) (raw_term_eval M e finalField)).
    set (tail3 := rawFormulaAndCode M
      (raw_term_eval M e field4) tail4).
    set (tail2 := rawFormulaAndCode M
      (raw_term_eval M e field3) tail3).
    set (tail1 := rawFormulaAndCode M
      (raw_term_eval M e field2) tail2).
    exists tail1, tail2, tail3, tail4.
    repeat split.
    + apply (proj2 (raw_sat_formulaAndCodeTermAt_iff M
        (scons M tail4 (scons M tail3 (scons M tail2 (scons M tail1 e))))
        (liftTerm 4 output) (liftTerm 4 field1) (tVar 3))).
      repeat rewrite raw_masterGraph_eval_liftTerm_four.
      cbn [raw_term_eval scons]. exact hroot.
    + apply (proj2 (raw_sat_formulaAndCodeTermAt_iff M
        (scons M tail4 (scons M tail3 (scons M tail2 (scons M tail1 e))))
        (tVar 3) (liftTerm 4 field2) (tVar 2))).
      rewrite raw_masterGraph_eval_liftTerm_four.
      cbn [raw_term_eval scons]. exact (eq_sym (eq_refl tail1)).
    + apply (proj2 (raw_sat_formulaAndCodeTermAt_iff M
        (scons M tail4 (scons M tail3 (scons M tail2 (scons M tail1 e))))
        (tVar 2) (liftTerm 4 field3) (tVar 1))).
      rewrite raw_masterGraph_eval_liftTerm_four.
      cbn [raw_term_eval scons]. exact (eq_sym (eq_refl tail2)).
    + apply (proj2 (raw_sat_formulaAndCodeTermAt_iff M
        (scons M tail4 (scons M tail3 (scons M tail2 (scons M tail1 e))))
        (tVar 1) (liftTerm 4 field4) (tVar 0))).
      rewrite raw_masterGraph_eval_liftTerm_four.
      cbn [raw_term_eval scons]. exact (eq_sym (eq_refl tail3)).
    + apply (proj2 (raw_sat_formulaAndCodeTermAt_iff M
        (scons M tail4 (scons M tail3 (scons M tail2 (scons M tail1 e))))
        (tVar 0) (liftTerm 4 field5) (liftTerm 4 finalField))).
      repeat rewrite raw_masterGraph_eval_liftTerm_four.
      cbn [raw_term_eval scons]. exact (eq_sym (eq_refl tail4)).
Qed.

Lemma raw_sixFieldMasterCodeAt_total : forall
    (M : RawPAModel) field1 field2 field3 field4 field5 finalField,
  RawSixFieldMasterCodeAt M
    (rawSixFieldMasterCode M
      field1 field2 field3 field4 field5 finalField)
    field1 field2 field3 field4 field5 finalField.
Proof.
  intros. reflexivity.
Qed.

Lemma raw_sixFieldMasterCodeAt_functional : forall
    (M : RawPAModel) output1 output2
      field1 field2 field3 field4 field5 finalField,
  RawSixFieldMasterCodeAt M output1
    field1 field2 field3 field4 field5 finalField ->
  RawSixFieldMasterCodeAt M output2
    field1 field2 field3 field4 field5 finalField ->
  output1 = output2.
Proof.
  intros M output1 output2 field1 field2 field3 field4 field5 finalField
    houtput1 houtput2.
  unfold RawSixFieldMasterCodeAt in *. congruence.
Qed.

(** The direct package used by model-internal induction: the existential
    witness is simultaneously the graph-selected master formula and the
    target of a genuine ordinary PA proof certificate. *)
Definition sixFieldMasterProvabilityTermAt
    (field1 field2 field3 field4 field5 finalField : term) : formula :=
  pEx
    (pAnd
      (sixFieldMasterCodeTermAt
        (tVar 0)
        (liftTerm 1 field1) (liftTerm 1 field2)
        (liftTerm 1 field3) (liftTerm 1 field4)
        (liftTerm 1 field5) (liftTerm 1 finalField))
      (codedPAProvabilityTermAt (tVar 0))).

Lemma raw_masterGraph_eval_liftTerm_one : forall
    (M : RawPAModel) a (e : nat -> M) t,
  raw_term_eval M (scons M a e) (liftTerm 1 t) =
  raw_term_eval M e t.
Proof.
  intros M a e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro i.
  replace (i + 1) with (S i) by lia. reflexivity.
Qed.

Lemma raw_sat_sixFieldMasterProvabilityTermAt_iff : forall
    (M : RawPAModel) e field1 field2 field3 field4 field5 finalField,
  raw_formula_sat M e
    (sixFieldMasterProvabilityTermAt
      field1 field2 field3 field4 field5 finalField) <->
  exists master certificate : M,
    RawSixFieldMasterCodeAt M master
      (raw_term_eval M e field1)
      (raw_term_eval M e field2)
      (raw_term_eval M e field3)
      (raw_term_eval M e field4)
      (raw_term_eval M e field5)
      (raw_term_eval M e finalField) /\
    RawCodedPAProofOf M master certificate.
Proof.
  intros M e field1 field2 field3 field4 field5 finalField.
  unfold sixFieldMasterProvabilityTermAt.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_sixFieldMasterCodeTermAt_iff.
  setoid_rewrite raw_sat_codedPAProvabilityTermAt_iff.
  repeat setoid_rewrite raw_masterGraph_eval_liftTerm_one.
  cbn [raw_term_eval scons].
  split.
  - intros (master & hmaster & certificate & hcertificate).
    exists master, certificate. split; assumption.
  - intros (master & certificate & hmaster & hcertificate).
    exists master. split; [exact hmaster |].
    exists certificate. exact hcertificate.
Qed.

(** The package's sixth coordinate is genuinely forced.  This theorem is
    the generic final-extraction callback for any future PA-internal master
    package induction. *)
Theorem raw_sixFieldMasterProvability_final : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      field1 field2 field3 field4 field5 finalField,
  (exists master certificate : M,
    RawSixFieldMasterCodeAt M master
      field1 field2 field3 field4 field5 finalField /\
    RawCodedPAProofOf M master certificate) ->
  exists finalCertificate : M,
    RawCodedPAProofOf M finalField finalCertificate.
Proof.
  intros M hPA field1 field2 field3 field4 field5 finalField
    (master & certificate & hmaster & hcertificate).
  unfold RawSixFieldMasterCodeAt in hmaster. subst master.
  exact (raw_codedPAProofOf_sixFieldMaster_final M hPA
    field1 field2 field3 field4 field5 finalField
    certificate hcertificate).
Qed.

End PABoundedRawCodedTruthCertificateMasterGraph.
