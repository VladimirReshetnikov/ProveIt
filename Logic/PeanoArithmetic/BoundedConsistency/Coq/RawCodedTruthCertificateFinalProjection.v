(**
  Structural projection from a six-field master proof certificate.

  The Lean uniform theorem retains five reusable dynamic-truth fields beside
  the final restricted-consistency field.  A Coq successor compiler should do
  the same: retaining only a proof of the final field discards precisely the
  state needed at the next level.  This file validates the corresponding raw
  package shape independently of how those six fields are produced.

  The master code is a right-associated conjunction.  Five already verified
  And-E2 constructors project its forced last coordinate while preserving the
  witnessed PA-axiom list and exact base context hidden in the incoming proof
  certificate.  Thus any future model-internal master-package induction feeds
  the existing compact selector without a weakening theorem.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedProofAndEConstructors
  RawCodedPALocalProofExistential
  RawCodedPALocalProofConjunction
  RawCodedPAProvability.

Module PABoundedRawCodedTruthCertificateFinalProjection.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofAndEConstructors.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPAProvability.

(** The final coordinate is syntactically forced: a compiler cannot satisfy
    the package by choosing an easier sixth formula. *)
Definition rawSixFieldMasterCode (M : RawPAModel)
    (field1 field2 field3 field4 field5 finalField : M) : M :=
  rawFormulaAndCode M field1
    (rawFormulaAndCode M field2
      (rawFormulaAndCode M field3
        (rawFormulaAndCode M field4
          (rawFormulaAndCode M field5 finalField)))).

Arguments rawSixFieldMasterCode
  M field1 field2 field3 field4 field5 finalField : clear implicits.

(** The exact root obtained by applying the right projection five times. *)
Definition rawSixFieldFinalProjectionRoot (M : RawPAModel)
    (context field1 field2 field3 field4 field5 finalField root : M) : M :=
  let tail1 := rawFormulaAndCode M field2
    (rawFormulaAndCode M field3
      (rawFormulaAndCode M field4
        (rawFormulaAndCode M field5 finalField))) in
  let proof1 := rawProofAndERoot M RawAndRight
    context field1 tail1 root in
  let tail2 := rawFormulaAndCode M field3
    (rawFormulaAndCode M field4
      (rawFormulaAndCode M field5 finalField)) in
  let proof2 := rawProofAndERoot M RawAndRight
    context field2 tail2 proof1 in
  let tail3 := rawFormulaAndCode M field4
    (rawFormulaAndCode M field5 finalField) in
  let proof3 := rawProofAndERoot M RawAndRight
    context field3 tail3 proof2 in
  let tail4 := rawFormulaAndCode M field5 finalField in
  let proof4 := rawProofAndERoot M RawAndRight
    context field4 tail4 proof3 in
  rawProofAndERoot M RawAndRight
    context field5 finalField proof4.

Arguments rawSixFieldFinalProjectionRoot
  M context field1 field2 field3 field4 field5 finalField root
  : clear implicits.

Theorem raw_codedPALocalProofOf_sixFieldMaster_final : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context field1 field2 field3 field4 field5 finalField root,
  RawCodedPALocalProofOf M context
    (rawSixFieldMasterCode M
      field1 field2 field3 field4 field5 finalField) root ->
  RawCodedPALocalProofOf M context finalField
    (rawSixFieldFinalProjectionRoot M context
      field1 field2 field3 field4 field5 finalField root).
Proof.
  intros M hPA context field1 field2 field3 field4 field5 finalField
    root hmaster.
  unfold rawSixFieldMasterCode in hmaster.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA context
    field1
    (rawFormulaAndCode M field2
      (rawFormulaAndCode M field3
        (rawFormulaAndCode M field4
          (rawFormulaAndCode M field5 finalField))))
    root hmaster) as h1.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA context
    field2
    (rawFormulaAndCode M field3
      (rawFormulaAndCode M field4
        (rawFormulaAndCode M field5 finalField)))
    (rawProofAndERoot M RawAndRight context field1
      (rawFormulaAndCode M field2
        (rawFormulaAndCode M field3
          (rawFormulaAndCode M field4
            (rawFormulaAndCode M field5 finalField)))) root)
    h1) as h2.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA context
    field3
    (rawFormulaAndCode M field4
      (rawFormulaAndCode M field5 finalField))
    (rawProofAndERoot M RawAndRight context field2
      (rawFormulaAndCode M field3
        (rawFormulaAndCode M field4
          (rawFormulaAndCode M field5 finalField)))
      (rawProofAndERoot M RawAndRight context field1
        (rawFormulaAndCode M field2
          (rawFormulaAndCode M field3
            (rawFormulaAndCode M field4
              (rawFormulaAndCode M field5 finalField)))) root))
    h2) as h3.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA context
    field4 (rawFormulaAndCode M field5 finalField)
    (rawProofAndERoot M RawAndRight context field3
      (rawFormulaAndCode M field4
        (rawFormulaAndCode M field5 finalField))
      (rawProofAndERoot M RawAndRight context field2
        (rawFormulaAndCode M field3
          (rawFormulaAndCode M field4
            (rawFormulaAndCode M field5 finalField)))
        (rawProofAndERoot M RawAndRight context field1
          (rawFormulaAndCode M field2
            (rawFormulaAndCode M field3
              (rawFormulaAndCode M field4
                (rawFormulaAndCode M field5 finalField)))) root)))
    h3) as h4.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA context
    field5 finalField
    (rawProofAndERoot M RawAndRight context field4
      (rawFormulaAndCode M field5 finalField)
      (rawProofAndERoot M RawAndRight context field3
        (rawFormulaAndCode M field4
          (rawFormulaAndCode M field5 finalField))
        (rawProofAndERoot M RawAndRight context field2
          (rawFormulaAndCode M field3
            (rawFormulaAndCode M field4
              (rawFormulaAndCode M field5 finalField)))
          (rawProofAndERoot M RawAndRight context field1
            (rawFormulaAndCode M field2
              (rawFormulaAndCode M field3
                (rawFormulaAndCode M field4
                  (rawFormulaAndCode M field5 finalField)))) root))))
    h4) as h5.
  change (RawCodedPALocalProofOf M context finalField
    (rawSixFieldFinalProjectionRoot M context
      field1 field2 field3 field4 field5 finalField root)).
  exact h5.
Qed.

(** Repackage the projected root with the incoming certificate's same
    witnessed axiom list and context. *)
Theorem raw_codedPAProofOf_sixFieldMaster_final : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      field1 field2 field3 field4 field5 finalField certificate,
  RawCodedPAProofOf M
    (rawSixFieldMasterCode M
      field1 field2 field3 field4 field5 finalField) certificate ->
  exists finalCertificate : M,
    RawCodedPAProofOf M finalField finalCertificate.
Proof.
  intros M hPA field1 field2 field3 field4 field5 finalField
    certificate
    (witnessList & root & context & hcertificate & hwitness &
      hcoverage & hendpoint).
  set (finalRoot := rawSixFieldFinalProjectionRoot M context
    field1 field2 field3 field4 field5 finalField root).
  assert (hfinal : RawCodedPALocalProofOf M context finalField finalRoot).
  {
    unfold finalRoot.
    apply (raw_codedPALocalProofOf_sixFieldMaster_final M hPA).
    split; assumption.
  }
  exists (rawCodeList3 M
    (rawNumeralValue M 0) witnessList finalRoot).
  exists witnessList, finalRoot, context.
  split; [reflexivity |].
  destruct hfinal as [hfinalCoverage hfinalEndpoint].
  repeat split; assumption.
Qed.

End PABoundedRawCodedTruthCertificateFinalProjection.
