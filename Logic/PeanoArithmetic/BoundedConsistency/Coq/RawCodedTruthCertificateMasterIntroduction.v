(**
  Structural introduction of a six-field truth-certificate master proof.

  The final-projection construction consumes a proof of the right-associated
  master conjunction.  Concrete base and successor compilers naturally
  produce the six component proofs separately, however, and all six proofs
  must use one honest witnessed-PA-axiom context before conjunction
  introduction is sound.  This module records that exact common-context
  interface and builds the five [RP_andI] nodes bottom-up.

  No field is decoded and no standardness condition is imposed on any formula
  or proof code.  Consequently the constructor is usable at arbitrary,
  possibly nonstandard, elements of a raw PA model.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedProofAndIConstructor
  RawCodedPALocalProofExistential
  RawCodedPALocalProofAndIntroduction
  RawCodedRestrictedPAProof
  RawCodedPAProvability
  RawCodedTruthCertificateFinalProjection.

Module PABoundedRawCodedTruthCertificateMasterIntroduction.

Import ListNotations.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofAndIConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofAndIntroduction.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedTruthCertificateFinalProjection.

(** The exact proof root obtained by introducing the right-associated master
    conjunction from the last pair outward. *)
Definition rawSixFieldMasterIntroductionRoot (M : RawPAModel)
    (context field1 field2 field3 field4 field5 finalField
      root1 root2 root3 root4 root5 finalRoot : M) : M :=
  let tail5 := rawFormulaAndCode M field5 finalField in
  let proof5 := rawProofAndIRoot M context
    field5 finalField root5 finalRoot in
  let tail4 := rawFormulaAndCode M field4 tail5 in
  let proof4 := rawProofAndIRoot M context
    field4 tail5 root4 proof5 in
  let tail3 := rawFormulaAndCode M field3 tail4 in
  let proof3 := rawProofAndIRoot M context
    field3 tail4 root3 proof4 in
  let tail2 := rawFormulaAndCode M field2 tail3 in
  let proof2 := rawProofAndIRoot M context
    field2 tail3 root2 proof3 in
  rawProofAndIRoot M context field1 tail2 root1 proof2.

Arguments rawSixFieldMasterIntroductionRoot
  M context field1 field2 field3 field4 field5 finalField
    root1 root2 root3 root4 root5 finalRoot : clear implicits.

(** Six covered proofs in one common context introduce the exact master
    formula.  Stating every root explicitly makes this theorem suitable for
    proof-producing successor stages, whose roots are carrier values rather
    than host-language derivation trees. *)
Theorem raw_codedPALocalProofOf_sixFieldMaster_intro : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context field1 field2 field3 field4 field5 finalField
      root1 root2 root3 root4 root5 finalRoot,
  RawCodedPALocalProofOf M context field1 root1 ->
  RawCodedPALocalProofOf M context field2 root2 ->
  RawCodedPALocalProofOf M context field3 root3 ->
  RawCodedPALocalProofOf M context field4 root4 ->
  RawCodedPALocalProofOf M context field5 root5 ->
  RawCodedPALocalProofOf M context finalField finalRoot ->
  RawCodedPALocalProofOf M context
    (rawSixFieldMasterCode M
      field1 field2 field3 field4 field5 finalField)
    (rawSixFieldMasterIntroductionRoot M context
      field1 field2 field3 field4 field5 finalField
      root1 root2 root3 root4 root5 finalRoot).
Proof.
  intros M hPA context field1 field2 field3 field4 field5 finalField
    root1 root2 root3 root4 root5 finalRoot
    hfield1 hfield2 hfield3 hfield4 hfield5 hfinal.
  pose proof (raw_codedPALocalProofOf_andI M hPA context
    field5 finalField root5 finalRoot hfield5 hfinal) as htail5.
  pose proof (raw_codedPALocalProofOf_andI M hPA context
    field4 (rawFormulaAndCode M field5 finalField)
    root4 (rawProofAndIRoot M context
      field5 finalField root5 finalRoot)
    hfield4 htail5) as htail4.
  pose proof (raw_codedPALocalProofOf_andI M hPA context
    field3
      (rawFormulaAndCode M field4
        (rawFormulaAndCode M field5 finalField))
    root3
      (rawProofAndIRoot M context field4
        (rawFormulaAndCode M field5 finalField) root4
        (rawProofAndIRoot M context
          field5 finalField root5 finalRoot))
    hfield3 htail4) as htail3.
  pose proof (raw_codedPALocalProofOf_andI M hPA context
    field2
      (rawFormulaAndCode M field3
        (rawFormulaAndCode M field4
          (rawFormulaAndCode M field5 finalField)))
    root2
      (rawProofAndIRoot M context field3
        (rawFormulaAndCode M field4
          (rawFormulaAndCode M field5 finalField)) root3
        (rawProofAndIRoot M context field4
          (rawFormulaAndCode M field5 finalField) root4
          (rawProofAndIRoot M context
            field5 finalField root5 finalRoot)))
    hfield2 htail3) as htail2.
  pose proof (raw_codedPALocalProofOf_andI M hPA context
    field1
      (rawFormulaAndCode M field2
        (rawFormulaAndCode M field3
          (rawFormulaAndCode M field4
            (rawFormulaAndCode M field5 finalField))))
    root1
      (rawProofAndIRoot M context field2
        (rawFormulaAndCode M field3
          (rawFormulaAndCode M field4
            (rawFormulaAndCode M field5 finalField))) root2
        (rawProofAndIRoot M context field3
          (rawFormulaAndCode M field4
            (rawFormulaAndCode M field5 finalField)) root3
          (rawProofAndIRoot M context field4
            (rawFormulaAndCode M field5 finalField) root4
            (rawProofAndIRoot M context
              field5 finalField root5 finalRoot))))
    hfield1 htail2) as hmaster.
  change (RawCodedPALocalProofOf M context
    (rawSixFieldMasterCode M
      field1 field2 field3 field4 field5 finalField)
    (rawSixFieldMasterIntroductionRoot M context
      field1 field2 field3 field4 field5 finalField
      root1 root2 root3 root4 root5 finalRoot)).
  exact hmaster.
Qed.

(** Package six common-context local proofs as an ordinary PA proof
    certificate.  The witnessed axiom list and context are reused verbatim;
    only the proof root is replaced by the conjunction-introduction tree. *)
Theorem raw_codedPAProofOf_sixFieldMaster_intro : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      witnessList context
      field1 field2 field3 field4 field5 finalField
      root1 root2 root3 root4 root5 finalRoot,
  RawCodedPAAxiomWitnessContext M witnessList context ->
  RawCodedPALocalProofOf M context field1 root1 ->
  RawCodedPALocalProofOf M context field2 root2 ->
  RawCodedPALocalProofOf M context field3 root3 ->
  RawCodedPALocalProofOf M context field4 root4 ->
  RawCodedPALocalProofOf M context field5 root5 ->
  RawCodedPALocalProofOf M context finalField finalRoot ->
  exists certificate : M,
    RawCodedPAProofOf M
      (rawSixFieldMasterCode M
        field1 field2 field3 field4 field5 finalField)
      certificate.
Proof.
  intros M hPA witnessList context
    field1 field2 field3 field4 field5 finalField
    root1 root2 root3 root4 root5 finalRoot
    hwitness hfield1 hfield2 hfield3 hfield4 hfield5 hfinal.
  set (masterRoot := rawSixFieldMasterIntroductionRoot M context
    field1 field2 field3 field4 field5 finalField
    root1 root2 root3 root4 root5 finalRoot).
  assert (hmaster : RawCodedPALocalProofOf M context
      (rawSixFieldMasterCode M
        field1 field2 field3 field4 field5 finalField)
      masterRoot).
  {
    unfold masterRoot.
    exact (raw_codedPALocalProofOf_sixFieldMaster_intro M hPA
      context field1 field2 field3 field4 field5 finalField
      root1 root2 root3 root4 root5 finalRoot
      hfield1 hfield2 hfield3 hfield4 hfield5 hfinal).
  }
  exists (rawCodeList3 M
    (rawNumeralValue M 0) witnessList masterRoot).
  exists witnessList, masterRoot, context.
  split; [reflexivity |].
  destruct hmaster as [hcoverage hendpoint].
  repeat split; assumption.
Qed.

(** For a standard zero stage it is often more convenient to prove the six
    closed components separately in the metatheoretic [BProv] calculus.  This
    corollary joins those derivations before quotation, so their possibly
    different finite PA-axiom bases are merged by the ordinary calculus rather
    than by a raw nonstandard weakening operation. *)
Theorem raw_codedPAProofOf_sixFieldMaster_of_BProv : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      field1 field2 field3 field4 field5 finalField,
  Formula.BProv Formula.Ax_s [] field1 ->
  Formula.BProv Formula.Ax_s [] field2 ->
  Formula.BProv Formula.Ax_s [] field3 ->
  Formula.BProv Formula.Ax_s [] field4 ->
  Formula.BProv Formula.Ax_s [] field5 ->
  Formula.BProv Formula.Ax_s [] finalField ->
  exists certificate : M,
    RawCodedPAProofOf M
      (rawSixFieldMasterCode M
        (rawQuotedFormulaCode M field1)
        (rawQuotedFormulaCode M field2)
        (rawQuotedFormulaCode M field3)
        (rawQuotedFormulaCode M field4)
        (rawQuotedFormulaCode M field5)
        (rawQuotedFormulaCode M finalField))
      certificate.
Proof.
  intros M hPA field1 field2 field3 field4 field5 finalField
    hfield1 hfield2 hfield3 hfield4 hfield5 hfinal.
  set (masterFormula := pAnd field1
    (pAnd field2
      (pAnd field3
        (pAnd field4 (pAnd field5 finalField))))).
  assert (hmaster : Formula.BProv Formula.Ax_s [] masterFormula).
  {
    unfold masterFormula.
    exact (Formula.BProv_andI Formula.Ax_s [] field1 _ hfield1
      (Formula.BProv_andI Formula.Ax_s [] field2 _ hfield2
        (Formula.BProv_andI Formula.Ax_s [] field3 _ hfield3
          (Formula.BProv_andI Formula.Ax_s [] field4 _ hfield4
            (Formula.BProv_andI Formula.Ax_s [] field5 finalField
              hfield5 hfinal))))).
  }
  destruct (raw_codedPAProofOf_of_BProv M hPA masterFormula hmaster)
    as [certificate hcertificate].
  exists certificate.
  rewrite <- (rawQuotedFormulaCode_standard M hPA masterFormula)
    in hcertificate.
  unfold masterFormula in hcertificate.
  cbn [rawQuotedFormulaCode] in hcertificate.
  exact hcertificate.
Qed.

End PABoundedRawCodedTruthCertificateMasterIntroduction.
