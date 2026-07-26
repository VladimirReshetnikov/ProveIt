(**
  Project every component of an exact six-field master certificate.

  [RawCodedPAProofOf] hides one witnessed PA-axiom list, one context, and one
  local proof root.  When its target is the transparent right-associated
  six-field master conjunction, checked And-E constructors project all six
  coordinates while retaining that same witnessed context.  This is a
  decomposition of the *current* package only; it neither constructs nor
  postulates any successor field.

  The second theorem applies this projection to exactly the graph and proof
  premises presented to the component successor bridge.  The concrete graph
  selects the six coordinates and fixes the current master to their
  conjunction; the exact proof then supplies their common-context roots.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedProofEndpoints
  RawCodedProofAndEConstructors
  RawCodedPALocalProofExistential
  RawCodedPALocalProofConjunction
  RawCodedPAProvability
  RawCodedRestrictedPAConsistencyFormulaCode
  CompactRestrictedPAConsistencyFormulaCodeGraph
  RawCodedTruthCertificateFinalProjection
  RawCodedTruthCertificateMasterGraph
  RawCodedTruthCertificateMasterAssembler
  RawCodedTruthCertificateMasterBaseBridge
  RawCodedTruthCertificateMasterSuccessorBridge.

Module PABoundedRawCodedTruthCertificateMasterComponentProjection.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofAndEConstructors.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedCompactRestrictedPAConsistencyFormulaCodeGraph.
Import PABoundedRawCodedTruthCertificateFinalProjection.
Import PABoundedRawCodedTruthCertificateMasterGraph.
Import PABoundedRawCodedTruthCertificateMasterAssembler.
Import PABoundedRawCodedTruthCertificateMasterBaseBridge.
Import PABoundedRawCodedTruthCertificateMasterSuccessorBridge.

(** An exact master proof contains local proofs of all six components in the
    certificate's original witnessed PA context.  The proof roots below are
    concrete And-E trees; no context weakening or fresh axiom witness is
    introduced. *)
Theorem raw_codedPAProofOf_sixFieldMaster_common_context : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      field1 field2 field3 field4 field5 finalField certificate,
  RawCodedPAProofOf M
    (rawSixFieldMasterCode M
      field1 field2 field3 field4 field5 finalField)
    certificate ->
  RawSixFieldMasterCommonContextProofsOf M
    field1 field2 field3 field4 field5 finalField.
Proof.
  intros M hPA field1 field2 field3 field4 field5 finalField
    certificate
    (witnessList & masterRoot & context & hcertificate & hwitness &
      hcoverage & hendpoint).

  (* Name the four conjunction suffixes once.  This keeps the exact And-E
     roots readable and makes their shared [context] syntactically visible. *)
  set (suffix5 := rawFormulaAndCode M field5 finalField).
  set (suffix4 := rawFormulaAndCode M field4 suffix5).
  set (suffix3 := rawFormulaAndCode M field3 suffix4).
  set (suffix2 := rawFormulaAndCode M field2 suffix3).
  assert (hmaster : RawCodedPALocalProofOf M context
      (rawFormulaAndCode M field1 suffix2) masterRoot).
  {
    split; [exact hcoverage |].
    change (RawProofEndpoint M masterRoot context
      (rawSixFieldMasterCode M
        field1 field2 field3 field4 field5 finalField)) in hendpoint.
    unfold rawSixFieldMasterCode in hendpoint.
    change (RawProofEndpoint M masterRoot context
      (rawFormulaAndCode M field1 suffix2)).
    exact hendpoint.
  }

  (* First coordinate and the suffix beginning with the second coordinate. *)
  set (field1Root := rawProofAndERoot M RawAndLeft
    context field1 suffix2 masterRoot).
  set (suffix2Root := rawProofAndERoot M RawAndRight
    context field1 suffix2 masterRoot).
  assert (hfield1 : RawCodedPALocalProofOf M context field1 field1Root).
  {
    unfold field1Root.
    exact (raw_codedPALocalProofOf_andE1 M hPA
      context field1 suffix2 masterRoot hmaster).
  }
  assert (hsuffix2 : RawCodedPALocalProofOf M context suffix2 suffix2Root).
  {
    unfold suffix2Root.
    exact (raw_codedPALocalProofOf_andE2 M hPA
      context field1 suffix2 masterRoot hmaster).
  }

  (* Second coordinate. *)
  set (field2Root := rawProofAndERoot M RawAndLeft
    context field2 suffix3 suffix2Root).
  set (suffix3Root := rawProofAndERoot M RawAndRight
    context field2 suffix3 suffix2Root).
  assert (hfield2 : RawCodedPALocalProofOf M context field2 field2Root).
  {
    unfold field2Root.
    apply (raw_codedPALocalProofOf_andE1 M hPA
      context field2 suffix3 suffix2Root).
    change (RawCodedPALocalProofOf M context
      (rawFormulaAndCode M field2 suffix3) suffix2Root).
    exact hsuffix2.
  }
  assert (hsuffix3 : RawCodedPALocalProofOf M context suffix3 suffix3Root).
  {
    unfold suffix3Root.
    apply (raw_codedPALocalProofOf_andE2 M hPA
      context field2 suffix3 suffix2Root).
    change (RawCodedPALocalProofOf M context
      (rawFormulaAndCode M field2 suffix3) suffix2Root).
    exact hsuffix2.
  }

  (* Third coordinate. *)
  set (field3Root := rawProofAndERoot M RawAndLeft
    context field3 suffix4 suffix3Root).
  set (suffix4Root := rawProofAndERoot M RawAndRight
    context field3 suffix4 suffix3Root).
  assert (hfield3 : RawCodedPALocalProofOf M context field3 field3Root).
  {
    unfold field3Root.
    apply (raw_codedPALocalProofOf_andE1 M hPA
      context field3 suffix4 suffix3Root).
    change (RawCodedPALocalProofOf M context
      (rawFormulaAndCode M field3 suffix4) suffix3Root).
    exact hsuffix3.
  }
  assert (hsuffix4 : RawCodedPALocalProofOf M context suffix4 suffix4Root).
  {
    unfold suffix4Root.
    apply (raw_codedPALocalProofOf_andE2 M hPA
      context field3 suffix4 suffix3Root).
    change (RawCodedPALocalProofOf M context
      (rawFormulaAndCode M field3 suffix4) suffix3Root).
    exact hsuffix3.
  }

  (* Fourth coordinate. *)
  set (field4Root := rawProofAndERoot M RawAndLeft
    context field4 suffix5 suffix4Root).
  set (suffix5Root := rawProofAndERoot M RawAndRight
    context field4 suffix5 suffix4Root).
  assert (hfield4 : RawCodedPALocalProofOf M context field4 field4Root).
  {
    unfold field4Root.
    apply (raw_codedPALocalProofOf_andE1 M hPA
      context field4 suffix5 suffix4Root).
    change (RawCodedPALocalProofOf M context
      (rawFormulaAndCode M field4 suffix5) suffix4Root).
    exact hsuffix4.
  }
  assert (hsuffix5 : RawCodedPALocalProofOf M context suffix5 suffix5Root).
  {
    unfold suffix5Root.
    apply (raw_codedPALocalProofOf_andE2 M hPA
      context field4 suffix5 suffix4Root).
    change (RawCodedPALocalProofOf M context
      (rawFormulaAndCode M field4 suffix5) suffix4Root).
    exact hsuffix4.
  }

  (* The last conjunction yields both the fifth and final coordinates. *)
  set (field5Root := rawProofAndERoot M RawAndLeft
    context field5 finalField suffix5Root).
  set (finalRoot := rawProofAndERoot M RawAndRight
    context field5 finalField suffix5Root).
  assert (hfield5 : RawCodedPALocalProofOf M context field5 field5Root).
  {
    unfold field5Root.
    apply (raw_codedPALocalProofOf_andE1 M hPA
      context field5 finalField suffix5Root).
    change (RawCodedPALocalProofOf M context
      (rawFormulaAndCode M field5 finalField) suffix5Root).
    exact hsuffix5.
  }
  assert (hfinal : RawCodedPALocalProofOf M context finalField finalRoot).
  {
    unfold finalRoot.
    apply (raw_codedPALocalProofOf_andE2 M hPA
      context field5 finalField suffix5Root).
    change (RawCodedPALocalProofOf M context
      (rawFormulaAndCode M field5 finalField) suffix5Root).
    exact hsuffix5.
  }

  unfold RawSixFieldMasterCommonContextProofsOf.
  exists witnessList, context,
    field1Root, field2Root, field3Root, field4Root, field5Root, finalRoot.
  split; [exact hwitness |].
  split; [exact hfield1 |].
  split; [exact hfield2 |].
  split; [exact hfield3 |].
  split; [exact hfield4 |].
  split; [exact hfield5 |].
  exact hfinal.
Qed.

(** Direct decomposition of the two current-package premises consumed by
    [RawSixFieldMasterRawComponentSuccessor].  The result contains only the
    graph-selected current fields and their projected current proofs. *)
Theorem raw_sixFieldMaster_current_components_of_graph_and_proof : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      field1Graph field2Graph field3Graph field4Graph field5Graph
      (tail : nat -> M) level currentMaster currentCertificate,
  raw_formula_sat M
    (scons M currentMaster (scons M level tail))
    (concreteSixFieldMasterGraph
      field1Graph field2Graph field3Graph field4Graph field5Graph) ->
  RawCodedPAProofOf M currentMaster currentCertificate ->
  exists field1 field2 field3 field4 field5 finalField : M,
    RawSixFieldMasterGraphWitnessesAt M
      field1Graph field2Graph field3Graph field4Graph field5Graph
      tail level field1 field2 field3 field4 field5 finalField /\
    RawSixFieldMasterCommonContextProofsOf M
      field1 field2 field3 field4 field5 finalField.
Proof.
  intros M hPA field1Graph field2Graph field3Graph field4Graph field5Graph
    tail level currentMaster currentCertificate hgraph hproof.
  pose proof (proj1 (raw_sat_concreteSixFieldMasterGraph_iff M
    field1Graph field2Graph field3Graph field4Graph field5Graph
    tail level currentMaster) hgraph) as hcomponents.
  destruct hcomponents as
    (field1 & field2 & field3 & field4 & field5 & finalField &
      hfield1Graph & hfield2Graph & hfield3Graph & hfield4Graph &
      hfield5Graph & hfinalCode & hmasterCode).
  unfold RawSixFieldMasterCodeAt in hmasterCode.
  assert (hexact : RawCodedPAProofOf M
      (rawSixFieldMasterCode M
        field1 field2 field3 field4 field5 finalField)
      currentCertificate).
  {
    rewrite <- hmasterCode. exact hproof.
  }
  exists field1, field2, field3, field4, field5, finalField.
  split.
  - unfold RawSixFieldMasterGraphWitnessesAt.
    split; [exact hfield1Graph |].
    split; [exact hfield2Graph |].
    split; [exact hfield3Graph |].
    split; [exact hfield4Graph |].
    split; [exact hfield5Graph |].
    exact (proj2
      (compactRestrictedPAConsistencyFormulaCodeGraph_representation
        M tail level finalField) hfinalCode).
  - exact (raw_codedPAProofOf_sixFieldMaster_common_context
      M hPA field1 field2 field3 field4 field5 finalField
      currentCertificate hexact).
Qed.

End PABoundedRawCodedTruthCertificateMasterComponentProjection.
