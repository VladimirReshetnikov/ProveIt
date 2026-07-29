(**
  Dependency-ordered conjunction over a growing witnessed PA tail.

  Six stable fields of the global traversal are available before the row
  compiler runs.  The row compiler may append helper axiom witnesses, so its
  seventh proof can live over a larger tail.  This module transports the six
  stable proofs exactly once to that selected tail and then applies the
  ordinary seven-way conjunction constructor.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedProofAndIConstructor
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPALocalProofAndIntroduction
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedLtSuccCasesProofCompilation.

Module PABoundedRawCodedPAGrowingTemplateConjunction.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofAndIConstructor.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofAndIntroduction.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedLtSuccCasesProofCompilation.

(** Assemble a right-associated seven-field record once all component proofs
    have reached one literal context.  Keeping this specialization here avoids
    enlarging the low-level binary [And-I] module's dependency surface. *)
Theorem raw_codedPALocalProofOf_and7I : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context a b c d f g h
      aRoot bRoot cRoot dRoot fRoot gRoot hRoot,
  RawCodedPALocalProofOf M context a aRoot ->
  RawCodedPALocalProofOf M context b bRoot ->
  RawCodedPALocalProofOf M context c cRoot ->
  RawCodedPALocalProofOf M context d dRoot ->
  RawCodedPALocalProofOf M context f fRoot ->
  RawCodedPALocalProofOf M context g gRoot ->
  RawCodedPALocalProofOf M context h hRoot ->
  exists root,
    RawCodedPALocalProofOf M context
      (rawFormulaAndCode M a
        (rawFormulaAndCode M b
          (rawFormulaAndCode M c
            (rawFormulaAndCode M d
              (rawFormulaAndCode M f
                (rawFormulaAndCode M g h)))))) root.
Proof.
  intros M hPA context a b c d f g h
    aRoot bRoot cRoot dRoot fRoot gRoot hRoot
    ha hb hc hd hf hg hh.
  pose proof (raw_codedPALocalProofOf_andI M hPA context
    g h gRoot hRoot hg hh) as hgh.
  lazymatch type of hgh with
  | RawCodedPALocalProofOf _ _ _ ?ghRoot =>
      pose proof (raw_codedPALocalProofOf_andI M hPA context
        f (rawFormulaAndCode M g h) fRoot ghRoot hf hgh) as hfgh
  end.
  lazymatch type of hfgh with
  | RawCodedPALocalProofOf _ _ _ ?fghRoot =>
      pose proof (raw_codedPALocalProofOf_andI M hPA context
        d (rawFormulaAndCode M f (rawFormulaAndCode M g h))
        dRoot fghRoot hd hfgh) as hdfgh
  end.
  lazymatch type of hdfgh with
  | RawCodedPALocalProofOf _ _ _ ?dfghRoot =>
      pose proof (raw_codedPALocalProofOf_andI M hPA context
        c (rawFormulaAndCode M d
          (rawFormulaAndCode M f (rawFormulaAndCode M g h)))
        cRoot dfghRoot hc hdfgh) as hcdfgh
  end.
  lazymatch type of hcdfgh with
  | RawCodedPALocalProofOf _ _ _ ?cdfghRoot =>
      pose proof (raw_codedPALocalProofOf_andI M hPA context
        b (rawFormulaAndCode M c
          (rawFormulaAndCode M d
            (rawFormulaAndCode M f (rawFormulaAndCode M g h))))
        bRoot cdfghRoot hb hcdfgh) as hbcdfgh
  end.
  lazymatch type of hbcdfgh with
  | RawCodedPALocalProofOf _ _ _ ?bcdfghRoot =>
      exists (rawProofAndIRoot M context a
        (rawFormulaAndCode M b
          (rawFormulaAndCode M c
            (rawFormulaAndCode M d
              (rawFormulaAndCode M f
                (rawFormulaAndCode M g h)))))
        aRoot bcdfghRoot);
      exact (raw_codedPALocalProofOf_andI M hPA context
        a (rawFormulaAndCode M b
          (rawFormulaAndCode M c
            (rawFormulaAndCode M d
              (rawFormulaAndCode M f
                (rawFormulaAndCode M g h)))))
        aRoot bcdfghRoot ha hbcdfgh)
  end.
Qed.

(** Combine six proofs fixed at the source tail with a seventh proof that is
    allowed to grow that tail.  This asymmetric statement follows the actual
    dependency order and therefore needs no merge of two independently grown
    contexts. *)
Theorem raw_codedPAGrowingTemplateLocalProofAt_and7_of_six_local : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    sourceWitnessList sourceContext prefix
    a b c d f g h
    aRoot bRoot cRoot dRoot fRoot gRoot,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext prefix)
    a aRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext prefix)
    b bRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext prefix)
    c cRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext prefix)
    d dRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext prefix)
    f fRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext prefix)
    g gRoot ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext prefix h ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext prefix
    (rawFormulaAndCode M a
      (rawFormulaAndCode M b
        (rawFormulaAndCode M c
          (rawFormulaAndCode M d
            (rawFormulaAndCode M f
              (rawFormulaAndCode M g h)))))).
Proof.
  intros M hPA translation sourceWitnessList sourceContext prefix
    a b c d f g h aRoot bRoot cRoot dRoot fRoot gRoot
    hsource ha hb hc hd hf hg
    (targetWitnessList & targetContext & hRoot &
      htarget & hincluded & hh).
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation sourceWitnessList sourceContext
      targetWitnessList targetContext prefix a aRoot
      hsource htarget hincluded ha) as [aRoot' ha'].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation sourceWitnessList sourceContext
      targetWitnessList targetContext prefix b bRoot
      hsource htarget hincluded hb) as [bRoot' hb'].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation sourceWitnessList sourceContext
      targetWitnessList targetContext prefix c cRoot
      hsource htarget hincluded hc) as [cRoot' hc'].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation sourceWitnessList sourceContext
      targetWitnessList targetContext prefix d dRoot
      hsource htarget hincluded hd) as [dRoot' hd'].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation sourceWitnessList sourceContext
      targetWitnessList targetContext prefix f fRoot
      hsource htarget hincluded hf) as [fRoot' hf'].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation sourceWitnessList sourceContext
      targetWitnessList targetContext prefix g gRoot
      hsource htarget hincluded hg) as [gRoot' hg'].
  destruct (raw_codedPALocalProofOf_and7I M hPA
    (rawTemplateContextCodeOnTail translation targetContext prefix)
    a b c d f g h aRoot' bRoot' cRoot' dRoot' fRoot' gRoot' hRoot
    ha' hb' hc' hd' hf' hg' hh) as [root hrecord].
  unfold RawCodedPAGrowingTemplateLocalProofAt.
  exists targetWitnessList, targetContext, root.
  split; [exact htarget |].
  split; [exact hincluded | exact hrecord].
Qed.

End PABoundedRawCodedPAGrowingTemplateConjunction.
