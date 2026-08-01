(**
  Dependency-ordered conjunction over a growing witnessed PA tail.

  Six stable fields of the global traversal are available before the row
  compiler runs.  The row compiler may append helper axiom witnesses, so its
  seventh proof can live over a larger tail.  This module transports the six
  stable proofs exactly once to that selected tail and then applies the
  ordinary seven-way conjunction constructor.
*)

From Stdlib Require Import List.
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
  RawCodedPALocalProofWitnessedContextMergeTransportComplete
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedLtSuccCasesProofCompilation.

Module PABoundedRawCodedPAGrowingTemplateConjunction.

Import ListNotations.
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
Import
  PABoundedRawCodedPALocalProofWitnessedContextMergeTransportComplete.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedLtSuccCasesProofCompilation.

(** Two independently growing proofs synchronized without discarding their
    common temporary template prefix.  This is the correct package for
    clients whose conclusions genuinely depend on assumptions above the
    witnessed PA tail. *)
Definition RawCodedPAGrowingTemplateLocalProofPairAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (sourceContext : M) (prefix : TemplateContext)
    (leftConclusion rightConclusion : M) : Prop :=
  exists targetWitnessList targetContext leftRoot rightRoot : M,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M sourceContext targetContext /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation targetContext prefix)
      leftConclusion leftRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation targetContext prefix)
      rightConclusion rightRoot.

Arguments RawCodedPAGrowingTemplateLocalProofPairAt
  M translation sourceContext prefix leftConclusion rightConclusion
  : clear implicits.

(** Merge the two selected witnessed tails and transport each proof beneath
    the unchanged prefix.  This factors the context synchronization needed
    by state-dependent dual-polarity traversal; no equality between prefix
    codes and no contraction back to either input tail is required. *)
Theorem raw_codedPAGrowingTemplateLocalProofAt_pair_at_prefix : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    sourceWitnessList sourceContext prefix leftConclusion rightConclusion,
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext prefix leftConclusion ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext prefix rightConclusion ->
  RawCodedPAGrowingTemplateLocalProofPairAt M translation sourceContext
    prefix leftConclusion rightConclusion.
Proof.
  intros M hPA translation sourceWitnessList sourceContext prefix
    leftConclusion rightConclusion
    (leftWitnessList & leftContext & leftRoot &
      hleftWitnessed & hsourceLeft & hleftProof)
    (rightWitnessList & rightContext & rightRoot &
      hrightWitnessed & _hsourceRight & hrightProof).
  destruct
    (raw_codedPAAxiomWitnessContext_prefixMerge M hPA
      leftWitnessList leftContext rightWitnessList rightContext
      hleftWitnessed hrightWitnessed)
    as (targetWitnessList & targetContext & htargetWitnessed &
      _hleftWitnessIncluded & hleftIncluded &
      _hrightWitnessIncluded & hrightIncluded & _hrightTransport).
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation leftWitnessList leftContext
      targetWitnessList targetContext prefix leftConclusion leftRoot
      hleftWitnessed htargetWitnessed hleftIncluded hleftProof)
    as [transportedLeftRoot htransportedLeft].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation rightWitnessList rightContext
      targetWitnessList targetContext prefix rightConclusion rightRoot
      hrightWitnessed htargetWitnessed hrightIncluded hrightProof)
    as [transportedRightRoot htransportedRight].
  exists targetWitnessList, targetContext,
    transportedLeftRoot, transportedRightRoot.
  split; [exact htargetWitnessed |].
  split.
  - intros member hmember.
    exact (hleftIncluded member (hsourceLeft member hmember)).
  - split; assumption.
Qed.

(** A pair of independently growing empty-prefix proofs after synchronization.
    The package keeps the original-tail inclusion because later clients must
    also transport roots which were compiled before either growing branch. *)
Definition RawCodedPAGrowingTemplateLocalProofPairAtEmpty
    (M : RawPAModel) (sourceContext leftConclusion rightConclusion : M)
    : Prop :=
  exists targetWitnessList targetContext leftRoot rightRoot : M,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M sourceContext targetContext /\
    RawCodedPALocalProofOf M targetContext leftConclusion leftRoot /\
    RawCodedPALocalProofOf M targetContext rightConclusion rightRoot.

Arguments RawCodedPAGrowingTemplateLocalProofPairAtEmpty
  M sourceContext leftConclusion rightConclusion : clear implicits.

(** Merge two independently selected growing tails.  Empty template prefixes
    are essential here: their operational proof contexts reduce literally to
    the selected PA tails, so the completed witnessed-context merge applies
    without any prefix-code equation.  Inclusion of the original source is
    composed through the left branch; either branch would give the same
    guarantee. *)
Theorem raw_codedPAGrowingTemplateLocalProofAt_pair_at_empty : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    sourceWitnessList sourceContext leftConclusion rightConclusion,
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext [] leftConclusion ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext [] rightConclusion ->
  RawCodedPAGrowingTemplateLocalProofPairAtEmpty M sourceContext
    leftConclusion rightConclusion.
Proof.
  intros M hPA translation sourceWitnessList sourceContext
    leftConclusion rightConclusion hleft hright.
  destruct
    (raw_codedPAGrowingTemplateLocalProofAt_pair_at_prefix
      M hPA translation sourceWitnessList sourceContext nil
      leftConclusion rightConclusion hleft hright)
    as (targetWitnessList & targetContext &
      transportedLeftRoot & transportedRightRoot &
      htargetWitnessed & hincluded &
      hleftTransported & hrightTransported).
  cbn [rawTemplateContextCodeOnTail]
    in hleftTransported, hrightTransported.
  exists targetWitnessList, targetContext,
    transportedLeftRoot, transportedRightRoot.
  split; [exact htargetWitnessed |].
  split; [exact hincluded |].
  split; assumption.
Qed.

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
