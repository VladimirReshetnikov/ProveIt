(**
  Carrier compiler for the growing synchronized native PA axiom rows.

  The closed template law proved by the companion module has two ordinary
  PA theorems among its hypotheses: universal context-membership transfer
  and universal beta-assignment definedness.  Compiling either theorem may
  add a finite prefix of standard PA axioms.  Consequently the honest
  carrier statement is growing: it returns one accumulated standard-witness
  prefix and proves the selected row over the corresponding enlarged tail.

  The proof below makes the dependency order explicit.  Transfer is
  compiled first, definedness second, and the transfer root is rebuilt
  through the second prefix.  The closed logical law and both helper roots
  are then transplanted beneath the four literal row assumptions.  Six
  represented implication eliminations finish the selected leaf.

  Two code identifications remain at the carrier boundary.  They say that
  the graph-selected, twice-shifted axiom field is the direct translation of
  the transparent row field and that the selected context-truth leaf is the
  direct translation of the transparent target.  Keeping these equations as
  an explicit record prevents the row compiler from silently mixing inputs
  or selectors chosen by different native packages.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofContextInsertUnconditional
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPAAxiomWitness
  RawCodedPAAxiomWitnessPrefix
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateNumeralParameters
  RawCodedTemplateTernaryApplication
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedFormulaBoundAllCarrierBoundary
  RawCodedDynamicContextTruthSelector
  RawCodedAssignmentUniversalDefinednessProofCompilation
  RawCodedContextMembershipTransferPA
  RawCodedRestrictedPAAxiomContextTruthNativeDirectBodyShell
  RawCodedRestrictedPAAxiomContextTruthNativeDirectTraversalLeaf
  RawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsWitnessShapes
  RawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsPointwise
  RawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsGrowingLaw.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsGrowingCarrier.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofContextInsertUnconditional.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedFormulaBoundAllCarrierBoundary.
Import PABoundedRawCodedDynamicContextTruthSelector.
Import PABoundedRawCodedAssignmentUniversalDefinednessProofCompilation.
Import PABoundedRawCodedContextMembershipTransferPA.
Import
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectBodyShell.
Import
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectTraversalLeaf.
Import
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsWitnessShapes.
Import
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsPointwise.
Import
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsGrowingLaw.

(** The direct-template prefix is in the same literal order as
    [rawCoqRestrictedPANativeAxiomContextTruthRowContext]. *)
Definition coqRestrictedPANativeAxiomRowsGrowingRowPrefix :
    TemplateContext :=
  [coqRestrictedPANativeAxiomRowsAdequateContextTemplate;
   coqRestrictedPANativeAxiomRowsBoundedContextTemplate;
   coqRestrictedPANativeAxiomRowsWitnessContextTemplate;
   coqRestrictedPANativeAxiomRowsFieldTemplate].

(** Insert a finite direct-template prefix above an existing local proof.
    This small local form avoids importing any rule-specific compiler: only
    uniform atomic adequacy of the direct translation is needed. *)
Lemma raw_coqRestrictedPANativeAxiomRows_directTemplatePrefix : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    baseContext prefix conclusion root,
  RawContextListRealizable M baseContext ->
  RawCodedPALocalProofOf M baseContext conclusion root ->
  exists prefixedRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        baseContext prefix)
      conclusion prefixedRoot.
Proof.
  intros M hPA inputs baseContext prefix.
  induction prefix as [| head tail ih];
    intros conclusion root hbase hproof.
  - cbn [rawTemplateContextCodeOnTail].
    exists root. exact hproof.
  - cbn [rawTemplateContextCodeOnTail].
    destruct (ih conclusion root hbase hproof)
      as [tailRoot htailProof].
    apply (raw_codedPALocalProof_adequateConsTransplant M hPA
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        baseContext tail)
      (rawDirectTemplateFormula inputs head)
      conclusion tailRoot).
    + exact (rawDirectTemplateFormula_atomically_adequate
        M hPA inputs head).
    + exact (raw_templateContextOnTail_realizable
        M hPA
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        baseContext tail hbase).
    + exact htailProof.
Qed.

(** Exact carrier identifications needed after the two graph-side binder
    shifts.  Both equalities are indexed by the same direct inputs and the
    same dependent selectors. *)
Record RawCoqRestrictedPANativeAxiomRowsGrowingIdentificationOn
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (parameters : RawCodedTemplateNumeralParameters M)
    (nextGlobalSigma shiftedAxiomSoundness : M)
    (sigmaApplicationSelector :
      RawCodedTernaryApplicationSelector M nextGlobalSigma)
    (contextApplicationSelector :
      RawCodedTernaryApplicationSelector M
        (rawDynamicContextAllSigmaCode sigmaApplicationSelector)) : Prop := {
  rawCoqRestrictedPANativeAxiomRowsGrowing_field_identification :
    rawDirectTemplateFormula inputs
      coqRestrictedPANativeAxiomRowsFieldTemplate =
    shiftedAxiomSoundness;
  rawCoqRestrictedPANativeAxiomRowsGrowing_target_identification :
    rawDirectTemplateFormula inputs
      coqRestrictedPANativeAxiomRowsTargetTemplate =
    rawCoqRestrictedPANativeAxiomContextSelectedLeafCode
      M parameters nextGlobalSigma sigmaApplicationSelector
      contextApplicationSelector
}.

Arguments RawCoqRestrictedPANativeAxiomRowsGrowingIdentificationOn
  M inputs parameters nextGlobalSigma shiftedAxiomSoundness
    sigmaApplicationSelector contextApplicationSelector : clear implicits.

(** With the field equation exposed, compiling the four template heads is
    definitionally the literal row context consumed by the traversal shell. *)
Lemma raw_coqRestrictedPANativeAxiomRowsGrowingRowPrefix_code : forall
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    shiftedAxiomSoundness tail,
  rawDirectTemplateFormula inputs
      coqRestrictedPANativeAxiomRowsFieldTemplate =
    shiftedAxiomSoundness ->
  rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      tail coqRestrictedPANativeAxiomRowsGrowingRowPrefix =
  rawCoqRestrictedPANativeAxiomContextTruthRowContext
      M inputs shiftedAxiomSoundness tail.
Proof.
  intros M hPA inputs shiftedAxiomSoundness tail hfield.
  unfold coqRestrictedPANativeAxiomRowsGrowingRowPrefix,
    rawCoqRestrictedPANativeAxiomContextTruthRowContext,
    rawCoqRestrictedPANativeAxiomContextAdequacyCode,
    rawCoqRestrictedPANativeAxiomContextBoundedCode,
    rawCoqRestrictedPANativeAxiomContextWitnessCode.
  cbn [rawTemplateContextCodeOnTail].
  change (rawTemplateFormula
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    coqRestrictedPANativeAxiomRowsFieldTemplate =
    shiftedAxiomSoundness) in hfield.
  now rewrite hfield.
Qed.

(** Honest growing replacement for the old fixed-tail synchronized-row
    compiler.  The returned prefix simultaneously extends the witness list
    and context; the inclusion conjunct records weakening from the caller's
    original tail. *)
Definition RawCoqRestrictedPANativeAxiomContextTruthGrowingRowsCompiler
    (M : RawPAModel) : Prop :=
  forall (parameters : RawCodedTemplateNumeralParameters M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    nextGlobalSigma
    (sigmaApplicationSelector :
      RawCodedTernaryApplicationSelector M nextGlobalSigma)
    (contextApplicationSelector :
      RawCodedTernaryApplicationSelector M
        (rawDynamicContextAllSigmaCode sigmaApplicationSelector))
    shiftedAxiomSoundness baseWitnessList baseTail,
  RawCoqRestrictedPANativeAxiomRowsGrowingIdentificationOn
    M inputs parameters nextGlobalSigma shiftedAxiomSoundness
    sigmaApplicationSelector contextApplicationSelector ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseTail ->
  exists (prefix : StandardPAAxiomWitnessPrefix) (leafRoot : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode
        M prefix baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseTail) /\
    RawContextListIncluded M baseTail
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseTail) /\
    RawCodedPALocalProofOf M
      (rawCoqRestrictedPANativeAxiomContextTruthRowContext
        M inputs shiftedAxiomSoundness
        (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseTail))
      (rawCoqRestrictedPANativeAxiomContextSelectedLeafCode
        M parameters nextGlobalSigma sigmaApplicationSelector
        contextApplicationSelector)
      leafRoot.

Arguments RawCoqRestrictedPANativeAxiomContextTruthGrowingRowsCompiler
  M : clear implicits.

(** The growing compiler is unconditional once the two exact carrier code
    identifications are supplied. *)
Theorem
    raw_coqRestrictedPANativeAxiomContextTruthGrowingRowsCompiler_compiled :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawCoqRestrictedPANativeAxiomContextTruthGrowingRowsCompiler M.
Proof.
  intros M hPA parameters inputs nextGlobalSigma
    sigmaApplicationSelector contextApplicationSelector
    shiftedAxiomSoundness baseWitnessList baseTail
    hidentification hbase.
  destruct hidentification as [hfield htarget].
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).

  (** First helper: universal transfer, compiled on the caller's witnessed
      tail. *)
  destruct
    (raw_codedTemplatePALocalProofOf_contextListMemberTransferUniversal_on_tail
      M hPA translation
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      baseWitnessList baseTail hbase)
    as (transferPrefix & transferRoot & htransferWitnessed & htransfer).

  (** Second helper: universal assignment definedness, compiled after the
      transfer prefix. *)
  destruct
    (raw_codedTemplatePALocalProofOf_of_BProv_on_witnessed_tail
      M hPA translation
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      (rawStandardPAAxiomWitnessPrefixWitnessListCode
        M transferPrefix baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode
        M transferPrefix baseTail)
      codedAssignmentUniversalDefinednessFormula
      htransferWitnessed
      PA_proves_codedAssignmentUniversalDefinednessFormula)
    as (definedPrefix & definedRoot & hdefinedWitnessed & hdefined).

  pose proof
    (raw_codedPAAxiomWitnessContext_context_realizable M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode
        M transferPrefix baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode
        M transferPrefix baseTail)
      htransferWitnessed) as htransferRealizable.

  (** The second helper prefix changes the local context, so the transfer
      root must be rebuilt through exactly that prefix. *)
  destruct
    (raw_codedPALocalProofOf_standardPAAxiomWitnessPrefix
      M hPA definedPrefix
      (rawStandardPAAxiomWitnessPrefixContextCode
        M transferPrefix baseTail)
      (rawTemplateFormula translation
        coqRestrictedPANativeAxiomRowsTransferSourceTemplate)
      transferRoot htransferRealizable htransfer)
    as [finalTransferRoot hfinalTransfer].

  set (finalWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M definedPrefix
      (rawStandardPAAxiomWitnessPrefixWitnessListCode
        M transferPrefix baseWitnessList)).
  set (finalTail :=
    rawStandardPAAxiomWitnessPrefixContextCode M definedPrefix
      (rawStandardPAAxiomWitnessPrefixContextCode
        M transferPrefix baseTail)).
  change (RawCodedPAAxiomWitnessContext M finalWitnessList finalTail)
    in hdefinedWitnessed.
  change (RawCodedPALocalProofOf M finalTail
    (rawTemplateFormula translation
      coqRestrictedPANativeAxiomRowsDefinedUniversalTemplate)
    definedRoot) in hdefined.
  change (RawCodedPALocalProofOf M finalTail
    (rawTemplateFormula translation
      coqRestrictedPANativeAxiomRowsTransferSourceTemplate)
    finalTransferRoot) in hfinalTransfer.

  pose proof
    (raw_codedPAAxiomWitnessContext_context_realizable M
      finalWitnessList finalTail hdefinedWitnessed) as hfinalRealizable.

  (** Compile the empty-context logical law over the fully accumulated
      witnessed tail.  Its derivation equations normalize the compiler's
      generic context and conclusion projections. *)
  pose proof
    coqRestrictedPANativeAxiomRowsGrowingLawRoot_derives as hlawDerives.
  destruct hlawDerives as [hlawValid [hlawContext hlawConclusion]].
  pose proof
    (raw_templateProofOnPAAxiomContext_localProof
      M hPA translation finalWitnessList finalTail
      coqRestrictedPANativeAxiomRowsGrowingLawRoot
      hdefinedWitnessed hlawValid) as hlawTail.
  rewrite hlawContext in hlawTail.
  rewrite hlawConclusion in hlawTail.
  cbn [rawTemplateContextCodeOnTail] in hlawTail.

  (** Put the logical law and both PA helpers under the same four direct row
      assumptions. *)
  destruct
    (raw_coqRestrictedPANativeAxiomRows_directTemplatePrefix
      M hPA inputs finalTail
      coqRestrictedPANativeAxiomRowsGrowingRowPrefix
      (rawTemplateFormula translation
        coqRestrictedPANativeAxiomRowsGrowingLawTemplate)
      (rawTemplateProofCodeOnTail translation finalTail
        coqRestrictedPANativeAxiomRowsGrowingLawRoot)
      hfinalRealizable hlawTail)
    as [rowLawRoot hrowLaw].
  destruct
    (raw_coqRestrictedPANativeAxiomRows_directTemplatePrefix
      M hPA inputs finalTail
      coqRestrictedPANativeAxiomRowsGrowingRowPrefix
      (rawTemplateFormula translation
        coqRestrictedPANativeAxiomRowsDefinedUniversalTemplate)
      definedRoot hfinalRealizable hdefined)
    as [rowDefinedRoot hrowDefined].
  destruct
    (raw_coqRestrictedPANativeAxiomRows_directTemplatePrefix
      M hPA inputs finalTail
      coqRestrictedPANativeAxiomRowsGrowingRowPrefix
      (rawTemplateFormula translation
        coqRestrictedPANativeAxiomRowsTransferSourceTemplate)
      finalTransferRoot hfinalRealizable hfinalTransfer)
    as [rowTransferRoot hrowTransfer].

  assert (hrowCode :
      rawTemplateContextCodeOnTail translation finalTail
        coqRestrictedPANativeAxiomRowsGrowingRowPrefix =
      rawCoqRestrictedPANativeAxiomContextTruthRowContext
        M inputs shiftedAxiomSoundness finalTail).
  {
    unfold translation.
    exact
      (raw_coqRestrictedPANativeAxiomRowsGrowingRowPrefix_code
        M hPA inputs shiftedAxiomSoundness finalTail hfield).
  }
  unfold translation in hrowCode.
  rewrite hrowCode in hrowLaw, hrowDefined, hrowTransfer.

  (** The remaining four sources are literal assumption leaves in the row
      context. *)
  pose proof
    (raw_coqRestrictedPANativeAxiomContextTruthRowProofInputs_exists
      M hPA inputs shiftedAxiomSoundness finalTail hfinalRealizable)
    as hrowInputs.
  destruct hrowInputs as
    [hwitnessRoot hboundedRoot hadequacyRoot hfieldRoot].
  destruct hwitnessRoot as [witnessRoot hwitness].
  destruct hboundedRoot as [boundedRoot hbounded].
  destruct hadequacyRoot as [adequacyRoot hadequacy].
  destruct hfieldRoot as [fieldRoot hfieldProof].

  change (RawCodedPALocalProofOf M
    (rawCoqRestrictedPANativeAxiomContextTruthRowContext
      M inputs shiftedAxiomSoundness finalTail)
    (rawTemplateFormula translation
      coqRestrictedPANativeAxiomRowsWitnessContextTemplate)
    witnessRoot) in hwitness.
  change (RawCodedPALocalProofOf M
    (rawCoqRestrictedPANativeAxiomContextTruthRowContext
      M inputs shiftedAxiomSoundness finalTail)
    (rawTemplateFormula translation
      coqRestrictedPANativeAxiomRowsBoundedContextTemplate)
    boundedRoot) in hbounded.
  change (RawCodedPALocalProofOf M
    (rawCoqRestrictedPANativeAxiomContextTruthRowContext
      M inputs shiftedAxiomSoundness finalTail)
    (rawTemplateFormula translation
      coqRestrictedPANativeAxiomRowsAdequateContextTemplate)
    adequacyRoot) in hadequacy.
  assert (hfieldDirect : RawCodedPALocalProofOf M
      (rawCoqRestrictedPANativeAxiomContextTruthRowContext
        M inputs shiftedAxiomSoundness finalTail)
      (rawTemplateFormula translation
        coqRestrictedPANativeAxiomRowsFieldTemplate)
      fieldRoot).
  {
    change (RawCodedPALocalProofOf M
      (rawCoqRestrictedPANativeAxiomContextTruthRowContext
        M inputs shiftedAxiomSoundness finalTail)
      (rawDirectTemplateFormula inputs
        coqRestrictedPANativeAxiomRowsFieldTemplate)
      fieldRoot).
    rewrite hfield.
    exact hfieldProof.
  }

  (** Expose the six implication constructors of the compiled law, then
      consume the helper roots and row assumptions in declaration order. *)
  unfold coqRestrictedPANativeAxiomRowsGrowingLawTemplate in hrowLaw.
  rewrite !rawTemplateFormula_imp in hrowLaw.
  pose proof
    (raw_codedPALocalProofOf_impE M hPA
      (rawCoqRestrictedPANativeAxiomContextTruthRowContext
        M inputs shiftedAxiomSoundness finalTail)
      _ _ rowLawRoot rowDefinedRoot hrowLaw hrowDefined)
    as hafterDefined.
  pose proof
    (raw_codedPALocalProofOf_impE M hPA
      (rawCoqRestrictedPANativeAxiomContextTruthRowContext
        M inputs shiftedAxiomSoundness finalTail)
      _ _ _ rowTransferRoot hafterDefined hrowTransfer)
    as hafterTransfer.
  pose proof
    (raw_codedPALocalProofOf_impE M hPA
      (rawCoqRestrictedPANativeAxiomContextTruthRowContext
        M inputs shiftedAxiomSoundness finalTail)
      _ _ _ fieldRoot hafterTransfer hfieldDirect)
    as hafterField.
  pose proof
    (raw_codedPALocalProofOf_impE M hPA
      (rawCoqRestrictedPANativeAxiomContextTruthRowContext
        M inputs shiftedAxiomSoundness finalTail)
      _ _ _ adequacyRoot hafterField hadequacy)
    as hafterAdequacy.
  pose proof
    (raw_codedPALocalProofOf_impE M hPA
      (rawCoqRestrictedPANativeAxiomContextTruthRowContext
        M inputs shiftedAxiomSoundness finalTail)
      _ _ _ boundedRoot hafterAdequacy hbounded)
    as hafterBounded.
  pose proof
    (raw_codedPALocalProofOf_impE M hPA
      (rawCoqRestrictedPANativeAxiomContextTruthRowContext
        M inputs shiftedAxiomSoundness finalTail)
      _ _ _ witnessRoot hafterBounded hwitness)
    as htargetProof.
  change (rawTemplateFormula translation
    coqRestrictedPANativeAxiomRowsTargetTemplate =
    rawCoqRestrictedPANativeAxiomContextSelectedLeafCode
      M parameters nextGlobalSigma sigmaApplicationSelector
      contextApplicationSelector) in htarget.
  rewrite htarget in htargetProof.

  exists (definedPrefix ++ transferPrefix).
  eexists.
  split.
  - rewrite rawStandardPAAxiomWitnessPrefixWitnessListCode_app.
    rewrite rawStandardPAAxiomWitnessPrefixContextCode_app.
    exact hdefinedWitnessed.
  - split.
    + exact
        (raw_standardPAAxiomWitnessPrefixContextCode_target_included
          M hPA (definedPrefix ++ transferPrefix) baseTail).
    + rewrite rawStandardPAAxiomWitnessPrefixContextCode_app.
      exact htargetProof.
Qed.

End
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsGrowingCarrier.
