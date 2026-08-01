(**
  The represented atomic-and-domain core for a direct implication child.

  Guarded predecessor exclusivity needs admissibility only after two facts
  have become available: the current formula is an implication with the
  displayed children, and the synchronized state formula is one of those
  children.  This module combines the separately proved atomic-adequacy and
  carrier-domain inheritance laws into exactly that branch-local interface.

  Assignment coverage is intentionally absent.  The predecessor pipeline
  already compiles it for the common child from the restricted proof bound;
  keeping it separate lets this theorem state the strongest constructor-only
  result and avoids duplicating the assignment compiler.
*)

From Stdlib Require Import List Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness
  RawCodedSyntaxConstructors
  RawCodedFixedLevelTruthTotality
  RawCodedDynamicTruthFixedSyntaxFragments
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedFormulaImpChildrenAtomicAdequacyProofCompilation
  RawCodedDynamicTruthImpChildrenDomainProofCompilation.

Module
  PABoundedRawCodedDynamicTruthImpDirectChildAdmissibilityProofCompilation.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedDynamicTruthFixedSyntaxFragments.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
Import
  PABoundedRawCodedFormulaImpChildrenAtomicAdequacyProofCompilation.
Import PABoundedRawCodedDynamicTruthImpChildrenDomainProofCompilation.

Definition RawDynamicTruthImpDirectChildAdmissibilityCoreAt
    (M : RawPAModel) (level parent left right child : M) : Prop :=
  RawCodedFormulaAtomicallyAdequate M child /\
  (RawDynamicTruthSigmaRecordDomain M level child \/
   RawDynamicTruthPiRecordDomain M level child).

Arguments RawDynamicTruthImpDirectChildAdmissibilityCoreAt
  M level parent left right child : clear implicits.

Lemma raw_dynamicTruthImpDirectChild_admissibility_core : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall level parent left right child,
  RawCodedFormulaAtomicallyAdequate M parent ->
  (RawDynamicTruthSigmaRecordDomain M level parent \/
   RawDynamicTruthPiRecordDomain M level parent) ->
  parent = rawFormulaImpCode M left right ->
  (child = left \/ child = right) ->
  RawDynamicTruthImpDirectChildAdmissibilityCoreAt M
    level parent left right child.
Proof.
  intros M hPA level parent left right child
    hatomic hdomain hshape hdirect.
  pose proof (raw_codedFormulaAtomicallyAdequate_imp_children M hPA
    parent left right hatomic hshape) as [hleftAtomic hrightAtomic].
  pose proof (raw_dynamicTruthRecordDomain_imp_children M hPA
    level parent left right hshape hdomain) as
    [hleftDomain hrightDomain].
  destruct hdirect as [hchild | hchild]; subst child.
  - split; assumption.
  - split; assumption.
Qed.

(** Binder order is carrier level, parent, left, right, common child. *)
Definition dynamicTruthImpDirectChildAdmissibilityCoreBodyFormula : formula :=
  pImp
    (codedFormulaAtomicallyAdequateTermAt (tVar 3))
    (pImp
      (pOr
        (dynamicTruthSigmaRecordDomainTermAt (tVar 4) (tVar 3))
        (dynamicTruthPiRecordDomainTermAt (tVar 4) (tVar 3)))
      (pImp
        (formulaImpCodeTermAt (tVar 3) (tVar 2) (tVar 1))
        (pImp
          (pOr
            (pEq (tVar 0) (tVar 2))
            (pEq (tVar 0) (tVar 1)))
          (pAnd
            (codedFormulaAtomicallyAdequateTermAt (tVar 0))
            (pOr
              (dynamicTruthSigmaRecordDomainTermAt
                (tVar 4) (tVar 0))
              (dynamicTruthPiRecordDomainTermAt
                (tVar 4) (tVar 0))))))).

Definition dynamicTruthImpDirectChildAdmissibilityCoreFormula : formula :=
  pAll (pAll (pAll (pAll (pAll
    dynamicTruthImpDirectChildAdmissibilityCoreBodyFormula)))).

Lemma raw_sat_dynamicTruthImpDirectChildAdmissibilityCoreFormula_iff :
    forall (M : RawPAModel) (e : nat -> M),
  raw_formula_sat M e
    dynamicTruthImpDirectChildAdmissibilityCoreFormula <->
  forall level parent left right child : M,
    RawCodedFormulaAtomicallyAdequate M parent ->
    (RawDynamicTruthSigmaRecordDomain M level parent \/
     RawDynamicTruthPiRecordDomain M level parent) ->
    parent = rawFormulaImpCode M left right ->
    (child = left \/ child = right) ->
    RawDynamicTruthImpDirectChildAdmissibilityCoreAt M
      level parent left right child.
Proof.
  intros M e.
  unfold dynamicTruthImpDirectChildAdmissibilityCoreFormula,
    dynamicTruthImpDirectChildAdmissibilityCoreBodyFormula,
    RawDynamicTruthImpDirectChildAdmissibilityCoreAt.
  cbn [raw_formula_sat].
  repeat setoid_rewrite raw_sat_codedFormulaAtomicallyAdequateTermAt_iff.
  repeat setoid_rewrite raw_sat_dynamicTruthSigmaRecordDomainTermAt_iff.
  repeat setoid_rewrite raw_sat_dynamicTruthPiRecordDomainTermAt_iff.
  setoid_rewrite raw_sat_formulaImpCodeTermAt_iff.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma dynamicTruthImpDirectChildAdmissibilityCoreFormula_sentence :
  Formula.Sentence dynamicTruthImpDirectChildAdmissibilityCoreFormula.
Proof.
  intros k hfree.
  unfold dynamicTruthImpDirectChildAdmissibilityCoreFormula,
    dynamicTruthImpDirectChildAdmissibilityCoreBodyFormula,
    codedFormulaAtomicallyAdequateTermAt,
    dynamicTruthSigmaRecordDomainTermAt,
    dynamicTruthPiRecordDomainTermAt in hfree.
  cbn in hfree. lia.
Qed.

Theorem dynamicTruthImpDirectChildAdmissibilityCoreFormula_raw_valid :
    forall (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e
    dynamicTruthImpDirectChildAdmissibilityCoreFormula.
Proof.
  intros M hPA e.
  apply (proj2
    (raw_sat_dynamicTruthImpDirectChildAdmissibilityCoreFormula_iff M e)).
  exact (raw_dynamicTruthImpDirectChild_admissibility_core M hPA).
Qed.

Theorem PA_proves_dynamicTruthImpDirectChildAdmissibilityCoreFormula :
  Formula.BProv Formula.Ax_s []
    dynamicTruthImpDirectChildAdmissibilityCoreFormula.
Proof.
  apply PA_BProv_of_raw_valid.
  - exact dynamicTruthImpDirectChildAdmissibilityCoreFormula_sentence.
  - exact dynamicTruthImpDirectChildAdmissibilityCoreFormula_raw_valid.
Qed.

Definition coqDynamicTruthImpDirectChildAdmissibilityCoreInstanceTemplate
    (level parent left right child : TemplateTerm) : TemplateFormula :=
  templateUniversalOpenManyOrBot
    (embedPAFormula dynamicTruthImpDirectChildAdmissibilityCoreFormula)
    [level; parent; left; right; child].

Lemma coqDynamicTruthImpDirectChildAdmissibilityCoreInstanceTemplate_open :
    forall level parent left right child,
  templateUniversalOpenMany
    (embedPAFormula dynamicTruthImpDirectChildAdmissibilityCoreFormula)
    [level; parent; left; right; child] =
  Some (coqDynamicTruthImpDirectChildAdmissibilityCoreInstanceTemplate
    level parent left right child).
Proof.
  intros level parent left right child.
  unfold coqDynamicTruthImpDirectChildAdmissibilityCoreInstanceTemplate,
    templateUniversalOpenManyOrBot,
    dynamicTruthImpDirectChildAdmissibilityCoreFormula.
  cbn [templateUniversalOpenMany embedPAFormula
    templateFormulaOpen templateFormulaSubst].
  reflexivity.
Qed.

Definition coqDynamicTruthImpDirectChildAtomicPremiseTemplate
    level parent left right child :=
  templateImpAntecedent
    (coqDynamicTruthImpDirectChildAdmissibilityCoreInstanceTemplate
      level parent left right child).

Definition coqDynamicTruthImpDirectChildDomainPremiseTemplate
    level parent left right child :=
  templateImpAntecedent (templateImpConsequent
    (coqDynamicTruthImpDirectChildAdmissibilityCoreInstanceTemplate
      level parent left right child)).

Definition coqDynamicTruthImpDirectChildShapePremiseTemplate
    level parent left right child :=
  templateImpAntecedent (templateImpConsequent (templateImpConsequent
    (coqDynamicTruthImpDirectChildAdmissibilityCoreInstanceTemplate
      level parent left right child))).

Definition coqDynamicTruthImpDirectChildGuardPremiseTemplate
    level parent left right child :=
  templateImpAntecedent (templateImpConsequent (templateImpConsequent
    (templateImpConsequent
      (coqDynamicTruthImpDirectChildAdmissibilityCoreInstanceTemplate
        level parent left right child)))).

Definition coqDynamicTruthImpDirectChildAdmissibilityCoreConclusionTemplate
    level parent left right child :=
  templateImpConsequent (templateImpConsequent (templateImpConsequent
    (templateImpConsequent
      (coqDynamicTruthImpDirectChildAdmissibilityCoreInstanceTemplate
        level parent left right child)))).

Lemma
    coqDynamicTruthImpDirectChildAdmissibilityCoreInstanceTemplate_imp4_shape :
  forall level parent left right child,
  coqDynamicTruthImpDirectChildAdmissibilityCoreInstanceTemplate
      level parent left right child =
  tfImp
    (coqDynamicTruthImpDirectChildAtomicPremiseTemplate
      level parent left right child)
    (tfImp
      (coqDynamicTruthImpDirectChildDomainPremiseTemplate
        level parent left right child)
      (tfImp
        (coqDynamicTruthImpDirectChildShapePremiseTemplate
          level parent left right child)
        (tfImp
          (coqDynamicTruthImpDirectChildGuardPremiseTemplate
            level parent left right child)
          (coqDynamicTruthImpDirectChildAdmissibilityCoreConclusionTemplate
            level parent left right child)))).
Proof.
  intros level parent left right child.
  unfold coqDynamicTruthImpDirectChildAtomicPremiseTemplate,
    coqDynamicTruthImpDirectChildDomainPremiseTemplate,
    coqDynamicTruthImpDirectChildShapePremiseTemplate,
    coqDynamicTruthImpDirectChildGuardPremiseTemplate,
    coqDynamicTruthImpDirectChildAdmissibilityCoreConclusionTemplate,
    coqDynamicTruthImpDirectChildAdmissibilityCoreInstanceTemplate,
    templateUniversalOpenManyOrBot,
    dynamicTruthImpDirectChildAdmissibilityCoreFormula,
    dynamicTruthImpDirectChildAdmissibilityCoreBodyFormula.
  cbn [templateUniversalOpenMany embedPAFormula
    templateFormulaOpen templateFormulaSubst
    templateImpAntecedent templateImpConsequent].
  reflexivity.
Qed.

Theorem
    raw_codedPALocalProofOf_dynamicTruthImpDirectChildAdmissibilityCore_instance_on_witnessed_tail :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext level parent left right child,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) proofRoot,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext)
      (rawTemplateFormula translation
        (coqDynamicTruthImpDirectChildAdmissibilityCoreInstanceTemplate
          level parent left right child)) proofRoot.
Proof.
  intros M hPA translation hagreement baseWitnessList baseContext
    level parent left right child hbase.
  exact
    (raw_codedTemplatePALocalProofOf_of_BProv_open_many_on_witnessed_tail
      M hPA translation hagreement baseWitnessList baseContext
      dynamicTruthImpDirectChildAdmissibilityCoreFormula
      [level; parent; left; right; child]
      (coqDynamicTruthImpDirectChildAdmissibilityCoreInstanceTemplate
        level parent left right child)
      hbase PA_proves_dynamicTruthImpDirectChildAdmissibilityCoreFormula
      (coqDynamicTruthImpDirectChildAdmissibilityCoreInstanceTemplate_open
        level parent left right child)).
Qed.

Theorem
    raw_codedPALocalProofOf_dynamicTruthImpDirectChildAdmissibilityCore_instance_on_witnessed_tail_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext prefix level parent left right child,
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) proofRoot,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext) prefix)
      (rawTemplateFormula translation
        (coqDynamicTruthImpDirectChildAdmissibilityCoreInstanceTemplate
          level parent left right child)) proofRoot.
Proof.
  intros M hPA translation hagreement baseWitnessList baseContext prefix
    level parent left right child hprefix hbase.
  destruct
    (raw_codedPALocalProofOf_dynamicTruthImpDirectChildAdmissibilityCore_instance_on_witnessed_tail
      M hPA translation hagreement baseWitnessList baseContext
      level parent left right child hbase)
    as (witnesses & sourceRoot & hextended & hsource).
  set (extendedWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses baseWitnessList).
  set (extendedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses baseContext).
  destruct (raw_codedPALocalProof_templatePrefix M hPA translation
    extendedContext prefix
    (rawTemplateFormula translation
      (coqDynamicTruthImpDirectChildAdmissibilityCoreInstanceTemplate
        level parent left right child)) sourceRoot
    (raw_codedPAAxiomWitnessPrefix_context_realizable_of_witnessed M
      extendedWitnessList extendedContext hextended)
    hprefix hsource) as [proofRoot hproof].
  exists witnesses, proofRoot. split; assumption.
Qed.

(** Generic synchronization kernel for a four-premise represented law.
    The first premise is eliminated directly and the remaining implication
    spine is delegated to the existing three-premise composition lemma. *)
Theorem
    raw_codedPALocalProofOf_templateImp4_of_roots_on_standard_witnessed_extension_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext prefix witnesses
      source first second third fourth conclusion
      implicationRoot firstRoot secondRoot thirdRoot fourthRoot,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPAAxiomWitnessContext M
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses baseWitnessList)
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses baseContext) ->
  source = tfImp first
    (tfImp second (tfImp third (tfImp fourth conclusion))) ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) prefix)
    (rawTemplateFormula translation source) implicationRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation first) firstRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation second) secondRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation third) thirdRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation fourth) fourthRoot ->
  exists resultRoot,
    RawContextListIncluded M baseContext
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext) prefix)
      (rawTemplateFormula translation conclusion) resultRoot.
Proof.
  intros M hPA translation hagreement baseWitnessList baseContext prefix
    witnesses source first second third fourth conclusion
    implicationRoot firstRoot secondRoot thirdRoot fourthRoot
    hbase hextended hsource himplication
    hfirst hsecond hthird hfourth.
  set (extendedWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses baseWitnessList).
  set (extendedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses baseContext).
  assert (hincluded : RawContextListIncluded M baseContext extendedContext).
  {
    unfold extendedContext.
    exact (raw_standardPAAxiomWitnessPrefixContextCode_target_included
      M hPA witnesses baseContext).
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      extendedWitnessList extendedContext prefix
      (rawTemplateFormula translation first)
      firstRoot hbase hextended hincluded hfirst)
    as [transportedFirstRoot htransportedFirst].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      extendedWitnessList extendedContext prefix
      (rawTemplateFormula translation second)
      secondRoot hbase hextended hincluded hsecond)
    as [transportedSecondRoot htransportedSecond].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      extendedWitnessList extendedContext prefix
      (rawTemplateFormula translation third)
      thirdRoot hbase hextended hincluded hthird)
    as [transportedThirdRoot htransportedThird].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      extendedWitnessList extendedContext prefix
      (rawTemplateFormula translation fourth)
      fourthRoot hbase hextended hincluded hfourth)
    as [transportedFourthRoot htransportedFourth].
  rewrite hsource in himplication.
  rewrite !rawTemplateFormula_imp in himplication.
  pose proof (raw_codedPALocalProofOf_impE M hPA
    (rawTemplateContextCodeOnTail translation extendedContext prefix)
    (rawTemplateFormula translation first)
    (rawFormulaImpCode M
      (rawTemplateFormula translation second)
      (rawFormulaImpCode M
        (rawTemplateFormula translation third)
        (rawFormulaImpCode M
          (rawTemplateFormula translation fourth)
          (rawTemplateFormula translation conclusion))))
    implicationRoot transportedFirstRoot
    himplication htransportedFirst) as hafterFirst.
  lazymatch type of hafterFirst with
  | RawCodedPALocalProofOf _ _ _ ?afterFirstRoot =>
      destruct (raw_codedPALocalProofOf_impE3 M hPA
        (rawTemplateContextCodeOnTail translation extendedContext prefix)
        (rawTemplateFormula translation second)
        (rawTemplateFormula translation third)
        (rawTemplateFormula translation fourth)
        (rawTemplateFormula translation conclusion)
        afterFirstRoot transportedSecondRoot transportedThirdRoot
        transportedFourthRoot hafterFirst htransportedSecond
        htransportedThird htransportedFourth) as [resultRoot hresult];
      exists resultRoot; split; [exact hincluded | exact hresult]
  end.
Qed.

(** Full context-safe application of the direct-child core. *)
Theorem
    raw_codedPALocalProofOf_dynamicTruthImpDirectChildAdmissibilityCore_of_roots_on_witnessed_extension_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext prefix level parent left right child
      atomicRoot domainRoot shapeRoot guardRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqDynamicTruthImpDirectChildAtomicPremiseTemplate
        level parent left right child)) atomicRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqDynamicTruthImpDirectChildDomainPremiseTemplate
        level parent left right child)) domainRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqDynamicTruthImpDirectChildShapePremiseTemplate
        level parent left right child)) shapeRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqDynamicTruthImpDirectChildGuardPremiseTemplate
        level parent left right child)) guardRoot ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) resultRoot,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawContextListIncluded M baseContext
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext) prefix)
      (rawTemplateFormula translation
        (coqDynamicTruthImpDirectChildAdmissibilityCoreConclusionTemplate
          level parent left right child)) resultRoot.
Proof.
  intros M hPA translation hagreement baseWitnessList baseContext prefix
    level parent left right child atomicRoot domainRoot shapeRoot guardRoot
    hprefix hbase hatomic hdomain hshape hguard.
  destruct
    (raw_codedPALocalProofOf_dynamicTruthImpDirectChildAdmissibilityCore_instance_on_witnessed_tail_under_prefix
      M hPA translation hagreement baseWitnessList baseContext prefix
      level parent left right child hprefix hbase)
    as (witnesses & implicationRoot & hextended & himplication).
  destruct
    (raw_codedPALocalProofOf_templateImp4_of_roots_on_standard_witnessed_extension_under_prefix
      M hPA translation hagreement baseWitnessList baseContext prefix
      witnesses
      (coqDynamicTruthImpDirectChildAdmissibilityCoreInstanceTemplate
        level parent left right child)
      (coqDynamicTruthImpDirectChildAtomicPremiseTemplate
        level parent left right child)
      (coqDynamicTruthImpDirectChildDomainPremiseTemplate
        level parent left right child)
      (coqDynamicTruthImpDirectChildShapePremiseTemplate
        level parent left right child)
      (coqDynamicTruthImpDirectChildGuardPremiseTemplate
        level parent left right child)
      (coqDynamicTruthImpDirectChildAdmissibilityCoreConclusionTemplate
        level parent left right child)
      implicationRoot atomicRoot domainRoot shapeRoot guardRoot
      hbase hextended
      (coqDynamicTruthImpDirectChildAdmissibilityCoreInstanceTemplate_imp4_shape
        level parent left right child)
      himplication hatomic hdomain hshape hguard)
    as (resultRoot & hincluded & hresult).
  exists witnesses, resultRoot.
  split; [exact hextended |].
  split; [exact hincluded | exact hresult].
Qed.

End
  PABoundedRawCodedDynamicTruthImpDirectChildAdmissibilityProofCompilation.
