(**
  Proof compilation for the native adjacent-level coherence field.

  The carrier polynomial has the literal shape

    All^3 (admissible ->
      ((sigmaDomain -> ((currentSigma -> nextSigma) /\
                        (nextSigma -> currentSigma))) /\
       (piDomain -> ((currentPi -> nextPi) /\
                     (nextPi -> currentPi))))).

  All connectives in this shell are compiled below with raw natural-
  deduction constructors.  The remaining dynamic obligation consists of
  four directional leaves, grouped into the two polarity-specific packages
  [RawDynamicTruthNativeCrossLevelSigmaLocalRootsAt] and
  [RawDynamicTruthNativeCrossLevelPiLocalRootsAt].  Their compiler is indexed
  by the adequate orbit and the literal successor/substitution/application
  trace.  It mentions neither the final field code nor an ordinary PA proof
  certificate and assumes no semantic validity or completeness principle.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedNumeralTermCode
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedRestrictedProofStandardAdequacy
  RawCodedRestrictedPAProof
  RawCodedContextShift
  RawCodedProofEndpoints
  RawCodedProofRuleCoverage
  RawCodedPAProvability
  RawCodedPALocalProofExistential
  RawCodedProofImpIConstructor
  RawCodedProofAndIConstructor
  RawCodedProofAllIConstructor
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofAndIntroduction
  RawCodedDynamicTruthNativeCrossLevelPositiveGraph.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthNativeCrossLevelProofCompilation.

Import PA.
Import PAListCode.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedRestrictedProofStandardAdequacy.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedProofAndIConstructor.
Import PABoundedRawCodedProofAllIConstructor.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPALocalProofAndIntroduction.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelPositiveGraph.

(** ------------------------------------------------------------------
    Exact shell codes and contexts. *)

Definition rawDynamicTruthNativeCrossLevelCoherenceBodyCode
    (M : RawPAModel)
    (sigmaDomain piDomain currentSigma currentPi nextSigma nextPi : M) : M :=
  rawFormulaImpCode M
    (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain)
    (rawFormulaAndCode M
      (rawDynamicTruthNativeCrossLevelGuardedEquivalenceCode M
        sigmaDomain currentSigma nextSigma)
      (rawDynamicTruthNativeCrossLevelGuardedEquivalenceCode M
        piDomain currentPi nextPi)).

Arguments rawDynamicTruthNativeCrossLevelCoherenceBodyCode
  M sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
  : clear implicits.

Lemma rawDynamicTruthNativeCrossLevelCoherenceFieldCode_as_all3 : forall
    (M : RawPAModel)
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi,
  rawDynamicTruthNativeCrossLevelCoherenceFieldCode M
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi =
    rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthNativeCrossLevelCoherenceBodyCode M
        sigmaDomain piDomain currentSigma currentPi nextSigma nextPi).
Proof.
  reflexivity.
Qed.

Definition rawDynamicTruthNativeCrossLevelAdmissibleContext
    (M : RawPAModel) (sigmaDomain piDomain : M) : M :=
  rawListNode M
    (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain)
    (raw_zero M).

Definition rawDynamicTruthNativeCrossLevelDomainContext
    (M : RawPAModel) (sigmaDomain piDomain domain : M) : M :=
  rawListNode M domain
    (rawDynamicTruthNativeCrossLevelAdmissibleContext M
      sigmaDomain piDomain).

Definition rawDynamicTruthNativeCrossLevelDirectionalContext
    (M : RawPAModel)
    (sigmaDomain piDomain domain assumption : M) : M :=
  rawListNode M assumption
    (rawDynamicTruthNativeCrossLevelDomainContext M
      sigmaDomain piDomain domain).

Arguments rawDynamicTruthNativeCrossLevelAdmissibleContext
  M sigmaDomain piDomain : clear implicits.
Arguments rawDynamicTruthNativeCrossLevelDomainContext
  M sigmaDomain piDomain domain : clear implicits.
Arguments rawDynamicTruthNativeCrossLevelDirectionalContext
  M sigmaDomain piDomain domain assumption : clear implicits.

(**
  Sigma coherence needs one leaf in each direction.  Both leaves retain the
  outer admissibility assumption and the Sigma-domain assumption, exactly in
  the cons order required by the two surrounding implication introductions.
*)
Definition RawDynamicTruthNativeCrossLevelSigmaLocalRootsAt
    (M : RawPAModel)
    (sigmaDomain piDomain currentSigma nextSigma : M) : Prop :=
  exists currentToNextRoot nextToCurrentRoot : M,
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeCrossLevelDirectionalContext M
        sigmaDomain piDomain sigmaDomain currentSigma)
      nextSigma currentToNextRoot /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeCrossLevelDirectionalContext M
        sigmaDomain piDomain sigmaDomain nextSigma)
      currentSigma nextToCurrentRoot.

Arguments RawDynamicTruthNativeCrossLevelSigmaLocalRootsAt
  M sigmaDomain piDomain currentSigma nextSigma : clear implicits.

(** The matching two directional leaves for Pi coherence. *)
Definition RawDynamicTruthNativeCrossLevelPiLocalRootsAt
    (M : RawPAModel)
    (sigmaDomain piDomain currentPi nextPi : M) : Prop :=
  exists currentToNextRoot nextToCurrentRoot : M,
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeCrossLevelDirectionalContext M
        sigmaDomain piDomain piDomain currentPi)
      nextPi currentToNextRoot /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeCrossLevelDirectionalContext M
        sigmaDomain piDomain piDomain nextPi)
      currentPi nextToCurrentRoot.

Arguments RawDynamicTruthNativeCrossLevelPiLocalRootsAt
  M sigmaDomain piDomain currentPi nextPi : clear implicits.

(** The fully assembled matrix body, before its three universal binders. *)
Definition RawDynamicTruthNativeCrossLevelBodyLocalRootAt
    (M : RawPAModel)
    (sigmaDomain piDomain currentSigma currentPi nextSigma nextPi : M)
    : Prop :=
  exists child : M,
    RawCodedPALocalProofOf M (raw_zero M)
      (rawDynamicTruthNativeCrossLevelCoherenceBodyCode M
        sigmaDomain piDomain currentSigma currentPi nextSigma nextPi)
      child.

Arguments RawDynamicTruthNativeCrossLevelBodyLocalRootAt
  M sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
  : clear implicits.

(**
  Compile the complete propositional shell.  The four dynamic roots are used
  only as leaves; every implication discharge and conjunction introduction
  is represented by its concrete raw proof constructor.
*)
Theorem raw_dynamicTruthNativeCrossLevelBodyLocalRootAt_of_polarity_roots :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi,
  RawDynamicTruthNativeCrossLevelSigmaLocalRootsAt M
    sigmaDomain piDomain currentSigma nextSigma ->
  RawDynamicTruthNativeCrossLevelPiLocalRootsAt M
    sigmaDomain piDomain currentPi nextPi ->
  RawDynamicTruthNativeCrossLevelBodyLocalRootAt M
    sigmaDomain piDomain currentSigma currentPi nextSigma nextPi.
Proof.
  intros M hPA sigmaDomain piDomain currentSigma currentPi
    nextSigma nextPi
    (sigmaForward & sigmaBackward & hsigmaForward & hsigmaBackward)
    (piForward & piBackward & hpiForward & hpiBackward).
  pose proof (raw_codedPALocalProofOf_impI M hPA
    (rawDynamicTruthNativeCrossLevelDomainContext M
      sigmaDomain piDomain sigmaDomain)
    currentSigma nextSigma sigmaForward hsigmaForward) as hsigmaForwardImp.
  pose proof (raw_codedPALocalProofOf_impI M hPA
    (rawDynamicTruthNativeCrossLevelDomainContext M
      sigmaDomain piDomain sigmaDomain)
    nextSigma currentSigma sigmaBackward hsigmaBackward) as hsigmaBackwardImp.
  pose proof (raw_codedPALocalProofOf_andI M hPA
    (rawDynamicTruthNativeCrossLevelDomainContext M
      sigmaDomain piDomain sigmaDomain)
    (rawFormulaImpCode M currentSigma nextSigma)
    (rawFormulaImpCode M nextSigma currentSigma)
    (rawProofImpIRoot M
      (rawDynamicTruthNativeCrossLevelDomainContext M
        sigmaDomain piDomain sigmaDomain)
      currentSigma nextSigma sigmaForward)
    (rawProofImpIRoot M
      (rawDynamicTruthNativeCrossLevelDomainContext M
        sigmaDomain piDomain sigmaDomain)
      nextSigma currentSigma sigmaBackward)
    hsigmaForwardImp hsigmaBackwardImp) as hsigmaPair.
  pose proof (raw_codedPALocalProofOf_impI M hPA
    (rawDynamicTruthNativeCrossLevelAdmissibleContext M
      sigmaDomain piDomain)
    sigmaDomain
    (rawFormulaAndCode M
      (rawFormulaImpCode M currentSigma nextSigma)
      (rawFormulaImpCode M nextSigma currentSigma))
    (rawProofAndIRoot M
      (rawDynamicTruthNativeCrossLevelDomainContext M
        sigmaDomain piDomain sigmaDomain)
      (rawFormulaImpCode M currentSigma nextSigma)
      (rawFormulaImpCode M nextSigma currentSigma)
      (rawProofImpIRoot M
        (rawDynamicTruthNativeCrossLevelDomainContext M
          sigmaDomain piDomain sigmaDomain)
        currentSigma nextSigma sigmaForward)
      (rawProofImpIRoot M
        (rawDynamicTruthNativeCrossLevelDomainContext M
          sigmaDomain piDomain sigmaDomain)
        nextSigma currentSigma sigmaBackward))
    hsigmaPair) as hsigmaGuard.
  pose proof (raw_codedPALocalProofOf_impI M hPA
    (rawDynamicTruthNativeCrossLevelDomainContext M
      sigmaDomain piDomain piDomain)
    currentPi nextPi piForward hpiForward) as hpiForwardImp.
  pose proof (raw_codedPALocalProofOf_impI M hPA
    (rawDynamicTruthNativeCrossLevelDomainContext M
      sigmaDomain piDomain piDomain)
    nextPi currentPi piBackward hpiBackward) as hpiBackwardImp.
  pose proof (raw_codedPALocalProofOf_andI M hPA
    (rawDynamicTruthNativeCrossLevelDomainContext M
      sigmaDomain piDomain piDomain)
    (rawFormulaImpCode M currentPi nextPi)
    (rawFormulaImpCode M nextPi currentPi)
    (rawProofImpIRoot M
      (rawDynamicTruthNativeCrossLevelDomainContext M
        sigmaDomain piDomain piDomain)
      currentPi nextPi piForward)
    (rawProofImpIRoot M
      (rawDynamicTruthNativeCrossLevelDomainContext M
        sigmaDomain piDomain piDomain)
      nextPi currentPi piBackward)
    hpiForwardImp hpiBackwardImp) as hpiPair.
  pose proof (raw_codedPALocalProofOf_impI M hPA
    (rawDynamicTruthNativeCrossLevelAdmissibleContext M
      sigmaDomain piDomain)
    piDomain
    (rawFormulaAndCode M
      (rawFormulaImpCode M currentPi nextPi)
      (rawFormulaImpCode M nextPi currentPi))
    (rawProofAndIRoot M
      (rawDynamicTruthNativeCrossLevelDomainContext M
        sigmaDomain piDomain piDomain)
      (rawFormulaImpCode M currentPi nextPi)
      (rawFormulaImpCode M nextPi currentPi)
      (rawProofImpIRoot M
        (rawDynamicTruthNativeCrossLevelDomainContext M
          sigmaDomain piDomain piDomain)
        currentPi nextPi piForward)
      (rawProofImpIRoot M
        (rawDynamicTruthNativeCrossLevelDomainContext M
          sigmaDomain piDomain piDomain)
        nextPi currentPi piBackward))
    hpiPair) as hpiGuard.
  pose proof (raw_codedPALocalProofOf_andI M hPA
    (rawDynamicTruthNativeCrossLevelAdmissibleContext M
      sigmaDomain piDomain)
    (rawDynamicTruthNativeCrossLevelGuardedEquivalenceCode M
      sigmaDomain currentSigma nextSigma)
    (rawDynamicTruthNativeCrossLevelGuardedEquivalenceCode M
      piDomain currentPi nextPi)
    _ _ hsigmaGuard hpiGuard) as hguards.
  pose proof (raw_codedPALocalProofOf_impI M hPA
    (raw_zero M)
    (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain)
    (rawFormulaAndCode M
      (rawDynamicTruthNativeCrossLevelGuardedEquivalenceCode M
        sigmaDomain currentSigma nextSigma)
      (rawDynamicTruthNativeCrossLevelGuardedEquivalenceCode M
        piDomain currentPi nextPi))
    _ hguards) as hbody.
  eexists.
  exact hbody.
Qed.

(** ------------------------------------------------------------------
    Triple universal closure and ordinary PA-certificate packaging. *)

Definition rawDynamicTruthNativeCrossLevelClose3Root
    (M : RawPAModel) (body child : M) : M :=
  rawProofAllIRoot M (raw_zero M)
    (rawFormulaAllCode M (rawFormulaAllCode M body))
    (rawProofAllIRoot M (raw_zero M)
      (rawFormulaAllCode M body)
      (rawProofAllIRoot M (raw_zero M) body child)).

Arguments rawDynamicTruthNativeCrossLevelClose3Root
  M body child : clear implicits.

Definition rawDynamicTruthNativeCrossLevelProofCertificate
    (M : RawPAModel) (body child : M) : M :=
  rawCodeList3 M (rawNumeralValue M 0) (raw_zero M)
    (rawDynamicTruthNativeCrossLevelClose3Root M body child).

Arguments rawDynamicTruthNativeCrossLevelProofCertificate
  M body child : clear implicits.

Lemma raw_dynamicTruthNativeCrossLevel_empty_witness_context : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedPAAxiomWitnessContext M (raw_zero M) (raw_zero M).
Proof.
  intros M hPA.
  pose proof (raw_codedPAAxiomWitnessContext_standard M hPA []) as h.
  cbn [rawQuotedPAAxiomWitnessList rawQuotedContextCode
    rawListCode map] in h.
  exact h.
Qed.

Theorem raw_codedPAProofOf_dynamicTruthNativeCrossLevelCoherenceField_of_body_root :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi,
  RawDynamicTruthNativeCrossLevelBodyLocalRootAt M
    sigmaDomain piDomain currentSigma currentPi nextSigma nextPi ->
  exists certificate : M,
    RawCodedPAProofOf M
      (rawDynamicTruthNativeCrossLevelCoherenceFieldCode M
        sigmaDomain piDomain currentSigma currentPi nextSigma nextPi)
      certificate.
Proof.
  intros M hPA sigmaDomain piDomain currentSigma currentPi
    nextSigma nextPi [child [hcoverage hendpoint]].
  set (body := rawDynamicTruthNativeCrossLevelCoherenceBodyCode M
    sigmaDomain piDomain currentSigma currentPi nextSigma nextPi).
  pose proof (raw_proofAllI_ruleCoverage M hPA
    (raw_zero M) (raw_zero M) body child
    (raw_contextShift_empty M hPA) hcoverage hendpoint) as hcoverage1.
  pose proof (raw_proofAllI_endpoint M
    (raw_zero M) body child) as hendpoint1.
  pose proof (raw_proofAllI_ruleCoverage M hPA
    (raw_zero M) (raw_zero M) (rawFormulaAllCode M body)
    (rawProofAllIRoot M (raw_zero M) body child)
    (raw_contextShift_empty M hPA) hcoverage1 hendpoint1) as hcoverage2.
  pose proof (raw_proofAllI_endpoint M (raw_zero M)
    (rawFormulaAllCode M body)
    (rawProofAllIRoot M (raw_zero M) body child)) as hendpoint2.
  pose proof (raw_proofAllI_ruleCoverage M hPA
    (raw_zero M) (raw_zero M)
    (rawFormulaAllCode M (rawFormulaAllCode M body))
    (rawProofAllIRoot M (raw_zero M)
      (rawFormulaAllCode M body)
      (rawProofAllIRoot M (raw_zero M) body child))
    (raw_contextShift_empty M hPA) hcoverage2 hendpoint2) as hcoverage3.
  pose proof (raw_proofAllI_endpoint M (raw_zero M)
    (rawFormulaAllCode M (rawFormulaAllCode M body))
    (rawProofAllIRoot M (raw_zero M)
      (rawFormulaAllCode M body)
      (rawProofAllIRoot M (raw_zero M) body child))) as hendpoint3.
  exists (rawDynamicTruthNativeCrossLevelProofCertificate M body child).
  rewrite rawDynamicTruthNativeCrossLevelCoherenceFieldCode_as_all3.
  exists (raw_zero M),
    (rawDynamicTruthNativeCrossLevelClose3Root M body child),
    (raw_zero M).
  split.
  - unfold rawDynamicTruthNativeCrossLevelProofCertificate. reflexivity.
  - repeat split.
    + exact (raw_dynamicTruthNativeCrossLevel_empty_witness_context M hPA).
    + exact hcoverage3.
    + change (RawProofEndpoint M
        (rawDynamicTruthNativeCrossLevelClose3Root M body child)
        (raw_zero M)
        (rawFormulaAllCode M
          (rawFormulaAllCode M (rawFormulaAllCode M body)))).
      exact hendpoint3.
Qed.

Corollary
    raw_codedPAProofOf_dynamicTruthNativeCrossLevelCoherenceField_of_polarity_roots :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi,
  RawDynamicTruthNativeCrossLevelSigmaLocalRootsAt M
    sigmaDomain piDomain currentSigma nextSigma ->
  RawDynamicTruthNativeCrossLevelPiLocalRootsAt M
    sigmaDomain piDomain currentPi nextPi ->
  exists certificate : M,
    RawCodedPAProofOf M
      (rawDynamicTruthNativeCrossLevelCoherenceFieldCode M
        sigmaDomain piDomain currentSigma currentPi nextSigma nextPi)
      certificate.
Proof.
  intros M hPA sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
    hsigma hpi.
  apply
    (raw_codedPAProofOf_dynamicTruthNativeCrossLevelCoherenceField_of_body_root
      M hPA sigmaDomain piDomain currentSigma currentPi nextSigma nextPi).
  exact (raw_dynamicTruthNativeCrossLevelBodyLocalRootAt_of_polarity_roots
    M hPA sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
    hsigma hpi).
Qed.

(** ------------------------------------------------------------------
    Exact structural trace and reduction of the original compiler. *)

Definition RawDynamicTruthNativeCrossLevelProofTraceAt
    (M : RawPAModel) (tail : nat -> M)
    (predecessorLevel currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi : M)
    : Prop :=
  RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
      tail (raw_succ M predecessorLevel)
      currentGlobalSigma currentGlobalPi /\
  exists currentLevel nextGlobalSigma nextGlobalPi currentLevelNumeral : M,
    currentLevel = raw_succ M predecessorLevel /\
    RawDynamicTruthPairedGlobalSuccessorAt M
      currentGlobalSigma currentGlobalPi currentLevel
      nextGlobalSigma nextGlobalPi /\
    RawNumeralTermCodeAt M currentLevel currentLevelNumeral /\
    RawCodedFormulaSingleSubstitution M currentLevelNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
      sigmaDomain /\
    RawCodedFormulaSingleSubstitution M currentLevelNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthLocalPiInputDomainTemplate))
      piDomain /\
    RawDynamicTruthLocalTernaryApplication M
      currentGlobalSigma currentSigma /\
    RawDynamicTruthLocalTernaryApplication M
      currentGlobalPi currentPi /\
    RawDynamicTruthLocalTernaryApplication M
      nextGlobalSigma nextSigma /\
    RawDynamicTruthLocalTernaryApplication M
      nextGlobalPi nextPi.

Arguments RawDynamicTruthNativeCrossLevelProofTraceAt
  M tail predecessorLevel currentGlobalSigma currentGlobalPi
  sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
  : clear implicits.

Definition RawDynamicTruthNativeCrossLevelLocalRootCompiler
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi,
    RawDynamicTruthNativeCrossLevelProofTraceAt M tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      currentSigma currentPi nextSigma nextPi ->
    RawDynamicTruthNativeCrossLevelSigmaLocalRootsAt M
      sigmaDomain piDomain currentSigma nextSigma /\
    RawDynamicTruthNativeCrossLevelPiLocalRootsAt M
      sigmaDomain piDomain currentPi nextPi.

Arguments RawDynamicTruthNativeCrossLevelLocalRootCompiler M
  : clear implicits.

Lemma raw_dynamicTruthNativeCrossLevelProofTraceAt_of_transform : forall
    (M : RawPAModel) (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi fieldCode,
  RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
    tail (raw_succ M predecessorLevel)
    currentGlobalSigma currentGlobalPi ->
  RawDynamicTruthNativeCrossLevelFieldTransformAt M
    currentGlobalSigma currentGlobalPi predecessorLevel fieldCode ->
  exists sigmaDomain piDomain currentSigma currentPi nextSigma nextPi : M,
    fieldCode = rawDynamicTruthNativeCrossLevelCoherenceFieldCode M
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi /\
    RawDynamicTruthNativeCrossLevelProofTraceAt M tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      currentSigma currentPi nextSigma nextPi.
Proof.
  intros M tail predecessorLevel currentGlobalSigma currentGlobalPi
    fieldCode horbit
    (currentLevel & nextGlobalSigma & nextGlobalPi & currentLevelNumeral &
      sigmaDomain & piDomain & currentSigma & currentPi & nextSigma &
      nextPi & hlevel & hsuccessor & hnumeral & hsigmaDomain & hpiDomain &
      hcurrentSigma & hcurrentPi & hnextSigma & hnextPi & hfield).
  exists sigmaDomain, piDomain, currentSigma, currentPi, nextSigma, nextPi.
  split; [exact hfield |].
  split; [exact horbit |].
  exists currentLevel, nextGlobalSigma, nextGlobalPi, currentLevelNumeral.
  repeat split; assumption.
Qed.

Theorem
    raw_dynamicTruthNativeCrossLevelCoherenceProofCompiler_of_local_roots :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeCrossLevelLocalRootCompiler M ->
  RawDynamicTruthNativeCrossLevelCoherenceProofCompiler M.
Proof.
  intros M hPA hlocal tail predecessorLevel
    currentGlobalSigma currentGlobalPi fieldCode horbit htransform.
  destruct (raw_dynamicTruthNativeCrossLevelProofTraceAt_of_transform
    M tail predecessorLevel currentGlobalSigma currentGlobalPi fieldCode
    horbit htransform) as
    (sigmaDomain & piDomain & currentSigma & currentPi & nextSigma & nextPi &
      hfield & htrace).
  destruct (hlocal tail predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain currentSigma currentPi nextSigma nextPi htrace) as
    [hsigma hpi].
  rewrite hfield.
  exact
    (raw_codedPAProofOf_dynamicTruthNativeCrossLevelCoherenceField_of_polarity_roots
      M hPA sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
      hsigma hpi).
Qed.

Corollary
    dynamicTruthNativeCrossLevelPositiveGraph_raw_proof_total_of_local_roots :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeCrossLevelLocalRootCompiler M ->
  RawDynamicTruthNativeCrossLevelPositiveProofTotal M.
Proof.
  intros M hPA hlocal.
  exact
    (dynamicTruthNativeCrossLevelPositiveGraph_raw_proof_total_of_compiler
      M hPA
      (raw_dynamicTruthNativeCrossLevelCoherenceProofCompiler_of_local_roots
        M hPA hlocal)).
Qed.

End PABoundedRawCodedDynamicTruthNativeCrossLevelProofCompilation.
