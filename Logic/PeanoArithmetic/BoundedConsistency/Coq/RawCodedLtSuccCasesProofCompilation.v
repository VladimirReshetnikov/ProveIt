(**
  Compile PA's successor-bound case split in any witnessed local context.

  This module is translation-generic: the fixed source contains no opaque
  leaves, so every template translation agreeing with ordinary PA syntax can
  instantiate it.  The endpoint transports a caller proof of [i < S b]
  through the selected finite PA-axiom prefix and returns a genuine local
  proof of [i < b \/ i = b].
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofPropositionalRules
  RawCodedPAAxiomWitnessPrefix
  RawCodedRestrictedPAProof
  RawCodedSyntaxConstructors
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedLtSuccCasesSource.

Module PABoundedRawCodedLtSuccCasesProofCompilation.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
Import PABoundedRawCodedLtSuccCasesSource.

Definition coqLtSuccCasesInstanceTemplate
    (index bound : TemplateTerm) : TemplateFormula :=
  templateUniversalOpenManyOrBot
    (embedPAFormula codedLtSuccCasesFormula) [index; bound].

Definition coqLtSuccCasesAntecedentTemplate
    (index bound : TemplateTerm) : TemplateFormula :=
  templateImpAntecedent (coqLtSuccCasesInstanceTemplate index bound).

Definition coqLtSuccCasesResultTemplate
    (index bound : TemplateTerm) : TemplateFormula :=
  templateImpConsequent (coqLtSuccCasesInstanceTemplate index bound).

Definition templateOrLeft (source : TemplateFormula) : TemplateFormula :=
  match source with
  | tfOr lhs _ => lhs
  | _ => tfBot
  end.

Definition templateOrRight (source : TemplateFormula) : TemplateFormula :=
  match source with
  | tfOr _ rhs => rhs
  | _ => tfBot
  end.

Definition coqLtSuccCasesBelowTemplate
    (index bound : TemplateTerm) : TemplateFormula :=
  templateOrLeft (coqLtSuccCasesResultTemplate index bound).

Definition coqLtSuccCasesEqualTemplate
    (index bound : TemplateTerm) : TemplateFormula :=
  templateOrRight (coqLtSuccCasesResultTemplate index bound).

Lemma coqLtSuccCasesInstanceTemplate_open : forall index bound,
  templateUniversalOpenMany
    (embedPAFormula codedLtSuccCasesFormula) [index; bound] =
  Some (coqLtSuccCasesInstanceTemplate index bound).
Proof.
  intros index bound.
  unfold coqLtSuccCasesInstanceTemplate,
    templateUniversalOpenManyOrBot,
    codedLtSuccCasesFormula.
  cbn [templateUniversalOpenMany embedPAFormula
    templateFormulaOpen templateFormulaSubst].
  reflexivity.
Qed.

(** Exact propositional shape after the two universal openings. *)
Lemma coqLtSuccCasesInstanceTemplate_shape : forall index bound,
  coqLtSuccCasesInstanceTemplate index bound =
    tfImp (coqLtSuccCasesAntecedentTemplate index bound)
      (coqLtSuccCasesResultTemplate index bound) /\
  coqLtSuccCasesResultTemplate index bound =
    tfOr (coqLtSuccCasesBelowTemplate index bound)
      (coqLtSuccCasesEqualTemplate index bound).
Proof.
  intros index bound.
  unfold coqLtSuccCasesInstanceTemplate,
    coqLtSuccCasesAntecedentTemplate,
    coqLtSuccCasesResultTemplate,
    coqLtSuccCasesBelowTemplate, coqLtSuccCasesEqualTemplate,
    templateImpAntecedent, templateImpConsequent,
    templateOrLeft, templateOrRight,
    templateUniversalOpenManyOrBot,
    codedLtSuccCasesFormula.
  cbn [templateUniversalOpenMany embedPAFormula
    templateFormulaOpen templateFormulaSubst].
  split; reflexivity.
Qed.

Theorem raw_codedPALocalProofOf_lt_succ_cases_instance_on_witnessed_tail :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext index bound,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) (root : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext)
      (rawTemplateFormula translation
        (coqLtSuccCasesInstanceTemplate index bound)) root.
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext index bound hbase.
  exact
    (raw_codedTemplatePALocalProofOf_of_BProv_open_many_on_witnessed_tail
      M hPA translation hagreement
      baseWitnessList baseContext codedLtSuccCasesFormula
      [index; bound] (coqLtSuccCasesInstanceTemplate index bound)
      hbase PA_proves_codedLtSuccCasesFormula
      (coqLtSuccCasesInstanceTemplate_open index bound)).
Qed.

Theorem raw_codedPALocalProofOf_lt_succ_cases_on_witnessed_tail :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext index bound antecedentRoot,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M baseContext
    (rawTemplateFormula translation
      (coqLtSuccCasesAntecedentTemplate index bound)) antecedentRoot ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) (root : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext)
      (rawTemplateFormula translation
        (coqLtSuccCasesResultTemplate index bound)) root.
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext index bound antecedentRoot
    hbase hantecedent.
  destruct
    (raw_codedPALocalProofOf_lt_succ_cases_instance_on_witnessed_tail
      M hPA translation hagreement baseWitnessList baseContext
      index bound hbase)
    as (witnesses & implicationRoot & hextended & himplication).
  destruct (raw_codedPALocalProofOf_standardPAAxiomWitnessPrefix
    M hPA witnesses baseContext
    (rawTemplateFormula translation
      (coqLtSuccCasesAntecedentTemplate index bound))
    antecedentRoot
    (raw_codedPAAxiomWitnessPrefix_context_realizable_of_witnessed
      M baseWitnessList baseContext hbase)
    hantecedent) as [transportedRoot htransported].
  destruct (coqLtSuccCasesInstanceTemplate_shape index bound)
    as [himpShape _].
  rewrite himpShape, rawTemplateFormula_imp in himplication.
  pose proof (raw_codedPALocalProofOf_impE M hPA
    (rawStandardPAAxiomWitnessPrefixContextCode M witnesses baseContext)
    (rawTemplateFormula translation
      (coqLtSuccCasesAntecedentTemplate index bound))
    (rawTemplateFormula translation
      (coqLtSuccCasesResultTemplate index bound))
    implicationRoot transportedRoot himplication htransported) as hresult.
  lazymatch type of hresult with
  | RawCodedPALocalProofOf _ _ _ ?root =>
      exists witnesses, root; split; [exact hextended | exact hresult]
  end.
Qed.

(** Prefix-general form used beneath existential and universal
    eigenvariables.  The caller supplies only atomic adequacy of the finite
    temporary prefix.  The selected PA-axiom witnesses remain in the tail,
    so the prefix order and every de Bruijn binder are preserved exactly. *)
Theorem
    raw_codedPALocalProofOf_lt_succ_cases_on_witnessed_tail_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext prefix index bound antecedentRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqLtSuccCasesAntecedentTemplate index bound)) antecedentRoot ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) (root : M),
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
        (coqLtSuccCasesResultTemplate index bound)) root.
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext prefix index bound antecedentRoot
    hprefix hbase hantecedent.
  destruct
    (raw_codedPALocalProofOf_lt_succ_cases_instance_on_witnessed_tail
      M hPA translation hagreement baseWitnessList baseContext
      index bound hbase)
    as (witnesses & implicationRoot & hextended & himplication).
  set (extendedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M witnesses baseContext).
  destruct (raw_codedPALocalProof_templatePrefix M hPA translation
    extendedContext prefix
    (rawTemplateFormula translation
      (coqLtSuccCasesInstanceTemplate index bound))
    implicationRoot
    (raw_codedPAAxiomWitnessPrefix_context_realizable_of_witnessed M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      extendedContext hextended)
    hprefix himplication) as [prefixedImplicationRoot hprefixedImplication].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation
      baseWitnessList baseContext
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      extendedContext prefix
      (rawTemplateFormula translation
        (coqLtSuccCasesAntecedentTemplate index bound))
      antecedentRoot hbase hextended
      (raw_standardPAAxiomWitnessPrefixContextCode_target_included
        M hPA witnesses baseContext)
      hantecedent) as [transportedAntecedentRoot htransportedAntecedent].
  destruct (coqLtSuccCasesInstanceTemplate_shape index bound)
    as [himpShape _].
  rewrite himpShape, rawTemplateFormula_imp in hprefixedImplication.
  pose proof (raw_codedPALocalProofOf_impE M hPA
    (rawTemplateContextCodeOnTail translation extendedContext prefix)
    (rawTemplateFormula translation
      (coqLtSuccCasesAntecedentTemplate index bound))
    (rawTemplateFormula translation
      (coqLtSuccCasesResultTemplate index bound))
    prefixedImplicationRoot transportedAntecedentRoot
    hprefixedImplication htransportedAntecedent) as hresult.
  exists witnesses.
  eexists.
  split; [exact hextended | exact hresult].
Qed.

(** Eliminate the represented arithmetic disjunction immediately.  Branch
    compilers receive the exact finite PA prefix selected for the case theorem,
    so they can build their roots in the literal cons contexts required by
    represented [OrE]. *)
Theorem raw_codedPALocalProofOf_lt_succ_cases_eliminate_on_witnessed_tail :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext index bound antecedentRoot conclusion,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M baseContext
    (rawTemplateFormula translation
      (coqLtSuccCasesAntecedentTemplate index bound)) antecedentRoot ->
  (forall witnesses,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) ->
    exists root,
      RawCodedPALocalProofOf M
        (rawListNode M
          (rawTemplateFormula translation
            (coqLtSuccCasesBelowTemplate index bound))
          (rawStandardPAAxiomWitnessPrefixContextCode M
            witnesses baseContext)) conclusion root) ->
  (forall witnesses,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) ->
    exists root,
      RawCodedPALocalProofOf M
        (rawListNode M
          (rawTemplateFormula translation
            (coqLtSuccCasesEqualTemplate index bound))
          (rawStandardPAAxiomWitnessPrefixContextCode M
            witnesses baseContext)) conclusion root) ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) (root : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) conclusion root.
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext index bound antecedentRoot conclusion
    hbase hantecedent hbelowBranch hequalBranch.
  destruct (raw_codedPALocalProofOf_lt_succ_cases_on_witnessed_tail
    M hPA translation hagreement
    baseWitnessList baseContext index bound antecedentRoot
    hbase hantecedent)
    as (witnesses & casesRoot & hextended & hcases).
  destruct (coqLtSuccCasesInstanceTemplate_shape index bound)
    as [_ hresultShape].
  rewrite hresultShape, rawTemplateFormula_or in hcases.
  destruct (hbelowBranch witnesses hextended)
    as [belowRoot hbelow].
  destruct (hequalBranch witnesses hextended)
    as [equalRoot hequal].
  pose proof (raw_codedPALocalProofOf_orE M hPA
    (rawStandardPAAxiomWitnessPrefixContextCode M witnesses baseContext)
    (rawTemplateFormula translation
      (coqLtSuccCasesBelowTemplate index bound))
    (rawTemplateFormula translation
      (coqLtSuccCasesEqualTemplate index bound))
    conclusion casesRoot belowRoot equalRoot hcases hbelow hequal)
    as hresult.
  exists witnesses.
  eexists.
  split; [exact hextended |].
  exact hresult.
Qed.

(** Represented Or-elimination under the same arbitrary temporary prefix.
    Both branch callbacks see the one concrete standard-axiom extension
    selected while compiling the arithmetic case theorem. *)
Theorem
    raw_codedPALocalProofOf_lt_succ_cases_eliminate_on_witnessed_tail_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext prefix index bound antecedentRoot
    conclusion,
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqLtSuccCasesAntecedentTemplate index bound)) antecedentRoot ->
  (forall witnesses,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) ->
    exists root,
      RawCodedPALocalProofOf M
        (rawListNode M
          (rawTemplateFormula translation
            (coqLtSuccCasesBelowTemplate index bound))
          (rawTemplateContextCodeOnTail translation
            (rawStandardPAAxiomWitnessPrefixContextCode M
              witnesses baseContext) prefix)) conclusion root) ->
  (forall witnesses,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) ->
    exists root,
      RawCodedPALocalProofOf M
        (rawListNode M
          (rawTemplateFormula translation
            (coqLtSuccCasesEqualTemplate index bound))
          (rawTemplateContextCodeOnTail translation
            (rawStandardPAAxiomWitnessPrefixContextCode M
              witnesses baseContext) prefix)) conclusion root) ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) (root : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext) prefix)
      conclusion root.
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext prefix index bound antecedentRoot conclusion
    hprefix hbase hantecedent hbelowBranch hequalBranch.
  destruct
    (raw_codedPALocalProofOf_lt_succ_cases_on_witnessed_tail_under_prefix
      M hPA translation hagreement
      baseWitnessList baseContext prefix index bound antecedentRoot
      hprefix hbase hantecedent)
    as (witnesses & casesRoot & hextended & hcases).
  destruct (coqLtSuccCasesInstanceTemplate_shape index bound)
    as [_ hresultShape].
  rewrite hresultShape, rawTemplateFormula_or in hcases.
  destruct (hbelowBranch witnesses hextended)
    as [belowRoot hbelow].
  destruct (hequalBranch witnesses hextended)
    as [equalRoot hequal].
  pose proof (raw_codedPALocalProofOf_orE M hPA
    (rawTemplateContextCodeOnTail translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) prefix)
    (rawTemplateFormula translation
      (coqLtSuccCasesBelowTemplate index bound))
    (rawTemplateFormula translation
      (coqLtSuccCasesEqualTemplate index bound))
    conclusion casesRoot belowRoot equalRoot hcases hbelow hequal)
    as hresult.
  exists witnesses.
  eexists.
  split; [exact hextended | exact hresult].
Qed.

(** A reusable output package for compilers that may enlarge an honestly
    witnessed PA tail while preserving a fixed temporary template prefix. *)
Definition RawCodedPAGrowingTemplateLocalProofAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (sourceWitnessList sourceContext : M)
    (prefix : TemplateContext) (conclusion : M) : Prop :=
  exists targetWitnessList targetContext root,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M sourceContext targetContext /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation targetContext prefix)
      conclusion root.

Arguments RawCodedPAGrowingTemplateLocalProofAt
  M translation sourceWitnessList sourceContext prefix conclusion
  : clear implicits.

(** A growing-tail form of represented case elimination.

    A branch compiler may itself instantiate another fixed PA theorem.  Its
    proof then lives over a further witnessed extension rather than over the
    witness tail originally selected for [i < S b -> i < b \/ i = b].  This
    is unavoidable for the appended-row equality branch, which invokes beta
    functionality only after the equality assumption has become the literal
    context head.

    The two callbacks below are consequently dependency ordered.  The first
    may choose an arbitrary honestly witnessed super-context; the second is
    invoked on that context and may grow it once more.  We transport both the
    arithmetic disjunction and the first branch proof to the final tail, then
    build one genuine represented [OrE] node there.  No merge, proof-code
    equality, or semantic context erasure is required. *)
Theorem
    raw_codedPALocalProofOf_lt_succ_cases_eliminate_on_growing_witnessed_tail_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext prefix index bound antecedentRoot
    conclusion,
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqLtSuccCasesAntecedentTemplate index bound)) antecedentRoot ->
  (forall sourceWitnessList sourceContext,
    RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
    RawCodedPAGrowingTemplateLocalProofAt M translation
      sourceWitnessList sourceContext
      (coqLtSuccCasesBelowTemplate index bound :: prefix) conclusion) ->
  (forall sourceWitnessList sourceContext,
    RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
    RawCodedPAGrowingTemplateLocalProofAt M translation
      sourceWitnessList sourceContext
      (coqLtSuccCasesEqualTemplate index bound :: prefix) conclusion) ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    baseWitnessList baseContext prefix conclusion.
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext prefix index bound antecedentRoot conclusion
    hprefix hbase hantecedent hbelowBranch hequalBranch.
  destruct
    (raw_codedPALocalProofOf_lt_succ_cases_on_witnessed_tail_under_prefix
      M hPA translation hagreement
      baseWitnessList baseContext prefix index bound antecedentRoot
      hprefix hbase hantecedent)
    as (caseWitnesses & casesRoot & hcaseContext & hcases).
  set (caseWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      caseWitnesses baseWitnessList).
  set (caseContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      caseWitnesses baseContext).
  destruct (hbelowBranch caseWitnessList caseContext hcaseContext)
    as (belowWitnessList & belowContext & belowRoot &
        hbelowContext & hcaseBelowIncluded & hbelow).
  destruct (hequalBranch belowWitnessList belowContext hbelowContext)
    as (finalWitnessList & finalContext & equalRoot &
        hfinalContext & hbelowFinalIncluded & hequal).
  assert (hcaseFinalIncluded :
      RawContextListIncluded M caseContext finalContext).
  {
    intros member hmember.
    exact (hbelowFinalIncluded member
      (hcaseBelowIncluded member hmember)).
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation
      caseWitnessList caseContext finalWitnessList finalContext
      prefix
      (rawTemplateFormula translation
        (coqLtSuccCasesResultTemplate index bound))
      casesRoot hcaseContext hfinalContext hcaseFinalIncluded hcases)
    as [transportedCasesRoot htransportedCases].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation
      belowWitnessList belowContext finalWitnessList finalContext
      (coqLtSuccCasesBelowTemplate index bound :: prefix)
      conclusion belowRoot hbelowContext hfinalContext
      hbelowFinalIncluded hbelow)
    as [transportedBelowRoot htransportedBelow].
  destruct (coqLtSuccCasesInstanceTemplate_shape index bound)
    as [_ hresultShape].
  rewrite hresultShape, rawTemplateFormula_or in htransportedCases.
  pose proof (raw_codedPALocalProofOf_orE M hPA
    (rawTemplateContextCodeOnTail translation finalContext prefix)
    (rawTemplateFormula translation
      (coqLtSuccCasesBelowTemplate index bound))
    (rawTemplateFormula translation
      (coqLtSuccCasesEqualTemplate index bound))
    conclusion transportedCasesRoot transportedBelowRoot equalRoot
    htransportedCases htransportedBelow hequal) as hresult.
  exists finalWitnessList, finalContext.
  eexists.
  split; [exact hfinalContext |].
  split.
  - intros member hmember.
    exact (hcaseFinalIncluded member
      (raw_standardPAAxiomWitnessPrefixContextCode_target_included
        M hPA caseWitnesses baseContext member hmember)).
  - exact hresult.
Qed.

End PABoundedRawCodedLtSuccCasesProofCompilation.
