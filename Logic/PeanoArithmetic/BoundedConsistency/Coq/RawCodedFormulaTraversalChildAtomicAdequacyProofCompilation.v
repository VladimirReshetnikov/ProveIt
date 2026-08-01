(**
  Represented inheritance of atomic adequacy by a syntax-traversal child.

  Formula syntax is stored occurrence-wise in a beta-coded table.  Once the
  table is known to be a syntax traversal and its equality rows have adequate
  term syntax, every strictly earlier row below the chosen root is itself an
  atomically adequate formula code.  This module turns that semantic closure
  fact into one closed PA theorem and permits all seven parameters to be
  instantiated by arbitrary template terms.

  The theorem is intentionally independent of dynamic truth.  Predecessor
  compilation is its first client, but any represented formula traversal can
  reuse the same law without adopting the predecessor binder layout.
*)

From Stdlib Require Import List Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedAssignment
  RawCodedFormulaRankTotality
  RawCodedFixedLevelTruthTotality
  RawCodedFormulaBoundAtomicallyAdequateTotality
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedPALocalProofUniversalEliminationChain.

Module PABoundedRawCodedFormulaTraversalChildAtomicAdequacyProofCompilation.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFormulaBoundAtomicallyAdequateTotality.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.

(** Binder order is formula table code, table step, traversal bound, root
    occurrence, root formula, child occurrence, and child formula.  Thus the
    body sees those parameters at de Bruijn indices [6] down to [0]. *)
Definition codedFormulaTraversalChildAtomicAdequacyBodyFormula : formula :=
  pImp
    (codedFormulaSyntaxTraversalTermAt
      (tVar 6) (tVar 5) (tVar 4) (tVar 3) (tVar 2))
    (pImp
      (codedFormulaAtomicTermAdequateTermAt
        (tVar 6) (tVar 5) (tVar 4))
      (pImp
        (Formula.ltTermAt (tVar 1) (tVar 3))
        (pImp
          (codedAssignmentLookupTermAt
            (tVar 6) (tVar 5) (tVar 1) (tVar 0))
          (codedFormulaAtomicallyAdequateTermAt (tVar 0))))).

Definition codedFormulaTraversalChildAtomicAdequacyFormula : formula :=
  pAll (pAll (pAll (pAll (pAll (pAll (pAll
    codedFormulaTraversalChildAtomicAdequacyBodyFormula)))))).

Lemma raw_sat_codedFormulaTraversalChildAtomicAdequacyFormula_iff : forall
    (M : RawPAModel) (e : nat -> M),
  raw_formula_sat M e codedFormulaTraversalChildAtomicAdequacyFormula <->
  forall formulaCode formulaStep bound rootIndex root childIndex child : M,
    RawCodedFormulaSyntaxTraversal M
      formulaCode formulaStep bound rootIndex root ->
    RawCodedFormulaAtomicTermAdequate M
      formulaCode formulaStep bound ->
    rawLt M childIndex rootIndex ->
    RawCodedAssignmentLookup M
      formulaCode formulaStep childIndex child ->
    RawCodedFormulaAtomicallyAdequate M child.
Proof.
  intros M e.
  unfold codedFormulaTraversalChildAtomicAdequacyFormula,
    codedFormulaTraversalChildAtomicAdequacyBodyFormula.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedFormulaSyntaxTraversalTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaAtomicTermAdequateTermAt_iff.
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedAssignmentLookupTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaAtomicallyAdequateTermAt_iff.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma codedFormulaTraversalChildAtomicAdequacyFormula_sentence :
  Formula.Sentence codedFormulaTraversalChildAtomicAdequacyFormula.
Proof.
  intros k hfree.
  unfold codedFormulaTraversalChildAtomicAdequacyFormula,
    codedFormulaTraversalChildAtomicAdequacyBodyFormula,
    codedFormulaSyntaxTraversalTermAt,
    codedFormulaAtomicTermAdequateTermAt,
    codedFormulaAtomicallyAdequateTermAt in hfree.
  cbn in hfree. lia.
Qed.

Theorem codedFormulaTraversalChildAtomicAdequacyFormula_raw_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e codedFormulaTraversalChildAtomicAdequacyFormula.
Proof.
  intros M hPA e.
  apply (proj2
    (raw_sat_codedFormulaTraversalChildAtomicAdequacyFormula_iff M e)).
  intros formulaCode formulaStep bound rootIndex root childIndex child
    htraversal hatomic hchild hlookup.
  exact (raw_codedFormulaAtomicallyAdequate_child_at M hPA
    formulaCode formulaStep bound rootIndex root childIndex child
    htraversal hatomic hchild hlookup).
Qed.

(** Completeness is applied to the fixed closed arithmetic sentence only;
    no carrier-valued formula is decoded in the metatheory. *)
Theorem PA_proves_codedFormulaTraversalChildAtomicAdequacyFormula :
  Formula.BProv Formula.Ax_s []
    codedFormulaTraversalChildAtomicAdequacyFormula.
Proof.
  apply PA_BProv_of_raw_valid.
  - exact codedFormulaTraversalChildAtomicAdequacyFormula_sentence.
  - exact codedFormulaTraversalChildAtomicAdequacyFormula_raw_valid.
Qed.

(** Capture-avoiding universal opening makes the represented theorem usable
    at arbitrary terms, including deeply shifted predecessor variables. *)
Definition coqFormulaTraversalChildAtomicAdequacyInstanceTemplate
    (formulaCode formulaStep bound rootIndex root childIndex child
      : TemplateTerm) : TemplateFormula :=
  templateUniversalOpenManyOrBot
    (embedPAFormula codedFormulaTraversalChildAtomicAdequacyFormula)
    [formulaCode; formulaStep; bound; rootIndex; root; childIndex; child].

Lemma coqFormulaTraversalChildAtomicAdequacyInstanceTemplate_open : forall
    formulaCode formulaStep bound rootIndex root childIndex child,
  templateUniversalOpenMany
    (embedPAFormula codedFormulaTraversalChildAtomicAdequacyFormula)
    [formulaCode; formulaStep; bound; rootIndex; root; childIndex; child] =
  Some (coqFormulaTraversalChildAtomicAdequacyInstanceTemplate
    formulaCode formulaStep bound rootIndex root childIndex child).
Proof.
  intros formulaCode formulaStep bound rootIndex root childIndex child.
  unfold coqFormulaTraversalChildAtomicAdequacyInstanceTemplate,
    templateUniversalOpenManyOrBot,
    codedFormulaTraversalChildAtomicAdequacyFormula.
  cbn [templateUniversalOpenMany embedPAFormula
    templateFormulaOpen templateFormulaSubst].
  reflexivity.
Qed.

(** Named projections keep clients independent of the concrete right-nested
    implication tree.  In particular, the predecessor specialization can
    identify each premise separately before any proof-code assembly begins. *)
Definition coqFormulaTraversalChildAtomicAdequacySyntaxPremiseTemplate
    formulaCode formulaStep bound rootIndex root childIndex child :=
  templateImpAntecedent
    (coqFormulaTraversalChildAtomicAdequacyInstanceTemplate
      formulaCode formulaStep bound rootIndex root childIndex child).

Definition coqFormulaTraversalChildAtomicAdequacyAtomicPremiseTemplate
    formulaCode formulaStep bound rootIndex root childIndex child :=
  templateImpAntecedent (templateImpConsequent
    (coqFormulaTraversalChildAtomicAdequacyInstanceTemplate
      formulaCode formulaStep bound rootIndex root childIndex child)).

Definition coqFormulaTraversalChildAtomicAdequacyBoundPremiseTemplate
    formulaCode formulaStep bound rootIndex root childIndex child :=
  templateImpAntecedent (templateImpConsequent (templateImpConsequent
    (coqFormulaTraversalChildAtomicAdequacyInstanceTemplate
      formulaCode formulaStep bound rootIndex root childIndex child))).

Definition coqFormulaTraversalChildAtomicAdequacyLookupPremiseTemplate
    formulaCode formulaStep bound rootIndex root childIndex child :=
  templateImpAntecedent (templateImpConsequent (templateImpConsequent
    (templateImpConsequent
      (coqFormulaTraversalChildAtomicAdequacyInstanceTemplate
        formulaCode formulaStep bound rootIndex root childIndex child)))).

Definition coqFormulaTraversalChildAtomicAdequacyConclusionTemplate
    formulaCode formulaStep bound rootIndex root childIndex child :=
  templateImpConsequent (templateImpConsequent (templateImpConsequent
    (templateImpConsequent
      (coqFormulaTraversalChildAtomicAdequacyInstanceTemplate
        formulaCode formulaStep bound rootIndex root childIndex child)))).

Lemma coqFormulaTraversalChildAtomicAdequacyInstanceTemplate_imp4_shape :
  forall formulaCode formulaStep bound rootIndex root childIndex child,
  coqFormulaTraversalChildAtomicAdequacyInstanceTemplate
      formulaCode formulaStep bound rootIndex root childIndex child =
  tfImp
    (coqFormulaTraversalChildAtomicAdequacySyntaxPremiseTemplate
      formulaCode formulaStep bound rootIndex root childIndex child)
    (tfImp
      (coqFormulaTraversalChildAtomicAdequacyAtomicPremiseTemplate
        formulaCode formulaStep bound rootIndex root childIndex child)
      (tfImp
        (coqFormulaTraversalChildAtomicAdequacyBoundPremiseTemplate
          formulaCode formulaStep bound rootIndex root childIndex child)
        (tfImp
          (coqFormulaTraversalChildAtomicAdequacyLookupPremiseTemplate
            formulaCode formulaStep bound rootIndex root childIndex child)
          (coqFormulaTraversalChildAtomicAdequacyConclusionTemplate
            formulaCode formulaStep bound rootIndex root childIndex child)))).
Proof.
  intros formulaCode formulaStep bound rootIndex root childIndex child.
  unfold coqFormulaTraversalChildAtomicAdequacySyntaxPremiseTemplate,
    coqFormulaTraversalChildAtomicAdequacyAtomicPremiseTemplate,
    coqFormulaTraversalChildAtomicAdequacyBoundPremiseTemplate,
    coqFormulaTraversalChildAtomicAdequacyLookupPremiseTemplate,
    coqFormulaTraversalChildAtomicAdequacyConclusionTemplate,
    coqFormulaTraversalChildAtomicAdequacyInstanceTemplate,
    templateUniversalOpenManyOrBot,
    codedFormulaTraversalChildAtomicAdequacyFormula,
    codedFormulaTraversalChildAtomicAdequacyBodyFormula.
  cbn [templateUniversalOpenMany embedPAFormula
    templateFormulaOpen templateFormulaSubst
    templateImpAntecedent templateImpConsequent].
  reflexivity.
Qed.

(** Compile one arbitrary seven-term instance on a finite witnessed PA-axiom
    extension.  The result remains an implication; clients can synchronize
    their four premise roots with this extension before applying [Imp-E]. *)
Theorem
    raw_codedPALocalProofOf_formulaTraversalChildAtomicAdequacy_instance_on_witnessed_tail :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext
      formulaCode formulaStep bound rootIndex root childIndex child,
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
        (coqFormulaTraversalChildAtomicAdequacyInstanceTemplate
          formulaCode formulaStep bound rootIndex root childIndex child))
      proofRoot.
Proof.
  intros M hPA translation hagreement baseWitnessList baseContext
    formulaCode formulaStep bound rootIndex root childIndex child hbase.
  exact
    (raw_codedTemplatePALocalProofOf_of_BProv_open_many_on_witnessed_tail
      M hPA translation hagreement baseWitnessList baseContext
      codedFormulaTraversalChildAtomicAdequacyFormula
      [formulaCode; formulaStep; bound; rootIndex; root; childIndex; child]
      (coqFormulaTraversalChildAtomicAdequacyInstanceTemplate
        formulaCode formulaStep bound rootIndex root childIndex child)
      hbase PA_proves_codedFormulaTraversalChildAtomicAdequacyFormula
      (coqFormulaTraversalChildAtomicAdequacyInstanceTemplate_open
        formulaCode formulaStep bound rootIndex root childIndex child)).
Qed.

(** Prefix-general version for constructor assumptions and eigenvariables. *)
Theorem
    raw_codedPALocalProofOf_formulaTraversalChildAtomicAdequacy_instance_on_witnessed_tail_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext prefix
      formulaCode formulaStep bound rootIndex root childIndex child,
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
        (coqFormulaTraversalChildAtomicAdequacyInstanceTemplate
          formulaCode formulaStep bound rootIndex root childIndex child))
      proofRoot.
Proof.
  intros M hPA translation hagreement baseWitnessList baseContext prefix
    formulaCode formulaStep bound rootIndex root childIndex child
    hprefix hbase.
  destruct
    (raw_codedPALocalProofOf_formulaTraversalChildAtomicAdequacy_instance_on_witnessed_tail
      M hPA translation hagreement baseWitnessList baseContext
      formulaCode formulaStep bound rootIndex root childIndex child hbase)
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
      (coqFormulaTraversalChildAtomicAdequacyInstanceTemplate
        formulaCode formulaStep bound rootIndex root childIndex child))
    sourceRoot
    (raw_codedPAAxiomWitnessPrefix_context_realizable_of_witnessed M
      extendedWitnessList extendedContext hextended)
    hprefix hsource) as [proofRoot hproof].
  exists witnesses, proofRoot. split; assumption.
Qed.

(** Compile the generic law, retain the selected PA witness extension, move
    all four caller roots to that exact tail, and eliminate the implication
    spine.  This is the reusable context-management kernel; it assumes no
    relationship between the seven terms beyond the four represented
    premises themselves. *)
Theorem
    raw_codedPALocalProofOf_formulaTraversalChildAtomicAdequacy_of_roots_on_witnessed_extension_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext prefix
      formulaCode formulaStep bound rootIndex root childIndex child
      syntaxRoot atomicRoot boundRoot lookupRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqFormulaTraversalChildAtomicAdequacySyntaxPremiseTemplate
        formulaCode formulaStep bound rootIndex root childIndex child))
    syntaxRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqFormulaTraversalChildAtomicAdequacyAtomicPremiseTemplate
        formulaCode formulaStep bound rootIndex root childIndex child))
    atomicRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqFormulaTraversalChildAtomicAdequacyBoundPremiseTemplate
        formulaCode formulaStep bound rootIndex root childIndex child))
    boundRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqFormulaTraversalChildAtomicAdequacyLookupPremiseTemplate
        formulaCode formulaStep bound rootIndex root childIndex child))
    lookupRoot ->
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
        (coqFormulaTraversalChildAtomicAdequacyConclusionTemplate
          formulaCode formulaStep bound rootIndex root childIndex child))
      resultRoot.
Proof.
  intros M hPA translation hagreement baseWitnessList baseContext prefix
    formulaCode formulaStep bound rootIndex root childIndex child
    syntaxRoot atomicRoot boundRoot lookupRoot hprefix hbase
    hsyntax hatomic hbound hlookup.
  destruct
    (raw_codedPALocalProofOf_formulaTraversalChildAtomicAdequacy_instance_on_witnessed_tail_under_prefix
      M hPA translation hagreement baseWitnessList baseContext prefix
      formulaCode formulaStep bound rootIndex root childIndex child
      hprefix hbase)
    as (witnesses & implicationRoot & hextended & himplication).
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
      (rawTemplateFormula translation
        (coqFormulaTraversalChildAtomicAdequacySyntaxPremiseTemplate
          formulaCode formulaStep bound rootIndex root childIndex child))
      syntaxRoot hbase hextended hincluded hsyntax)
    as [transportedSyntaxRoot htransportedSyntax].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      extendedWitnessList extendedContext prefix
      (rawTemplateFormula translation
        (coqFormulaTraversalChildAtomicAdequacyAtomicPremiseTemplate
          formulaCode formulaStep bound rootIndex root childIndex child))
      atomicRoot hbase hextended hincluded hatomic)
    as [transportedAtomicRoot htransportedAtomic].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      extendedWitnessList extendedContext prefix
      (rawTemplateFormula translation
        (coqFormulaTraversalChildAtomicAdequacyBoundPremiseTemplate
          formulaCode formulaStep bound rootIndex root childIndex child))
      boundRoot hbase hextended hincluded hbound)
    as [transportedBoundRoot htransportedBound].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      extendedWitnessList extendedContext prefix
      (rawTemplateFormula translation
        (coqFormulaTraversalChildAtomicAdequacyLookupPremiseTemplate
          formulaCode formulaStep bound rootIndex root childIndex child))
      lookupRoot hbase hextended hincluded hlookup)
    as [transportedLookupRoot htransportedLookup].
  rewrite
    coqFormulaTraversalChildAtomicAdequacyInstanceTemplate_imp4_shape
    in himplication.
  rewrite !rawTemplateFormula_imp in himplication.
  pose proof (raw_codedPALocalProofOf_impE M hPA
    (rawTemplateContextCodeOnTail translation extendedContext prefix)
    (rawTemplateFormula translation
      (coqFormulaTraversalChildAtomicAdequacySyntaxPremiseTemplate
        formulaCode formulaStep bound rootIndex root childIndex child))
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        (coqFormulaTraversalChildAtomicAdequacyAtomicPremiseTemplate
          formulaCode formulaStep bound rootIndex root childIndex child))
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          (coqFormulaTraversalChildAtomicAdequacyBoundPremiseTemplate
            formulaCode formulaStep bound rootIndex root childIndex child))
        (rawFormulaImpCode M
          (rawTemplateFormula translation
            (coqFormulaTraversalChildAtomicAdequacyLookupPremiseTemplate
              formulaCode formulaStep bound rootIndex root childIndex child))
          (rawTemplateFormula translation
            (coqFormulaTraversalChildAtomicAdequacyConclusionTemplate
              formulaCode formulaStep bound rootIndex root childIndex child)))))
    implicationRoot transportedSyntaxRoot
    himplication htransportedSyntax) as hafterSyntax.
  lazymatch type of hafterSyntax with
  | RawCodedPALocalProofOf _ _ _ ?afterSyntaxRoot =>
      pose proof (raw_codedPALocalProofOf_impE M hPA
        (rawTemplateContextCodeOnTail translation extendedContext prefix)
        (rawTemplateFormula translation
          (coqFormulaTraversalChildAtomicAdequacyAtomicPremiseTemplate
            formulaCode formulaStep bound rootIndex root childIndex child))
        (rawFormulaImpCode M
          (rawTemplateFormula translation
            (coqFormulaTraversalChildAtomicAdequacyBoundPremiseTemplate
              formulaCode formulaStep bound rootIndex root childIndex child))
          (rawFormulaImpCode M
            (rawTemplateFormula translation
              (coqFormulaTraversalChildAtomicAdequacyLookupPremiseTemplate
                formulaCode formulaStep bound rootIndex root childIndex child))
            (rawTemplateFormula translation
              (coqFormulaTraversalChildAtomicAdequacyConclusionTemplate
                formulaCode formulaStep bound rootIndex root childIndex child))))
        afterSyntaxRoot transportedAtomicRoot
        hafterSyntax htransportedAtomic) as hafterAtomic;
      lazymatch type of hafterAtomic with
      | RawCodedPALocalProofOf _ _ _ ?afterAtomicRoot =>
          pose proof (raw_codedPALocalProofOf_impE M hPA
            (rawTemplateContextCodeOnTail translation extendedContext prefix)
            (rawTemplateFormula translation
              (coqFormulaTraversalChildAtomicAdequacyBoundPremiseTemplate
                formulaCode formulaStep bound rootIndex root
                childIndex child))
            (rawFormulaImpCode M
              (rawTemplateFormula translation
                (coqFormulaTraversalChildAtomicAdequacyLookupPremiseTemplate
                  formulaCode formulaStep bound rootIndex root
                  childIndex child))
              (rawTemplateFormula translation
                (coqFormulaTraversalChildAtomicAdequacyConclusionTemplate
                  formulaCode formulaStep bound rootIndex root
                  childIndex child)))
            afterAtomicRoot transportedBoundRoot
            hafterAtomic htransportedBound) as hafterBound;
          lazymatch type of hafterBound with
          | RawCodedPALocalProofOf _ _ _ ?afterBoundRoot =>
              pose proof (raw_codedPALocalProofOf_impE M hPA
                (rawTemplateContextCodeOnTail translation
                  extendedContext prefix)
                (rawTemplateFormula translation
                  (coqFormulaTraversalChildAtomicAdequacyLookupPremiseTemplate
                    formulaCode formulaStep bound rootIndex root
                    childIndex child))
                (rawTemplateFormula translation
                  (coqFormulaTraversalChildAtomicAdequacyConclusionTemplate
                    formulaCode formulaStep bound rootIndex root
                    childIndex child))
                afterBoundRoot transportedLookupRoot
                hafterBound htransportedLookup) as hresult;
              lazymatch type of hresult with
              | RawCodedPALocalProofOf _ _ _ ?resultRoot =>
                  exists witnesses, resultRoot;
                  split; [exact hextended |];
                  split; [exact hincluded | exact hresult]
              end
          end
      end
  end.
Qed.

End PABoundedRawCodedFormulaTraversalChildAtomicAdequacyProofCompilation.
