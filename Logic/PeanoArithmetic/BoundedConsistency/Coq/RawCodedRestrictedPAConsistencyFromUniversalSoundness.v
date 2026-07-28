(**
  The exact carrier-level syntax and proof boundary for the
  consistency-from-soundness bridge.

  Lean proves the final consistency field from the universal invariant

      every restricted derivation preserves successor truth.

  The corresponding Rocq formula must remain meaningful when the
  restriction level and the truth predicate are nonstandard carrier
  objects.  In particular, the standard-level formula from
  [RawCodedRestrictedPADerivationSoundnessPredicate] cannot be substituted
  here: its [level : nat] is expanded metatheoretically.

  This module gives the missing invariant an honest finite
  [TemplateFormula].  Named parameters carry the two model-internal levels.
  The restricted-proof predicate, endpoint relation, proof-wide atomic,
  formula-coverage and rule-coverage certificates, assignment coverage, and
  quantifier-bound guard use the existing structural PA syntax.  The same
  proof-wide formula-coverage bound is linked to the current assignment so
  that recursive children inherit an honest admissibility witness.  Only the
  two relations which genuinely depend on the dynamically selected
  successor-truth formula remain opaque:

    - truth of every member of a proof context; and
    - truth of the conclusion formula.

  The universal soundness code is therefore no longer an unconstrained
  existential number.  It is exactly the structural translation of the
  displayed template.  The selected consistency target is likewise the
  structural translation of [restrictedPAConsistencyFormulaContext] at the
  *same* lower-level parameter; the target/template bridge proves that this
  is definitionally the raw graph-selected target code.

  Unlike Lean's theory-relative invariant, the Rocq invariant below is a
  context-preservation statement: it concludes truth only after assuming
  truth of the endpoint context.  Universal preservation therefore does not
  imply PA consistency on its own.  The graph-selected successor axiom-
  soundness root must first be connected to a uniform law saying that every
  witnessed, bounded, atomically adequate PA-axiom context is true.

  This module makes that extra dependency literal.  It defines the exact
  context-truth law using the *same* opaque context-truth predicate as the
  invariant.  A selected-axiom support package then carries, in the exact
  implication-tail context (before the universal invariant is assumed),

    - the staged [nextAxiomSoundness] proof root; and
    - a proof that this selected formula implies the context-truth law; and
    - the bottom-refutation law for the same selected conclusion-truth atom.

  These roots remain explicit proof-producing obligations and cannot depend
  circularly on the later universal-invariant assumption.  The remaining
  open compiler must carry their checked modus-ponens composite under that
  one literal head while opening the consistency target.  The final theorem
  performs implication
  introduction and identifies the graph-selected [nextFinal], but no longer
  discards the staged axiom-soundness dependency.  No semantic truth-to-proof
  conversion, standard-level substitution, dynamic soundness producer, or
  consistency successor is used.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedAssignment
  RawCodedProofRules
  RawCodedFixedLevelTruthTotality
  RawCodedContextBounds
  RawCodedProofAtomicAdequacy
  RawCodedProofFormulaCoverage
  RawCodedProofRuleCoverage
  RawCodedRestrictedPAProof
  RawCodedTemplateSyntax
  RawCodedTemplateStructuralTranslation
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedRestrictedTargetTemplateContext
  RawCodedRestrictedPAConsistencyTripleExDescent
  RawCodedRestrictedPAProjectedFieldRefutation
  RawCodedPALocalProofExistential
  RawCodedProofImpIConstructor
  RawCodedProofBinaryConstructors
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofComposition
  RawCodedDynamicTruthNativeFinalStagedRootCompilation.

Import ListNotations.

Module PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedContextBounds.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofFormulaCoverage.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedRestrictedTargetTemplateContext.
Import PABoundedRawCodedRestrictedPAConsistencyTripleExDescent.
Import PABoundedRawCodedRestrictedPAProjectedFieldRefutation.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.

(** ------------------------------------------------------------------
    The arbitrary-carrier derivation-soundness template. *)

Definition coqRestrictedPASoundnessLowerLevelParameterName
    : TemplateParameterName := 0.

Definition coqRestrictedPASoundnessUpperLevelParameterName
    : TemplateParameterName := 1.

Definition coqRestrictedPAContextTruthPredicateName
    : TemplatePredicateName := 0.

Definition coqRestrictedPAConclusionTruthPredicateName
    : TemplatePredicateName := 1.

Definition coqRestrictedPASoundnessLowerLevelTerm : TemplateTerm :=
  ttParameter coqRestrictedPASoundnessLowerLevelParameterName.

Definition coqRestrictedPASoundnessUpperLevelTerm : TemplateTerm :=
  ttParameter coqRestrictedPASoundnessUpperLevelParameterName.

(** Four endpoint witnesses are bound inside the unary predicate.  Their
    order agrees with the already audited standard-level spelling:

      context, conclusion, assignment code, assignment step.

    Hence, in the body, those values are [#3], [#2], [#1], and [#0], while
    the outer proof root has shifted to [#4]. *)

(** The occurrence-level restriction is kept as a named core because direct
    rule compilers still need to project precisely this dynamic-rank fact.
    The public premise below additionally carries the three proof-wide
    certificates which are stable under recursive-child descent. *)
Definition coqRestrictedPADerivationSoundnessRestrictedProofCoreTemplate
    : TemplateFormula :=
  restrictedTargetTemplateFormulaContext
    coqRestrictedPASoundnessLowerLevelTerm
    (restrictedTargetProofContext (tVar 4)).

Definition coqRestrictedPADerivationSoundnessProofWideCertificatesTemplate
    : TemplateFormula :=
  tfAnd
    (embedPAFormula
      (proofAtomicallyAdequateTermAt (tVar 4)))
    (tfAnd
      (embedPAFormula
        (proofHasFormulaCoverageTermAt (tVar 4)))
      (embedPAFormula
        (proofRuleCoverageTermAt (tVar 4)))).

Definition coqRestrictedPADerivationSoundnessRestrictedProofTemplate
    : TemplateFormula :=
  tfAnd
    coqRestrictedPADerivationSoundnessRestrictedProofCoreTemplate
    coqRestrictedPADerivationSoundnessProofWideCertificatesTemplate.

Definition coqRestrictedPADerivationSoundnessEndpointTemplate
    : TemplateFormula :=
  embedPAFormula
    (proofRuleValidTermAt (tVar 4) (tVar 3) (tVar 2)).

(** Dynamic counterpart of [fixedLevelTruthAdmissibleTermAt].  Keep the
    former conclusion-local condition available as a named core.  All fixed
    syntax remains embedded PA syntax; only the hierarchy-level hole in the
    Sigma/Pi domain test is filled by the named carrier parameter. *)
Definition coqRestrictedPADerivationSoundnessAdmissibleCoreTemplate
    : TemplateFormula :=
  tfAnd
    (embedPAFormula
      (codedFormulaAtomicallyAdequateTermAt (tVar 2)))
    (tfAnd
      (embedPAFormula
        (codedAssignmentDefinedThroughTermAt
          (tVar 1) (tVar 0) (tVar 2)))
      (restrictedTargetTemplateFormulaContext
        coqRestrictedPASoundnessLowerLevelTerm
        (restrictedTargetFormulaQuantifierBoundedContext (tVar 2)))).

(** A single hidden bound covers every formula in the proof and is also in
    the domain of the current beta assignment.  Before [pEx], the proof root
    and assignment pair occupy [#4], [#1], and [#0].  The fresh coverage
    witness occupies [#0]; the body therefore refers to those lifted outer
    values as [#5], [#2], and [#1], respectively. *)
Definition coqRestrictedPADerivationSoundnessCommonCoverageTemplate
    : TemplateFormula :=
  embedPAFormula
    (pEx
      (pAnd
        (proofFormulaCoverageTermAt
          (tVar 5) (tVar 0))
        (codedAssignmentDefinedThroughTermAt
          (tVar 2)
          (tVar 1)
          (tVar 0)))).

Definition coqRestrictedPADerivationSoundnessAdmissibleTemplate
    : TemplateFormula :=
  tfAnd
    coqRestrictedPADerivationSoundnessAdmissibleCoreTemplate
    coqRestrictedPADerivationSoundnessCommonCoverageTemplate.

(** These are the only opaque atoms.  Both explicitly carry the two named
    levels.  A concrete structural translation may close over the selected
    predecessor truth-formula code, but it must provide honest shift and
    opening trees for these applications through
    [RawCodedTemplateStructuralInputs]. *)
Definition coqRestrictedPADerivationSoundnessContextTruthTemplate
    : TemplateFormula :=
  tfOpaque coqRestrictedPAContextTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     ttVar 3; ttVar 1; ttVar 0].

Definition coqRestrictedPADerivationSoundnessConclusionTruthTemplate
    : TemplateFormula :=
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     ttVar 2; ttVar 1; ttVar 0].

(** The exact context-level consequence required before the preservation
    invariant can exclude a PA proof of falsity.  The outer binders are,
    in order, the axiom-witness list and the represented proof context, so
    their body occurrences are [#1] and [#0].  Boundedness uses the same
    lower-level parameter as restricted proof syntax, while the conclusion
    is the same opaque successor context-truth application used above, at
    the total zero assignment. *)
Definition coqRestrictedPAAxiomContextsTruthTemplate : TemplateFormula :=
  tfAll (tfAll
    (tfImp
      (embedPAFormula
        (codedPAAxiomWitnessContextTermAt (tVar 1) (tVar 0)))
      (tfImp
        (restrictedTargetTemplateFormulaContext
          coqRestrictedPASoundnessLowerLevelTerm
          (restrictedTargetContextAllBoundedContext (tVar 0)))
        (tfImp
          (embedPAFormula
            (contextAllAtomicallyAdequateTermAt (tVar 0)))
          (tfOpaque coqRestrictedPAContextTruthPredicateName
            [coqRestrictedPASoundnessLowerLevelTerm;
             coqRestrictedPASoundnessUpperLevelTerm;
             ttVar 0; ttZero; ttZero]))))).

(** The second exact truth coherence needed by consistency-from-soundness.
    After preservation is instantiated at the bottom endpoint and the total
    zero assignment, its opaque conclusion must imply object-level bottom.
    The formula-code argument is the ordinary PA term which denotes the code
    of [pBot], not a metatheoretically decoded carrier element. *)
Definition coqRestrictedPABottomTruthRefutationTemplate : TemplateFormula :=
  tfImp
    (tfOpaque coqRestrictedPAConclusionTruthPredicateName
      [coqRestrictedPASoundnessLowerLevelTerm;
       coqRestrictedPASoundnessUpperLevelTerm;
       embedPATerm rawFormulaBotCodeTerm; ttZero; ttZero])
    tfBot.

Definition coqRestrictedPADerivationSoundnessPredicateTemplate
    : TemplateFormula :=
  tfAll (tfAll (tfAll (tfAll
    (tfImp
      coqRestrictedPADerivationSoundnessRestrictedProofTemplate
      (tfImp
        coqRestrictedPADerivationSoundnessEndpointTemplate
        (tfImp
          coqRestrictedPADerivationSoundnessAdmissibleTemplate
          (tfImp
            coqRestrictedPADerivationSoundnessContextTruthTemplate
            coqRestrictedPADerivationSoundnessConclusionTruthTemplate))))))).

(** The exact invariant produced by represented strong induction on proof
    roots.  The extra [tfAll] binds the root of the unary predicate above. *)
Definition coqRestrictedPADerivationSoundnessUniversalTemplate
    : TemplateFormula :=
  tfAll coqRestrictedPADerivationSoundnessPredicateTemplate.

(** The right-hand side of Lean's fixed source implication, using the same
    lower-level parameter as the restricted-proof premise. *)
Definition coqRestrictedPAConsistencyFromUniversalSoundnessTargetTemplate
    : TemplateFormula :=
  restrictedTargetTemplateFormulaContext
    coqRestrictedPASoundnessLowerLevelTerm
    restrictedPAConsistencyFormulaContext.

Definition coqRestrictedPAConsistencyFromUniversalSoundnessBridgeTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADerivationSoundnessUniversalTemplate
    coqRestrictedPAConsistencyFromUniversalSoundnessTargetTemplate.

(** ------------------------------------------------------------------
    Exact raw-code views. *)

Definition rawCoqRestrictedPADerivationSoundnessPredicateCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawStructuralTemplateFormula inputs
    coqRestrictedPADerivationSoundnessPredicateTemplate.

Definition rawCoqRestrictedPADerivationSoundnessUniversalCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawStructuralTemplateFormula inputs
    coqRestrictedPADerivationSoundnessUniversalTemplate.

Definition rawCoqRestrictedPAAxiomContextsTruthCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawStructuralTemplateFormula inputs
    coqRestrictedPAAxiomContextsTruthTemplate.

Definition rawCoqRestrictedPABottomTruthRefutationCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawStructuralTemplateFormula inputs
    coqRestrictedPABottomTruthRefutationTemplate.

Definition rawCoqRestrictedPAConsistencyFromSoundnessTargetCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawStructuralTemplateFormula inputs
    coqRestrictedPAConsistencyFromUniversalSoundnessTargetTemplate.

Definition rawCoqRestrictedPAConsistencyFromSoundnessBridgeCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawStructuralTemplateFormula inputs
    coqRestrictedPAConsistencyFromUniversalSoundnessBridgeTemplate.

(** Keep the constructor equation polymorphic in its children.  Reducing the
    same equation after instantiating it with the sizeable soundness template
    makes Rocq normalize both children and consumes a prohibitive amount of
    memory. *)
Lemma rawStructuralTemplateFormula_imp_code : forall
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    left right,
  rawStructuralTemplateFormula inputs (tfImp left right) =
  rawFormulaImpCode M
    (rawStructuralTemplateFormula inputs left)
    (rawStructuralTemplateFormula inputs right).
Proof.
  reflexivity.
Qed.

Lemma rawStructuralTemplateFormula_all_code : forall
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) body,
  rawStructuralTemplateFormula inputs (tfAll body) =
  rawFormulaAllCode M (rawStructuralTemplateFormula inputs body).
Proof.
  reflexivity.
Qed.

Arguments rawCoqRestrictedPADerivationSoundnessPredicateCode M inputs
  : clear implicits.
Arguments rawCoqRestrictedPADerivationSoundnessUniversalCode M inputs
  : clear implicits.
Arguments rawCoqRestrictedPAAxiomContextsTruthCode M inputs
  : clear implicits.
Arguments rawCoqRestrictedPABottomTruthRefutationCode M inputs
  : clear implicits.
Arguments rawCoqRestrictedPAConsistencyFromSoundnessTargetCode M inputs
  : clear implicits.
Arguments rawCoqRestrictedPAConsistencyFromSoundnessBridgeCode M inputs
  : clear implicits.

(** Record each transparent definition once, before sealing it.  All later
    conversions proceed by these equations and never ask the kernel to
    normalize a concrete soundness formula. *)
Lemma raw_coqRestrictedPADerivationSoundnessPredicateCode_structural : forall
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M),
  rawCoqRestrictedPADerivationSoundnessPredicateCode M inputs =
  rawStructuralTemplateFormula inputs
    coqRestrictedPADerivationSoundnessPredicateTemplate.
Proof.
  reflexivity.
Qed.

Lemma raw_coqRestrictedPADerivationSoundnessUniversalCode_structural : forall
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M),
  rawCoqRestrictedPADerivationSoundnessUniversalCode M inputs =
  rawStructuralTemplateFormula inputs
    coqRestrictedPADerivationSoundnessUniversalTemplate.
Proof.
  reflexivity.
Qed.

Lemma raw_coqRestrictedPAAxiomContextsTruthCode_structural : forall
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M),
  rawCoqRestrictedPAAxiomContextsTruthCode M inputs =
  rawStructuralTemplateFormula inputs
    coqRestrictedPAAxiomContextsTruthTemplate.
Proof.
  reflexivity.
Qed.

Lemma raw_coqRestrictedPABottomTruthRefutationCode_structural : forall
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M),
  rawCoqRestrictedPABottomTruthRefutationCode M inputs =
  rawStructuralTemplateFormula inputs
    coqRestrictedPABottomTruthRefutationTemplate.
Proof.
  reflexivity.
Qed.

Lemma raw_coqRestrictedPAConsistencyFromSoundnessTargetCode_structural : forall
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M),
  rawCoqRestrictedPAConsistencyFromSoundnessTargetCode M inputs =
  rawStructuralTemplateFormula inputs
    coqRestrictedPAConsistencyFromUniversalSoundnessTargetTemplate.
Proof.
  reflexivity.
Qed.

Lemma raw_coqRestrictedPAConsistencyFromSoundnessBridgeCode_structural : forall
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M),
  rawCoqRestrictedPAConsistencyFromSoundnessBridgeCode M inputs =
  rawStructuralTemplateFormula inputs
    coqRestrictedPAConsistencyFromUniversalSoundnessBridgeTemplate.
Proof.
  reflexivity.
Qed.

Global Opaque
  rawCoqRestrictedPADerivationSoundnessPredicateCode
  rawCoqRestrictedPADerivationSoundnessUniversalCode
  rawCoqRestrictedPAAxiomContextsTruthCode
  rawCoqRestrictedPABottomTruthRefutationCode
  rawCoqRestrictedPAConsistencyFromSoundnessTargetCode
  rawCoqRestrictedPAConsistencyFromSoundnessBridgeCode.

Theorem raw_coqRestrictedPADerivationSoundnessUniversalCode_view : forall
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M),
  rawCoqRestrictedPADerivationSoundnessUniversalCode M inputs =
  rawFormulaAllCode M
    (rawCoqRestrictedPADerivationSoundnessPredicateCode M inputs).
Proof.
  intros M inputs.
  rewrite raw_coqRestrictedPADerivationSoundnessUniversalCode_structural.
  unfold coqRestrictedPADerivationSoundnessUniversalTemplate.
  rewrite rawStructuralTemplateFormula_all_code.
  now rewrite <-
    raw_coqRestrictedPADerivationSoundnessPredicateCode_structural.
Qed.

(** The new restricted-target/template bridge removes the enormous target
    normalization from this seam.  This equation is valid for every
    structural parameter code, including a nonstandard numeral-term code. *)
Theorem raw_coqRestrictedPAConsistencyFromSoundnessTargetCode_exact : forall
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M),
  rawCoqRestrictedPAConsistencyFromSoundnessTargetCode M inputs =
  rawRestrictedTargetFormulaContextCode M
    (rawStructuralTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm)
    restrictedPAConsistencyFormulaContext.
Proof.
  intros M inputs.
  rewrite raw_coqRestrictedPAConsistencyFromSoundnessTargetCode_structural.
  unfold coqRestrictedPAConsistencyFromUniversalSoundnessTargetTemplate.
  apply rawStructural_restrictedPAConsistencyTemplate.
Qed.

Theorem raw_coqRestrictedPAConsistencyFromSoundnessBridgeCode_view : forall
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M),
  rawCoqRestrictedPAConsistencyFromSoundnessBridgeCode M inputs =
  rawFormulaImpCode M
    (rawCoqRestrictedPADerivationSoundnessUniversalCode M inputs)
    (rawRestrictedTargetFormulaContextCode M
      (rawStructuralTemplateTerm inputs
        coqRestrictedPASoundnessLowerLevelTerm)
      restrictedPAConsistencyFormulaContext).
Proof.
  intros M inputs.
  etransitivity.
  - exact
      (raw_coqRestrictedPAConsistencyFromSoundnessBridgeCode_structural
        M inputs).
  - unfold coqRestrictedPAConsistencyFromUniversalSoundnessBridgeTemplate.
    etransitivity.
    + apply rawStructuralTemplateFormula_imp_code.
    + apply f_equal2.
      * symmetry.
        exact
          (raw_coqRestrictedPADerivationSoundnessUniversalCode_structural
            M inputs).
      * unfold
          coqRestrictedPAConsistencyFromUniversalSoundnessTargetTemplate.
        apply rawStructural_restrictedPAConsistencyTemplate.
Qed.

(** ------------------------------------------------------------------
    The selected axiom-soundness/context-truth support. *)

Definition rawCoqRestrictedPAConsistencyBridgeContextCode
    (M : RawPAModel) (numeralCode baseContext : M) : M :=
  rawRestrictedPAFieldsContextCode M numeralCode
    (rawRestrictedPACanonicalShiftedProofContextCode
      M baseContext numeralCode).

Arguments rawCoqRestrictedPAConsistencyBridgeContextCode
  M numeralCode baseContext : clear implicits.

Definition rawCoqRestrictedPAConsistencyBridgeBodyContextCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    (numeralCode baseContext : M) : M :=
  rawListNode M
    (rawCoqRestrictedPADerivationSoundnessUniversalCode M inputs)
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M numeralCode baseContext).

Arguments rawCoqRestrictedPAConsistencyBridgeBodyContextCode
  M inputs numeralCode baseContext : clear implicits.

(** A completely syntactic coherence package for the graph-selected axiom
    field.  The selected formula itself and a proof that it entails the
    displayed witnessed-context truth law have already been carried into the
    exact implication-tail context.  Requiring the literal witnessed PA-
    axiom base rules out the former, unimplementable quantification over
    arbitrary malformed context tails.

    This record does not assert that an arbitrary opaque interpretation has
    the desired property.  Constructing it must identify the two opaque
    truth applications with the same graph-selected successor formula and
    compile the finite axiom-to-context traversal proof.  The final field is
    the complementary bottom-refutation law for the selected conclusion-
    truth atom. *)
Definition RawCoqRestrictedPASelectedAxiomContextTruthSupport
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    (numeralCode witnessList baseContext nextAxiomSoundness
      nextAxiomSoundnessRoot coherenceRoot bottomRefutationRoot : M) : Prop :=
  RawCodedPAAxiomWitnessContext M witnessList baseContext /\
  RawCodedPALocalProofOf M
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M numeralCode baseContext)
    nextAxiomSoundness nextAxiomSoundnessRoot /\
  RawCodedPALocalProofOf M
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M numeralCode baseContext)
    (rawFormulaImpCode M nextAxiomSoundness
      (rawCoqRestrictedPAAxiomContextsTruthCode M inputs))
    coherenceRoot /\
  RawCodedPALocalProofOf M
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M numeralCode baseContext)
    (rawCoqRestrictedPABottomTruthRefutationCode M inputs)
    bottomRefutationRoot.

Arguments RawCoqRestrictedPASelectedAxiomContextTruthSupport
  M inputs numeralCode witnessList baseContext nextAxiomSoundness
    nextAxiomSoundnessRoot coherenceRoot bottomRefutationRoot
  : clear implicits.

Definition rawCoqRestrictedPAAxiomContextsTruthRoot
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    (numeralCode baseContext nextAxiomSoundness
      nextAxiomSoundnessRoot coherenceRoot : M) : M :=
  rawProofImpERoot M
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M numeralCode baseContext)
    nextAxiomSoundness
    (rawCoqRestrictedPAAxiomContextsTruthCode M inputs)
    coherenceRoot nextAxiomSoundnessRoot.

Arguments rawCoqRestrictedPAAxiomContextsTruthRoot
  M inputs numeralCode baseContext nextAxiomSoundness
    nextAxiomSoundnessRoot coherenceRoot : clear implicits.

(** The support package exposes an ordinary local proof of the context-truth
    law by one checked implication elimination. *)
Theorem raw_coqRestrictedPAAxiomContextsTruth_of_selected_support : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateStructuralInputs M)
      numeralCode witnessList baseContext nextAxiomSoundness
      nextAxiomSoundnessRoot coherenceRoot bottomRefutationRoot,
  RawCoqRestrictedPASelectedAxiomContextTruthSupport M inputs
    numeralCode witnessList baseContext nextAxiomSoundness
    nextAxiomSoundnessRoot coherenceRoot bottomRefutationRoot ->
  RawCodedPALocalProofOf M
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M numeralCode baseContext)
    (rawCoqRestrictedPAAxiomContextsTruthCode M inputs)
    (rawCoqRestrictedPAAxiomContextsTruthRoot M inputs
      numeralCode baseContext nextAxiomSoundness
      nextAxiomSoundnessRoot coherenceRoot).
Proof.
  intros M hPA inputs numeralCode witnessList baseContext
    nextAxiomSoundness nextAxiomSoundnessRoot coherenceRoot
    bottomRefutationRoot (_ & hnextAxiom & hcoherence & _).
  unfold rawCoqRestrictedPAAxiomContextsTruthRoot.
  exact (raw_codedPALocalProofOf_impE M hPA
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M numeralCode baseContext)
    nextAxiomSoundness
    (rawCoqRestrictedPAAxiomContextsTruthCode M inputs)
    coherenceRoot nextAxiomSoundnessRoot hcoherence hnextAxiom).
Qed.

(** The remaining fixed source compiler asks only for the body of implication
    introduction.  In contrast to the former interface, it is restricted to
    a witnessed PA-axiom base and receives the selected axiom/context-truth
    support explicitly.  A faithful Coq analogue of Lean's fixed bridge must
    carry both the resulting context-truth law and the bottom-refutation law
    under the one universal-invariant head, then use them when instantiating
    the context-preservation invariant.

    The interface remains pointwise in [inputs].  Quantifying over unrelated
    interpretations of the two opaque truth atoms would be false. *)
Definition RawCoqRestrictedPAConsistencyFromUniversalSoundnessOpenCompiler
    (M : RawPAModel)
    (inputs : RawCodedTemplateStructuralInputs M) : Prop :=
  forall numeralCode witnessList baseContext nextAxiomSoundness
      nextAxiomSoundnessRoot coherenceRoot bottomRefutationRoot,
    rawStructuralTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm = numeralCode ->
    RawCoqRestrictedPASelectedAxiomContextTruthSupport M inputs
      numeralCode witnessList baseContext nextAxiomSoundness
      nextAxiomSoundnessRoot coherenceRoot bottomRefutationRoot ->
    exists child : M,
      RawCodedPALocalProofOf M
        (rawCoqRestrictedPAConsistencyBridgeBodyContextCode
          M inputs numeralCode baseContext)
        (rawRestrictedTargetFormulaContextCode M numeralCode
          restrictedPAConsistencyFormulaContext)
        child.

Arguments
  RawCoqRestrictedPAConsistencyFromUniversalSoundnessOpenCompiler M inputs
  : clear implicits.

Definition rawCoqRestrictedPAConsistencyFromSoundnessBridgeRoot
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    (numeralCode baseContext child : M) : M :=
  rawProofImpIRoot M
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M numeralCode baseContext)
    (rawCoqRestrictedPADerivationSoundnessUniversalCode M inputs)
    (rawRestrictedTargetFormulaContextCode M numeralCode
      restrictedPAConsistencyFormulaContext)
    child.

Arguments rawCoqRestrictedPAConsistencyFromSoundnessBridgeRoot
  M inputs numeralCode baseContext child : clear implicits.

Theorem raw_coqRestrictedPAConsistencyFromSoundnessBridge_of_open : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall (inputs : RawCodedTemplateStructuralInputs M),
  RawCoqRestrictedPAConsistencyFromUniversalSoundnessOpenCompiler M inputs ->
  forall numeralCode witnessList baseContext nextAxiomSoundness
      nextAxiomSoundnessRoot coherenceRoot bottomRefutationRoot,
    rawStructuralTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm = numeralCode ->
    RawCoqRestrictedPASelectedAxiomContextTruthSupport M inputs
      numeralCode witnessList baseContext nextAxiomSoundness
      nextAxiomSoundnessRoot coherenceRoot bottomRefutationRoot ->
    exists bridgeRoot : M,
      RawCodedPALocalProofOf M
        (rawCoqRestrictedPAConsistencyBridgeContextCode
          M numeralCode baseContext)
        (rawCoqRestrictedPAConsistencyFromSoundnessBridgeCode M inputs)
        bridgeRoot.
Proof.
  intros M hPA inputs hopen numeralCode witnessList baseContext
    nextAxiomSoundness nextAxiomSoundnessRoot coherenceRoot
    bottomRefutationRoot hlevel hsupport.
  destruct (hopen numeralCode witnessList baseContext nextAxiomSoundness
    nextAxiomSoundnessRoot coherenceRoot bottomRefutationRoot
    hlevel hsupport)
    as [child hchild].
  exists (rawCoqRestrictedPAConsistencyFromSoundnessBridgeRoot M
    inputs numeralCode baseContext child).
  unfold rawCoqRestrictedPAConsistencyFromSoundnessBridgeRoot.
  rewrite raw_coqRestrictedPAConsistencyFromSoundnessBridgeCode_view,
    hlevel.
  exact (raw_codedPALocalProofOf_impI M hPA
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M numeralCode baseContext)
    (rawCoqRestrictedPADerivationSoundnessUniversalCode M inputs)
    (rawRestrictedTargetFormulaContextCode M numeralCode
      restrictedPAConsistencyFormulaContext)
    child hchild).
Qed.

(** ------------------------------------------------------------------
    Exact adapter to the final staged graph.

    This compiler returns only the middle root, pointwise at the same selected
    structural inputs.  The invariant root and the target-refutation root
    remain separate, as required by the three-link composition module. *)

(** Carry the graph-selected axiom-soundness proof and its syntactic
    truth-coherence proofs into the literal implication-tail context.  The
    staged prerequisites provide the selected root only over [baseContext].
    This compiler deliberately exposes the still-required guarded context
    transport and the fixed axiom-to-context proof instead of silently
    discarding them. *)
Definition RawDynamicTruthNativeFinalSelectedAxiomContextTruthSupportCompiler
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : Prop :=
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode witnessList baseContext,
    RawDynamicTruthNativeFinalStagedGraphTraceAt M tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode ->
    RawDynamicTruthNativeFinalStagedPrerequisitesOn M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness ->
    rawStructuralTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm = successorNumeralCode ->
    exists nextAxiomSoundnessRoot coherenceRoot bottomRefutationRoot : M,
      RawCoqRestrictedPASelectedAxiomContextTruthSupport M inputs
        successorNumeralCode witnessList baseContext nextAxiomSoundness
        nextAxiomSoundnessRoot coherenceRoot bottomRefutationRoot.

Arguments
  RawDynamicTruthNativeFinalSelectedAxiomContextTruthSupportCompiler M inputs
  : clear implicits.

Definition
    RawDynamicTruthNativeFinalConsistencyFromUniversalSoundnessCompiler
    (M : RawPAModel)
    (inputs : RawCodedTemplateStructuralInputs M) : Prop :=
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode witnessList baseContext,
    RawDynamicTruthNativeFinalStagedGraphTraceAt M tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode ->
    RawDynamicTruthNativeFinalStagedPrerequisitesOn M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness ->
    rawStructuralTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm = successorNumeralCode ->
    exists bridgeRoot : M,
      RawCodedPALocalProofOf M
        (rawCoqRestrictedPAConsistencyBridgeContextCode
          M successorNumeralCode baseContext)
        (rawFormulaImpCode M
          (rawCoqRestrictedPADerivationSoundnessUniversalCode M inputs)
          nextFinal)
        bridgeRoot.

Arguments
  RawDynamicTruthNativeFinalConsistencyFromUniversalSoundnessCompiler M inputs
  : clear implicits.

Theorem
    raw_dynamicTruthNativeFinalConsistencyFromUniversalSoundnessCompiler_of_open_and_axiom_support
    : forall (M : RawPAModel), RawPASatisfies M ->
  forall (inputs : RawCodedTemplateStructuralInputs M),
  RawCoqRestrictedPAConsistencyFromUniversalSoundnessOpenCompiler M inputs ->
  RawDynamicTruthNativeFinalSelectedAxiomContextTruthSupportCompiler
    M inputs ->
  RawDynamicTruthNativeFinalConsistencyFromUniversalSoundnessCompiler
    M inputs.
Proof.
  intros M hPA inputs hopen hsupportCompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    htrace hprerequisites hlevel.
  destruct (hsupportCompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    htrace hprerequisites hlevel) as
    (nextAxiomSoundnessRoot & coherenceRoot & bottomRefutationRoot &
      hsupport).
  destruct htrace as
    [hcurrent hnextLocal hnextCross hnextShift hnextSubstitution
      hnextAxiom hnextFinal hsource].
  destruct hsource as
    [hcurrentTarget hnumeral hnextTarget hsubstitution].
  destruct (raw_coqRestrictedPAConsistencyFromSoundnessBridge_of_open
    M hPA inputs hopen successorNumeralCode witnessList baseContext
    nextAxiomSoundness nextAxiomSoundnessRoot coherenceRoot
    bottomRefutationRoot hlevel hsupport)
    as [bridgeRoot hbridge].
  exists bridgeRoot.
  rewrite raw_coqRestrictedPAConsistencyFromSoundnessBridgeCode_view,
    hlevel in hbridge.
  now rewrite hnextTarget.
Qed.

End PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
