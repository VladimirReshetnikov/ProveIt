(**
  A fixed-level, unary proof-code soundness predicate.

  This is the first raw-syntax counterpart of Lean's
  [DynamicTruthRestrictedSoundnessPredicate].  The induction variable is a
  *proof code*, while [level] is a fixed metatheoretic natural.  In
  particular, none of the induction data below is the older induction on
  restriction levels.

  The Rocq proof calculus has one conclusion formula rather than a sequent.
  Its faithful invariant therefore says that every endpoint carried by a
  restricted proof root preserves the existing fixed-level Sigma truth
  relation.  Context truth and endpoint admissibility stay explicit, exactly
  as in [RawCodedRestrictedProofSoundness].

  The unary predicate [P(d)] and its strong prefix

      K(d) := forall e < d, P(e)

  are ordinary PA formulas with one free variable.  The final section quotes
  [K] and supplies all represented syntax-operation data consumed by
  [RawCodedPAClosureInductionCompiler].  It deliberately does not manufacture
  either the zero proof or the successor proof: those are the mathematical
  proof-producing obligations of represented strong induction.

  This standard-level slice is not yet the arbitrary carrier-level predicate
  needed by the uniform nonstandard theorem.  That later port must replace
  [level : nat] and the recursively expanded fixed truth certificate by a
  carrier-valued restriction graph and an opaque translated successor-truth
  application.  Keeping that boundary explicit prevents this module from
  silently proving only the standard cases and advertising them as uniform.
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedNumeralTermCode
  RawCodedFormulaOperations
  RawCodedFormulaOperationsStandardAdequacy
  RawCodedFormulaOperationsStandardRealization
  RawCodedFormulaDiagonalOperationComposition
  RawCodedScopedFormulaDiagonalSubstitution
  RawCodedUniversalClosureDiagonalSubstitution
  RawCodedStandardFormulaScopeTransport
  RawCodedPAAxiomWitness
  RawCodedProofRules
  RawCodedRestrictedProofTraversal
  RawCodedRestrictedPAProof
  RawCodedFixedLevelTruthTraversal
  RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelContextTruth
  RawCodedRestrictedProofSoundness
  RawCodedPAInductionAxiomCertificate
  RawCodedPAClosureInductionCompiler.

Module PABoundedRawCodedRestrictedPADerivationSoundnessPredicate.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaOperationsStandardAdequacy.
Import PABoundedRawCodedFormulaOperationsStandardRealization.
Import PABoundedRawCodedFormulaDiagonalOperationComposition.
Import PABoundedRawCodedScopedFormulaDiagonalSubstitution.
Import PABoundedRawCodedUniversalClosureDiagonalSubstitution.
Import PABoundedRawCodedStandardFormulaScopeTransport.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedRestrictedProofTraversal.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelContextTruth.
Import PABoundedRawCodedRestrictedProofSoundness.
Import PABoundedRawCodedPAInductionAxiomCertificate.
Import PABoundedRawCodedPAClosureInductionCompiler.

(** Four endpoint witnesses are bound inside the unary predicate. *)
Definition restrictedPADerivationSoundnessAll4 (body : formula) : formula :=
  pAll (pAll (pAll (pAll body))).

Lemma raw_restrictedPADerivationSoundness_eval_liftTerm_four : forall
    (M : RawPAModel) a b c d (e : nat -> M) input,
  raw_term_eval M
    (scons M a (scons M b (scons M c (scons M d e))))
    (liftTerm 4 input) = raw_term_eval M e input.
Proof.
  intros M a b c d e input. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro index.
  replace (index + 4) with (S (S (S (S index)))) by lia.
  reflexivity.
Qed.

(** [P(root)]: every valid endpoint of this restricted proof root maps a
    true context to a true conclusion.  Binder order in the body is
    [context, conclusion, assignmentCode, assignmentStep]. *)
Definition restrictedPADerivationSoundnessPredicateTermAt
    (level : nat) (root : term) : formula :=
  restrictedPADerivationSoundnessAll4
    (pImp
      (restrictedProofTermAt level (liftTerm 4 root))
      (pImp
        (proofRuleValidTermAt
          (liftTerm 4 root) (tVar 3) (tVar 2))
        (pImp
          (fixedLevelTruthAdmissibleTermAt level
            (tVar 2) (tVar 1) (tVar 0))
          (pImp
            (contextAllSigmaTrueTermAt (S level)
              (tVar 3) (tVar 1) (tVar 0))
            (fixedLevelSigmaTruthCertificateTermAt (S level)
              (tVar 2) (tVar 1) (tVar 0)))))).

Definition RawRestrictedPADerivationSoundnessAt
    (M : RawPAModel) (level : nat) (root : M) : Prop :=
  forall context conclusion assignmentCode assignmentStep,
    RawRestrictedProof M level root ->
    RawProofRuleValid M root context conclusion ->
    RawFixedLevelTruthAdmissible M level
      conclusion assignmentCode assignmentStep ->
    RawContextAllSigmaTrue M (S level)
      context assignmentCode assignmentStep ->
    RawFixedLevelSigmaTruthCertificate M (S level)
      conclusion assignmentCode assignmentStep.

Arguments RawRestrictedPADerivationSoundnessAt M level root
  : clear implicits.

Lemma raw_sat_restrictedPADerivationSoundnessPredicateTermAt_iff : forall
    (M : RawPAModel) e level root,
  raw_formula_sat M e
    (restrictedPADerivationSoundnessPredicateTermAt level root) <->
  RawRestrictedPADerivationSoundnessAt M level
    (raw_term_eval M e root).
Proof.
  intros M e level root.
  unfold restrictedPADerivationSoundnessPredicateTermAt,
    restrictedPADerivationSoundnessAll4,
    RawRestrictedPADerivationSoundnessAt.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_restrictedProofTermAt_iff.
  setoid_rewrite raw_sat_proofRuleValidTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelTruthAdmissibleTermAt_iff.
  setoid_rewrite raw_sat_contextAllSigmaTrueTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelSigmaTruthCertificateTermAt_iff.
  repeat setoid_rewrite
    raw_restrictedPADerivationSoundness_eval_liftTerm_four.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** The Lean-shaped strong prefix [K(current) = forall root < current,
    P(root)].  Notice that the endpoint witnesses remain inside [P]; this is
    the literal quantifier ordering of the source predicate, not a use of
    induction on [level]. *)
Definition restrictedPADerivationSoundnessPrefixTermAt
    (level : nat) (current : term) : formula :=
  pAll
    (pImp
      (Formula.ltTermAt (tVar 0) (liftTerm 1 current))
      (restrictedPADerivationSoundnessPredicateTermAt level (tVar 0))).

Definition RawRestrictedPADerivationSoundnessPrefix
    (M : RawPAModel) (level : nat) (current : M) : Prop :=
  forall root,
    rawLt M root current ->
    RawRestrictedPADerivationSoundnessAt M level root.

Arguments RawRestrictedPADerivationSoundnessPrefix M level current
  : clear implicits.

Lemma raw_sat_restrictedPADerivationSoundnessPrefixTermAt_iff : forall
    (M : RawPAModel) e level current,
  raw_formula_sat M e
    (restrictedPADerivationSoundnessPrefixTermAt level current) <->
  RawRestrictedPADerivationSoundnessPrefix M level
    (raw_term_eval M e current).
Proof.
  intros M e level current.
  unfold restrictedPADerivationSoundnessPrefixTermAt,
    RawRestrictedPADerivationSoundnessPrefix.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite
    raw_sat_restrictedPADerivationSoundnessPredicateTermAt_iff.
  setoid_rewrite raw_restrictedProof_eval_liftTerm_one.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** The prefix is propositionally the invariant already used by the raw
    semantic soundness proof.  The formulas are intentionally not identified
    syntactically: the older spelling floats the four endpoint quantifiers
    across the guard, whereas the Lean source keeps them inside [P(root)]. *)
Lemma raw_restrictedPADerivationSoundnessPrefix_iff_sigmaSoundBelow : forall
    (M : RawPAModel) level current,
  RawRestrictedPADerivationSoundnessPrefix M level current <->
  RawRestrictedProofSigmaSoundBelow M level current.
Proof.
  intros M level current. split.
  - intros hprefix root context conclusion assignmentCode assignmentStep
      hbelow hrestricted hvalid hadmissible hcontext.
    exact (hprefix root hbelow context conclusion
      assignmentCode assignmentStep hrestricted hvalid
      hadmissible hcontext).
  - intros hbelow root hroot context conclusion
      assignmentCode assignmentStep hrestricted hvalid
      hadmissible hcontext.
    exact (hbelow root context conclusion assignmentCode assignmentStep
      hroot hrestricted hvalid hadmissible hcontext).
Qed.

(** The represented strong-step premise, still at one fixed proof
    restriction level. *)
Definition restrictedPADerivationSoundnessStrongStepFormula
    (level : nat) : formula :=
  pAll
    (pImp
      (restrictedPADerivationSoundnessPrefixTermAt level (tVar 0))
      (restrictedPADerivationSoundnessPredicateTermAt level (tVar 0))).

Definition RawRestrictedPADerivationSoundnessStrongStep
    (M : RawPAModel) (level : nat) : Prop :=
  forall current,
    RawRestrictedPADerivationSoundnessPrefix M level current ->
    RawRestrictedPADerivationSoundnessAt M level current.

Arguments RawRestrictedPADerivationSoundnessStrongStep M level
  : clear implicits.

Lemma raw_sat_restrictedPADerivationSoundnessStrongStepFormula_iff : forall
    (M : RawPAModel) e level,
  raw_formula_sat M e
    (restrictedPADerivationSoundnessStrongStepFormula level) <->
  RawRestrictedPADerivationSoundnessStrongStep M level.
Proof.
  intros M e level.
  unfold restrictedPADerivationSoundnessStrongStepFormula,
    RawRestrictedPADerivationSoundnessStrongStep.
  cbn [raw_formula_sat].
  setoid_rewrite
    raw_sat_restrictedPADerivationSoundnessPrefixTermAt_iff.
  setoid_rewrite
    raw_sat_restrictedPADerivationSoundnessPredicateTermAt_iff.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** Stable names for the three exact quoted formulas. *)
Definition rawRestrictedPADerivationSoundnessPredicateCode
    (M : RawPAModel) (level : nat) : M :=
  rawQuotedFormulaCode M
    (restrictedPADerivationSoundnessPredicateTermAt level (tVar 0)).

Definition rawRestrictedPADerivationSoundnessPrefixCode
    (M : RawPAModel) (level : nat) : M :=
  rawQuotedFormulaCode M
    (restrictedPADerivationSoundnessPrefixTermAt level (tVar 0)).

Definition rawRestrictedPADerivationSoundnessStrongStepCode
    (M : RawPAModel) (level : nat) : M :=
  rawQuotedFormulaCode M
    (restrictedPADerivationSoundnessStrongStepFormula level).

Arguments rawRestrictedPADerivationSoundnessPredicateCode
  M level : clear implicits.
Arguments rawRestrictedPADerivationSoundnessPrefixCode
  M level : clear implicits.
Arguments rawRestrictedPADerivationSoundnessStrongStepCode
  M level : clear implicits.

(** The constructor-local soundness seam already used by the semantic raw
    proof analysis gives exactly this *proof-code* strong step. *)
Theorem raw_restrictedPADerivationSoundnessStrongStep_of_rule_sound : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawRestrictedProofRuleTruthSound M level ->
  RawRestrictedPADerivationSoundnessStrongStep M level.
Proof.
  intros M hPA level hlocal current hprefix
    context conclusion assignmentCode assignmentStep
    hrestricted hvalid hadmissible hcontext.
  apply (hlocal current context conclusion assignmentCode assignmentStep
    hrestricted hvalid hadmissible hcontext).
  intros nodeContext a b c t child1 child2 child3 hconstructor
    fields children hentry hfields child hchild
    childContext childConclusion hchildValid
    hchildAdmissible hchildContext.
  destruct (raw_restrictedProof_recursive_child M hPA level current
    hrestricted nodeContext a b c t child1 child2 child3 hconstructor
    fields children hentry hfields child hchild)
    as [hchildRestricted hchildBelow].
  exact (hprefix child hchildBelow
    childContext childConclusion assignmentCode assignmentStep
    hchildRestricted hchildValid hchildAdmissible hchildContext).
Qed.

(** ------------------------------------------------------------------
    Quoted ordinary-induction data for the strong prefix.

    PA's ordinary induction acts on [K], not on [level].  A proof of the
    strong-step formula is what later builds the successor proof for [K]. *)

Definition restrictedPADerivationSoundnessInductionSourceFormula
    (level : nat) : formula :=
  restrictedPADerivationSoundnessPrefixTermAt level (tVar 0).

Definition restrictedPADerivationSoundnessInductionShiftedFormula
    (level : nat) : formula :=
  standardPAAxiomInductionShifted
    (restrictedPADerivationSoundnessInductionSourceFormula level).

Definition restrictedPADerivationSoundnessInductionSuccessorFormula
    (level : nat) : formula :=
  standardPAAxiomInductionSuccessorInstance
    (restrictedPADerivationSoundnessInductionSourceFormula level).

Definition restrictedPADerivationSoundnessInductionZeroFormula
    (level : nat) : formula :=
  standardPAAxiomInductionZeroInstance
    (restrictedPADerivationSoundnessInductionSourceFormula level).

Definition restrictedPADerivationSoundnessInductionBodyFormula
    (level : nat) : formula :=
  standardPAAxiomInductionBody
    (restrictedPADerivationSoundnessInductionSourceFormula level).

Definition restrictedPADerivationSoundnessInductionAxiomFormula
    (level : nat) : formula :=
  Formula.sealPA
    (restrictedPADerivationSoundnessInductionBodyFormula level).

(** The following hypothesis isolates a purely syntactic fact.  It is kept
    explicit here because the current scope library has no compositional
    scope theorem for the recursively expanded fixed-level truth traversal.
    For each metatheoretic [level] the proposition is decidable by
    [standardFormulaScopedb]; it is not a semantic assumption. *)
Definition RestrictedPADerivationSoundnessPrefixScoped
    (level : nat) : Prop :=
  StandardFormulaScoped 1
    (restrictedPADerivationSoundnessInductionSourceFormula level).

Lemma restrictedPADerivationSoundnessInductionSuccessorFormula_scoped :
    forall level,
  RestrictedPADerivationSoundnessPrefixScoped level ->
  StandardFormulaScoped 1
    (restrictedPADerivationSoundnessInductionSuccessorFormula level).
Proof.
  intros level hsource.
  unfold restrictedPADerivationSoundnessInductionSuccessorFormula,
    standardPAAxiomInductionSuccessorInstance.
  rewrite standardFormulaShift_one_one_then_substitute_succ.
  apply (standardFormulaSubstitution_scoped 1 1
    (restrictedPADerivationSoundnessInductionSourceFormula level)
    Formula.substSuccVar).
  - exact hsource.
  - intros [|sourceIndex] hindex; [|lia].
    intros index hfree.
    cbn [Formula.substSuccVar Term.Free] in hfree. lia.
Qed.

Lemma restrictedPADerivationSoundnessInductionZeroFormula_closed :
    forall level,
  RestrictedPADerivationSoundnessPrefixScoped level ->
  StandardFormulaScoped 0
    (restrictedPADerivationSoundnessInductionZeroFormula level).
Proof.
  intros level hsource.
  unfold restrictedPADerivationSoundnessInductionZeroFormula,
    standardPAAxiomInductionZeroInstance.
  rewrite standardFormulaSingleSubstitution_zero.
  apply (standardFormulaSubstitution_scoped 1 0
    (restrictedPADerivationSoundnessInductionSourceFormula level)
    (Formula.instTerm tZero)).
  - exact hsource.
  - intros [|sourceIndex] hindex; [|lia].
    intros index hfree.
    cbn [Formula.instTerm Term.Free] in hfree. contradiction.
Qed.

Lemma restrictedPADerivationSoundnessInductionBodyFormula_closed :
    forall level,
  RestrictedPADerivationSoundnessPrefixScoped level ->
  StandardFormulaScoped 0
    (restrictedPADerivationSoundnessInductionBodyFormula level).
Proof.
  intros level hsource.
  unfold restrictedPADerivationSoundnessInductionBodyFormula,
    standardPAAxiomInductionBody.
  intros index hfree.
  cbn [Formula.Free] in hfree.
  destruct hfree as [[hzero | hstep] | hsourceFree].
  - exact (restrictedPADerivationSoundnessInductionZeroFormula_closed
      level hsource index hzero).
  - destruct hstep as [hsourceFree | hsuccessor].
    + pose proof (hsource (S index) hsourceFree). lia.
    + pose proof
        (restrictedPADerivationSoundnessInductionSuccessorFormula_scoped
          level hsource (S index) hsuccessor). lia.
  - pose proof (hsource (S index) hsourceFree). lia.
Qed.

Theorem raw_codedRestrictedPADerivationSoundnessInductionBody_diagonal :
    forall (M : RawPAModel), RawPASatisfies M -> forall
    level numeralBound numeralCode,
  RestrictedPADerivationSoundnessPrefixScoped level ->
  RawNumeralTermCodeAt M numeralBound numeralCode ->
  RawCodedFormulaDiagonalSubstitutionAtAllDepths M numeralCode
    (rawQuotedFormulaCode M
      (restrictedPADerivationSoundnessInductionBodyFormula level)).
Proof.
  intros M hPA level numeralBound numeralCode hscope hnumeral.
  unfold restrictedPADerivationSoundnessInductionBodyFormula,
    standardPAAxiomInductionBody.
  apply (raw_codedFormulaDiagonalSubstitutionAtAllDepths_inductionBody
    M hPA numeralCode
    (rawQuotedFormulaCode M
      (restrictedPADerivationSoundnessInductionSourceFormula level))
    (rawQuotedFormulaCode M
      (restrictedPADerivationSoundnessInductionSuccessorFormula level))
    (rawQuotedFormulaCode M
      (restrictedPADerivationSoundnessInductionZeroFormula level))).
  - exact (raw_codedFormulaDiagonalSubstitution_standard_positive
      M hPA numeralBound numeralCode
      (restrictedPADerivationSoundnessInductionSourceFormula level)
      hnumeral hscope).
  - exact (raw_codedFormulaDiagonalSubstitution_standard_positive
      M hPA numeralBound numeralCode
      (restrictedPADerivationSoundnessInductionSuccessorFormula level)
      hnumeral
      (restrictedPADerivationSoundnessInductionSuccessorFormula_scoped
        level hscope)).
  - exact (raw_codedFormulaDiagonalSubstitution_standard_closed
      M hPA numeralBound numeralCode
      (restrictedPADerivationSoundnessInductionZeroFormula level)
      hnumeral
      (restrictedPADerivationSoundnessInductionZeroFormula_closed
        level hscope)).
Qed.

Definition rawRestrictedPADerivationSoundnessInductionSourceCode
    (M : RawPAModel) (level : nat) : M :=
  rawQuotedFormulaCode M
    (restrictedPADerivationSoundnessInductionSourceFormula level).

Definition rawRestrictedPADerivationSoundnessInductionShiftedCode
    (M : RawPAModel) (level : nat) : M :=
  rawQuotedFormulaCode M
    (restrictedPADerivationSoundnessInductionShiftedFormula level).

Definition rawRestrictedPADerivationSoundnessInductionSuccessorCode
    (M : RawPAModel) (level : nat) : M :=
  rawQuotedFormulaCode M
    (restrictedPADerivationSoundnessInductionSuccessorFormula level).

Definition rawRestrictedPADerivationSoundnessInductionZeroCode
    (M : RawPAModel) (level : nat) : M :=
  rawQuotedFormulaCode M
    (restrictedPADerivationSoundnessInductionZeroFormula level).

Definition rawRestrictedPADerivationSoundnessInductionSourceAllCode
    (M : RawPAModel) (level : nat) : M :=
  rawFormulaAllCode M
    (rawRestrictedPADerivationSoundnessInductionSourceCode M level).

Definition rawRestrictedPADerivationSoundnessInductionStepImpCode
    (M : RawPAModel) (level : nat) : M :=
  rawFormulaImpCode M
    (rawRestrictedPADerivationSoundnessInductionSourceCode M level)
    (rawRestrictedPADerivationSoundnessInductionSuccessorCode M level).

Definition rawRestrictedPADerivationSoundnessInductionStepAllCode
    (M : RawPAModel) (level : nat) : M :=
  rawFormulaAllCode M
    (rawRestrictedPADerivationSoundnessInductionStepImpCode M level).

Definition rawRestrictedPADerivationSoundnessInductionPremiseCode
    (M : RawPAModel) (level : nat) : M :=
  rawFormulaAndCode M
    (rawRestrictedPADerivationSoundnessInductionZeroCode M level)
    (rawRestrictedPADerivationSoundnessInductionStepAllCode M level).

Definition rawRestrictedPADerivationSoundnessInductionBodyCode
    (M : RawPAModel) (level : nat) : M :=
  rawQuotedFormulaCode M
    (restrictedPADerivationSoundnessInductionBodyFormula level).

Definition rawRestrictedPADerivationSoundnessInductionClosureCount
    (M : RawPAModel) (level : nat) : M :=
  rawNumeralValue M
    (Formula.bound
      (restrictedPADerivationSoundnessInductionBodyFormula level)).

Definition rawRestrictedPADerivationSoundnessInductionAxiomCode
    (M : RawPAModel) (level : nat) : M :=
  rawQuotedFormulaCode M
    (restrictedPADerivationSoundnessInductionAxiomFormula level).

Arguments rawRestrictedPADerivationSoundnessInductionSourceCode
  M level : clear implicits.
Arguments rawRestrictedPADerivationSoundnessInductionShiftedCode
  M level : clear implicits.
Arguments rawRestrictedPADerivationSoundnessInductionSuccessorCode
  M level : clear implicits.
Arguments rawRestrictedPADerivationSoundnessInductionZeroCode
  M level : clear implicits.
Arguments rawRestrictedPADerivationSoundnessInductionSourceAllCode
  M level : clear implicits.
Arguments rawRestrictedPADerivationSoundnessInductionStepImpCode
  M level : clear implicits.
Arguments rawRestrictedPADerivationSoundnessInductionStepAllCode
  M level : clear implicits.
Arguments rawRestrictedPADerivationSoundnessInductionPremiseCode
  M level : clear implicits.
Arguments rawRestrictedPADerivationSoundnessInductionBodyCode
  M level : clear implicits.
Arguments rawRestrictedPADerivationSoundnessInductionClosureCount
  M level : clear implicits.
Arguments rawRestrictedPADerivationSoundnessInductionAxiomCode
  M level : clear implicits.

Theorem raw_codedRestrictedPADerivationSoundnessClosureInductionData :
    forall (M : RawPAModel), RawPASatisfies M -> forall
    level numeralBound numeralCode,
  RestrictedPADerivationSoundnessPrefixScoped level ->
  RawNumeralTermCodeAt M numeralBound numeralCode ->
  RawCodedPAClosureInductionData M numeralCode
    (rawRestrictedPADerivationSoundnessInductionSourceCode M level)
    (rawRestrictedPADerivationSoundnessInductionAxiomCode M level)
    (rawRestrictedPADerivationSoundnessInductionShiftedCode M level)
    (rawRestrictedPADerivationSoundnessInductionSuccessorCode M level)
    (rawRestrictedPADerivationSoundnessInductionZeroCode M level)
    (rawRestrictedPADerivationSoundnessInductionSourceAllCode M level)
    (rawRestrictedPADerivationSoundnessInductionStepImpCode M level)
    (rawRestrictedPADerivationSoundnessInductionStepAllCode M level)
    (rawRestrictedPADerivationSoundnessInductionPremiseCode M level)
    (rawRestrictedPADerivationSoundnessInductionBodyCode M level)
    (rawRestrictedPADerivationSoundnessInductionClosureCount M level).
Proof.
  intros M hPA level numeralBound numeralCode hscope hnumeral.
  unfold RawCodedPAClosureInductionData.
  repeat apply conj.
  - unfold rawRestrictedPADerivationSoundnessInductionSourceCode,
      rawRestrictedPADerivationSoundnessInductionShiftedCode,
      restrictedPADerivationSoundnessInductionShiftedFormula,
      standardPAAxiomInductionShifted.
    exact (raw_codedFormulaShift_standard M hPA 1 1
      (restrictedPADerivationSoundnessInductionSourceFormula level)).
  - rewrite <- rawQuotedTermCode_standard by exact hPA.
    unfold rawRestrictedPADerivationSoundnessInductionShiftedCode,
      rawRestrictedPADerivationSoundnessInductionSuccessorCode,
      restrictedPADerivationSoundnessInductionSuccessorFormula,
      standardPAAxiomInductionSuccessorInstance.
    exact (raw_codedFormulaSingleSubstitution_standard_recursive M hPA
      (tSucc (tVar 0))
      (restrictedPADerivationSoundnessInductionShiftedFormula level)).
  - rewrite <- rawQuotedTermCode_standard by exact hPA.
    unfold rawRestrictedPADerivationSoundnessInductionSourceCode,
      rawRestrictedPADerivationSoundnessInductionZeroCode,
      restrictedPADerivationSoundnessInductionZeroFormula,
      standardPAAxiomInductionZeroInstance.
    exact (raw_codedFormulaSingleSubstitution_standard_recursive M hPA
      tZero
      (restrictedPADerivationSoundnessInductionSourceFormula level)).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold rawRestrictedPADerivationSoundnessInductionPremiseCode,
      rawRestrictedPADerivationSoundnessInductionStepAllCode,
      rawRestrictedPADerivationSoundnessInductionStepImpCode,
      rawRestrictedPADerivationSoundnessInductionSourceAllCode,
      rawRestrictedPADerivationSoundnessInductionZeroCode,
      rawRestrictedPADerivationSoundnessInductionSuccessorCode,
      rawRestrictedPADerivationSoundnessInductionSourceCode,
      rawRestrictedPADerivationSoundnessInductionBodyCode,
      restrictedPADerivationSoundnessInductionBodyFormula,
      standardPAAxiomInductionBody.
    reflexivity.
  - unfold rawRestrictedPADerivationSoundnessInductionBodyCode,
      rawRestrictedPADerivationSoundnessInductionClosureCount.
    exact (raw_codedFormulaBound_standard M hPA
      (restrictedPADerivationSoundnessInductionBodyFormula level)).
  - unfold rawRestrictedPADerivationSoundnessInductionClosureCount,
      rawRestrictedPADerivationSoundnessInductionBodyCode,
      rawRestrictedPADerivationSoundnessInductionAxiomCode,
      restrictedPADerivationSoundnessInductionAxiomFormula,
      Formula.sealPA.
    exact (raw_codedUniversalClosure_standard M hPA
      (Formula.bound
        (restrictedPADerivationSoundnessInductionBodyFormula level))
      (restrictedPADerivationSoundnessInductionBodyFormula level)).
  - apply (raw_codedUniversalClosureSelfInstantiationThrough_of_diagonal
      M hPA numeralCode
      (rawRestrictedPADerivationSoundnessInductionBodyCode M level)
      (rawRestrictedPADerivationSoundnessInductionClosureCount M level)).
    unfold rawRestrictedPADerivationSoundnessInductionBodyCode.
    exact (raw_codedRestrictedPADerivationSoundnessInductionBody_diagonal
      M hPA level numeralBound numeralCode hscope hnumeral).
Qed.

End PABoundedRawCodedRestrictedPADerivationSoundnessPredicate.
