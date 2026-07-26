(**
  Deep ternary closure and capture-avoiding opening.

  The deep-closure invariant fixes a predicate under substitution only when
  the replacement is honestly represented term syntax.  This is the exact
  boundary at which an opening theorem is sound: the legacy unguarded
  relation quantifies every carrier value as a replacement, including values
  which cannot be the source of a represented term operation.

  This module therefore first states the guarded relation-level theorem.  It
  also isolates the two concrete lower substitution laws and the small source
  syntax fact needed to recover the guard from an incoming substitution atom.
  Once those three facts are available, the public selector law has exactly
  the existing [RawCodedTernaryApplicationOpeningCommutingOnSyntax] type.

  The lower laws are kept in an explicit record so that their substantial
  represented-induction proof remains independent of this short ternary
  assembly argument.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedAssignment
  RawCodedAssignmentTotality
  RawCodedFormulaOperations
  RawCodedFormulaRankTotality
  RawCodedFormulaSingleSubstitutionAtomicAdequacy
  RawCodedTermEvaluationRealization
  RawCodedTermOpeningAfterShiftSyntaxStability
  RawCodedTemplateTernaryApplication
  RawCodedTemplateTernaryApplicationFunctionality
  RawCodedTernaryPredicateDeepClosure.

Module PABoundedRawCodedTernaryPredicateDeepClosureOpeningInterchange.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedAssignmentTotality.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedFormulaSingleSubstitutionAtomicAdequacy.
Import PABoundedRawCodedTermEvaluationRealization.
Import PABoundedRawCodedTermOpeningAfterShiftSyntaxStability.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTemplateTernaryApplicationFunctionality.
Import PABoundedRawCodedTernaryPredicateDeepClosure.

(** The two lower algebra laws needed by the generic ternary assembly.  A
    syntax guard is retained because the concrete proof may use represented
    totality for the replacement.  Every actual substitution atom supplies
    this guard through [RawCodedFormulaSubstitutionAtomSourceSyntax] below. *)
Record RawCodedFormulaSubstitutionAtomConcreteLawsOnSyntax
    (M : RawPAModel) : Prop := {
  rawFormulaSubstitutionAtom_protective_on_syntax :
    forall replacement,
      RawCodedTermSyntax M replacement ->
      RawCodedFormulaOperationProtectiveShiftStable M
        (RawCodedFormulaSubstitutionAtom M) replacement;
  rawFormulaSubstitutionAtom_interchange_on_syntax :
    forall replacement,
      RawCodedTermSyntax M replacement ->
      RawCodedFormulaOperationSingleSubstitutionInterchange M
        (RawCodedFormulaSubstitutionAtom M) replacement
}.

Arguments RawCodedFormulaSubstitutionAtomConcreteLawsOnSyntax M
  : clear implicits.

(** A represented substitution atom contains a shift trace whose source is
    its displayed replacement.  This interface names the corresponding
    source-syntax projection without baking its independent support-table
    construction into the ternary theorem. *)
Definition RawCodedFormulaSubstitutionAtomSourceSyntax
    (M : RawPAModel) : Prop :=
  forall replacement depth input output,
    RawCodedFormulaSubstitutionAtom M replacement depth input output ->
    RawCodedTermSyntax M replacement.

Arguments RawCodedFormulaSubstitutionAtomSourceSyntax M : clear implicits.

(** The relation-level contract with the only honest extra premise made
    explicit.  The assignment columns are exposed because that is precisely
    the certificate consumed by deep closure. *)
Definition RawCodedTernaryApplicationOpeningInterchangeOnRealizableReplacement
    (M : RawPAModel) (predicate : M) : Prop :=
  forall replacement assignmentCode assignmentStep,
    RawTermSyntaxRealizable M replacement assignmentCode assignmentStep ->
  forall depth
      first openedFirst second openedSecond third openedThird sourceOutput,
    RawCodedFormulaSubstitutionAtom M
      replacement depth first openedFirst ->
    RawCodedFormulaSubstitutionAtom M
      replacement depth second openedSecond ->
    RawCodedFormulaSubstitutionAtom M
      replacement depth third openedThird ->
    RawCodedTernaryApplication M
      predicate first second third sourceOutput ->
    exists targetOutput : M,
      RawCodedTernaryApplication M predicate
        openedFirst openedSecond openedThird targetOutput /\
      RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
        replacement depth sourceOutput targetOutput.

Arguments
  RawCodedTernaryApplicationOpeningInterchangeOnRealizableReplacement
  M predicate : clear implicits.

(** Passing three public arguments raises the internal operation depth by
    three, hence it is always above the ternary root cutoff. *)
Lemma raw_deepOpening_three_le_triple_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall depth : M,
  rawLe M (rawNumeralValue M 3)
    (raw_succ M (raw_succ M (raw_succ M depth))).
Proof.
  intros M hPA depth.
  change (rawLe M
    (raw_succ M (raw_succ M (raw_succ M (raw_zero M))))
    (raw_succ M (raw_succ M (raw_succ M depth)))).
  apply raw_rank_succ_le; [exact hPA |].
  apply raw_rank_succ_le; [exact hPA |].
  apply raw_rank_succ_le; [exact hPA |].
  apply raw_rank_zero_le. exact hPA.
Qed.

(** The target of a substitution atom is honest syntax when its replacement
    is.  The unconditional PA stability theorem does the real work; all-zero
    assignment columns merely package the existential public interface. *)
Lemma raw_codedFormulaSubstitutionAtom_target_syntax_of_realizable : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    replacement assignmentCode assignmentStep depth input output,
  RawTermSyntaxRealizable M replacement assignmentCode assignmentStep ->
  RawCodedFormulaSubstitutionAtom M replacement depth input output ->
  RawCodedTermSyntax M output.
Proof.
  intros M hPA replacement assignmentCode assignmentStep
    depth input output hreplacement hatom.
  exists (raw_zero M), (raw_zero M).
  apply (raw_codedFormulaSubstitutionAtom_target_syntax_of_opening_stable
    M (raw_codedTermOpeningAfterShiftSyntaxStable_of_PA M hPA)
    replacement depth input output hatom
    assignmentCode assignmentStep hreplacement
    (raw_zero M) (raw_zero M) (raw_succ M output)).
  - exact (raw_assignment_lt_self_succ M hPA output).
  - exact (raw_codedZeroAssignment_defined_all M hPA
      (raw_succ M output)).
Qed.

(** Deep closure supplies predicate fixedness at the arbitrary nonstandard
    depth reached after three applications.  The concrete lower laws then
    assemble the three substitution squares. *)
Theorem
    raw_codedTernaryApplicationOpeningInterchangeOnRealizableReplacement_of_deepClosed :
  forall (M : RawPAModel), RawPASatisfies M -> forall predicate,
  RawCodedFormulaSubstitutionAtomConcreteLawsOnSyntax M ->
  RawCodedTernaryPredicateDeepClosed M predicate ->
  RawCodedTernaryApplicationOpeningInterchangeOnRealizableReplacement
    M predicate.
Proof.
  intros M hPA predicate hlaws
    [hadequate [_ hpredicate]]
    replacement assignmentCode assignmentStep hreplacement
    depth first openedFirst second openedSecond third openedThird
    sourceOutput hfirst hsecond hthird hsource.
  assert (hreplacementSyntax : RawCodedTermSyntax M replacement).
  { exists assignmentCode, assignmentStep. exact hreplacement. }
  pose proof
    (rawFormulaSubstitutionAtom_protective_on_syntax
      M hlaws replacement hreplacementSyntax) as hprotect.
  pose proof
    (rawFormulaSubstitutionAtom_interchange_on_syntax
      M hlaws replacement hreplacementSyntax) as hinterchange.
  apply (raw_codedTernaryApplication_opening_interchange_on_syntax_of_laws
    M hPA predicate replacement depth
    first openedFirst second openedSecond third openedThird sourceOutput
    hadequate hprotect hinterchange).
  - apply (hpredicate replacement assignmentCode assignmentStep
      (raw_succ M (raw_succ M (raw_succ M depth))) hreplacement).
    apply raw_deepOpening_three_le_triple_succ. exact hPA.
  - exact (raw_codedFormulaSubstitutionAtom_target_syntax_of_realizable
      M hPA replacement assignmentCode assignmentStep
      depth first openedFirst hreplacement hfirst).
  - exact (raw_codedFormulaSubstitutionAtom_target_syntax_of_realizable
      M hPA replacement assignmentCode assignmentStep
      depth second openedSecond hreplacement hsecond).
  - exact (raw_codedFormulaSubstitutionAtom_target_syntax_of_realizable
      M hPA replacement assignmentCode assignmentStep
      depth third openedThird hreplacement hthird).
  - exact hfirst.
  - exact hsecond.
  - exact hthird.
  - exact hsource.
Qed.

(** Although the legacy relation does not display a syntax guard, each use
    supplies three substitution atoms.  The first atom already certifies
    that its replacement is the source of a represented term shift.  Thus,
    once the independent source-syntax projection is proved, the apparently
    arbitrary replacement is genuinely justified and the legacy relation is
    a sound corollary of the guarded theorem. *)
Theorem raw_codedTernaryApplicationOpeningInterchange_of_deepClosed :
  forall (M : RawPAModel), RawPASatisfies M -> forall predicate,
  RawCodedFormulaSubstitutionAtomConcreteLawsOnSyntax M ->
  RawCodedFormulaSubstitutionAtomSourceSyntax M ->
  RawCodedTernaryPredicateDeepClosed M predicate ->
  RawCodedTernaryApplicationOpeningInterchange M predicate.
Proof.
  intros M hPA predicate hlaws hsourceSyntax hdeep
    replacement depth first openedFirst second openedSecond
    third openedThird sourceOutput hfirst hsecond hthird hsource.
  destruct (hsourceSyntax replacement depth first openedFirst hfirst)
    as (assignmentCode & assignmentStep & hreplacement).
  exact
    (raw_codedTernaryApplicationOpeningInterchangeOnRealizableReplacement_of_deepClosed
      M hPA predicate hlaws hdeep
      replacement assignmentCode assignmentStep hreplacement depth
      first openedFirst second openedSecond third openedThird sourceOutput
      hfirst hsecond hthird hsource).
Qed.

(** An incoming atom recovers the missing replacement certificate, so the
    guarded relational theorem is enough to establish the existing selector
    contract.  Importantly, no unguarded relation-level claim is made. *)
Theorem rawTernaryApplicationSelector_opening_commuting_on_syntax_of_deepClosed :
  forall (M : RawPAModel), RawPASatisfies M -> forall predicate
    (selector : RawCodedTernaryApplicationSelector M predicate),
  RawCodedFormulaSubstitutionAtomConcreteLawsOnSyntax M ->
  RawCodedFormulaSubstitutionAtomSourceSyntax M ->
  RawCodedTernaryPredicateDeepClosed M predicate ->
  RawCodedTernaryApplicationOpeningCommutingOnSyntax
    M predicate selector.
Proof.
  intros M hPA predicate selector hlaws hsourceSyntax hdeep.
  apply (rawTernaryApplicationSelector_opening_commuting_on_syntax
    M hPA predicate selector).
  exact (raw_codedTernaryApplicationOpeningInterchange_of_deepClosed
    M hPA predicate hlaws hsourceSyntax hdeep).
Qed.

End PABoundedRawCodedTernaryPredicateDeepClosureOpeningInterchange.
