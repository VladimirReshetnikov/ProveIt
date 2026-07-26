(**
  Functionality and the honest selector boundary for ternary application.

  Cross-trace functionality makes the five-step application relation itself
  functional.  Thus every selector agrees on the represented syntax domain,
  even when its constituent shift/substitution traces were chosen
  independently.

  The original selector deliberately says nothing off that domain.  A global
  commutation law therefore needs either an operation-to-syntax recovery
  theorem or explicit syntax premises; it does not follow from the selector
  record alone.  This module records the domain-explicit laws and proves that
  their only remaining input is *relational* interchange existence.  Selector
  coherence is no longer a separate assumption.
*)

From Stdlib Require Import List Arith.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedFormulaOperations RawCodedFixedLevelTruthTotality
  RawCodedTemplateTernaryApplication
  RawCodedTermOperationCrossTraceFunctionality
  RawCodedFormulaOperationCrossTraceFunctionality.

Module PABoundedRawCodedTemplateTernaryApplicationFunctionality.

Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTermOperationCrossTraceFunctionality.
Import PABoundedRawCodedFormulaOperationCrossTraceFunctionality.

(** All five independently packaged traces have unique endpoints. *)
Theorem raw_codedTernaryApplication_functional : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      predicate first second third output output',
  RawCodedTernaryApplication M
    predicate first second third output ->
  RawCodedTernaryApplication M
    predicate first second third output' ->
  output = output'.
Proof.
  intros M hPA predicate first second third output output'
    (firstLifted & secondLifted & firstResult & secondResult &
     hfirstShift & hsecondShift & hfirstSubstitution &
     hsecondSubstitution & hthirdSubstitution)
    (firstLifted' & secondLifted' & firstResult' & secondResult' &
     hfirstShift' & hsecondShift' & hfirstSubstitution' &
     hsecondSubstitution' & hthirdSubstitution').
  pose proof (raw_codedTermShift_functional M hPA
    (raw_zero M) (rawNumeralValue M 2) first
    firstLifted firstLifted' hfirstShift hfirstShift') as hfirstLifted.
  pose proof (raw_codedTermShift_functional M hPA
    (raw_zero M) (rawNumeralValue M 1) second
    secondLifted secondLifted' hsecondShift hsecondShift') as hsecondLifted.
  subst firstLifted'. subst secondLifted'.
  pose proof (raw_codedFormulaSingleSubstitution_functional M hPA
    firstLifted predicate firstResult firstResult'
    hfirstSubstitution hfirstSubstitution') as hfirstResult.
  subst firstResult'.
  pose proof (raw_codedFormulaSingleSubstitution_functional M hPA
    secondLifted firstResult secondResult secondResult'
    hsecondSubstitution hsecondSubstitution') as hsecondResult.
  subst secondResult'.
  exact (raw_codedFormulaSingleSubstitution_functional M hPA
    third secondResult output output'
    hthirdSubstitution hthirdSubstitution').
Qed.

(** Every selector value is the unique relational output on honest inputs. *)
Corollary rawTernaryApplicationOutput_unique : forall
    (M : RawPAModel), RawPASatisfies M -> forall predicate
    (selector : RawCodedTernaryApplicationSelector M predicate)
    first second third output,
  RawCodedTermSyntax M first ->
  RawCodedTermSyntax M second ->
  RawCodedTermSyntax M third ->
  RawCodedTernaryApplication M
    predicate first second third output ->
  rawTernaryApplicationOutput selector first second third = output.
Proof.
  intros M hPA predicate selector first second third output
    hfirst hsecond hthird houtput.
  exact (raw_codedTernaryApplication_functional M hPA
    predicate first second third
    (rawTernaryApplicationOutput selector first second third) output
    (rawTernaryApplicationOutput_trace selector
      first second third hfirst hsecond hthird)
    houtput).
Qed.

Corollary rawTernaryApplicationSelectors_agree_on_syntax : forall
    (M : RawPAModel), RawPASatisfies M -> forall predicate
    (left right : RawCodedTernaryApplicationSelector M predicate)
    first second third,
  RawCodedTermSyntax M first ->
  RawCodedTermSyntax M second ->
  RawCodedTermSyntax M third ->
  rawTernaryApplicationOutput left first second third =
  rawTernaryApplicationOutput right first second third.
Proof.
  intros M hPA predicate left right first second third
    hfirst hsecond hthird.
  exact (raw_codedTernaryApplication_functional M hPA
    predicate first second third
    (rawTernaryApplicationOutput left first second third)
    (rawTernaryApplicationOutput right first second third)
    (rawTernaryApplicationOutput_trace left
      first second third hfirst hsecond hthird)
    (rawTernaryApplicationOutput_trace right
      first second third hfirst hsecond hthird)).
Qed.

(** ------------------------------------------------------------------
    Relation-level interchange existence.

    These contracts mention no selector.  They ask only for construction of
    one commuting output trace.  Cross-trace functionality above then forces
    every honest selector to choose that same output. *)

Definition RawCodedTernaryApplicationShiftInterchange
    (M : RawPAModel) (predicate : M) : Prop :=
  forall cutoff amount
      first shiftedFirst second shiftedSecond third shiftedThird
      sourceOutput : M,
    RawCodedTermShift M cutoff amount first shiftedFirst ->
    RawCodedTermShift M cutoff amount second shiftedSecond ->
    RawCodedTermShift M cutoff amount third shiftedThird ->
    RawCodedTernaryApplication M
      predicate first second third sourceOutput ->
    exists targetOutput : M,
      RawCodedTernaryApplication M predicate
        shiftedFirst shiftedSecond shiftedThird targetOutput /\
      RawCodedFormulaShift M cutoff amount sourceOutput targetOutput.

Arguments RawCodedTernaryApplicationShiftInterchange
  M predicate : clear implicits.

Definition RawCodedTernaryApplicationOpeningInterchange
    (M : RawPAModel) (predicate : M) : Prop :=
  forall replacement depth
      first openedFirst second openedSecond third openedThird
      sourceOutput : M,
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

Arguments RawCodedTernaryApplicationOpeningInterchange
  M predicate : clear implicits.

(** ------------------------------------------------------------------
    The smallest lower-level laws which construct either interchange.

    [rawFormulaOperation_singleSubstitution_interchange] is the genuine
    cross-trace square.  The outer operation at [S depth] acts on the source
    formula before one opening, while its atom at [depth] acts on the
    replacement.  The result is the outer operation after the opening.

    The two protective fields state that the same atom operation can be
    transported through the fixed lifts used by ternary application. *)

Definition RawCodedFormulaOperationSingleSubstitutionInterchange
    (M : RawPAModel) (atom : M -> M -> M -> M -> Prop)
    (parameter : M) : Prop :=
  forall depth replacement transformedReplacement
      input transformedInput output transformedOutput : M,
    atom parameter depth replacement transformedReplacement ->
    RawCodedFormulaOperation M atom parameter (raw_succ M depth)
      input transformedInput ->
    RawCodedFormulaSingleSubstitution M replacement input output ->
    RawCodedFormulaSingleSubstitution M
      transformedReplacement transformedInput transformedOutput ->
    RawCodedFormulaOperation M atom parameter depth
      output transformedOutput.

Arguments RawCodedFormulaOperationSingleSubstitutionInterchange
  M atom parameter : clear implicits.

Record RawCodedFormulaOperationProtectiveShiftStable
    (M : RawPAModel) (atom : M -> M -> M -> M -> Prop)
    (parameter : M) : Prop := {
  rawFormulaOperation_protect_one :
    forall depth input transformedInput liftedInput liftedTransformedInput,
      atom parameter depth input transformedInput ->
      RawCodedTermShift M
        (raw_zero M) (rawNumeralValue M 1) input liftedInput ->
      RawCodedTermShift M
        (raw_zero M) (rawNumeralValue M 1)
        transformedInput liftedTransformedInput ->
      atom parameter (raw_succ M depth)
        liftedInput liftedTransformedInput;
  rawFormulaOperation_protect_two :
    forall depth input transformedInput liftedInput liftedTransformedInput,
      atom parameter depth input transformedInput ->
      RawCodedTermShift M
        (raw_zero M) (rawNumeralValue M 2) input liftedInput ->
      RawCodedTermShift M
        (raw_zero M) (rawNumeralValue M 2)
        transformedInput liftedTransformedInput ->
      atom parameter (raw_succ M (raw_succ M depth))
        liftedInput liftedTransformedInput
}.

(** Three uses of the one-opening square assemble the complete ternary
    diagram.  No selector or functionality argument occurs in this proof. *)
Theorem raw_codedTernaryApplication_operation_interchange : forall
    (M : RawPAModel) predicate
    (atom : M -> M -> M -> M -> Prop) parameter,
  RawCodedFormulaOperationProtectiveShiftStable M atom parameter ->
  RawCodedFormulaOperationSingleSubstitutionInterchange
    M atom parameter ->
  forall depth
      first transformedFirst second transformedSecond
      third transformedThird sourceOutput targetOutput,
  RawCodedFormulaOperation M atom parameter
    (raw_succ M (raw_succ M (raw_succ M depth)))
    predicate predicate ->
  atom parameter depth first transformedFirst ->
  atom parameter depth second transformedSecond ->
  atom parameter depth third transformedThird ->
  RawCodedTernaryApplication M
    predicate first second third sourceOutput ->
  RawCodedTernaryApplication M predicate
    transformedFirst transformedSecond transformedThird targetOutput ->
  RawCodedFormulaOperation M atom parameter depth
    sourceOutput targetOutput.
Proof.
  intros M predicate atom parameter hprotect hinterchange depth
    first transformedFirst second transformedSecond third transformedThird
    sourceOutput targetOutput hpredicate
    hfirstAtom hsecondAtom hthirdAtom
    (firstLifted & secondLifted & firstResult & secondResult &
     hfirstShift & hsecondShift & hfirstSubstitution &
     hsecondSubstitution & hthirdSubstitution)
    (transformedFirstLifted & transformedSecondLifted &
     transformedFirstResult & transformedSecondResult &
     htransformedFirstShift & htransformedSecondShift &
     htransformedFirstSubstitution & htransformedSecondSubstitution &
     htransformedThirdSubstitution).
  pose proof (rawFormulaOperation_protect_two
    M atom parameter hprotect depth
    first transformedFirst firstLifted transformedFirstLifted
    hfirstAtom hfirstShift htransformedFirstShift) as hfirstLiftedAtom.
  pose proof (rawFormulaOperation_protect_one
    M atom parameter hprotect depth
    second transformedSecond secondLifted transformedSecondLifted
    hsecondAtom hsecondShift htransformedSecondShift) as hsecondLiftedAtom.
  pose proof (hinterchange
    (raw_succ M (raw_succ M depth))
    firstLifted transformedFirstLifted predicate predicate
    firstResult transformedFirstResult
    hfirstLiftedAtom hpredicate
    hfirstSubstitution htransformedFirstSubstitution) as hfirstResult.
  pose proof (hinterchange (raw_succ M depth)
    secondLifted transformedSecondLifted
    firstResult transformedFirstResult
    secondResult transformedSecondResult
    hsecondLiftedAtom hfirstResult
    hsecondSubstitution htransformedSecondSubstitution) as hsecondResult.
  exact (hinterchange depth third transformedThird
    secondResult transformedSecondResult sourceOutput targetOutput
    hthirdAtom hsecondResult hthirdSubstitution
    htransformedThirdSubstitution).
Qed.

(** Shift and opening require no further ternary algebra.  Once a target
    application trace exists on the honest syntax domain, the preceding
    theorem constructs the desired outer operation directly. *)

Theorem raw_codedTernaryApplication_shift_interchange_on_syntax_of_laws :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    predicate cutoff amount
    first shiftedFirst second shiftedSecond third shiftedThird sourceOutput,
  RawCodedFormulaAtomicallyAdequate M predicate ->
  RawCodedFormulaOperationProtectiveShiftStable M
    (RawCodedFormulaShiftAtom M) amount ->
  RawCodedFormulaOperationSingleSubstitutionInterchange M
    (RawCodedFormulaShiftAtom M) amount ->
  RawCodedFormulaShift M
    (raw_succ M (raw_succ M (raw_succ M cutoff))) amount
    predicate predicate ->
  RawCodedTermSyntax M shiftedFirst ->
  RawCodedTermSyntax M shiftedSecond ->
  RawCodedTermSyntax M shiftedThird ->
  RawCodedTermShift M cutoff amount first shiftedFirst ->
  RawCodedTermShift M cutoff amount second shiftedSecond ->
  RawCodedTermShift M cutoff amount third shiftedThird ->
  RawCodedTernaryApplication M
    predicate first second third sourceOutput ->
  exists targetOutput : M,
    RawCodedTernaryApplication M predicate
      shiftedFirst shiftedSecond shiftedThird targetOutput /\
    RawCodedFormulaShift M cutoff amount sourceOutput targetOutput.
Proof.
  intros M hPA predicate cutoff amount
    first shiftedFirst second shiftedSecond third shiftedThird sourceOutput
    hadequate hprotect hinterchange hpredicate
    hshiftedFirst hshiftedSecond hshiftedThird
    hfirst hsecond hthird hsource.
  destruct (raw_codedTernaryApplication_exists M hPA predicate
    shiftedFirst shiftedSecond shiftedThird hadequate
    hshiftedFirst hshiftedSecond hshiftedThird)
    as [targetOutput [htarget _]].
  exists targetOutput. split; [exact htarget |].
  exact (raw_codedTernaryApplication_operation_interchange
    M predicate (RawCodedFormulaShiftAtom M) amount
    hprotect hinterchange cutoff
    first shiftedFirst second shiftedSecond third shiftedThird
    sourceOutput targetOutput hpredicate
    hfirst hsecond hthird hsource htarget).
Qed.

Theorem raw_codedTernaryApplication_opening_interchange_on_syntax_of_laws :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    predicate replacement depth
    first openedFirst second openedSecond third openedThird sourceOutput,
  RawCodedFormulaAtomicallyAdequate M predicate ->
  RawCodedFormulaOperationProtectiveShiftStable M
    (RawCodedFormulaSubstitutionAtom M) replacement ->
  RawCodedFormulaOperationSingleSubstitutionInterchange M
    (RawCodedFormulaSubstitutionAtom M) replacement ->
  RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
    replacement (raw_succ M (raw_succ M (raw_succ M depth)))
    predicate predicate ->
  RawCodedTermSyntax M openedFirst ->
  RawCodedTermSyntax M openedSecond ->
  RawCodedTermSyntax M openedThird ->
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
Proof.
  intros M hPA predicate replacement depth
    first openedFirst second openedSecond third openedThird sourceOutput
    hadequate hprotect hinterchange hpredicate
    hopenedFirst hopenedSecond hopenedThird
    hfirst hsecond hthird hsource.
  destruct (raw_codedTernaryApplication_exists M hPA predicate
    openedFirst openedSecond openedThird hadequate
    hopenedFirst hopenedSecond hopenedThird)
    as [targetOutput [htarget _]].
  exists targetOutput. split; [exact htarget |].
  exact (raw_codedTernaryApplication_operation_interchange
    M predicate (RawCodedFormulaSubstitutionAtom M) replacement
    hprotect hinterchange depth
    first openedFirst second openedSecond third openedThird
    sourceOutput targetOutput hpredicate
    hfirst hsecond hthird hsource htarget).
Qed.

(** Root-level selector diagrams, in the exact unit-shift/single-opening form
    used by structural template translation. *)
Corollary rawTernaryApplicationSelector_unit_shift_on_syntax_of_laws :
  forall (M : RawPAModel), RawPASatisfies M -> forall predicate
    (selector : RawCodedTernaryApplicationSelector M predicate),
  RawCodedTernaryPredicateRootClosed M predicate ->
  RawCodedFormulaOperationProtectiveShiftStable M
    (RawCodedFormulaShiftAtom M) (rawNumeralValue M 1) ->
  RawCodedFormulaOperationSingleSubstitutionInterchange M
    (RawCodedFormulaShiftAtom M) (rawNumeralValue M 1) ->
  forall first shiftedFirst second shiftedSecond third shiftedThird,
  RawCodedTermSyntax M first -> RawCodedTermSyntax M shiftedFirst ->
  RawCodedTermSyntax M second -> RawCodedTermSyntax M shiftedSecond ->
  RawCodedTermSyntax M third -> RawCodedTermSyntax M shiftedThird ->
  RawCodedTermShift M
    (raw_zero M) (rawNumeralValue M 1) first shiftedFirst ->
  RawCodedTermShift M
    (raw_zero M) (rawNumeralValue M 1) second shiftedSecond ->
  RawCodedTermShift M
    (raw_zero M) (rawNumeralValue M 1) third shiftedThird ->
  RawCodedFormulaShift M
    (raw_zero M) (rawNumeralValue M 1)
    (rawTernaryApplicationOutput selector first second third)
    (rawTernaryApplicationOutput selector
      shiftedFirst shiftedSecond shiftedThird).
Proof.
  intros M hPA predicate selector
    [hadequate [hpredicate _]] hprotect hinterchange
    first shiftedFirst second shiftedSecond third shiftedThird
    hfirst hshiftedFirst hsecond hshiftedSecond hthird hshiftedThird
    hfirstShift hsecondShift hthirdShift.
  pose proof (rawTernaryApplicationOutput_trace selector
    first second third hfirst hsecond hthird) as hsource.
  destruct (raw_codedTernaryApplication_shift_interchange_on_syntax_of_laws
    M hPA predicate (raw_zero M) (rawNumeralValue M 1)
    first shiftedFirst second shiftedSecond third shiftedThird
    (rawTernaryApplicationOutput selector first second third)
    hadequate hprotect hinterchange hpredicate
    hshiftedFirst hshiftedSecond hshiftedThird
    hfirstShift hsecondShift hthirdShift hsource)
    as [targetOutput [htarget hshift]].
  pose proof (rawTernaryApplicationOutput_unique M hPA predicate selector
    shiftedFirst shiftedSecond shiftedThird targetOutput
    hshiftedFirst hshiftedSecond hshiftedThird htarget) as htargetEq.
  rewrite htargetEq. exact hshift.
Qed.

Corollary rawTernaryApplicationSelector_single_opening_on_syntax_of_laws :
  forall (M : RawPAModel), RawPASatisfies M -> forall predicate
    (selector : RawCodedTernaryApplicationSelector M predicate)
    replacement,
  RawCodedTernaryPredicateRootClosed M predicate ->
  RawCodedTermSyntax M replacement ->
  RawCodedFormulaOperationProtectiveShiftStable M
    (RawCodedFormulaSubstitutionAtom M) replacement ->
  RawCodedFormulaOperationSingleSubstitutionInterchange M
    (RawCodedFormulaSubstitutionAtom M) replacement ->
  forall first openedFirst second openedSecond third openedThird,
  RawCodedTermSyntax M first -> RawCodedTermSyntax M openedFirst ->
  RawCodedTermSyntax M second -> RawCodedTermSyntax M openedSecond ->
  RawCodedTermSyntax M third -> RawCodedTermSyntax M openedThird ->
  RawCodedFormulaSubstitutionAtom M
    replacement (raw_zero M) first openedFirst ->
  RawCodedFormulaSubstitutionAtom M
    replacement (raw_zero M) second openedSecond ->
  RawCodedFormulaSubstitutionAtom M
    replacement (raw_zero M) third openedThird ->
  RawCodedFormulaSingleSubstitution M replacement
    (rawTernaryApplicationOutput selector first second third)
    (rawTernaryApplicationOutput selector
      openedFirst openedSecond openedThird).
Proof.
  intros M hPA predicate selector replacement
    [hadequate [_ hpredicate]]
    (replacementAssignmentCode & replacementAssignmentStep & hreplacement)
    hprotect hinterchange
    first openedFirst second openedSecond third openedThird
    hfirst hopenedFirst hsecond hopenedSecond hthird hopenedThird
    hfirstOpening hsecondOpening hthirdOpening.
  pose proof (hpredicate replacement
    replacementAssignmentCode replacementAssignmentStep hreplacement)
    as hpredicateFixed.
  pose proof (rawTernaryApplicationOutput_trace selector
    first second third hfirst hsecond hthird) as hsource.
  destruct
    (raw_codedTernaryApplication_opening_interchange_on_syntax_of_laws
      M hPA predicate replacement (raw_zero M)
      first openedFirst second openedSecond third openedThird
      (rawTernaryApplicationOutput selector first second third)
      hadequate hprotect hinterchange hpredicateFixed
      hopenedFirst hopenedSecond hopenedThird
      hfirstOpening hsecondOpening hthirdOpening hsource)
    as [targetOutput [htarget hopening]].
  pose proof (rawTernaryApplicationOutput_unique M hPA predicate selector
    openedFirst openedSecond openedThird targetOutput
    hopenedFirst hopenedSecond hopenedThird htarget) as htargetEq.
  rewrite htargetEq. exact hopening.
Qed.

(** Domain-correct selector laws.  Both source and target syntax premises
    are explicit because the selector record intentionally constrains only
    those inputs. *)
Definition RawCodedTernaryApplicationShiftCommutingOnSyntax
    (M : RawPAModel) (predicate : M)
    (selector : RawCodedTernaryApplicationSelector M predicate) : Prop :=
  forall cutoff amount
      first shiftedFirst second shiftedSecond third shiftedThird : M,
    RawCodedTermSyntax M first -> RawCodedTermSyntax M shiftedFirst ->
    RawCodedTermSyntax M second -> RawCodedTermSyntax M shiftedSecond ->
    RawCodedTermSyntax M third -> RawCodedTermSyntax M shiftedThird ->
    RawCodedTermShift M cutoff amount first shiftedFirst ->
    RawCodedTermShift M cutoff amount second shiftedSecond ->
    RawCodedTermShift M cutoff amount third shiftedThird ->
    RawCodedFormulaShift M cutoff amount
      (rawTernaryApplicationOutput selector first second third)
      (rawTernaryApplicationOutput selector
        shiftedFirst shiftedSecond shiftedThird).

Arguments RawCodedTernaryApplicationShiftCommutingOnSyntax
  M predicate selector : clear implicits.

Definition RawCodedTernaryApplicationOpeningCommutingOnSyntax
    (M : RawPAModel) (predicate : M)
    (selector : RawCodedTernaryApplicationSelector M predicate) : Prop :=
  forall replacement depth
      first openedFirst second openedSecond third openedThird : M,
    RawCodedTermSyntax M first -> RawCodedTermSyntax M openedFirst ->
    RawCodedTermSyntax M second -> RawCodedTermSyntax M openedSecond ->
    RawCodedTermSyntax M third -> RawCodedTermSyntax M openedThird ->
    RawCodedFormulaSubstitutionAtom M
      replacement depth first openedFirst ->
    RawCodedFormulaSubstitutionAtom M
      replacement depth second openedSecond ->
    RawCodedFormulaSubstitutionAtom M
      replacement depth third openedThird ->
    RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
      replacement depth
      (rawTernaryApplicationOutput selector first second third)
      (rawTernaryApplicationOutput selector
        openedFirst openedSecond openedThird).

Arguments RawCodedTernaryApplicationOpeningCommutingOnSyntax
  M predicate selector : clear implicits.

(** Selector shift coherence follows solely from relational interchange. *)
Theorem rawTernaryApplicationSelector_shift_commuting_on_syntax : forall
    (M : RawPAModel), RawPASatisfies M -> forall predicate
    (selector : RawCodedTernaryApplicationSelector M predicate),
  RawCodedTernaryApplicationShiftInterchange M predicate ->
  RawCodedTernaryApplicationShiftCommutingOnSyntax
    M predicate selector.
Proof.
  intros M hPA predicate selector hinterchange
    cutoff amount first shiftedFirst second shiftedSecond
    third shiftedThird
    hfirst hshiftedFirst hsecond hshiftedSecond hthird hshiftedThird
    hfirstShift hsecondShift hthirdShift.
  pose proof (rawTernaryApplicationOutput_trace selector
    first second third hfirst hsecond hthird) as hsource.
  destruct (hinterchange cutoff amount
    first shiftedFirst second shiftedSecond third shiftedThird
    (rawTernaryApplicationOutput selector first second third)
    hfirstShift hsecondShift hthirdShift hsource)
    as [targetOutput [htarget hshift]].
  pose proof (rawTernaryApplicationOutput_unique M hPA predicate selector
    shiftedFirst shiftedSecond shiftedThird targetOutput
    hshiftedFirst hshiftedSecond hshiftedThird htarget) as htargetEq.
  rewrite htargetEq. exact hshift.
Qed.

Theorem rawTernaryApplicationSelector_opening_commuting_on_syntax : forall
    (M : RawPAModel), RawPASatisfies M -> forall predicate
    (selector : RawCodedTernaryApplicationSelector M predicate),
  RawCodedTernaryApplicationOpeningInterchange M predicate ->
  RawCodedTernaryApplicationOpeningCommutingOnSyntax
    M predicate selector.
Proof.
  intros M hPA predicate selector hinterchange
    replacement depth first openedFirst second openedSecond
    third openedThird
    hfirst hopenedFirst hsecond hopenedSecond hthird hopenedThird
    hfirstOpening hsecondOpening hthirdOpening.
  pose proof (rawTernaryApplicationOutput_trace selector
    first second third hfirst hsecond hthird) as hsource.
  destruct (hinterchange replacement depth
    first openedFirst second openedSecond third openedThird
    (rawTernaryApplicationOutput selector first second third)
    hfirstOpening hsecondOpening hthirdOpening hsource)
    as [targetOutput [htarget hopening]].
  pose proof (rawTernaryApplicationOutput_unique M hPA predicate selector
    openedFirst openedSecond openedThird targetOutput
    hopenedFirst hopenedSecond hopenedThird htarget) as htargetEq.
  rewrite htargetEq. exact hopening.
Qed.

End PABoundedRawCodedTemplateTernaryApplicationFunctionality.
