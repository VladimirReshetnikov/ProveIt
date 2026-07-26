(**
  Represented ternary application for opaque proof-template atoms.

  A raw PA formula uses one de Bruijn namespace for both the three formal
  arguments of a represented predicate and the variables of the surrounding
  proof template.  Consequently simultaneous application cannot be encoded
  by three naive openings.  If the intended arguments are [first], [second],
  and [third], the first two must be protected from the later openings:

      first  -- shift by 2 --> firstLifted
      second -- shift by 1 --> secondLifted

      predicate[firstLifted/0][secondLifted/0][third/0].

  This is exactly the calculation behind the historical fixed replacements
  [#6], [#4], and [#0].  The relation below performs the same construction
  for arbitrary, possibly nonstandard, term and formula codes.

  Atomic adequacy plus the already proved term-operation totality is enough
  to construct all five represented traces and to keep every intermediate
  formula atomically adequate.  It is *not* enough to identify independently
  constructed traces.  The final two definitions therefore name, without
  postulating, the precise commuting diagrams needed by
  [RawCodedTemplateTranslation]: formula shift after application versus
  application of shifted arguments, and formula opening after application
  versus application of opened arguments.

  No cross-trace functionality theorem is smuggled into these interfaces.
  The raw operation library currently proves functionality only when two
  roots are looked up in the same target table.  A future discharge may prove
  these diagrams from a represented three-variable scope invariant; clients
  can already state and audit exactly that missing fact here.
*)

From Stdlib Require Import List Arith Lia Classical ClassicalChoice.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax RawCodedSyntaxConstructors RawCodedAssignment
  RawCodedAssignmentTotality
  RawCodedTermEvaluationRealization RawCodedTermShiftSyntaxRealization
  RawCodedFormulaOperations RawCodedTermOperationsStandardAdequacy
  RawCodedFormulaOperationsStandardAdequacy
  RawCodedFormulaOperationsStandardRealization
  RawCodedFormulaShiftTotality RawCodedFormulaOperationTraceConcatenation
  RawCodedFixedLevelTruthTotality
  RawCodedFormulaSingleSubstitutionAtomicAdequacy
  RawCodedTermOpeningAfterShiftSyntaxStability
  RawCodedProofAtomicAdequacyStandard
  RawCodedScopedFormulaDiagonalSubstitution
  RawCodedDynamicTruthGlobalPolarityFormulaCodeGraphs.

Import ListNotations.

Module PABoundedRawCodedTemplateTernaryApplication.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedAssignmentTotality.
Import PABoundedRawCodedTermEvaluationRealization.
Import PABoundedRawCodedTermShiftSyntaxRealization.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTermOperationsStandardAdequacy.
Import PABoundedRawCodedFormulaOperationsStandardAdequacy.
Import PABoundedRawCodedFormulaOperationsStandardRealization.
Import PABoundedRawCodedFormulaShiftTotality.
Import PABoundedRawCodedFormulaOperationTraceConcatenation.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFormulaSingleSubstitutionAtomicAdequacy.
Import PABoundedRawCodedTermOpeningAfterShiftSyntaxStability.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedScopedFormulaDiagonalSubstitution.
Import PABoundedRawCodedDynamicTruthGlobalPolarityFormulaCodeGraphs.

(** A term is in the honest represented syntax domain when some assignment
    columns make its syntax certificate realizable.  Hiding the columns is
    convenient for an application interface whose arguments may originate
    in different template subterms. *)
Definition RawCodedTermSyntax (M : RawPAModel) (input : M) : Prop :=
  exists assignmentCode assignmentStep : M,
    RawTermSyntaxRealizable M input assignmentCode assignmentStep.

Arguments RawCodedTermSyntax M input : clear implicits.

(** Every target selected by a represented term shift is honest term syntax.
    The shift trace itself provides the structural information; the all-zero
    beta assignment supplies values for every variable index. *)
Lemma raw_codedTermShift_target_syntax : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff amount input output,
  RawCodedTermShift M cutoff amount input output ->
  RawCodedTermSyntax M output.
Proof.
  intros M hPA cutoff amount input output hshift.
  exists (raw_zero M), (raw_zero M).
  apply (raw_codedTermShift_target_syntax_realizable M hPA
    cutoff amount input output
    (raw_zero M) (raw_zero M) (raw_succ M output)).
  - exact hshift.
  - exact (raw_assignment_lt_self_succ M hPA output).
  - exact (raw_codedZeroAssignment_defined_all M hPA
      (raw_succ M output)).
Qed.

(** The raw five-trace implementation of simultaneous ternary application.
    The first two witnesses are protected replacements; the last two are the
    intermediate formula codes. *)
Definition RawCodedTernaryApplication (M : RawPAModel)
    (predicate first second third output : M) : Prop :=
  exists firstLifted secondLifted firstResult secondResult : M,
    RawCodedTermShift M
      (raw_zero M) (rawNumeralValue M 2) first firstLifted /\
    RawCodedTermShift M
      (raw_zero M) (rawNumeralValue M 1) second secondLifted /\
    RawCodedFormulaSingleSubstitution M
      firstLifted predicate firstResult /\
    RawCodedFormulaSingleSubstitution M
      secondLifted firstResult secondResult /\
    RawCodedFormulaSingleSubstitution M
      third secondResult output.

Arguments RawCodedTernaryApplication
  M predicate first second third output : clear implicits.

(** The metatheoretic counterpart, used only to validate the ordering and
    lifting convention on ordinary quoted syntax. *)
Definition standardTernaryApplication
    (predicate : formula) (first second third : term) : formula :=
  Formula.subst (Formula.instTerm third)
    (Formula.subst
      (Formula.instTerm (standardTermShift 0 1 second))
      (Formula.subst
        (Formula.instTerm (standardTermShift 0 2 first))
        predicate)).

(** A direct standard realization of all five represented traces. *)
Theorem raw_codedTernaryApplication_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      predicate first second third,
  RawCodedTernaryApplication M
    (rawQuotedFormulaCode M predicate)
    (rawQuotedTermCode M first)
    (rawQuotedTermCode M second)
    (rawQuotedTermCode M third)
    (rawQuotedFormulaCode M
      (standardTernaryApplication predicate first second third)).
Proof.
  intros M hPA predicate first second third.
  unfold RawCodedTernaryApplication, standardTernaryApplication.
  set (firstLifted := standardTermShift 0 2 first).
  set (secondLifted := standardTermShift 0 1 second).
  set (firstResult := Formula.subst
    (Formula.instTerm firstLifted) predicate).
  set (secondResult := Formula.subst
    (Formula.instTerm secondLifted) firstResult).
  exists (rawQuotedTermCode M firstLifted),
    (rawQuotedTermCode M secondLifted),
    (rawQuotedFormulaCode M firstResult),
    (rawQuotedFormulaCode M secondResult).
  repeat split.
  - change (RawCodedTermShift M
      (rawNumeralValue M 0) (rawNumeralValue M 2)
      (rawQuotedTermCode M first)
      (rawQuotedTermCode M (standardTermShift 0 2 first))).
    apply raw_codedTermShift_standard. exact hPA.
  - change (RawCodedTermShift M
      (rawNumeralValue M 0) (rawNumeralValue M 1)
      (rawQuotedTermCode M second)
      (rawQuotedTermCode M (standardTermShift 0 1 second))).
    apply raw_codedTermShift_standard. exact hPA.
  - apply raw_codedFormulaSingleSubstitution_standard. exact hPA.
  - apply raw_codedFormulaSingleSubstitution_standard. exact hPA.
  - apply raw_codedFormulaSingleSubstitution_standard. exact hPA.
Qed.

(** The three openings implement literal simultaneous substitution whenever
    the source predicate has no free variable at index three or above. *)
Definition standardTernarySubstitution
    (first second third : term) (index : nat) : term :=
  match index with
  | 0 => first
  | 1 => second
  | 2 => third
  | S (S (S tailIndex)) => tVar tailIndex
  end.

(** Opening is a left inverse to a one-place lift.  Stating this small term
    calculation explicitly keeps the simultaneous-application proof below
    independent of large normalization tactics. *)
Lemma standardTermSubst_after_shift_one : forall replacement input,
  Term.subst (Formula.instTerm replacement)
    (standardTermShift 0 1 input) = input.
Proof.
  intros replacement input.
  induction input as [index | | child ih | left ihLeft right ihRight |
      left ihLeft right ihRight];
    cbn [standardTermShift Term.subst].
  - replace (index + 1) with (S index) by lia. reflexivity.
  - reflexivity.
  - now rewrite ih.
  - now rewrite ihLeft, ihRight.
  - now rewrite ihLeft, ihRight.
Qed.

Lemma standardTermShift_one_twice : forall input,
  standardTermShift 0 1 (standardTermShift 0 1 input) =
  standardTermShift 0 2 input.
Proof.
  intro input.
  induction input as [index | | child ih | left ihLeft right ihRight |
      left ihLeft right ihRight];
    cbn [standardTermShift].
  - assert (hindex : (index <? 0) = false)
      by (apply Nat.ltb_ge; lia).
    rewrite hindex.
    cbn [standardTermShift].
    assert (hshifted : (index + 1 <? 0) = false)
      by (apply Nat.ltb_ge; lia).
    rewrite hshifted.
    f_equal. lia.
  - reflexivity.
  - now rewrite ih.
  - now rewrite ihLeft, ihRight.
  - now rewrite ihLeft, ihRight.
Qed.

Lemma standardTermSubst_after_shift_two : forall
    first second third,
  Term.subst (Formula.instTerm third)
    (Term.subst
      (Formula.instTerm (standardTermShift 0 1 second))
      (standardTermShift 0 2 first)) = first.
Proof.
  intros first second third.
  rewrite <- standardTermShift_one_twice.
  rewrite standardTermSubst_after_shift_one.
  apply standardTermSubst_after_shift_one.
Qed.

Lemma standardTernaryApplication_eq_subst : forall
    predicate first second third,
  StandardFormulaScoped 3 predicate ->
  standardTernaryApplication predicate first second third =
    Formula.subst (standardTernarySubstitution first second third)
      predicate.
Proof.
  intros predicate first second third hscope.
  unfold standardTernaryApplication.
  rewrite !Formula.subst_comp.
  apply Formula.subst_ext_free.
  intros index hfree.
  specialize (hscope index hfree).
  destruct index as [|[|[|tailIndex]]];
    cbn [Formula.instTerm standardTernarySubstitution Term.subst].
  - rewrite <- Term.subst_comp.
    apply standardTermSubst_after_shift_two.
  - apply standardTermSubst_after_shift_one.
  - reflexivity.
  - lia.
Qed.

(** The output of any honest application remains atomically adequate.  This
    is independent of how the operation witnesses were chosen. *)
Theorem raw_codedTernaryApplication_target_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      predicate first second third output,
  RawCodedFormulaAtomicallyAdequate M predicate ->
  RawCodedTermSyntax M third ->
  RawCodedTernaryApplication M
    predicate first second third output ->
  RawCodedFormulaAtomicallyAdequate M output.
Proof.
  intros M hPA predicate first second third output
    hpredicate hthird
    (firstLifted & secondLifted & firstResult & secondResult &
     hfirstShift & hsecondShift & hfirstSubstitution &
     hsecondSubstitution & hthirdSubstitution).
  destruct (raw_codedTermShift_target_syntax M hPA
    (raw_zero M) (rawNumeralValue M 2)
    first firstLifted hfirstShift) as
    (firstAssignmentCode & firstAssignmentStep & hfirstLifted).
  destruct (raw_codedTermShift_target_syntax M hPA
    (raw_zero M) (rawNumeralValue M 1)
    second secondLifted hsecondShift) as
    (secondAssignmentCode & secondAssignmentStep & hsecondLifted).
  destruct hthird as
    (thirdAssignmentCode & thirdAssignmentStep & hthird).
  pose proof
    (raw_codedTermOpeningAfterShiftSyntaxStable_of_PA M hPA) as hstable.
  pose proof (raw_codedFormulaSingleSubstitution_target_atomically_adequate
    M hPA hstable firstLifted firstAssignmentCode firstAssignmentStep
    hfirstLifted predicate firstResult hfirstSubstitution) as hfirstResult.
  pose proof (raw_codedFormulaSingleSubstitution_target_atomically_adequate
    M hPA hstable secondLifted secondAssignmentCode secondAssignmentStep
    hsecondLifted firstResult secondResult hsecondSubstitution)
    as hsecondResult.
  exact (raw_codedFormulaSingleSubstitution_target_atomically_adequate
    M hPA hstable third thirdAssignmentCode thirdAssignmentStep hthird
    secondResult output hthirdSubstitution).
Qed.

(** Totality on the exact honest domain.  Notice that no formula decoding or
    standardness premise occurs. *)
Theorem raw_codedTernaryApplication_exists : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      predicate first second third,
  RawCodedFormulaAtomicallyAdequate M predicate ->
  RawCodedTermSyntax M first ->
  RawCodedTermSyntax M second ->
  RawCodedTermSyntax M third ->
  exists output : M,
    RawCodedTernaryApplication M
      predicate first second third output /\
    RawCodedFormulaAtomicallyAdequate M output.
Proof.
  intros M hPA predicate first second third hpredicate
    (firstAssignmentCode & firstAssignmentStep & hfirst)
    (secondAssignmentCode & secondAssignmentStep & hsecond)
    (thirdAssignmentCode & thirdAssignmentStep & hthird).
  destruct (raw_codedTermShift_exists_of_syntax_realizable M hPA
    first firstAssignmentCode firstAssignmentStep hfirst
    (raw_zero M) (rawNumeralValue M 2)) as
    [firstLifted hfirstShift].
  destruct (raw_codedTermShift_exists_of_syntax_realizable M hPA
    second secondAssignmentCode secondAssignmentStep hsecond
    (raw_zero M) (rawNumeralValue M 1)) as
    [secondLifted hsecondShift].
  destruct (raw_codedTermShift_target_syntax M hPA
    (raw_zero M) (rawNumeralValue M 2)
    first firstLifted hfirstShift) as
    (firstLiftedAssignmentCode & firstLiftedAssignmentStep &
     hfirstLifted).
  destruct (raw_codedTermShift_target_syntax M hPA
    (raw_zero M) (rawNumeralValue M 1)
    second secondLifted hsecondShift) as
    (secondLiftedAssignmentCode & secondLiftedAssignmentStep &
     hsecondLifted).
  destruct (raw_codedFormulaSingleSubstitution_three_exists_total
    M hPA predicate hpredicate
    firstLifted firstLiftedAssignmentCode firstLiftedAssignmentStep
      hfirstLifted
    secondLifted secondLiftedAssignmentCode secondLiftedAssignmentStep
      hsecondLifted
    third thirdAssignmentCode thirdAssignmentStep hthird) as
    (firstResult & secondResult & output &
     hfirstSubstitution & hfirstAdequate &
     hsecondSubstitution & hsecondAdequate &
     hthirdSubstitution & houtputAdequate).
  exists output. split; [|exact houtputAdequate].
  exists firstLifted, secondLifted, firstResult, secondResult.
  repeat split; assumption.
Qed.

(** A selector is the small amount of noncomputable data needed by the
    template translator, whose formula interpretation is a function rather
    than a relation.  Its correctness field is deliberately guarded by the
    honest term-syntax domain. *)
Record RawCodedTernaryApplicationSelector (M : RawPAModel)
    (predicate : M) : Type := {
  rawTernaryApplicationOutput : M -> M -> M -> M;
  rawTernaryApplicationOutput_trace : forall first second third,
    RawCodedTermSyntax M first ->
    RawCodedTermSyntax M second ->
    RawCodedTermSyntax M third ->
    RawCodedTernaryApplication M predicate first second third
      (rawTernaryApplicationOutput first second third)
}.

Arguments rawTernaryApplicationOutput {M predicate} _ first second third.
Arguments rawTernaryApplicationOutput_trace {M predicate} _
  first second third _ _ _.

(** Classical choice is used only to select one already proved relational
    output.  The logical content remains [raw_codedTernaryApplication_exists]. *)
Theorem raw_codedTernaryApplicationSelector_exists : forall
    (M : RawPAModel), RawPASatisfies M -> forall predicate,
  RawCodedFormulaAtomicallyAdequate M predicate ->
  exists selector : RawCodedTernaryApplicationSelector M predicate, True.
Proof.
  intros M hPA predicate hpredicate.
  assert (hall : forall inputs : M * M * M,
      exists output : M,
        let '(first, second, third) := inputs in
        RawCodedTermSyntax M first ->
        RawCodedTermSyntax M second ->
        RawCodedTermSyntax M third ->
        RawCodedTernaryApplication M
          predicate first second third output).
  {
    intros [[first second] third].
    destruct (classic (RawCodedTermSyntax M first /\
      RawCodedTermSyntax M second /\ RawCodedTermSyntax M third))
      as [[hfirst [hsecond hthird]] | hnot].
    - destruct (raw_codedTernaryApplication_exists M hPA
        predicate first second third hpredicate
        hfirst hsecond hthird) as [output [houtput _]].
      exists output. intros _ _ _. exact houtput.
    - exists (raw_zero M). intros hfirst hsecond hthird.
      exfalso. apply hnot. repeat split; assumption.
  }
  destruct (@choice (M * M * M) M
    (fun inputs output =>
      let '(first, second, third) := inputs in
      RawCodedTermSyntax M first ->
      RawCodedTermSyntax M second ->
      RawCodedTermSyntax M third ->
      RawCodedTernaryApplication M
        predicate first second third output)
    hall) as [choose hchoose].
  refine (ex_intro _
    {| rawTernaryApplicationOutput :=
         fun first second third => choose (first, second, third);
       rawTernaryApplicationOutput_trace := _ |} I).
  intros first second third hfirst hsecond hthird.
  exact (hchoose (first, second, third) hfirst hsecond hthird).
Qed.

(** ------------------------------------------------------------------
    The exact atom-level commutation seam.

    A formula shift visits an opaque application as a complete arithmetic
    formula.  The desired target is the selected application of the three
    shifted argument terms.  This relation compares those independently
    generated traces directly. *)
Definition RawCodedTernaryApplicationShiftCommuting
    (M : RawPAModel) (predicate : M)
    (selector : RawCodedTernaryApplicationSelector M predicate) : Prop :=
  forall cutoff amount
      first shiftedFirst second shiftedSecond third shiftedThird : M,
    RawCodedTermShift M cutoff amount first shiftedFirst ->
    RawCodedTermShift M cutoff amount second shiftedSecond ->
    RawCodedTermShift M cutoff amount third shiftedThird ->
    RawCodedFormulaShift M cutoff amount
      (rawTernaryApplicationOutput selector first second third)
      (rawTernaryApplicationOutput selector
        shiftedFirst shiftedSecond shiftedThird).

Arguments RawCodedTernaryApplicationShiftCommuting
  M predicate selector : clear implicits.

(** Formula single substitution shifts the replacement to the current
    binder depth and then opens every atomic term.  Supplying the three
    [RawCodedFormulaSubstitutionAtom] premises therefore says exactly that
    [openedFirst], [openedSecond], and [openedThird] are the translated
    template arguments after opening. *)
Definition RawCodedTernaryApplicationOpeningCommuting
    (M : RawPAModel) (predicate : M)
    (selector : RawCodedTernaryApplicationSelector M predicate) : Prop :=
  forall replacement depth
      first openedFirst second openedSecond third openedThird : M,
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

Arguments RawCodedTernaryApplicationOpeningCommuting
  M predicate selector : clear implicits.

Record RawCodedTernaryApplicationCommuting
    (M : RawPAModel) (predicate : M)
    (selector : RawCodedTernaryApplicationSelector M predicate) : Prop := {
  rawTernaryApplication_shift_commuting :
    RawCodedTernaryApplicationShiftCommuting M predicate selector;
  rawTernaryApplication_opening_commuting :
    RawCodedTernaryApplicationOpeningCommuting M predicate selector
}.

(** Root-level projections are the two precise fields consumed by
    [RawCodedTemplateTranslation]. *)
Corollary raw_codedTernaryApplication_unit_shift : forall
    (M : RawPAModel) predicate
    (selector : RawCodedTernaryApplicationSelector M predicate),
  RawCodedTernaryApplicationCommuting M predicate selector ->
  forall first shiftedFirst second shiftedSecond third shiftedThird,
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
  intros M predicate selector hcommuting.
  exact (rawTernaryApplication_shift_commuting
    M predicate selector hcommuting
    (raw_zero M) (rawNumeralValue M 1)).
Qed.

Corollary raw_codedTernaryApplication_single_opening : forall
    (M : RawPAModel) predicate
    (selector : RawCodedTernaryApplicationSelector M predicate),
  RawCodedTernaryApplicationCommuting M predicate selector ->
  forall replacement first openedFirst second openedSecond
      third openedThird,
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
  intros M predicate selector hcommuting replacement
    first openedFirst second openedSecond third openedThird.
  exact (rawTernaryApplication_opening_commuting
    M predicate selector hcommuting replacement (raw_zero M)
    first openedFirst second openedSecond third openedThird).
Qed.

(** A represented analogue of three-variable scope.  These two fixed-point
    traces are necessary closure data for deriving the commuting diagrams,
    but the current operation library has no theorem showing they are
    sufficient: that would require shift/substitution and
    substitution/substitution interchange across distinct traversal tables. *)
Definition RawCodedTernaryPredicateRootClosed
    (M : RawPAModel) (predicate : M) : Prop :=
  RawCodedFormulaAtomicallyAdequate M predicate /\
  RawCodedFormulaShift M
    (rawNumeralValue M 3) (rawNumeralValue M 1)
    predicate predicate /\
  forall replacement assignmentCode assignmentStep : M,
    RawTermSyntaxRealizable M replacement assignmentCode assignmentStep ->
    RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
      replacement (rawNumeralValue M 3) predicate predicate.

Arguments RawCodedTernaryPredicateRootClosed M predicate : clear implicits.

(** For standard quotations, syntactic three-variable scope gives the shift
    half of the preceding represented closure literally. *)
Lemma standardFormulaShift_identity_of_scoped : forall scope amount input,
  StandardFormulaScoped scope input ->
  standardFormulaShift scope amount input = input.
Proof.
  intros scope amount input hscope.
  rewrite standardFormulaShift_as_rename.
  transitivity (Formula.rename (fun index => index) input).
  - apply Formula.rename_ext_free.
    intros index hfree.
    specialize (hscope index hfree).
    unfold standardShiftRenaming.
    assert (hbelow : (index <? scope) = true)
      by (apply Nat.ltb_lt; exact hscope).
    rewrite hbelow. reflexivity.
  - apply Formula.rename_id.
Qed.

Corollary raw_codedFormulaShift_standard_scoped_identity : forall
    (M : RawPAModel), RawPASatisfies M -> forall scope amount input,
  StandardFormulaScoped scope input ->
  RawCodedFormulaShift M
    (rawNumeralValue M scope) (rawNumeralValue M amount)
    (rawQuotedFormulaCode M input) (rawQuotedFormulaCode M input).
Proof.
  intros M hPA scope amount input hscope.
  rewrite <- (standardFormulaShift_identity_of_scoped
    scope amount input hscope) at 2.
  apply raw_codedFormulaShift_standard. exact hPA.
Qed.

(** The global truth-code orbit already supplies the honest nonstandard
    application domain.  What it does not currently supply is
    [RawCodedTernaryPredicateRootClosed] or either commuting diagram. *)
Corollary dynamicTruthGlobalSigmaCode_ternary_application_exists : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (tail : nat -> M) level first second third,
  RawCodedTermSyntax M first ->
  RawCodedTermSyntax M second ->
  RawCodedTermSyntax M third ->
  exists globalSigmaCode output : M,
    raw_formula_sat M
      (scons M globalSigmaCode (scons M level tail))
      dynamicTruthGlobalSigmaFormulaCodeGraph /\
    RawCodedTernaryApplication M
      globalSigmaCode first second third output /\
    RawCodedFormulaAtomicallyAdequate M output.
Proof.
  intros M hPA tail level first second third
    hfirst hsecond hthird.
  destruct (dynamicTruthGlobalSigmaFormulaCodeGraph_raw_adequate_total
    M hPA tail level) as
    (globalSigmaCode & hgraph & hadequate).
  destruct (raw_codedTernaryApplication_exists M hPA
    globalSigmaCode first second third hadequate
    hfirst hsecond hthird) as [output [happlication houtput]].
  exists globalSigmaCode, output. repeat split; assumption.
Qed.

Corollary dynamicTruthGlobalPiCode_ternary_application_exists : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (tail : nat -> M) level first second third,
  RawCodedTermSyntax M first ->
  RawCodedTermSyntax M second ->
  RawCodedTermSyntax M third ->
  exists globalPiCode output : M,
    raw_formula_sat M
      (scons M globalPiCode (scons M level tail))
      dynamicTruthGlobalPiFormulaCodeGraph /\
    RawCodedTernaryApplication M
      globalPiCode first second third output /\
    RawCodedFormulaAtomicallyAdequate M output.
Proof.
  intros M hPA tail level first second third
    hfirst hsecond hthird.
  destruct (dynamicTruthGlobalPiFormulaCodeGraph_raw_adequate_total
    M hPA tail level) as
    (globalPiCode & hgraph & hadequate).
  destruct (raw_codedTernaryApplication_exists M hPA
    globalPiCode first second third hadequate
    hfirst hsecond hthird) as [output [happlication houtput]].
  exists globalPiCode, output. repeat split; assumption.
Qed.

End PABoundedRawCodedTemplateTernaryApplication.
