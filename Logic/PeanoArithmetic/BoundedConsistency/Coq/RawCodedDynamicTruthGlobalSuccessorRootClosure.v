(**
  Root closure through the paired global dynamic-truth successor.

  A global successor is assembled in two stages.  The local successor graph
  first returns two eight-witness row codes.  A transparent constructor-only
  wrapper then places those row codes beneath ten existential traversal
  witnesses and five universal row witnesses.  Consequently a root operation
  beginning at the three public predicate variables reaches each literal
  local-row leaf at cutoff [3 + 10 + 5 = 18].

  This module proves the wrapper part completely, without decoding either
  local row.  It also isolates the remaining local-successor obligation as a
  named operational-closure callback.  Atomic adequacy does not occur in that
  callback: the existing adequate-total successor theorem already supplies it.
  Thus the premise records exactly the two traces still needed at the local
  leaves--unit shift and arbitrary represented substitution at cutoff 18.
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedNumeralTermCode
  RawCodedScopedFormulaDiagonalSubstitution
  RawCodedStandardFormulaScopeDecision
  RawCodedBasicFormulaScopes
  RawCodedStandardFormulaScopeCombinators
  RawCodedSyntaxConstructors
  RawCodedTermEvaluationRealization
  RawCodedFormulaRankTotality
  RawCodedFormulaOperations
  RawCodedFormulaDiagonalOperation
  RawCodedFormulaShiftTreeRealization
  RawCodedFormulaOperationCompositionality
  RawCodedFormulaOperationTraceConcatenation
  RawCodedFormulaSingleSubstitutionAtomicAdequacy
  RawCodedTermOpeningAfterShiftSyntaxStability
  RawCodedFixedLevelTruth
  RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelTruthTraversal
  RawCodedProofAtomicAdequacyStandard
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthTernaryApplicationTotality
  RawCodedDynamicTruthPairedSuccessorRowGraph
  RawCodedDynamicTruthPairedSuccessorAdequacy
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedTemplateTernaryApplication
  RawCodedTernaryPredicateRootClosure
  RawCodedDynamicTruthGlobalBaseRootClosure.

Module PABoundedRawCodedDynamicTruthGlobalSuccessorRootClosure.

Import PA.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedNumeralTermCode.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedScopedFormulaDiagonalSubstitution.
Import PABoundedRawCodedStandardFormulaScopeDecision.
Import PABoundedRawCodedBasicFormulaScopes.
Import PABoundedRawCodedStandardFormulaScopeCombinators.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedTermEvaluationRealization.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaDiagonalOperation.
Import PABoundedRawCodedFormulaShiftTreeRealization.
Import PABoundedRawCodedFormulaOperationCompositionality.
Import PABoundedRawCodedFormulaOperationTraceConcatenation.
Import PABoundedRawCodedFormulaSingleSubstitutionAtomicAdequacy.
Import PABoundedRawCodedTermOpeningAfterShiftSyntaxStability.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthTernaryApplicationTotality.
Import PABoundedRawCodedDynamicTruthPairedSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedSuccessorAdequacy.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTernaryPredicateRootClosure.
Import PABoundedRawCodedDynamicTruthGlobalBaseRootClosure.

(** Operational closure at an arbitrary carrier-valued cutoff.  Separating
    this from atomic adequacy lets the successor callback state only what is
    not already returned by the adequate local-row graph. *)
Definition RawCodedFormulaOperationallyClosedAt (M : RawPAModel)
    (cutoff code : M) : Prop :=
  RawCodedFormulaShift M cutoff (rawNumeralValue M 1) code code /\
  forall replacement assignmentCode assignmentStep : M,
    RawTermSyntaxRealizable M replacement assignmentCode assignmentStep ->
    RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
      replacement cutoff code code.

Arguments RawCodedFormulaOperationallyClosedAt M cutoff code
  : clear implicits.

Definition RawCodedFormulaRootClosedAt (M : RawPAModel)
    (cutoff code : M) : Prop :=
  RawCodedFormulaAtomicallyAdequate M code /\
  RawCodedFormulaOperationallyClosedAt M cutoff code.

Arguments RawCodedFormulaRootClosedAt M cutoff code : clear implicits.

(** [RawCodedFormulaRootClosedAt] is intentionally a one-cutoff property.
    Nothing below silently promotes it to all larger (especially
    nonstandard) cutoffs.  Such a promotion is not available from the current
    operation library and would be needed before using this invariant as a
    substitute for arbitrary-depth ternary-operation interchange. *)

(** The established ternary interface is exactly the specialization at the
    numeral three.  These bridges avoid introducing a competing notion of
    root closure into downstream orbit code. *)
Lemma rawCodedFormulaRootClosedAt_three_iff : forall
    (M : RawPAModel) code,
  RawCodedFormulaRootClosedAt M (rawNumeralValue M 3) code <->
  RawCodedTernaryPredicateRootClosed M code.
Proof.
  intros M code.
  unfold RawCodedFormulaRootClosedAt,
    RawCodedFormulaOperationallyClosedAt,
    RawCodedTernaryPredicateRootClosed.
  tauto.
Qed.

(** Standard scoped quotations are closed at their scope cutoff, including
    against arbitrary, possibly nonstandard, represented replacements. *)
Theorem raw_quotedFormula_root_closed_at_scope : forall
    (M : RawPAModel), RawPASatisfies M -> forall scope input,
  StandardFormulaScoped scope input ->
  RawCodedFormulaRootClosedAt M (rawNumeralValue M scope)
    (rawQuotedFormulaCode M input).
Proof.
  intros M hPA scope input hscope.
  split.
  - exact (raw_quotedFormula_atomically_adequate M hPA input).
  - split.
    + exact (raw_codedFormulaShift_standard_scoped_identity
        M hPA scope 1 input hscope).
    + intros replacement assignmentCode assignmentStep hreplacement.
      apply (raw_codedFormulaOperation_of_diagonal M hPA
        (RawCodedFormulaSubstitutionAtom M) replacement
        (rawNumeralValue M scope) (rawQuotedFormulaCode M input)).
      apply
        (raw_codedFormulaDiagonalSubstitution_standard_scoped_of_syntax
          M hPA replacement assignmentCode assignmentStep scope
          (rawNumeralValue M scope) input hreplacement hscope).
      apply raw_rank_le_refl. exact hPA.
Qed.

Lemma raw_fixedFormulaNumeralCode_root_closed_at_scope : forall
    (M : RawPAModel), RawPASatisfies M -> forall scope input,
  StandardFormulaScoped scope input ->
  RawCodedFormulaRootClosedAt M (rawNumeralValue M scope)
    (rawFixedFormulaNumeralCode M input).
Proof.
  intros M hPA scope input hscope.
  rewrite (rawFixedFormulaNumeralCode_eq_quoted M hPA input).
  exact (raw_quotedFormula_root_closed_at_scope
    M hPA scope input hscope).
Qed.

(** Root closure is compositional for each raw formula constructor. *)
Lemma rawFormulaShiftBinaryCode_root_closed_at : forall
    (M : RawPAModel), RawPASatisfies M -> forall kind cutoff left right,
  RawCodedFormulaRootClosedAt M cutoff left ->
  RawCodedFormulaRootClosedAt M cutoff right ->
  RawCodedFormulaRootClosedAt M cutoff
    (rawFormulaShiftBinaryCode M kind left right).
Proof.
  intros M hPA kind cutoff left right
    [hleftAdequate [hleftShift hleftSubstitution]]
    [hrightAdequate [hrightShift hrightSubstitution]].
  split.
  - destruct kind; cbn [rawFormulaShiftBinaryCode].
    + exact (raw_formulaImpCode_atomically_adequate
        M hPA left right hleftAdequate hrightAdequate).
    + exact (raw_formulaAndCode_atomically_adequate
        M hPA left right hleftAdequate hrightAdequate).
    + exact (raw_formulaOrCode_atomically_adequate
        M hPA left right hleftAdequate hrightAdequate).
  - split.
    + exact (raw_codedFormulaShift_binary_composition M hPA kind
        cutoff (rawNumeralValue M 1) left left right right
        hleftShift hrightShift).
    + intros replacement assignmentCode assignmentStep hreplacement.
      exact (raw_codedFormulaSubstitution_binary_composition M hPA
        replacement kind cutoff left left right right
        (hleftSubstitution replacement assignmentCode assignmentStep
          hreplacement)
        (hrightSubstitution replacement assignmentCode assignmentStep
          hreplacement)).
Qed.

Lemma rawFormulaShiftUnaryCode_root_closed_at : forall
    (M : RawPAModel), RawPASatisfies M -> forall kind cutoff child,
  RawCodedFormulaRootClosedAt M (raw_succ M cutoff) child ->
  RawCodedFormulaRootClosedAt M cutoff
    (rawFormulaShiftUnaryCode M kind child).
Proof.
  intros M hPA kind cutoff child
    [hchildAdequate [hchildShift hchildSubstitution]].
  split.
  - destruct kind; cbn [rawFormulaShiftUnaryCode].
    + exact (raw_formulaAllCode_atomically_adequate
        M hPA child hchildAdequate).
    + exact (raw_formulaExCode_atomically_adequate
        M hPA child hchildAdequate).
  - split.
    + exact (raw_codedFormulaShift_unary_composition M hPA kind
        cutoff (rawNumeralValue M 1) child child hchildShift).
    + intros replacement assignmentCode assignmentStep hreplacement.
      exact (raw_codedFormulaSubstitution_unary_composition M hPA
        replacement kind cutoff child child
        (hchildSubstitution replacement assignmentCode assignmentStep
          hreplacement)).
Qed.

Corollary rawFormulaImpCode_root_closed_at : forall
    (M : RawPAModel), RawPASatisfies M -> forall cutoff left right,
  RawCodedFormulaRootClosedAt M cutoff left ->
  RawCodedFormulaRootClosedAt M cutoff right ->
  RawCodedFormulaRootClosedAt M cutoff
    (rawFormulaImpCode M left right).
Proof.
  intros M hPA cutoff left right hleft hright.
  exact (rawFormulaShiftBinaryCode_root_closed_at M hPA
    RFSBImp cutoff left right hleft hright).
Qed.

Corollary rawFormulaAndCode_root_closed_at : forall
    (M : RawPAModel), RawPASatisfies M -> forall cutoff left right,
  RawCodedFormulaRootClosedAt M cutoff left ->
  RawCodedFormulaRootClosedAt M cutoff right ->
  RawCodedFormulaRootClosedAt M cutoff
    (rawFormulaAndCode M left right).
Proof.
  intros M hPA cutoff left right hleft hright.
  exact (rawFormulaShiftBinaryCode_root_closed_at M hPA
    RFSBAnd cutoff left right hleft hright).
Qed.

Corollary rawFormulaOrCode_root_closed_at : forall
    (M : RawPAModel), RawPASatisfies M -> forall cutoff left right,
  RawCodedFormulaRootClosedAt M cutoff left ->
  RawCodedFormulaRootClosedAt M cutoff right ->
  RawCodedFormulaRootClosedAt M cutoff
    (rawFormulaOrCode M left right).
Proof.
  intros M hPA cutoff left right hleft hright.
  exact (rawFormulaShiftBinaryCode_root_closed_at M hPA
    RFSBOr cutoff left right hleft hright).
Qed.

Corollary rawFormulaAllCode_root_closed_at : forall
    (M : RawPAModel), RawPASatisfies M -> forall cutoff child,
  RawCodedFormulaRootClosedAt M (raw_succ M cutoff) child ->
  RawCodedFormulaRootClosedAt M cutoff
    (rawFormulaAllCode M child).
Proof.
  intros M hPA cutoff child hchild.
  exact (rawFormulaShiftUnaryCode_root_closed_at M hPA
    RFSUAll cutoff child hchild).
Qed.

Corollary rawFormulaExCode_root_closed_at : forall
    (M : RawPAModel), RawPASatisfies M -> forall cutoff child,
  RawCodedFormulaRootClosedAt M (raw_succ M cutoff) child ->
  RawCodedFormulaRootClosedAt M cutoff
    (rawFormulaExCode M child).
Proof.
  intros M hPA cutoff child hchild.
  exact (rawFormulaShiftUnaryCode_root_closed_at M hPA
    RFSUEx cutoff child hchild).
Qed.

(** The small folds below mirror the transparent wrapper polynomial. *)
Lemma rawDynamicTruthFormulaAll5Code_root_closed_at : forall
    (M : RawPAModel), RawPASatisfies M -> forall cutoff child,
  RawCodedFormulaRootClosedAt M
    (raw_succ M (raw_succ M (raw_succ M (raw_succ M
      (raw_succ M cutoff))))) child ->
  RawCodedFormulaRootClosedAt M cutoff
    (rawDynamicTruthFormulaAll5Code M child).
Proof.
  intros M hPA cutoff child hchild.
  unfold rawDynamicTruthFormulaAll5Code.
  repeat eapply (rawFormulaAllCode_root_closed_at M hPA).
  exact hchild.
Qed.

Lemma rawDynamicTruthFormulaEx10Code_root_closed_at : forall
    (M : RawPAModel), RawPASatisfies M -> forall cutoff child,
  RawCodedFormulaRootClosedAt M
    (raw_succ M (raw_succ M (raw_succ M (raw_succ M
      (raw_succ M (raw_succ M (raw_succ M (raw_succ M
        (raw_succ M (raw_succ M cutoff)))))))))) child ->
  RawCodedFormulaRootClosedAt M cutoff
    (rawDynamicTruthFormulaEx10Code M child).
Proof.
  intros M hPA cutoff child hchild.
  unfold rawDynamicTruthFormulaEx10Code, rawFormulaEx8Code.
  repeat eapply (rawFormulaExCode_root_closed_at M hPA).
  exact hchild.
Qed.

Lemma rawDynamicTruthFormulaAnd7Code_root_closed_at : forall
    (M : RawPAModel), RawPASatisfies M -> forall cutoff a b c d f g h,
  RawCodedFormulaRootClosedAt M cutoff a ->
  RawCodedFormulaRootClosedAt M cutoff b ->
  RawCodedFormulaRootClosedAt M cutoff c ->
  RawCodedFormulaRootClosedAt M cutoff d ->
  RawCodedFormulaRootClosedAt M cutoff f ->
  RawCodedFormulaRootClosedAt M cutoff g ->
  RawCodedFormulaRootClosedAt M cutoff h ->
  RawCodedFormulaRootClosedAt M cutoff
    (rawDynamicTruthFormulaAnd7Code M a b c d f g h).
Proof.
  intros M hPA cutoff a b c d f g h
    ha hb hc hd hf hg hh.
  unfold rawDynamicTruthFormulaAnd7Code.
  repeat eapply (rawFormulaAndCode_root_closed_at M hPA);
    assumption.
Qed.

(** All fixed wrapper leaves have the displayed finite scopes.  Executable
    checks keep this syntactic bookkeeping independent of semantic claims. *)
Local Ltac solve_scope :=
  apply (proj1 (standardFormulaScopedb_spec _ _));
  vm_compute; reflexivity.

Lemma dynamicTruthGlobalModeDefinedFormula_scoped_13 :
  StandardFormulaScoped 13 dynamicTruthGlobalModeDefinedFormula.
Proof. solve_scope. Qed.

Lemma dynamicTruthGlobalFormulaDefinedFormula_scoped_13 :
  StandardFormulaScoped 13 dynamicTruthGlobalFormulaDefinedFormula.
Proof. solve_scope. Qed.

Lemma dynamicTruthGlobalAssignmentCodeDefinedFormula_scoped_13 :
  StandardFormulaScoped 13
    dynamicTruthGlobalAssignmentCodeDefinedFormula.
Proof. solve_scope. Qed.

Lemma dynamicTruthGlobalAssignmentStepDefinedFormula_scoped_13 :
  StandardFormulaScoped 13
    dynamicTruthGlobalAssignmentStepDefinedFormula.
Proof. solve_scope. Qed.

Lemma dynamicTruthGlobalRootBoundFormula_scoped_13 :
  StandardFormulaScoped 13 dynamicTruthGlobalRootBoundFormula.
Proof. solve_scope. Qed.

Lemma dynamicTruthGlobalRootLookupFormula_scoped_13 : forall rootMode,
  StandardTermScoped 13 rootMode ->
  StandardFormulaScoped 13
    (dynamicTruthGlobalRootLookupFormula rootMode).
Proof.
  intros rootMode hrootMode.
  unfold dynamicTruthGlobalRootLookupFormula,
    fixedLevelStateLookupTermAt, fixedLevelAnd4.
  apply standardFormulaScoped_and.
  { apply standardFormulaScoped_codedAssignmentLookupTermAt.
    - apply standardTermScoped_var. lia.
    - apply standardTermScoped_var. lia.
    - apply standardTermScoped_var. lia.
    - exact hrootMode. }
  apply standardFormulaScoped_and.
  { apply standardFormulaScoped_codedAssignmentLookupTermAt;
      apply standardTermScoped_var; lia. }
  apply standardFormulaScoped_and.
  { apply standardFormulaScoped_codedAssignmentLookupTermAt;
      apply standardTermScoped_var; lia. }
  apply standardFormulaScoped_codedAssignmentLookupTermAt;
    apply standardTermScoped_var; lia.
Qed.

Lemma dynamicTruthGlobalRowBoundFormula_scoped_18 :
  StandardFormulaScoped 18 dynamicTruthGlobalRowBoundFormula.
Proof. solve_scope. Qed.

Lemma dynamicTruthGlobalRowLookupFormula_scoped_18 :
  StandardFormulaScoped 18 dynamicTruthGlobalRowLookupFormula.
Proof. solve_scope. Qed.

Lemma dynamicTruthGlobalSigmaModeFormula_scoped_18 :
  StandardFormulaScoped 18 dynamicTruthGlobalSigmaModeFormula.
Proof. solve_scope. Qed.

Lemma dynamicTruthGlobalPiModeFormula_scoped_18 :
  StandardFormulaScoped 18 dynamicTruthGlobalPiModeFormula.
Proof. solve_scope. Qed.

(** The exact local interface consumed by the wrapper. *)
Definition RawDynamicTruthPairedLocalRowsRootClosedAtWrapperDepth
    (M : RawPAModel) (localSigma localPi : M) : Prop :=
  RawCodedFormulaRootClosedAt M (rawNumeralValue M 18) localSigma /\
  RawCodedFormulaRootClosedAt M (rawNumeralValue M 18) localPi.

Arguments RawDynamicTruthPairedLocalRowsRootClosedAtWrapperDepth
  M localSigma localPi : clear implicits.

Lemma rawDynamicTruthGlobalRowChoiceCode_root_closed : forall
    (M : RawPAModel), RawPASatisfies M -> forall localSigma localPi,
  RawDynamicTruthPairedLocalRowsRootClosedAtWrapperDepth
    M localSigma localPi ->
  RawCodedFormulaRootClosedAt M (rawNumeralValue M 18)
    (rawDynamicTruthGlobalRowChoiceCode M localSigma localPi).
Proof.
  intros M hPA localSigma localPi [hSigma hPi].
  unfold rawDynamicTruthGlobalRowChoiceCode.
  apply rawFormulaOrCode_root_closed_at.
  - exact hPA.
  - apply rawFormulaAndCode_root_closed_at.
    + exact hPA.
    + apply raw_fixedFormulaNumeralCode_root_closed_at_scope.
      * exact hPA.
      * exact dynamicTruthGlobalSigmaModeFormula_scoped_18.
    + exact hSigma.
  - apply rawFormulaAndCode_root_closed_at.
    + exact hPA.
    + apply raw_fixedFormulaNumeralCode_root_closed_at_scope.
      * exact hPA.
      * exact dynamicTruthGlobalPiModeFormula_scoped_18.
    + exact hPi.
Qed.

Lemma rawDynamicTruthGlobalRowsCode_root_closed : forall
    (M : RawPAModel), RawPASatisfies M -> forall localSigma localPi,
  RawDynamicTruthPairedLocalRowsRootClosedAtWrapperDepth
    M localSigma localPi ->
  RawCodedFormulaRootClosedAt M (rawNumeralValue M 13)
    (rawDynamicTruthGlobalRowsCode M localSigma localPi).
Proof.
  intros M hPA localSigma localPi hlocal.
  unfold rawDynamicTruthGlobalRowsCode.
  apply rawDynamicTruthFormulaAll5Code_root_closed_at.
  - exact hPA.
  - change (RawCodedFormulaRootClosedAt M (rawNumeralValue M 18)
      (rawFormulaImpCode M
        (rawFixedFormulaNumeralCode M dynamicTruthGlobalRowBoundFormula)
        (rawFormulaImpCode M
          (rawFixedFormulaNumeralCode M
            dynamicTruthGlobalRowLookupFormula)
          (rawDynamicTruthGlobalRowChoiceCode M localSigma localPi)))).
    apply rawFormulaImpCode_root_closed_at.
    + exact hPA.
    + apply raw_fixedFormulaNumeralCode_root_closed_at_scope.
      * exact hPA.
      * exact dynamicTruthGlobalRowBoundFormula_scoped_18.
    + apply rawFormulaImpCode_root_closed_at.
      * exact hPA.
      * apply raw_fixedFormulaNumeralCode_root_closed_at_scope.
        -- exact hPA.
        -- exact dynamicTruthGlobalRowLookupFormula_scoped_18.
      * exact (rawDynamicTruthGlobalRowChoiceCode_root_closed
          M hPA localSigma localPi hlocal).
Qed.

(** Complete wrapper preservation.  The root-mode term is metatheoretic
    syntax (zero or one at the public call sites); only the local row codes
    may be genuinely nonstandard. *)
Theorem rawDynamicTruthGlobalFormulaCode_root_closed_of_local_rows : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      rootMode localSigma localPi,
  StandardTermScoped 13 rootMode ->
  RawDynamicTruthPairedLocalRowsRootClosedAtWrapperDepth
    M localSigma localPi ->
  RawCodedTernaryPredicateRootClosed M
    (rawDynamicTruthGlobalFormulaCode M
      rootMode localSigma localPi).
Proof.
  intros M hPA rootMode localSigma localPi hrootMode hlocal.
  apply (proj1 (rawCodedFormulaRootClosedAt_three_iff M _)).
  unfold rawDynamicTruthGlobalFormulaCode.
  apply rawDynamicTruthFormulaEx10Code_root_closed_at.
  - exact hPA.
  - change (RawCodedFormulaRootClosedAt M (rawNumeralValue M 13)
      (rawDynamicTruthFormulaAnd7Code M
        (rawFixedFormulaNumeralCode M
          dynamicTruthGlobalModeDefinedFormula)
        (rawFixedFormulaNumeralCode M
          dynamicTruthGlobalFormulaDefinedFormula)
        (rawFixedFormulaNumeralCode M
          dynamicTruthGlobalAssignmentCodeDefinedFormula)
        (rawFixedFormulaNumeralCode M
          dynamicTruthGlobalAssignmentStepDefinedFormula)
        (rawFixedFormulaNumeralCode M
          dynamicTruthGlobalRootBoundFormula)
        (rawFixedFormulaNumeralCode M
          (dynamicTruthGlobalRootLookupFormula rootMode))
        (rawDynamicTruthGlobalRowsCode M localSigma localPi))).
    apply rawDynamicTruthFormulaAnd7Code_root_closed_at; try exact hPA.
    + apply raw_fixedFormulaNumeralCode_root_closed_at_scope;
        [exact hPA | exact dynamicTruthGlobalModeDefinedFormula_scoped_13].
    + apply raw_fixedFormulaNumeralCode_root_closed_at_scope;
        [exact hPA | exact dynamicTruthGlobalFormulaDefinedFormula_scoped_13].
    + apply raw_fixedFormulaNumeralCode_root_closed_at_scope;
        [exact hPA |
         exact dynamicTruthGlobalAssignmentCodeDefinedFormula_scoped_13].
    + apply raw_fixedFormulaNumeralCode_root_closed_at_scope;
        [exact hPA |
         exact dynamicTruthGlobalAssignmentStepDefinedFormula_scoped_13].
    + apply raw_fixedFormulaNumeralCode_root_closed_at_scope;
        [exact hPA | exact dynamicTruthGlobalRootBoundFormula_scoped_13].
    + apply raw_fixedFormulaNumeralCode_root_closed_at_scope.
      * exact hPA.
      * exact (dynamicTruthGlobalRootLookupFormula_scoped_13
          rootMode hrootMode).
    + exact (rawDynamicTruthGlobalRowsCode_root_closed
        M hPA localSigma localPi hlocal).
Qed.

Theorem dynamicTruthPairedGlobalWrapperAt_root_closed : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      localSigma localPi globalSigma globalPi,
  RawDynamicTruthPairedGlobalWrapperAt M
    localSigma localPi globalSigma globalPi ->
  RawDynamicTruthPairedLocalRowsRootClosedAtWrapperDepth
    M localSigma localPi ->
  RawCodedTernaryPredicateRootClosed M globalSigma /\
  RawCodedTernaryPredicateRootClosed M globalPi.
Proof.
  intros M hPA localSigma localPi globalSigma globalPi
    [-> ->] hlocal.
  split.
  - apply rawDynamicTruthGlobalFormulaCode_root_closed_of_local_rows;
      try assumption.
    apply (proj1 (standardTermScopedb_spec 13 tZero)).
    reflexivity.
  - apply rawDynamicTruthGlobalFormulaCode_root_closed_of_local_rows;
      try assumption.
    apply (proj1 (standardTermScopedb_spec 13 (Term.numeral 1))).
    reflexivity.
Qed.

(** Atomic adequacy of an arbitrary local-row witness follows from the
    traces carried by the relation itself.  This is stronger than merely
    reusing the particular witnesses selected by adequate totality, and lets
    the relation-level successor theorem destruct its own existential. *)
Lemma raw_fixedReplacement_substitution_target_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall replacement input output,
  RawCodedFormulaSingleSubstitution M
    (rawNumeralValue M (termCode replacement)) input output ->
  RawCodedFormulaAtomicallyAdequate M output.
Proof.
  intros M hPA replacement input output hsubstitution.
  exact (raw_codedFormulaSingleSubstitution_target_atomically_adequate
    M hPA (raw_codedTermOpeningAfterShiftSyntaxStable_of_PA M hPA)
    (rawNumeralValue M (termCode replacement))
    (raw_zero M) (raw_zero M)
    (raw_dynamicTruthApplication_fixedReplacement_syntax
      M hPA replacement)
    input output hsubstitution).
Qed.

Lemma raw_dynamicTruthSigmaLower_target_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall input output,
  RawDynamicTruthCoqLowerApplication M input output ->
  RawCodedFormulaAtomicallyAdequate M output.
Proof.
  intros M hPA input output
    (first & second & _ & _ & hthird).
  exact (raw_fixedReplacement_substitution_target_atomically_adequate
    M hPA dynamicTruthCoqLowerThirdReplacement second output hthird).
Qed.

Lemma raw_dynamicTruthPiLower_target_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall input output,
  RawDynamicTruthPiCoqLowerApplication M input output ->
  RawCodedFormulaAtomicallyAdequate M output.
Proof.
  intros M hPA input output
    (first & second & _ & _ & hthird).
  exact (raw_fixedReplacement_substitution_target_atomically_adequate
    M hPA dynamicTruthPiCoqLowerThirdReplacement second output hthird).
Qed.

Lemma raw_dynamicTruthDomain_target_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      bound numeralCode templateCode domain,
  RawNumeralTermCodeAt M bound numeralCode ->
  RawCodedFormulaSingleSubstitution M
    numeralCode (rawNumeralValue M templateCode) domain ->
  RawCodedFormulaAtomicallyAdequate M domain.
Proof.
  intros M hPA bound numeralCode templateCode domain
    hnumeral hsubstitution.
  exact (raw_codedFormulaSingleSubstitution_target_atomically_adequate
    M hPA (raw_codedTermOpeningAfterShiftSyntaxStable_of_PA M hPA)
    numeralCode (raw_zero M) (raw_zero M)
    (raw_numeralTermCode_syntax_realizable_zero
      M hPA bound numeralCode hnumeral)
    (rawNumeralValue M templateCode) domain hsubstitution).
Qed.

Theorem rawDynamicTruthPairedSuccessorRowAt_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      previousSigma previousPi lowerLevel localSigma localPi,
  RawDynamicTruthPairedSuccessorRowAt M
    previousSigma previousPi lowerLevel localSigma localPi ->
  RawCodedFormulaAtomicallyAdequate M localSigma /\
  RawCodedFormulaAtomicallyAdequate M localPi.
Proof.
  intros M hPA previousSigma previousPi lowerLevel
    localSigma localPi [hSigma hPi].
  destruct hSigma as
    (sigmaNumeral & sigmaDomain & sigmaLower & hsigmaNumeral &
     hsigmaDomain & hsigmaLower & ->).
  destruct hPi as
    (piNumeral & piDomain & piLower & hpiNumeral &
     hpiDomain & hpiLower & ->).
  assert (hsigmaDomainAdequate :
      RawCodedFormulaAtomicallyAdequate M sigmaDomain).
  { exact (raw_dynamicTruthDomain_target_atomically_adequate M hPA
      (raw_succ M lowerLevel) sigmaNumeral
      dynamicTruthSigmaRowDomainTemplateCode sigmaDomain
      hsigmaNumeral hsigmaDomain). }
  assert (hpiDomainAdequate :
      RawCodedFormulaAtomicallyAdequate M piDomain).
  { exact (raw_dynamicTruthDomain_target_atomically_adequate M hPA
      (raw_succ M lowerLevel) piNumeral
      (formulaCode dynamicTruthPiRowDomainTemplate) piDomain
      hpiNumeral hpiDomain). }
  assert (hsigmaLowerAdequate :
      RawCodedFormulaAtomicallyAdequate M sigmaLower).
  { exact (raw_dynamicTruthSigmaLower_target_atomically_adequate
      M hPA previousPi sigmaLower hsigmaLower). }
  assert (hpiLowerAdequate :
      RawCodedFormulaAtomicallyAdequate M piLower).
  { exact (raw_dynamicTruthPiLower_target_atomically_adequate
      M hPA previousSigma piLower hpiLower). }
  split.
  - exact (rawDynamicTruthSigmaSuccessorRowCode_atomically_adequate
      M hPA sigmaDomain sigmaLower
      hsigmaDomainAdequate hsigmaLowerAdequate).
  - exact (rawDynamicTruthPiSuccessorRowCode_atomically_adequate
      M hPA piDomain piLower hpiDomainAdequate hpiLowerAdequate).
Qed.

(** The narrow unresolved local-row invariant.  It asks only for operational
    closure of actual row witnesses at cutoff 18.  Previous root closure is
    available because the lower-application traces depend on the opposite
    polarity's previous global predicate. *)
Definition RawDynamicTruthPairedGlobalSuccessorLocalClosure
    (M : RawPAModel) : Prop :=
  forall previousSigma previousPi lowerLevel localSigma localPi,
    RawCodedTernaryPredicateRootClosed M previousSigma ->
    RawCodedTernaryPredicateRootClosed M previousPi ->
    RawDynamicTruthPairedSuccessorRowAt M
      previousSigma previousPi lowerLevel localSigma localPi ->
    RawCodedFormulaOperationallyClosedAt M
      (rawNumeralValue M 18) localSigma /\
    RawCodedFormulaOperationallyClosedAt M
      (rawNumeralValue M 18) localPi.

Arguments RawDynamicTruthPairedGlobalSuccessorLocalClosure M
  : clear implicits.

(** Relation-level successor preservation.  The preceding adequacy theorem
    means we can destruct the actual global-successor witness directly; no
    selector-specific local rows or extra adequacy hypotheses are exposed. *)
Theorem dynamicTruthPairedGlobalSuccessorAt_root_closed : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPairedGlobalSuccessorLocalClosure M ->
  forall previousSigma previousPi lowerLevel nextSigma nextPi,
  RawCodedTernaryPredicateRootClosed M previousSigma ->
  RawCodedTernaryPredicateRootClosed M previousPi ->
  RawDynamicTruthPairedGlobalSuccessorAt M
    previousSigma previousPi lowerLevel nextSigma nextPi ->
  RawCodedTernaryPredicateRootClosed M nextSigma /\
  RawCodedTernaryPredicateRootClosed M nextPi.
Proof.
  intros M hPA hlocalClosure previousSigma previousPi lowerLevel
    nextSigma nextPi hpreviousSigma hpreviousPi
    (localSigma & localPi & hrow & hwrapper).
  destruct (rawDynamicTruthPairedSuccessorRowAt_atomically_adequate
    M hPA previousSigma previousPi lowerLevel localSigma localPi hrow)
    as [hlocalSigma hlocalPi].
  destruct (hlocalClosure previousSigma previousPi lowerLevel
    localSigma localPi hpreviousSigma hpreviousPi hrow)
    as [hSigmaOperational hPiOperational].
  apply (dynamicTruthPairedGlobalWrapperAt_root_closed M hPA
    localSigma localPi nextSigma nextPi hwrapper).
  split; split; assumption.
Qed.

(** Direct callback shape consumed by carrier-indexed paired orbit induction.
    Its output is the established three-variable, fixed-root interface.  The
    theorem must not be read as an arbitrary-depth commuting certificate. *)
Definition RawDynamicTruthPairedGlobalRootClosedSuccessorTotal
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) lowerLevel previousSigma previousPi,
    RawCodedTernaryPredicateRootClosed M previousSigma ->
    RawCodedTernaryPredicateRootClosed M previousPi ->
    exists nextSigma nextPi : M,
      raw_formula_sat M
        (scons M nextSigma (scons M nextPi
          (scons M previousSigma (scons M previousPi
            (scons M lowerLevel tail)))))
        dynamicTruthPairedGlobalSuccessorGraph /\
      RawCodedTernaryPredicateRootClosed M nextSigma /\
      RawCodedTernaryPredicateRootClosed M nextPi.

Arguments RawDynamicTruthPairedGlobalRootClosedSuccessorTotal M
  : clear implicits.

Theorem dynamicTruthPairedGlobalSuccessorGraph_raw_root_closed_total : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPairedGlobalSuccessorLocalClosure M ->
  RawDynamicTruthPairedGlobalRootClosedSuccessorTotal M.
Proof.
  intros M hPA hlocalClosure tail lowerLevel previousSigma previousPi
    hpreviousSigma hpreviousPi.
  destruct (dynamicTruthPairedSuccessorRowGraph_raw_adequate_total
    M hPA tail lowerLevel previousSigma previousPi
    (proj1 hpreviousSigma) (proj1 hpreviousPi)) as
    (localSigma & localPi & hlocalGraph & _ & _).
  pose proof (proj1
    (raw_sat_dynamicTruthPairedSuccessorRowGraph_iff M tail lowerLevel
      previousSigma previousPi localSigma localPi) hlocalGraph) as hrow.
  set (nextSigma := rawDynamicTruthGlobalFormulaCode M
    tZero localSigma localPi).
  set (nextPi := rawDynamicTruthGlobalFormulaCode M
    (Term.numeral 1) localSigma localPi).
  exists nextSigma, nextPi.
  assert (hwrapper : RawDynamicTruthPairedGlobalWrapperAt M
      localSigma localPi nextSigma nextPi).
  { unfold RawDynamicTruthPairedGlobalWrapperAt, nextSigma, nextPi.
    split; reflexivity. }
  split.
  - apply (proj2
      (raw_sat_dynamicTruthPairedGlobalSuccessorGraph_iff M tail
        lowerLevel previousSigma previousPi nextSigma nextPi)).
    exists localSigma, localPi. split; assumption.
  - exact (dynamicTruthPairedGlobalSuccessorAt_root_closed
      M hPA hlocalClosure previousSigma previousPi lowerLevel
      nextSigma nextPi hpreviousSigma hpreviousPi
      (ex_intro _ localSigma (ex_intro _ localPi (conj hrow hwrapper)))).
Qed.

(** The base half of the same invariant is already unconditional. *)
Theorem dynamicTruthPairedGlobalBaseGraph_raw_root_closed_total : forall
    (M : RawPAModel), RawPASatisfies M -> forall (tail : nat -> M),
  exists globalSigma globalPi : M,
    raw_formula_sat M
      (scons M globalSigma (scons M globalPi tail))
      dynamicTruthPairedGlobalBaseGraph /\
    RawCodedTernaryPredicateRootClosed M globalSigma /\
    RawCodedTernaryPredicateRootClosed M globalPi.
Proof.
  intros M hPA tail.
  destruct (dynamicTruthPairedGlobalBaseGraph_raw_adequate_total
    M hPA tail) as (globalSigma & globalPi & hgraph & _).
  exists globalSigma, globalPi. split; [exact hgraph |].
  apply (dynamicTruthPairedGlobalBaseAt_root_closed
    M hPA globalSigma globalPi).
  exact (proj1
    (raw_sat_dynamicTruthPairedGlobalBaseGraph_iff M tail
      globalSigma globalPi) hgraph).
Qed.

End PABoundedRawCodedDynamicTruthGlobalSuccessorRootClosure.
