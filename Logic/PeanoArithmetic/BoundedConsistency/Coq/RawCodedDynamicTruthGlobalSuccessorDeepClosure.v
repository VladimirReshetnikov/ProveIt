(**
  Deep closure through the paired global dynamic-truth successor.

  A root operation on the public ternary predicate enters ten existential
  wrapper binders and then five universal row binders before reaching either
  actual local row.  Therefore an arbitrary root cutoff [c >= 3] reaches a
  local row at [c + 15 >= 18].  The fixed-cutoff root-closure interface is
  insufficient here: deep closure must quantify over all carrier-valued
  cutoffs and all shift amounts.

  We first formulate the contextual invariant "deeply closed from [root]".
  Formula constructors preserve it transparently.  This proves every wrapper
  law without inspecting local rows and isolates the remaining obligation as
  operational deep closure of the *actual* local-row witnesses from cutoff
  eighteen.  Atomic adequacy is intentionally absent from that callback,
  because the successor-row relation already proves it.
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedNumeralTermCode
  RawCodedFormulaOperations
  RawCodedTermEvaluationRealization
  RawCodedFixedLevelTruthTotality
  RawCodedFormulaRankTotality
  RawCodedFormulaDiagonalOperation
  RawCodedFormulaShiftTreeRealization
  RawCodedFormulaOperationCompositionality
  RawCodedFormulaOperationTraceConcatenation
  RawCodedScopedFormulaDiagonalSubstitution
  RawCodedStandardFormulaScopeDecision
  RawCodedProofAtomicAdequacyStandard
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPairedSuccessorRowGraph
  RawCodedDynamicTruthPairedSuccessorAdequacy
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthGlobalSuccessorRootClosure
  RawCodedTernaryPredicateRootClosure
  RawCodedTernaryPredicateDeepClosure.

Module PABoundedRawCodedDynamicTruthGlobalSuccessorDeepClosure.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTermEvaluationRealization.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedFormulaDiagonalOperation.
Import PABoundedRawCodedFormulaShiftTreeRealization.
Import PABoundedRawCodedFormulaOperationCompositionality.
Import PABoundedRawCodedFormulaOperationTraceConcatenation.
Import PABoundedRawCodedScopedFormulaDiagonalSubstitution.
Import PABoundedRawCodedStandardFormulaScopeDecision.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedSuccessorAdequacy.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedDynamicTruthGlobalSuccessorRootClosure.
Import PABoundedRawCodedTernaryPredicateRootClosure.
Import PABoundedRawCodedTernaryPredicateDeepClosure.

(** Operational closure at every cutoff above an arbitrary carrier root. *)
Definition RawCodedFormulaDeepOperationallyClosedFrom
    (M : RawPAModel) (root code : M) : Prop :=
  (forall cutoff amount : M,
    rawLe M root cutoff ->
    RawCodedFormulaShift M cutoff amount code code) /\
  (forall replacement assignmentCode assignmentStep depth : M,
    RawTermSyntaxRealizable M
      replacement assignmentCode assignmentStep ->
    rawLe M root depth ->
    RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
      replacement depth code code).

Definition RawCodedFormulaDeepClosedFrom
    (M : RawPAModel) (root code : M) : Prop :=
  RawCodedFormulaAtomicallyAdequate M code /\
  RawCodedFormulaDeepOperationallyClosedFrom M root code.

Arguments RawCodedFormulaDeepOperationallyClosedFrom M root code
  : clear implicits.
Arguments RawCodedFormulaDeepClosedFrom M root code : clear implicits.

(** The public ternary invariant is exactly the specialization at three. *)
Lemma rawCodedFormulaDeepClosedFrom_three_iff : forall
    (M : RawPAModel) code,
  RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 3) code <->
  RawCodedTernaryPredicateDeepClosed M code.
Proof.
  intros M code.
  unfold RawCodedFormulaDeepClosedFrom,
    RawCodedFormulaDeepOperationallyClosedFrom,
    RawCodedTernaryPredicateDeepClosed.
  tauto.
Qed.

(** Standard scoped quotations satisfy the contextual invariant at their
    displayed scope, even for nonstandard cutoffs and replacement terms. *)
Theorem raw_quotedFormula_deep_closed_from_scope : forall
    (M : RawPAModel), RawPASatisfies M -> forall scope input,
  StandardFormulaScoped scope input ->
  RawCodedFormulaDeepClosedFrom M (rawNumeralValue M scope)
    (rawQuotedFormulaCode M input).
Proof.
  intros M hPA scope input hscope.
  split.
  - exact (raw_quotedFormula_atomically_adequate M hPA input).
  - split.
    + intros cutoff amount hcutoff.
      exact (raw_codedFormulaShift_standard_scoped_identity_at_raw_cutoff
        M hPA scope cutoff amount input hscope hcutoff).
    + intros replacement assignmentCode assignmentStep depth
        hreplacement hdepth.
      apply (raw_codedFormulaOperation_of_diagonal M hPA
        (RawCodedFormulaSubstitutionAtom M) replacement depth
        (rawQuotedFormulaCode M input)).
      exact
        (raw_codedFormulaDiagonalSubstitution_standard_scoped_of_syntax
          M hPA replacement assignmentCode assignmentStep
          scope depth input hreplacement hscope hdepth).
Qed.

Lemma raw_fixedFormulaNumeralCode_deep_closed_from_scope : forall
    (M : RawPAModel), RawPASatisfies M -> forall scope input,
  StandardFormulaScoped scope input ->
  RawCodedFormulaDeepClosedFrom M (rawNumeralValue M scope)
    (rawFixedFormulaNumeralCode M input).
Proof.
  intros M hPA scope input hscope.
  rewrite (rawFixedFormulaNumeralCode_eq_quoted M hPA input).
  exact (raw_quotedFormula_deep_closed_from_scope
    M hPA scope input hscope).
Qed.

(** Binary constructors preserve the same contextual root. *)
Lemma rawFormulaShiftBinaryCode_deep_closed_from : forall
    (M : RawPAModel), RawPASatisfies M -> forall kind root left right,
  RawCodedFormulaDeepClosedFrom M root left ->
  RawCodedFormulaDeepClosedFrom M root right ->
  RawCodedFormulaDeepClosedFrom M root
    (rawFormulaShiftBinaryCode M kind left right).
Proof.
  intros M hPA kind root left right
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
    + intros cutoff amount hcutoff.
      exact (raw_codedFormulaShift_binary_composition M hPA kind
        cutoff amount left left right right
        (hleftShift cutoff amount hcutoff)
        (hrightShift cutoff amount hcutoff)).
    + intros replacement assignmentCode assignmentStep depth
        hreplacement hdepth.
      exact (raw_codedFormulaSubstitution_binary_composition M hPA
        replacement kind depth left left right right
        (hleftSubstitution replacement assignmentCode assignmentStep
          depth hreplacement hdepth)
        (hrightSubstitution replacement assignmentCode assignmentStep
          depth hreplacement hdepth)).
Qed.

(** A binder increments both the contextual root and every concrete
    operation depth.  The successor monotonicity law is valid for arbitrary
    carrier values, so no standardness premise is introduced. *)
Lemma rawFormulaShiftUnaryCode_deep_closed_from : forall
    (M : RawPAModel), RawPASatisfies M -> forall kind root child,
  RawCodedFormulaDeepClosedFrom M (raw_succ M root) child ->
  RawCodedFormulaDeepClosedFrom M root
    (rawFormulaShiftUnaryCode M kind child).
Proof.
  intros M hPA kind root child
    [hchildAdequate [hchildShift hchildSubstitution]].
  split.
  - destruct kind; cbn [rawFormulaShiftUnaryCode].
    + exact (raw_formulaAllCode_atomically_adequate
        M hPA child hchildAdequate).
    + exact (raw_formulaExCode_atomically_adequate
        M hPA child hchildAdequate).
  - split.
    + intros cutoff amount hcutoff.
      exact (raw_codedFormulaShift_unary_composition M hPA kind
        cutoff amount child child
        (hchildShift (raw_succ M cutoff) amount
          (raw_rank_succ_le M hPA root cutoff hcutoff))).
    + intros replacement assignmentCode assignmentStep depth
        hreplacement hdepth.
      exact (raw_codedFormulaSubstitution_unary_composition M hPA
        replacement kind depth child child
        (hchildSubstitution replacement assignmentCode assignmentStep
          (raw_succ M depth) hreplacement
          (raw_rank_succ_le M hPA root depth hdepth))).
Qed.

Corollary rawFormulaImpCode_deep_closed_from : forall
    (M : RawPAModel), RawPASatisfies M -> forall root left right,
  RawCodedFormulaDeepClosedFrom M root left ->
  RawCodedFormulaDeepClosedFrom M root right ->
  RawCodedFormulaDeepClosedFrom M root
    (rawFormulaImpCode M left right).
Proof.
  intros M hPA root left right hleft hright.
  exact (rawFormulaShiftBinaryCode_deep_closed_from M hPA
    RFSBImp root left right hleft hright).
Qed.

Corollary rawFormulaAndCode_deep_closed_from : forall
    (M : RawPAModel), RawPASatisfies M -> forall root left right,
  RawCodedFormulaDeepClosedFrom M root left ->
  RawCodedFormulaDeepClosedFrom M root right ->
  RawCodedFormulaDeepClosedFrom M root
    (rawFormulaAndCode M left right).
Proof.
  intros M hPA root left right hleft hright.
  exact (rawFormulaShiftBinaryCode_deep_closed_from M hPA
    RFSBAnd root left right hleft hright).
Qed.

Corollary rawFormulaOrCode_deep_closed_from : forall
    (M : RawPAModel), RawPASatisfies M -> forall root left right,
  RawCodedFormulaDeepClosedFrom M root left ->
  RawCodedFormulaDeepClosedFrom M root right ->
  RawCodedFormulaDeepClosedFrom M root
    (rawFormulaOrCode M left right).
Proof.
  intros M hPA root left right hleft hright.
  exact (rawFormulaShiftBinaryCode_deep_closed_from M hPA
    RFSBOr root left right hleft hright).
Qed.

Corollary rawFormulaAllCode_deep_closed_from : forall
    (M : RawPAModel), RawPASatisfies M -> forall root child,
  RawCodedFormulaDeepClosedFrom M (raw_succ M root) child ->
  RawCodedFormulaDeepClosedFrom M root
    (rawFormulaAllCode M child).
Proof.
  intros M hPA root child hchild.
  exact (rawFormulaShiftUnaryCode_deep_closed_from M hPA
    RFSUAll root child hchild).
Qed.

Corollary rawFormulaExCode_deep_closed_from : forall
    (M : RawPAModel), RawPASatisfies M -> forall root child,
  RawCodedFormulaDeepClosedFrom M (raw_succ M root) child ->
  RawCodedFormulaDeepClosedFrom M root
    (rawFormulaExCode M child).
Proof.
  intros M hPA root child hchild.
  exact (rawFormulaShiftUnaryCode_deep_closed_from M hPA
    RFSUEx root child hchild).
Qed.

(** Transparent folds used by the global wrapper. *)
Lemma rawDynamicTruthFormulaAll5Code_deep_closed_from : forall
    (M : RawPAModel), RawPASatisfies M -> forall root child,
  RawCodedFormulaDeepClosedFrom M
    (raw_succ M (raw_succ M (raw_succ M (raw_succ M
      (raw_succ M root))))) child ->
  RawCodedFormulaDeepClosedFrom M root
    (rawDynamicTruthFormulaAll5Code M child).
Proof.
  intros M hPA root child hchild.
  unfold rawDynamicTruthFormulaAll5Code.
  repeat eapply (rawFormulaAllCode_deep_closed_from M hPA).
  exact hchild.
Qed.

Lemma rawDynamicTruthFormulaEx10Code_deep_closed_from : forall
    (M : RawPAModel), RawPASatisfies M -> forall root child,
  RawCodedFormulaDeepClosedFrom M
    (raw_succ M (raw_succ M (raw_succ M (raw_succ M
      (raw_succ M (raw_succ M (raw_succ M (raw_succ M
        (raw_succ M (raw_succ M root)))))))))) child ->
  RawCodedFormulaDeepClosedFrom M root
    (rawDynamicTruthFormulaEx10Code M child).
Proof.
  intros M hPA root child hchild.
  unfold rawDynamicTruthFormulaEx10Code, rawFormulaEx8Code.
  repeat eapply (rawFormulaExCode_deep_closed_from M hPA).
  exact hchild.
Qed.

Lemma rawDynamicTruthFormulaAnd7Code_deep_closed_from : forall
    (M : RawPAModel), RawPASatisfies M -> forall root a b c d f g h,
  RawCodedFormulaDeepClosedFrom M root a ->
  RawCodedFormulaDeepClosedFrom M root b ->
  RawCodedFormulaDeepClosedFrom M root c ->
  RawCodedFormulaDeepClosedFrom M root d ->
  RawCodedFormulaDeepClosedFrom M root f ->
  RawCodedFormulaDeepClosedFrom M root g ->
  RawCodedFormulaDeepClosedFrom M root h ->
  RawCodedFormulaDeepClosedFrom M root
    (rawDynamicTruthFormulaAnd7Code M a b c d f g h).
Proof.
  intros M hPA root a b c d f g h ha hb hc hd hf hg hh.
  unfold rawDynamicTruthFormulaAnd7Code.
  repeat eapply (rawFormulaAndCode_deep_closed_from M hPA);
    assumption.
Qed.

(** The exact local-row interface consumed by the transparent wrapper.  It
    begins at eighteen but continues through *all* larger carrier cutoffs. *)
Definition RawDynamicTruthPairedLocalRowsDeepClosedAtWrapperDepth
    (M : RawPAModel) (localSigma localPi : M) : Prop :=
  RawCodedFormulaDeepClosedFrom M
    (rawNumeralValue M 18) localSigma /\
  RawCodedFormulaDeepClosedFrom M
    (rawNumeralValue M 18) localPi.

Arguments RawDynamicTruthPairedLocalRowsDeepClosedAtWrapperDepth
  M localSigma localPi : clear implicits.

Lemma rawDynamicTruthGlobalRowChoiceCode_deep_closed : forall
    (M : RawPAModel), RawPASatisfies M -> forall localSigma localPi,
  RawDynamicTruthPairedLocalRowsDeepClosedAtWrapperDepth
    M localSigma localPi ->
  RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 18)
    (rawDynamicTruthGlobalRowChoiceCode M localSigma localPi).
Proof.
  intros M hPA localSigma localPi [hSigma hPi].
  unfold rawDynamicTruthGlobalRowChoiceCode.
  apply rawFormulaOrCode_deep_closed_from.
  - exact hPA.
  - apply rawFormulaAndCode_deep_closed_from.
    + exact hPA.
    + apply raw_fixedFormulaNumeralCode_deep_closed_from_scope.
      * exact hPA.
      * exact dynamicTruthGlobalSigmaModeFormula_scoped_18.
    + exact hSigma.
  - apply rawFormulaAndCode_deep_closed_from.
    + exact hPA.
    + apply raw_fixedFormulaNumeralCode_deep_closed_from_scope.
      * exact hPA.
      * exact dynamicTruthGlobalPiModeFormula_scoped_18.
    + exact hPi.
Qed.

Lemma rawDynamicTruthGlobalRowsCode_deep_closed : forall
    (M : RawPAModel), RawPASatisfies M -> forall localSigma localPi,
  RawDynamicTruthPairedLocalRowsDeepClosedAtWrapperDepth
    M localSigma localPi ->
  RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 13)
    (rawDynamicTruthGlobalRowsCode M localSigma localPi).
Proof.
  intros M hPA localSigma localPi hlocal.
  unfold rawDynamicTruthGlobalRowsCode.
  apply rawDynamicTruthFormulaAll5Code_deep_closed_from.
  - exact hPA.
  - change (RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 18)
      (rawFormulaImpCode M
        (rawFixedFormulaNumeralCode M dynamicTruthGlobalRowBoundFormula)
        (rawFormulaImpCode M
          (rawFixedFormulaNumeralCode M
            dynamicTruthGlobalRowLookupFormula)
          (rawDynamicTruthGlobalRowChoiceCode M localSigma localPi)))).
    apply rawFormulaImpCode_deep_closed_from.
    + exact hPA.
    + apply raw_fixedFormulaNumeralCode_deep_closed_from_scope.
      * exact hPA.
      * exact dynamicTruthGlobalRowBoundFormula_scoped_18.
    + apply rawFormulaImpCode_deep_closed_from.
      * exact hPA.
      * apply raw_fixedFormulaNumeralCode_deep_closed_from_scope.
        -- exact hPA.
        -- exact dynamicTruthGlobalRowLookupFormula_scoped_18.
      * exact (rawDynamicTruthGlobalRowChoiceCode_deep_closed
          M hPA localSigma localPi hlocal).
Qed.

(** Complete transparent-wrapper preservation at every cutoff/depth. *)
Theorem rawDynamicTruthGlobalFormulaCode_deep_closed_of_local_rows : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      rootMode localSigma localPi,
  StandardTermScoped 13 rootMode ->
  RawDynamicTruthPairedLocalRowsDeepClosedAtWrapperDepth
    M localSigma localPi ->
  RawCodedTernaryPredicateDeepClosed M
    (rawDynamicTruthGlobalFormulaCode M
      rootMode localSigma localPi).
Proof.
  intros M hPA rootMode localSigma localPi hrootMode hlocal.
  apply (proj1 (rawCodedFormulaDeepClosedFrom_three_iff M _)).
  unfold rawDynamicTruthGlobalFormulaCode.
  apply rawDynamicTruthFormulaEx10Code_deep_closed_from.
  - exact hPA.
  - change (RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 13)
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
    apply rawDynamicTruthFormulaAnd7Code_deep_closed_from; try exact hPA.
    + apply raw_fixedFormulaNumeralCode_deep_closed_from_scope;
        [exact hPA | exact dynamicTruthGlobalModeDefinedFormula_scoped_13].
    + apply raw_fixedFormulaNumeralCode_deep_closed_from_scope;
        [exact hPA | exact dynamicTruthGlobalFormulaDefinedFormula_scoped_13].
    + apply raw_fixedFormulaNumeralCode_deep_closed_from_scope;
        [exact hPA |
         exact dynamicTruthGlobalAssignmentCodeDefinedFormula_scoped_13].
    + apply raw_fixedFormulaNumeralCode_deep_closed_from_scope;
        [exact hPA |
         exact dynamicTruthGlobalAssignmentStepDefinedFormula_scoped_13].
    + apply raw_fixedFormulaNumeralCode_deep_closed_from_scope;
        [exact hPA | exact dynamicTruthGlobalRootBoundFormula_scoped_13].
    + apply raw_fixedFormulaNumeralCode_deep_closed_from_scope.
      * exact hPA.
      * exact (dynamicTruthGlobalRootLookupFormula_scoped_13
          rootMode hrootMode).
    + exact (rawDynamicTruthGlobalRowsCode_deep_closed
        M hPA localSigma localPi hlocal).
Qed.

Theorem dynamicTruthPairedGlobalWrapperAt_deep_closed : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      localSigma localPi globalSigma globalPi,
  RawDynamicTruthPairedGlobalWrapperAt M
    localSigma localPi globalSigma globalPi ->
  RawDynamicTruthPairedLocalRowsDeepClosedAtWrapperDepth
    M localSigma localPi ->
  RawCodedTernaryPredicateDeepClosed M globalSigma /\
  RawCodedTernaryPredicateDeepClosed M globalPi.
Proof.
  intros M hPA localSigma localPi globalSigma globalPi
    [-> ->] hlocal.
  split.
  - apply rawDynamicTruthGlobalFormulaCode_deep_closed_of_local_rows;
      try assumption.
    apply (proj1 (standardTermScopedb_spec 13 tZero)).
    reflexivity.
  - apply rawDynamicTruthGlobalFormulaCode_deep_closed_of_local_rows;
      try assumption.
    apply (proj1 (standardTermScopedb_spec 13 (Term.numeral 1))).
    reflexivity.
Qed.

(** Minimal unresolved local-row premise.  Adequacy is deliberately omitted;
    only arbitrary-cutoff operational fixedness from eighteen is requested. *)
Definition RawDynamicTruthPairedGlobalSuccessorLocalDeepClosure
    (M : RawPAModel) : Prop :=
  forall previousSigma previousPi lowerLevel localSigma localPi,
    RawCodedTernaryPredicateDeepClosed M previousSigma ->
    RawCodedTernaryPredicateDeepClosed M previousPi ->
    RawDynamicTruthPairedSuccessorRowAt M
      previousSigma previousPi lowerLevel localSigma localPi ->
    RawCodedFormulaDeepOperationallyClosedFrom M
      (rawNumeralValue M 18) localSigma /\
    RawCodedFormulaDeepOperationallyClosedFrom M
      (rawNumeralValue M 18) localPi.

Arguments RawDynamicTruthPairedGlobalSuccessorLocalDeepClosure M
  : clear implicits.

(** Relation-level successor preservation. *)
Theorem dynamicTruthPairedGlobalSuccessorAt_deep_closed : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPairedGlobalSuccessorLocalDeepClosure M ->
  forall previousSigma previousPi lowerLevel nextSigma nextPi,
  RawCodedTernaryPredicateDeepClosed M previousSigma ->
  RawCodedTernaryPredicateDeepClosed M previousPi ->
  RawDynamicTruthPairedGlobalSuccessorAt M
    previousSigma previousPi lowerLevel nextSigma nextPi ->
  RawCodedTernaryPredicateDeepClosed M nextSigma /\
  RawCodedTernaryPredicateDeepClosed M nextPi.
Proof.
  intros M hPA hlocalClosure previousSigma previousPi lowerLevel
    nextSigma nextPi hpreviousSigma hpreviousPi
    (localSigma & localPi & hrow & hwrapper).
  destruct (rawDynamicTruthPairedSuccessorRowAt_atomically_adequate
    M hPA previousSigma previousPi lowerLevel localSigma localPi hrow)
    as [hlocalSigmaAdequate hlocalPiAdequate].
  destruct (hlocalClosure previousSigma previousPi lowerLevel
    localSigma localPi hpreviousSigma hpreviousPi hrow)
    as [hlocalSigmaOperational hlocalPiOperational].
  apply (dynamicTruthPairedGlobalWrapperAt_deep_closed M hPA
    localSigma localPi nextSigma nextPi hwrapper).
  split; split; assumption.
Qed.

(** Direct successor-totality shape consumed by the paired deep orbit. *)
Definition RawDynamicTruthPairedGlobalDeepClosedSuccessorTotal
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) lowerLevel previousSigma previousPi,
    RawCodedTernaryPredicateDeepClosed M previousSigma ->
    RawCodedTernaryPredicateDeepClosed M previousPi ->
    exists nextSigma nextPi : M,
      raw_formula_sat M
        (scons M nextSigma (scons M nextPi
          (scons M previousSigma (scons M previousPi
            (scons M lowerLevel tail)))))
        dynamicTruthPairedGlobalSuccessorGraph /\
      RawCodedTernaryPredicateDeepClosed M nextSigma /\
      RawCodedTernaryPredicateDeepClosed M nextPi.

Arguments RawDynamicTruthPairedGlobalDeepClosedSuccessorTotal M
  : clear implicits.

Theorem dynamicTruthPairedGlobalSuccessorGraph_raw_deep_closed_total : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPairedGlobalSuccessorLocalDeepClosure M ->
  RawDynamicTruthPairedGlobalDeepClosedSuccessorTotal M.
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
  - exact (dynamicTruthPairedGlobalSuccessorAt_deep_closed
      M hPA hlocalClosure previousSigma previousPi lowerLevel
      nextSigma nextPi hpreviousSigma hpreviousPi
      (ex_intro _ localSigma (ex_intro _ localPi (conj hrow hwrapper)))).
Qed.

End PABoundedRawCodedDynamicTruthGlobalSuccessorDeepClosure.
