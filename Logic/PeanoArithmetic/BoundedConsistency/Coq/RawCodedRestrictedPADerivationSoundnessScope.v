(**
  Metatheoretic scope certificates for the fixed-level proof-code
  soundness predicate.

  The two fixed truth traversals are mutually recursive.  Their only
  nonlocal leaves occur below the three binders introduced by an assignment
  prepend.  We therefore prove their scope interface simultaneously, with
  arbitrary scoped terms for the formula code and the two assignment-table
  parameters.  The remainder of the file composes that interface through
  admissibility, context truth, and the represented proof checker.
*)

From Stdlib Require Import List Arith Lia.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From BoundedPAConsistency Require Import
  RawCodedScopedFormulaDiagonalSubstitution
  RawCodedStandardFormulaScopeCombinators
  RawCodedStandardFormulaScopeDecision
  RawCodedAssignment
  RawCodedBasicFormulaScopes
  RawCodedContextLists
  RawCodedContextListScopes
  RawCodedFormulaOperationScopes
  RawCodedPAAxiomWitnessBoundScopes
  RawCodedPAAxiomWitnessScopes
  RawCodedRestrictedPADynamicSoundnessFieldScopes
  RawCodedRestrictedPADynamicSoundnessRemainingFieldScopes
  RawCodedTermEvaluationTraversal
  RawCodedRankZeroTruthTraversal
  RawCodedFixedLevelTruth
  RawCodedFixedLevelTruthTraversal
  RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelContextTruth
  RawCodedContextBounds
  RawCodedProofTraversal
  RawCodedRestrictedProofTraversal
  RawCodedRestrictedPAProof
  RawCodedProofRules
  RawCodedRestrictedPADerivationSoundnessPredicate.

Module PABoundedRawCodedRestrictedPADerivationSoundnessScope.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PABoundedRawCodedScopedFormulaDiagonalSubstitution.
Import PABoundedRawCodedStandardFormulaScopeCombinators.
Import PABoundedRawCodedStandardFormulaScopeDecision.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedBasicFormulaScopes.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextListScopes.
Import PABoundedRawCodedFormulaOperationScopes.
Import PABoundedRawCodedPAAxiomWitnessBoundScopes.
Import PABoundedRawCodedPAAxiomWitnessScopes.
Import PABoundedRawCodedRestrictedPADynamicSoundnessFieldScopes.
Import PABoundedRawCodedRestrictedPADynamicSoundnessRemainingFieldScopes.
Import PABoundedRawCodedTermEvaluationTraversal.
Import PABoundedRawCodedRankZeroTruthTraversal.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelContextTruth.
Import PABoundedRawCodedContextBounds.
Import PABoundedRawCodedProofTraversal.
Import PABoundedRawCodedRestrictedProofTraversal.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedRestrictedPADerivationSoundnessPredicate.

Lemma standardFormulaScoped_codedAssignmentPrependTermAt : forall scope
    sourceCode sourceStep head bound targetCode targetStep,
  StandardTermScoped scope sourceCode ->
  StandardTermScoped scope sourceStep ->
  StandardTermScoped scope head ->
  StandardTermScoped scope bound ->
  StandardTermScoped scope targetCode ->
  StandardTermScoped scope targetStep ->
  StandardFormulaScoped scope
    (codedAssignmentPrependTermAt
      sourceCode sourceStep head bound targetCode targetStep).
Proof.
  intros scope sourceCode sourceStep head bound targetCode targetStep
    hsourceCode hsourceStep hhead hbound htargetCode htargetStep.
  apply standardFormulaScoped_of_rename_invariant.
  intros renaming hfix.
  unfold codedAssignmentPrependTermAt.
  rewrite Formula.rename_betaPrependPrefixTermAt.
  rewrite (standardTermScoped_rename_fixed
    scope sourceCode renaming hsourceCode hfix).
  rewrite (standardTermScoped_rename_fixed
    scope sourceStep renaming hsourceStep hfix).
  rewrite (standardTermScoped_rename_fixed
    scope head renaming hhead hfix).
  rewrite (standardTermScoped_rename_fixed
    scope bound renaming hbound hfix).
  rewrite (standardTermScoped_rename_fixed
    scope targetCode renaming htargetCode hfix).
  rewrite (standardTermScoped_rename_fixed
    scope targetStep renaming htargetStep hfix).
  reflexivity.
Qed.

(** The rank-zero truth leaf contains a second, nested traversal for term
    evaluation.  Factoring these named scope lemmas prevents the generic
    syntax tactic from expanding the complete two-level graph in one kernel
    reduction. *)
Lemma termEvaluationClosedWitnessRowTermAt_scoped : forall scope
    code value assignmentCode assignmentStep tableCode tableStep
    supportCode supportStep left leftValue right rightValue,
  StandardTermScoped scope code ->
  StandardTermScoped scope value ->
  StandardTermScoped scope assignmentCode ->
  StandardTermScoped scope assignmentStep ->
  StandardTermScoped scope tableCode ->
  StandardTermScoped scope tableStep ->
  StandardTermScoped scope supportCode ->
  StandardTermScoped scope supportStep ->
  StandardTermScoped scope left ->
  StandardTermScoped scope leftValue ->
  StandardTermScoped scope right ->
  StandardTermScoped scope rightValue ->
  StandardFormulaScoped scope
    (termEvaluationClosedWitnessRowTermAt
      code value assignmentCode assignmentStep tableCode tableStep
      supportCode supportStep left leftValue right rightValue).
Proof.
  intros scope code value assignmentCode assignmentStep tableCode tableStep
    supportCode supportStep left leftValue right rightValue
    hcode hvalue hassignmentCode hassignmentStep htableCode htableStep
    hsupportCode hsupportStep hleft hleftValue hright hrightValue.
  unfold termEvaluationClosedWitnessRowTermAt,
    termSuccEvaluationClosedRowTermAt,
    termAddEvaluationClosedRowTermAt,
    termMulEvaluationClosedRowTermAt, pAnd3, pAnd4.
  repeat first
    [apply standardFormulaScoped_or | apply standardFormulaScoped_and].
  all: raw_scope_formula.
Qed.

Lemma termEvaluationClosedStepTermAt_scoped : forall scope
    code value assignmentCode assignmentStep tableCode tableStep
    supportCode supportStep,
  StandardTermScoped scope code ->
  StandardTermScoped scope value ->
  StandardTermScoped scope assignmentCode ->
  StandardTermScoped scope assignmentStep ->
  StandardTermScoped scope tableCode ->
  StandardTermScoped scope tableStep ->
  StandardTermScoped scope supportCode ->
  StandardTermScoped scope supportStep ->
  StandardFormulaScoped scope
    (termEvaluationClosedStepTermAt
      code value assignmentCode assignmentStep tableCode tableStep
      supportCode supportStep).
Proof.
  intros scope code value assignmentCode assignmentStep tableCode tableStep
    supportCode supportStep hcode hvalue hassignmentCode hassignmentStep
    htableCode htableStep hsupportCode hsupportStep.
  unfold termEvaluationClosedStepTermAt, pEx4.
  repeat apply standardFormulaScoped_ex.
  apply termEvaluationClosedWitnessRowTermAt_scoped;
    raw_scope_term.
Qed.

Lemma termEvaluationTraversalTermAt_scoped : forall scope
    bound assignmentCode assignmentStep tableCode tableStep
    supportCode supportStep,
  StandardTermScoped scope bound ->
  StandardTermScoped scope assignmentCode ->
  StandardTermScoped scope assignmentStep ->
  StandardTermScoped scope tableCode ->
  StandardTermScoped scope tableStep ->
  StandardTermScoped scope supportCode ->
  StandardTermScoped scope supportStep ->
  StandardFormulaScoped scope
    (termEvaluationTraversalTermAt
      bound assignmentCode assignmentStep tableCode tableStep
      supportCode supportStep).
Proof.
  intros scope bound assignmentCode assignmentStep tableCode tableStep
    supportCode supportStep hbound hassignmentCode hassignmentStep
    htableCode htableStep hsupportCode hsupportStep.
  unfold termEvaluationTraversalTermAt, pAnd3.
  repeat apply standardFormulaScoped_and.
  - raw_scope_formula.
  - raw_scope_formula.
  - apply standardFormulaScoped_all.
    repeat apply standardFormulaScoped_imp.
    + raw_scope_formula.
    + raw_scope_formula.
    + apply standardFormulaScoped_ex.
      apply standardFormulaScoped_and.
      * raw_scope_formula.
      * apply termEvaluationClosedStepTermAt_scoped;
          raw_scope_term.
Qed.

Lemma termEvaluationCertificateWithTablesTermAt_scoped : forall scope
    root value assignmentCode assignmentStep tableCode tableStep
    supportCode supportStep,
  StandardTermScoped scope root ->
  StandardTermScoped scope value ->
  StandardTermScoped scope assignmentCode ->
  StandardTermScoped scope assignmentStep ->
  StandardTermScoped scope tableCode ->
  StandardTermScoped scope tableStep ->
  StandardTermScoped scope supportCode ->
  StandardTermScoped scope supportStep ->
  StandardFormulaScoped scope
    (termEvaluationCertificateWithTablesTermAt
      root value assignmentCode assignmentStep tableCode tableStep
      supportCode supportStep).
Proof.
  intros scope root value assignmentCode assignmentStep tableCode tableStep
    supportCode supportStep hroot hvalue hassignmentCode hassignmentStep
    htableCode htableStep hsupportCode hsupportStep.
  unfold termEvaluationCertificateWithTablesTermAt.
  apply standardFormulaScoped_and.
  - apply termEvaluationTraversalTermAt_scoped; raw_scope_term.
  - apply standardFormulaScoped_and; raw_scope_formula.
Qed.

Lemma termEvaluationCertificateTermAt_scoped : forall scope
    root value assignmentCode assignmentStep,
  StandardTermScoped scope root ->
  StandardTermScoped scope value ->
  StandardTermScoped scope assignmentCode ->
  StandardTermScoped scope assignmentStep ->
  StandardFormulaScoped scope
    (termEvaluationCertificateTermAt
      root value assignmentCode assignmentStep).
Proof.
  intros scope root value assignmentCode assignmentStep
    hroot hvalue hassignmentCode hassignmentStep.
  unfold termEvaluationCertificateTermAt, pEx4.
  repeat apply standardFormulaScoped_ex.
  apply termEvaluationCertificateWithTablesTermAt_scoped;
    raw_scope_term.
Qed.

Lemma rankZeroEqCertifiedRowTermAt_scoped : forall scope
    code output assignmentCode assignmentStep
    left leftValue right rightValue,
  StandardTermScoped scope code ->
  StandardTermScoped scope output ->
  StandardTermScoped scope assignmentCode ->
  StandardTermScoped scope assignmentStep ->
  StandardTermScoped scope left ->
  StandardTermScoped scope leftValue ->
  StandardTermScoped scope right ->
  StandardTermScoped scope rightValue ->
  StandardFormulaScoped scope
    (rankZeroEqCertifiedRowTermAt
      code output assignmentCode assignmentStep
      left leftValue right rightValue).
Proof.
  intros scope code output assignmentCode assignmentStep
    left leftValue right rightValue
    hcode houtput hassignmentCode hassignmentStep
    hleft hleftValue hright hrightValue.
  unfold rankZeroEqCertifiedRowTermAt.
  apply standardFormulaScoped_and.
  - raw_scope_formula.
  - apply standardFormulaScoped_and.
    + apply termEvaluationCertificateTermAt_scoped; assumption.
    + apply standardFormulaScoped_and.
      * apply termEvaluationCertificateTermAt_scoped; assumption.
      * raw_scope_formula.
Qed.

Lemma rankZeroTruthClosedWitnessRowTermAt_scoped : forall scope
    code output assignmentCode assignmentStep truthCode truthStep
    supportCode supportStep left leftValue right rightValue,
  StandardTermScoped scope code ->
  StandardTermScoped scope output ->
  StandardTermScoped scope assignmentCode ->
  StandardTermScoped scope assignmentStep ->
  StandardTermScoped scope truthCode ->
  StandardTermScoped scope truthStep ->
  StandardTermScoped scope supportCode ->
  StandardTermScoped scope supportStep ->
  StandardTermScoped scope left ->
  StandardTermScoped scope leftValue ->
  StandardTermScoped scope right ->
  StandardTermScoped scope rightValue ->
  StandardFormulaScoped scope
    (rankZeroTruthClosedWitnessRowTermAt
      code output assignmentCode assignmentStep truthCode truthStep
      supportCode supportStep left leftValue right rightValue).
Proof.
  intros scope code output assignmentCode assignmentStep truthCode truthStep
    supportCode supportStep left leftValue right rightValue
    hcode houtput hassignmentCode hassignmentStep htruthCode htruthStep
    hsupportCode hsupportStep hleft hleftValue hright hrightValue.
  unfold rankZeroTruthClosedWitnessRowTermAt,
    rankZeroImpClosedRowTermAt,
    rankZeroAndClosedRowTermAt,
    rankZeroOrClosedRowTermAt, pAnd4.
  repeat first
    [apply standardFormulaScoped_or | apply standardFormulaScoped_and].
  all: first
    [apply rankZeroEqCertifiedRowTermAt_scoped; assumption
    |raw_scope_formula].
Qed.

Lemma rankZeroTruthClosedStepTermAt_scoped : forall scope
    code output assignmentCode assignmentStep truthCode truthStep
    supportCode supportStep,
  StandardTermScoped scope code ->
  StandardTermScoped scope output ->
  StandardTermScoped scope assignmentCode ->
  StandardTermScoped scope assignmentStep ->
  StandardTermScoped scope truthCode ->
  StandardTermScoped scope truthStep ->
  StandardTermScoped scope supportCode ->
  StandardTermScoped scope supportStep ->
  StandardFormulaScoped scope
    (rankZeroTruthClosedStepTermAt
      code output assignmentCode assignmentStep truthCode truthStep
      supportCode supportStep).
Proof.
  intros scope code output assignmentCode assignmentStep truthCode truthStep
    supportCode supportStep hcode houtput hassignmentCode hassignmentStep
    htruthCode htruthStep hsupportCode hsupportStep.
  unfold rankZeroTruthClosedStepTermAt, pEx4.
  repeat apply standardFormulaScoped_ex.
  apply rankZeroTruthClosedWitnessRowTermAt_scoped;
    raw_scope_term.
Qed.

Lemma rankZeroTruthTraversalTermAt_scoped : forall scope
    bound assignmentCode assignmentStep truthCode truthStep
    supportCode supportStep,
  StandardTermScoped scope bound ->
  StandardTermScoped scope assignmentCode ->
  StandardTermScoped scope assignmentStep ->
  StandardTermScoped scope truthCode ->
  StandardTermScoped scope truthStep ->
  StandardTermScoped scope supportCode ->
  StandardTermScoped scope supportStep ->
  StandardFormulaScoped scope
    (rankZeroTruthTraversalTermAt
      bound assignmentCode assignmentStep truthCode truthStep
      supportCode supportStep).
Proof.
  intros scope bound assignmentCode assignmentStep truthCode truthStep
    supportCode supportStep hbound hassignmentCode hassignmentStep
    htruthCode htruthStep hsupportCode hsupportStep.
  unfold rankZeroTruthTraversalTermAt, pAnd3.
  repeat apply standardFormulaScoped_and.
  - raw_scope_formula.
  - raw_scope_formula.
  - apply standardFormulaScoped_all.
    repeat apply standardFormulaScoped_imp.
    + raw_scope_formula.
    + raw_scope_formula.
    + apply standardFormulaScoped_ex.
      apply standardFormulaScoped_and.
      * raw_scope_formula.
      * apply rankZeroTruthClosedStepTermAt_scoped;
          raw_scope_term.
Qed.

Lemma rankZeroTruthCertificateWithTablesTermAt_scoped : forall scope
    root output assignmentCode assignmentStep truthCode truthStep
    supportCode supportStep,
  StandardTermScoped scope root ->
  StandardTermScoped scope output ->
  StandardTermScoped scope assignmentCode ->
  StandardTermScoped scope assignmentStep ->
  StandardTermScoped scope truthCode ->
  StandardTermScoped scope truthStep ->
  StandardTermScoped scope supportCode ->
  StandardTermScoped scope supportStep ->
  StandardFormulaScoped scope
    (rankZeroTruthCertificateWithTablesTermAt
      root output assignmentCode assignmentStep truthCode truthStep
      supportCode supportStep).
Proof.
  intros scope root output assignmentCode assignmentStep truthCode truthStep
    supportCode supportStep hroot houtput hassignmentCode hassignmentStep
    htruthCode htruthStep hsupportCode hsupportStep.
  unfold rankZeroTruthCertificateWithTablesTermAt.
  apply standardFormulaScoped_and.
  - apply rankZeroTruthTraversalTermAt_scoped; raw_scope_term.
  - apply standardFormulaScoped_and.
    + raw_scope_formula.
    + apply standardFormulaScoped_and; raw_scope_formula.
Qed.

Lemma rankZeroTruthCertificateTermAt_scoped : forall scope
    root output assignmentCode assignmentStep,
  StandardTermScoped scope root ->
  StandardTermScoped scope output ->
  StandardTermScoped scope assignmentCode ->
  StandardTermScoped scope assignmentStep ->
  StandardFormulaScoped scope
    (rankZeroTruthCertificateTermAt
      root output assignmentCode assignmentStep).
Proof.
  intros scope root output assignmentCode assignmentStep
    hroot houtput hassignmentCode hassignmentStep.
  unfold rankZeroTruthCertificateTermAt, pEx4.
  repeat apply standardFormulaScoped_ex.
  apply rankZeroTruthCertificateWithTablesTermAt_scoped;
    raw_scope_term.
Qed.

Lemma fixedLevelNoBinderCounterexampleTermAt_scoped : forall scope
    lowerEvidence assignmentCode assignmentStep bound,
  StandardFormulaScoped (S (S (S scope))) lowerEvidence ->
  StandardTermScoped scope assignmentCode ->
  StandardTermScoped scope assignmentStep ->
  StandardTermScoped scope bound ->
  StandardFormulaScoped scope
    (fixedLevelNoBinderCounterexampleTermAt
      lowerEvidence assignmentCode assignmentStep bound).
Proof.
  intros scope lowerEvidence assignmentCode assignmentStep bound
    hlower hassignmentCode hassignmentStep hbound.
  unfold fixedLevelNoBinderCounterexampleTermAt, fixedLevelEx3.
  apply standardFormulaScoped_imp.
  - repeat apply standardFormulaScoped_ex.
    apply standardFormulaScoped_and.
    + apply standardFormulaScoped_codedAssignmentPrependTermAt;
        raw_scope_term.
    + exact hlower.
  - apply standardFormulaScoped_bot.
Qed.

Lemma fixedLevelStateLookupTermAt_scoped : forall scope
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    index mode code assignmentCode assignmentStep,
  StandardTermScoped scope modeCode ->
  StandardTermScoped scope modeStep ->
  StandardTermScoped scope formulaCode ->
  StandardTermScoped scope formulaStep ->
  StandardTermScoped scope assignmentCodeCode ->
  StandardTermScoped scope assignmentCodeStep ->
  StandardTermScoped scope assignmentStepCode ->
  StandardTermScoped scope assignmentStepStep ->
  StandardTermScoped scope index ->
  StandardTermScoped scope mode ->
  StandardTermScoped scope code ->
  StandardTermScoped scope assignmentCode ->
  StandardTermScoped scope assignmentStep ->
  StandardFormulaScoped scope
    (fixedLevelStateLookupTermAt
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      index mode code assignmentCode assignmentStep).
Proof.
  intros scope modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    index mode code assignmentCode assignmentStep
    hmodeCode hmodeStep hformulaCode hformulaStep
    hassignmentCodeCode hassignmentCodeStep
    hassignmentStepCode hassignmentStepStep
    hindex hmode hcode hassignmentCode hassignmentStep.
  unfold fixedLevelStateLookupTermAt, fixedLevelAnd4.
  apply standardFormulaScoped_and; [raw_scope_formula |].
  apply standardFormulaScoped_and; [raw_scope_formula |].
  apply standardFormulaScoped_and; raw_scope_formula.
Qed.

Lemma fixedLevelEarlierStateTermAt_scoped : forall scope
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    currentIndex childIndex expectedMode childCode
    childAssignmentCode childAssignmentStep,
  StandardTermScoped scope modeCode ->
  StandardTermScoped scope modeStep ->
  StandardTermScoped scope formulaCode ->
  StandardTermScoped scope formulaStep ->
  StandardTermScoped scope assignmentCodeCode ->
  StandardTermScoped scope assignmentCodeStep ->
  StandardTermScoped scope assignmentStepCode ->
  StandardTermScoped scope assignmentStepStep ->
  StandardTermScoped scope currentIndex ->
  StandardTermScoped scope childIndex ->
  StandardTermScoped scope expectedMode ->
  StandardTermScoped scope childCode ->
  StandardTermScoped scope childAssignmentCode ->
  StandardTermScoped scope childAssignmentStep ->
  StandardFormulaScoped scope
    (fixedLevelEarlierStateTermAt
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      currentIndex childIndex expectedMode childCode
      childAssignmentCode childAssignmentStep).
Proof.
  intros scope modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    currentIndex childIndex expectedMode childCode
    childAssignmentCode childAssignmentStep
    hmodeCode hmodeStep hformulaCode hformulaStep
    hassignmentCodeCode hassignmentCodeStep
    hassignmentStepCode hassignmentStepStep
    hcurrentIndex hchildIndex hexpectedMode hchildCode
    hchildAssignmentCode hchildAssignmentStep.
  unfold fixedLevelEarlierStateTermAt.
  apply standardFormulaScoped_and.
  - raw_scope_formula.
  - apply fixedLevelStateLookupTermAt_scoped; assumption.
Qed.

Ltac split_visible_scope_connectives :=
  repeat lazymatch goal with
  | |- StandardFormulaScoped _ (pAnd _ _) =>
      apply standardFormulaScoped_and
  | |- StandardFormulaScoped _ (pOr _ _) =>
      apply standardFormulaScoped_or
  end.

Lemma fixedLevelSigmaSuccessorWitnessRowTermAt_scoped : forall
    scope level lowerPiEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep
    leftIndex leftCode rightIndex rightCode
    witness newAssignmentCode newAssignmentStep spare,
  StandardFormulaScoped (S (S (S scope))) lowerPiEvidence ->
  StandardTermScoped scope modeCode ->
  StandardTermScoped scope modeStep ->
  StandardTermScoped scope formulaCode ->
  StandardTermScoped scope formulaStep ->
  StandardTermScoped scope assignmentCodeCode ->
  StandardTermScoped scope assignmentCodeStep ->
  StandardTermScoped scope assignmentStepCode ->
  StandardTermScoped scope assignmentStepStep ->
  StandardTermScoped scope currentIndex ->
  StandardTermScoped scope code ->
  StandardTermScoped scope assignmentCode ->
  StandardTermScoped scope assignmentStep ->
  StandardTermScoped scope leftIndex ->
  StandardTermScoped scope leftCode ->
  StandardTermScoped scope rightIndex ->
  StandardTermScoped scope rightCode ->
  StandardTermScoped scope witness ->
  StandardTermScoped scope newAssignmentCode ->
  StandardTermScoped scope newAssignmentStep ->
  StandardTermScoped scope spare ->
  StandardFormulaScoped scope
    (fixedLevelSigmaSuccessorWitnessRowTermAt level lowerPiEvidence
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      currentIndex code assignmentCode assignmentStep
      leftIndex leftCode rightIndex rightCode
      witness newAssignmentCode newAssignmentStep spare).
Proof.
  intros scope level lowerPiEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep
    leftIndex leftCode rightIndex rightCode
    witness newAssignmentCode newAssignmentStep spare
    hlower hmodeCode hmodeStep hformulaCode hformulaStep
    hassignmentCodeCode hassignmentCodeStep
    hassignmentStepCode hassignmentStepStep
    hcurrentIndex hcode hassignmentCode hassignmentStep
    hleftIndex hleftCode hrightIndex hrightCode
    hwitness hnewAssignmentCode hnewAssignmentStep hspare.
  unfold fixedLevelSigmaSuccessorWitnessRowTermAt.
  apply standardFormulaScoped_and.
  - raw_scope_formula.
  - unfold fixedLevelOr7, fixedLevelAnd3.
    split_visible_scope_connectives.
    all: lazymatch goal with
    | |- StandardFormulaScoped _
        (rankZeroTruthCertificateTermAt _ _ _ _) =>
        apply rankZeroTruthCertificateTermAt_scoped; raw_scope_term
    | |- StandardFormulaScoped _
        (codedAssignmentPrependTermAt _ _ _ _ _ _) =>
        apply standardFormulaScoped_codedAssignmentPrependTermAt;
          raw_scope_term
    | |- StandardFormulaScoped _
        (fixedLevelNoBinderCounterexampleTermAt _ _ _ _) =>
        apply fixedLevelNoBinderCounterexampleTermAt_scoped;
          assumption
    | |- StandardFormulaScoped _
        (fixedLevelEarlierStateTermAt _ _ _ _ _ _ _ _ _ _ _ _ _ _) =>
        apply fixedLevelEarlierStateTermAt_scoped; raw_scope_term
    | |- _ => raw_scope_formula
    end.
Qed.

Lemma fixedLevelPiSuccessorWitnessRowTermAt_scoped : forall
    scope level lowerSigmaEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep
    leftIndex leftCode rightIndex rightCode
    witness newAssignmentCode newAssignmentStep spare,
  StandardFormulaScoped (S (S (S scope))) lowerSigmaEvidence ->
  StandardTermScoped scope modeCode ->
  StandardTermScoped scope modeStep ->
  StandardTermScoped scope formulaCode ->
  StandardTermScoped scope formulaStep ->
  StandardTermScoped scope assignmentCodeCode ->
  StandardTermScoped scope assignmentCodeStep ->
  StandardTermScoped scope assignmentStepCode ->
  StandardTermScoped scope assignmentStepStep ->
  StandardTermScoped scope currentIndex ->
  StandardTermScoped scope code ->
  StandardTermScoped scope assignmentCode ->
  StandardTermScoped scope assignmentStep ->
  StandardTermScoped scope leftIndex ->
  StandardTermScoped scope leftCode ->
  StandardTermScoped scope rightIndex ->
  StandardTermScoped scope rightCode ->
  StandardTermScoped scope witness ->
  StandardTermScoped scope newAssignmentCode ->
  StandardTermScoped scope newAssignmentStep ->
  StandardTermScoped scope spare ->
  StandardFormulaScoped scope
    (fixedLevelPiSuccessorWitnessRowTermAt level lowerSigmaEvidence
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      currentIndex code assignmentCode assignmentStep
      leftIndex leftCode rightIndex rightCode
      witness newAssignmentCode newAssignmentStep spare).
Proof.
  intros scope level lowerSigmaEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep
    leftIndex leftCode rightIndex rightCode
    witness newAssignmentCode newAssignmentStep spare
    hlower hmodeCode hmodeStep hformulaCode hformulaStep
    hassignmentCodeCode hassignmentCodeStep
    hassignmentStepCode hassignmentStepStep
    hcurrentIndex hcode hassignmentCode hassignmentStep
    hleftIndex hleftCode hrightIndex hrightCode
    hwitness hnewAssignmentCode hnewAssignmentStep hspare.
  unfold fixedLevelPiSuccessorWitnessRowTermAt.
  apply standardFormulaScoped_and.
  - raw_scope_formula.
  - unfold fixedLevelOr6, fixedLevelAnd3, fixedLevelAnd4.
    split_visible_scope_connectives.
    all: lazymatch goal with
    | |- StandardFormulaScoped _
        (rankZeroTruthCertificateTermAt _ _ _ _) =>
        apply rankZeroTruthCertificateTermAt_scoped; raw_scope_term
    | |- StandardFormulaScoped _
        (codedAssignmentPrependTermAt _ _ _ _ _ _) =>
        apply standardFormulaScoped_codedAssignmentPrependTermAt;
          raw_scope_term
    | |- StandardFormulaScoped _
        (fixedLevelNoBinderCounterexampleTermAt _ _ _ _) =>
        apply fixedLevelNoBinderCounterexampleTermAt_scoped;
          assumption
    | |- StandardFormulaScoped _
        (fixedLevelEarlierStateTermAt _ _ _ _ _ _ _ _ _ _ _ _ _ _) =>
        apply fixedLevelEarlierStateTermAt_scoped; raw_scope_term
    | |- _ => raw_scope_formula
    end.
Qed.

(** The higher-order evidence parameters are required at every syntactic
    scope.  This is exactly what the simultaneous induction below supplies;
    in the opposite-quantifier branch the application sits below the row's
    eight witnesses and the assignment-prepend clause's three witnesses. *)
Lemma fixedLevelClosedSuccessorRowTermAt_scoped : forall
    lower
    (lowerSigmaEvidence lowerPiEvidence : term -> term -> term -> formula),
  (forall scope child assignmentCode assignmentStep,
    StandardTermScoped scope child ->
    StandardTermScoped scope assignmentCode ->
    StandardTermScoped scope assignmentStep ->
    StandardFormulaScoped scope
      (lowerSigmaEvidence child assignmentCode assignmentStep)) ->
  (forall scope child assignmentCode assignmentStep,
    StandardTermScoped scope child ->
    StandardTermScoped scope assignmentCode ->
    StandardTermScoped scope assignmentStep ->
    StandardFormulaScoped scope
      (lowerPiEvidence child assignmentCode assignmentStep)) ->
  forall scope
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    index mode code assignmentCode assignmentStep,
  StandardTermScoped scope modeCode ->
  StandardTermScoped scope modeStep ->
  StandardTermScoped scope formulaCode ->
  StandardTermScoped scope formulaStep ->
  StandardTermScoped scope assignmentCodeCode ->
  StandardTermScoped scope assignmentCodeStep ->
  StandardTermScoped scope assignmentStepCode ->
  StandardTermScoped scope assignmentStepStep ->
  StandardTermScoped scope index ->
  StandardTermScoped scope mode ->
  StandardTermScoped scope code ->
  StandardTermScoped scope assignmentCode ->
  StandardTermScoped scope assignmentStep ->
  StandardFormulaScoped scope
    (fixedLevelClosedSuccessorRowTermAt lower
      lowerSigmaEvidence lowerPiEvidence
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      index mode code assignmentCode assignmentStep).
Proof.
  intros lower lowerSigmaEvidence lowerPiEvidence
    hSigma hPi scope
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    index mode code assignmentCode assignmentStep
    hmodeCode hmodeStep hformulaCode hformulaStep
    hassignmentCodeCode hassignmentCodeStep
    hassignmentStepCode hassignmentStepStep
    hindex hmode hcode hassignmentCode hassignmentStep.
  unfold fixedLevelClosedSuccessorRowTermAt.
  apply standardFormulaScoped_or.
  - apply standardFormulaScoped_and.
    + apply standardFormulaScoped_eq; raw_scope_term.
    + unfold fixedLevelEx8.
      repeat apply standardFormulaScoped_ex.
      eapply fixedLevelSigmaSuccessorWitnessRowTermAt_scoped.
      1: apply hPi; raw_scope_term.
      all: raw_scope_term.
  - apply standardFormulaScoped_and.
    + apply standardFormulaScoped_eq; raw_scope_term.
    + unfold fixedLevelEx8.
      repeat apply standardFormulaScoped_ex.
      eapply fixedLevelPiSuccessorWitnessRowTermAt_scoped.
      1: apply hSigma; raw_scope_term.
      all: raw_scope_term.
Qed.

Lemma fixedLevelZeroTruthTraversalRowsTermAt_scoped : forall scope
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound,
  StandardTermScoped scope modeCode ->
  StandardTermScoped scope modeStep ->
  StandardTermScoped scope formulaCode ->
  StandardTermScoped scope formulaStep ->
  StandardTermScoped scope assignmentCodeCode ->
  StandardTermScoped scope assignmentCodeStep ->
  StandardTermScoped scope assignmentStepCode ->
  StandardTermScoped scope assignmentStepStep ->
  StandardTermScoped scope bound ->
  StandardFormulaScoped scope
    (fixedLevelZeroTruthTraversalRowsTermAt
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound).
Proof.
  intros scope modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound
    hmodeCode hmodeStep hformulaCode hformulaStep
    hassignmentCodeCode hassignmentCodeStep
    hassignmentStepCode hassignmentStepStep hbound.
  unfold fixedLevelZeroTruthTraversalRowsTermAt,
    fixedTruthTraversalAll5.
  repeat apply standardFormulaScoped_all.
  repeat apply standardFormulaScoped_imp.
  all: raw_scope_formula.
Qed.

Lemma fixedLevelSuccessorTruthTraversalRowsTermAt_scoped : forall
    lower
    (lowerSigmaEvidence lowerPiEvidence : term -> term -> term -> formula),
  (forall scope child assignmentCode assignmentStep,
    StandardTermScoped scope child ->
    StandardTermScoped scope assignmentCode ->
    StandardTermScoped scope assignmentStep ->
    StandardFormulaScoped scope
      (lowerSigmaEvidence child assignmentCode assignmentStep)) ->
  (forall scope child assignmentCode assignmentStep,
    StandardTermScoped scope child ->
    StandardTermScoped scope assignmentCode ->
    StandardTermScoped scope assignmentStep ->
    StandardFormulaScoped scope
      (lowerPiEvidence child assignmentCode assignmentStep)) ->
  forall scope
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound,
  StandardTermScoped scope modeCode ->
  StandardTermScoped scope modeStep ->
  StandardTermScoped scope formulaCode ->
  StandardTermScoped scope formulaStep ->
  StandardTermScoped scope assignmentCodeCode ->
  StandardTermScoped scope assignmentCodeStep ->
  StandardTermScoped scope assignmentStepCode ->
  StandardTermScoped scope assignmentStepStep ->
  StandardTermScoped scope bound ->
  StandardFormulaScoped scope
    (fixedLevelSuccessorTruthTraversalRowsTermAt lower
      lowerSigmaEvidence lowerPiEvidence
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound).
Proof.
  intros lower lowerSigmaEvidence lowerPiEvidence hSigma hPi
    scope modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound
    hmodeCode hmodeStep hformulaCode hformulaStep
    hassignmentCodeCode hassignmentCodeStep
    hassignmentStepCode hassignmentStepStep hbound.
  unfold fixedLevelSuccessorTruthTraversalRowsTermAt,
    fixedTruthTraversalAll5.
  repeat apply standardFormulaScoped_all.
  apply standardFormulaScoped_imp.
  - raw_scope_formula.
  - apply standardFormulaScoped_imp.
    + apply fixedLevelStateLookupTermAt_scoped; raw_scope_term.
    + eapply fixedLevelClosedSuccessorRowTermAt_scoped.
      1: exact hSigma.
      1: exact hPi.
      all: raw_scope_term.
Qed.

Lemma fixedLevelZeroTruthTraversalTermAt_scoped : forall scope
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep,
  StandardTermScoped scope modeCode ->
  StandardTermScoped scope modeStep ->
  StandardTermScoped scope formulaCode ->
  StandardTermScoped scope formulaStep ->
  StandardTermScoped scope assignmentCodeCode ->
  StandardTermScoped scope assignmentCodeStep ->
  StandardTermScoped scope assignmentStepCode ->
  StandardTermScoped scope assignmentStepStep ->
  StandardTermScoped scope bound ->
  StandardTermScoped scope rootIndex ->
  StandardTermScoped scope rootMode ->
  StandardTermScoped scope root ->
  StandardTermScoped scope assignmentCode ->
  StandardTermScoped scope assignmentStep ->
  StandardFormulaScoped scope
    (fixedLevelZeroTruthTraversalTermAt
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound rootIndex rootMode root assignmentCode assignmentStep).
Proof.
  intros scope modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep
    hmodeCode hmodeStep hformulaCode hformulaStep
    hassignmentCodeCode hassignmentCodeStep
    hassignmentStepCode hassignmentStepStep
    hbound hrootIndex hrootMode hroot hassignmentCode hassignmentStep.
  unfold fixedLevelZeroTruthTraversalTermAt, fixedTruthTraversalAnd7.
  repeat apply standardFormulaScoped_and.
  all: try raw_scope_formula.
  apply fixedLevelZeroTruthTraversalRowsTermAt_scoped;
    assumption.
Qed.

Lemma fixedLevelSuccessorTruthTraversalTermAt_scoped : forall
    lower
    (lowerSigmaEvidence lowerPiEvidence : term -> term -> term -> formula),
  (forall scope child assignmentCode assignmentStep,
    StandardTermScoped scope child ->
    StandardTermScoped scope assignmentCode ->
    StandardTermScoped scope assignmentStep ->
    StandardFormulaScoped scope
      (lowerSigmaEvidence child assignmentCode assignmentStep)) ->
  (forall scope child assignmentCode assignmentStep,
    StandardTermScoped scope child ->
    StandardTermScoped scope assignmentCode ->
    StandardTermScoped scope assignmentStep ->
    StandardFormulaScoped scope
      (lowerPiEvidence child assignmentCode assignmentStep)) ->
  forall scope
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep,
  StandardTermScoped scope modeCode ->
  StandardTermScoped scope modeStep ->
  StandardTermScoped scope formulaCode ->
  StandardTermScoped scope formulaStep ->
  StandardTermScoped scope assignmentCodeCode ->
  StandardTermScoped scope assignmentCodeStep ->
  StandardTermScoped scope assignmentStepCode ->
  StandardTermScoped scope assignmentStepStep ->
  StandardTermScoped scope bound ->
  StandardTermScoped scope rootIndex ->
  StandardTermScoped scope rootMode ->
  StandardTermScoped scope root ->
  StandardTermScoped scope assignmentCode ->
  StandardTermScoped scope assignmentStep ->
  StandardFormulaScoped scope
    (fixedLevelSuccessorTruthTraversalTermAt lower
      lowerSigmaEvidence lowerPiEvidence
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound rootIndex rootMode root assignmentCode assignmentStep).
Proof.
  intros lower lowerSigmaEvidence lowerPiEvidence hSigma hPi
    scope modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep
    hmodeCode hmodeStep hformulaCode hformulaStep
    hassignmentCodeCode hassignmentCodeStep
    hassignmentStepCode hassignmentStepStep
    hbound hrootIndex hrootMode hroot hassignmentCode hassignmentStep.
  unfold fixedLevelSuccessorTruthTraversalTermAt,
    fixedTruthTraversalAnd7.
  repeat apply standardFormulaScoped_and.
  all: try raw_scope_formula.
  eapply fixedLevelSuccessorTruthTraversalRowsTermAt_scoped;
    first [exact hSigma | exact hPi | assumption | raw_scope_term].
Qed.

Lemma fixedLevelZeroTruthCertificateTermAt_scoped : forall
    scope root assignmentCode assignmentStep,
  StandardTermScoped scope root ->
  StandardTermScoped scope assignmentCode ->
  StandardTermScoped scope assignmentStep ->
  StandardFormulaScoped scope
    (fixedLevelSigmaTruthCertificateTermAt 0
      root assignmentCode assignmentStep).
Proof.
  intros scope root assignmentCode assignmentStep
    hroot hassignmentCode hassignmentStep.
  cbn [fixedLevelSigmaTruthCertificateTermAt].
  unfold fixedTruthTraversalEx10, fixedLevelEx8.
  repeat apply standardFormulaScoped_ex.
  apply fixedLevelZeroTruthTraversalTermAt_scoped;
    raw_scope_term.
Qed.

Lemma fixedLevelZeroFalsityCertificateTermAt_scoped : forall
    scope root assignmentCode assignmentStep,
  StandardTermScoped scope root ->
  StandardTermScoped scope assignmentCode ->
  StandardTermScoped scope assignmentStep ->
  StandardFormulaScoped scope
    (fixedLevelPiFalsityCertificateTermAt 0
      root assignmentCode assignmentStep).
Proof.
  intros scope root assignmentCode assignmentStep
    hroot hassignmentCode hassignmentStep.
  cbn [fixedLevelPiFalsityCertificateTermAt].
  unfold fixedTruthTraversalEx10, fixedLevelEx8.
  repeat apply standardFormulaScoped_ex.
  apply fixedLevelZeroTruthTraversalTermAt_scoped;
    raw_scope_term.
Qed.

(** Simultaneous scope preservation for the mutually recursive fixed truth
    and fixed falsity certificates.  The theorem is uniform both in the
    external truth level and in the ambient free-variable scope. *)
Theorem fixedLevelTruthCertificateTermAt_scoped : forall level,
  (forall scope root assignmentCode assignmentStep,
    StandardTermScoped scope root ->
    StandardTermScoped scope assignmentCode ->
    StandardTermScoped scope assignmentStep ->
    StandardFormulaScoped scope
      (fixedLevelSigmaTruthCertificateTermAt level
        root assignmentCode assignmentStep)) /\
  (forall scope root assignmentCode assignmentStep,
    StandardTermScoped scope root ->
    StandardTermScoped scope assignmentCode ->
    StandardTermScoped scope assignmentStep ->
    StandardFormulaScoped scope
      (fixedLevelPiFalsityCertificateTermAt level
        root assignmentCode assignmentStep)).
Proof.
  induction level as [|lower [IHsigma IHpi]].
  - split.
    + exact fixedLevelZeroTruthCertificateTermAt_scoped.
    + exact fixedLevelZeroFalsityCertificateTermAt_scoped.
  - split; intros scope root assignmentCode assignmentStep
      hroot hassignmentCode hassignmentStep.
    + cbn [fixedLevelSigmaTruthCertificateTermAt].
      unfold fixedTruthTraversalEx10, fixedLevelEx8.
      repeat apply standardFormulaScoped_ex.
      eapply fixedLevelSuccessorTruthTraversalTermAt_scoped;
        first [exact IHsigma | exact IHpi | assumption | raw_scope_term].
    + cbn [fixedLevelPiFalsityCertificateTermAt].
      unfold fixedTruthTraversalEx10, fixedLevelEx8.
      repeat apply standardFormulaScoped_ex.
      eapply fixedLevelSuccessorTruthTraversalTermAt_scoped;
        first [exact IHsigma | exact IHpi | assumption | raw_scope_term].
Qed.

Corollary fixedLevelSigmaTruthCertificateTermAt_scoped : forall level
    scope root assignmentCode assignmentStep,
  StandardTermScoped scope root ->
  StandardTermScoped scope assignmentCode ->
  StandardTermScoped scope assignmentStep ->
  StandardFormulaScoped scope
    (fixedLevelSigmaTruthCertificateTermAt level
      root assignmentCode assignmentStep).
Proof.
  intro level.
  exact (proj1 (fixedLevelTruthCertificateTermAt_scoped level)).
Qed.

Corollary fixedLevelPiFalsityCertificateTermAt_scoped : forall level
    scope root assignmentCode assignmentStep,
  StandardTermScoped scope root ->
  StandardTermScoped scope assignmentCode ->
  StandardTermScoped scope assignmentStep ->
  StandardFormulaScoped scope
    (fixedLevelPiFalsityCertificateTermAt level
      root assignmentCode assignmentStep).
Proof.
  intro level.
  exact (proj2 (fixedLevelTruthCertificateTermAt_scoped level)).
Qed.

(** Scope interfaces for the four nonrecursive premises surrounding the
    recursive truth conclusion in the unary soundness predicate. *)
Lemma fixedLevelTruthAdmissibleTermAt_scoped : forall level scope
    root assignmentCode assignmentStep,
  StandardTermScoped scope root ->
  StandardTermScoped scope assignmentCode ->
  StandardTermScoped scope assignmentStep ->
  StandardFormulaScoped scope
    (fixedLevelTruthAdmissibleTermAt level
      root assignmentCode assignmentStep).
Proof.
  intros level scope root assignmentCode assignmentStep
    hroot hassignmentCode hassignmentStep.
  unfold fixedLevelTruthAdmissibleTermAt.
  raw_scope_formula.
Qed.

Lemma contextAllSigmaTrueWithTablesTermAt_scoped : forall level scope
    bound headCode headStep assignmentCode assignmentStep,
  StandardTermScoped scope bound ->
  StandardTermScoped scope headCode ->
  StandardTermScoped scope headStep ->
  StandardTermScoped scope assignmentCode ->
  StandardTermScoped scope assignmentStep ->
  StandardFormulaScoped scope
    (contextAllSigmaTrueWithTablesTermAt level
      bound headCode headStep assignmentCode assignmentStep).
Proof.
  intros level scope bound headCode headStep assignmentCode assignmentStep
    hbound hheadCode hheadStep hassignmentCode hassignmentStep.
  unfold contextAllSigmaTrueWithTablesTermAt.
  apply standardFormulaScoped_all.
  apply standardFormulaScoped_imp.
  - raw_scope_formula.
  - apply standardFormulaScoped_all.
    apply standardFormulaScoped_imp.
    + raw_scope_formula.
    + apply fixedLevelSigmaTruthCertificateTermAt_scoped;
        raw_scope_term.
Qed.

Lemma contextAllSigmaTrueTermAt_scoped : forall level scope
    root assignmentCode assignmentStep,
  StandardTermScoped scope root ->
  StandardTermScoped scope assignmentCode ->
  StandardTermScoped scope assignmentStep ->
  StandardFormulaScoped scope
    (contextAllSigmaTrueTermAt level
      root assignmentCode assignmentStep).
Proof.
  intros level scope root assignmentCode assignmentStep
    hroot hassignmentCode hassignmentStep.
  unfold contextAllSigmaTrueTermAt, contextListEx5.
  repeat apply standardFormulaScoped_ex.
  apply standardFormulaScoped_and.
  - apply standardFormulaScoped_contextListTraversalTermAt;
      raw_scope_term.
  - apply contextAllSigmaTrueWithTablesTermAt_scoped;
      raw_scope_term.
Qed.

Lemma proofRuleValidTermAt_scoped : forall scope code context conclusion,
  StandardTermScoped scope code ->
  StandardTermScoped scope context ->
  StandardTermScoped scope conclusion ->
  StandardFormulaScoped scope
    (proofRuleValidTermAt code context conclusion).
Proof.
  intros scope code context conclusion hcode hcontext hconclusion.
  raw_scope_formula.
Qed.

(** The restricted proof checker is substantially larger than the truth
    certificate above.  Its four node fields are deliberately sealed behind
    separate scope lemmas: asking the syntax-directed tactic to expand the
    entire checker in one proof duplicates the constructor tables and creates
    an unnecessarily enormous proof term. *)
Lemma proofSyntaxStepTermAt_scoped : forall scope code supportCode supportStep,
  StandardTermScoped scope code ->
  StandardTermScoped scope supportCode ->
  StandardTermScoped scope supportStep ->
  StandardFormulaScoped scope
    (proofSyntaxStepTermAt code supportCode supportStep).
Proof.
  intros scope code supportCode supportStep hcode hsupportCode hsupportStep.
  raw_scope_formula.
Qed.

Lemma proofRuleEndpointExistsTermAt_scoped : forall scope code,
  StandardTermScoped scope code ->
  StandardFormulaScoped scope (proofRuleEndpointExistsTermAt code).
Proof.
  intros scope code hcode.
  unfold proofRuleEndpointExistsTermAt, restrictedProofEx2.
  apply standardFormulaScoped_ex.
  apply standardFormulaScoped_ex.
  exact (proofRuleValidTermAt_scoped
    (S (S scope)) (liftTerm 2 code) (tVar 1) (tVar 0)
    (standardTermScoped_lift scope 2 code hcode)
    (standardTermScoped_var (S (S scope)) 1 (ltac:(lia)))
    (standardTermScoped_var (S (S scope)) 0 (ltac:(lia)))).
Qed.

(** Constructor-occurrence boundedness repeats the same rank and context
    checks for seventeen proof constructors.  These generic list lemmas keep
    those checks opaque instead of expanding their arithmetic graphs once per
    constructor. *)
Lemma formulaQuantifierBoundedTermAt_scoped : forall level scope code,
  StandardTermScoped scope code ->
  StandardFormulaScoped scope
    (formulaQuantifierBoundedTermAt level code).
Proof.
  intros level scope code hcode.
  unfold formulaQuantifierBoundedTermAt.
  apply standardFormulaScoped_or; raw_scope_formula.
Qed.

Lemma contextAllBoundedWithTablesTermAt_scoped : forall
    level scope bound headCode headStep,
  StandardTermScoped scope bound ->
  StandardTermScoped scope headCode ->
  StandardTermScoped scope headStep ->
  StandardFormulaScoped scope
    (contextAllBoundedWithTablesTermAt level bound headCode headStep).
Proof.
  intros level scope bound headCode headStep hbound hheadCode hheadStep.
  unfold contextAllBoundedWithTablesTermAt.
  apply standardFormulaScoped_all.
  apply standardFormulaScoped_imp.
  - apply standardFormulaScoped_ltTermAt; raw_scope_term.
  - apply standardFormulaScoped_all.
    apply standardFormulaScoped_imp.
    + apply standardFormulaScoped_codedAssignmentLookupTermAt;
        raw_scope_term.
    + apply formulaQuantifierBoundedTermAt_scoped; raw_scope_term.
Qed.

Lemma contextAllBoundedTermAt_scoped : forall level scope root,
  StandardTermScoped scope root ->
  StandardFormulaScoped scope (contextAllBoundedTermAt level root).
Proof.
  intros level scope root hroot.
  unfold contextAllBoundedTermAt, contextListEx5.
  repeat apply standardFormulaScoped_ex.
  apply standardFormulaScoped_and.
  - apply standardFormulaScoped_contextListTraversalTermAt;
      raw_scope_term.
  - apply contextAllBoundedWithTablesTermAt_scoped;
      raw_scope_term.
Qed.

Lemma proofFormulaFieldsBoundedTermAt_scoped : forall
    level scope fields,
  Forall (StandardTermScoped scope) fields ->
  StandardFormulaScoped scope
    (proofFormulaFieldsBoundedTermAt level fields).
Proof.
  intros level scope fields hfields.
  induction hfields as [|field tail hfield htail IH].
  - cbn [proofFormulaFieldsBoundedTermAt].
    apply standardFormulaScoped_eq;
      apply standardTermScoped_zero.
  - cbn [proofFormulaFieldsBoundedTermAt].
    apply standardFormulaScoped_and.
    + apply formulaQuantifierBoundedTermAt_scoped. exact hfield.
    + exact IH.
Qed.

Lemma proofOccurrenceCasesBoundedTermAt_scoped : forall
    level scope code context cases,
  StandardTermScoped scope code ->
  StandardTermScoped scope context ->
  Forall
    (fun entry =>
      StandardTermScoped scope (fst entry) /\
      Forall (StandardTermScoped scope) (snd entry))
    cases ->
  StandardFormulaScoped scope
    (proofOccurrenceCasesBoundedTermAt level code context cases).
Proof.
  intros level scope code context cases hcode hcontext hcases.
  induction hcases as [|[constructorCode formulaFields] tail
      [hconstructor hfields] htail IH].
  - cbn [proofOccurrenceCasesBoundedTermAt].
    apply standardFormulaScoped_eq;
      apply standardTermScoped_zero.
  - cbn [fst snd proofOccurrenceCasesBoundedTermAt].
    apply standardFormulaScoped_and.
    + apply standardFormulaScoped_imp.
      * apply standardFormulaScoped_eq; assumption.
      * apply standardFormulaScoped_and.
        -- apply contextAllBoundedTermAt_scoped. exact hcontext.
        -- apply proofFormulaFieldsBoundedTermAt_scoped. exact hfields.
    + exact IH.
Qed.

Lemma proofOccurrenceCasesTerms_scoped : forall scope
    context a b c t child1 child2 child3,
  StandardTermScoped scope context ->
  StandardTermScoped scope a ->
  StandardTermScoped scope b ->
  StandardTermScoped scope c ->
  StandardTermScoped scope t ->
  StandardTermScoped scope child1 ->
  StandardTermScoped scope child2 ->
  StandardTermScoped scope child3 ->
  Forall
    (fun entry =>
      StandardTermScoped scope (fst entry) /\
      Forall (StandardTermScoped scope) (snd entry))
    (proofOccurrenceCasesTerms
      context a b c t child1 child2 child3).
Proof.
  intros scope context a b c t child1 child2 child3
    hcontext ha hb hc ht hchild1 hchild2 hchild3.
  unfold proofOccurrenceCasesTerms.
  repeat constructor; raw_scope_term.
Qed.

Lemma proofConstructorOccurrencesBoundedTermAt_scoped : forall
    level scope code,
  StandardTermScoped scope code ->
  StandardFormulaScoped scope
    (proofConstructorOccurrencesBoundedTermAt level code).
Proof.
  intros level scope code hcode.
  unfold proofConstructorOccurrencesBoundedTermAt, restrictedProofAll8.
  repeat apply standardFormulaScoped_all.
  apply proofOccurrenceCasesBoundedTermAt_scoped.
  - raw_scope_term.
  - raw_scope_term.
  - apply proofOccurrenceCasesTerms_scoped; raw_scope_term.
Qed.

Lemma proofEndpointOccurrencesBoundedTermAt_scoped : forall
    level scope code,
  StandardTermScoped scope code ->
  StandardFormulaScoped scope
    (proofEndpointOccurrencesBoundedTermAt level code).
Proof.
  intros level scope code hcode.
  raw_scope_formula.
Qed.

Lemma restrictedProofNodeTermAt_scoped : forall
    level scope code supportCode supportStep,
  StandardTermScoped scope code ->
  StandardTermScoped scope supportCode ->
  StandardTermScoped scope supportStep ->
  StandardFormulaScoped scope
    (restrictedProofNodeTermAt level code supportCode supportStep).
Proof.
  intros level scope code supportCode supportStep
    hcode hsupportCode hsupportStep.
  unfold restrictedProofNodeTermAt, restrictedProofAnd4.
  apply standardFormulaScoped_and.
  - apply proofSyntaxStepTermAt_scoped; assumption.
  - apply standardFormulaScoped_and.
    + apply proofRuleEndpointExistsTermAt_scoped; assumption.
    + apply standardFormulaScoped_and.
      * apply proofConstructorOccurrencesBoundedTermAt_scoped; assumption.
      * apply proofEndpointOccurrencesBoundedTermAt_scoped; assumption.
Qed.

Lemma proofCodeSupportedTermAt_scoped : forall
    scope supportCode supportStep code,
  StandardTermScoped scope supportCode ->
  StandardTermScoped scope supportStep ->
  StandardTermScoped scope code ->
  StandardFormulaScoped scope
    (proofCodeSupportedTermAt supportCode supportStep code).
Proof.
  intros scope supportCode supportStep code
    hsupportCode hsupportStep hcode.
  unfold proofCodeSupportedTermAt.
  apply standardFormulaScoped_codedAssignmentLookupTermAt;
    try assumption.
  apply standardTermScoped_numeral.
Qed.

Lemma restrictedProofTraversalTermAt_scoped : forall
    level scope bound supportCode supportStep,
  StandardTermScoped scope bound ->
  StandardTermScoped scope supportCode ->
  StandardTermScoped scope supportStep ->
  StandardFormulaScoped scope
    (restrictedProofTraversalTermAt level bound supportCode supportStep).
Proof.
  intros level scope bound supportCode supportStep
    hbound hsupportCode hsupportStep.
  unfold restrictedProofTraversalTermAt.
  apply standardFormulaScoped_and.
  - apply standardFormulaScoped_codedAssignmentDefinedThroughTermAt;
      assumption.
  - apply standardFormulaScoped_all.
    apply standardFormulaScoped_imp.
    + apply standardFormulaScoped_ltTermAt; raw_scope_term.
    + apply standardFormulaScoped_imp.
      * apply proofCodeSupportedTermAt_scoped; raw_scope_term.
      * apply restrictedProofNodeTermAt_scoped; raw_scope_term.
Qed.

Lemma restrictedProofCertificateWithSupportTermAt_scoped : forall
    level scope root supportCode supportStep,
  StandardTermScoped scope root ->
  StandardTermScoped scope supportCode ->
  StandardTermScoped scope supportStep ->
  StandardFormulaScoped scope
    (restrictedProofCertificateWithSupportTermAt
      level root supportCode supportStep).
Proof.
  intros level scope root supportCode supportStep
    hroot hsupportCode hsupportStep.
  unfold restrictedProofCertificateWithSupportTermAt.
  apply standardFormulaScoped_and.
  - apply restrictedProofTraversalTermAt_scoped;
      try assumption.
  - apply proofCodeSupportedTermAt_scoped; assumption.
Qed.

Lemma restrictedProofTermAt_scoped : forall level scope root,
  StandardTermScoped scope root ->
  StandardFormulaScoped scope (restrictedProofTermAt level root).
Proof.
  intros level scope root hroot.
  unfold restrictedProofTermAt, restrictedProofEx2.
  repeat apply standardFormulaScoped_ex.
  apply restrictedProofCertificateWithSupportTermAt_scoped;
    raw_scope_term.
Qed.

Lemma restrictedPADerivationSoundnessPredicateTermAt_scoped : forall
    level scope root,
  StandardTermScoped scope root ->
  StandardFormulaScoped scope
    (restrictedPADerivationSoundnessPredicateTermAt level root).
Proof.
  intros level scope root hroot.
  unfold restrictedPADerivationSoundnessPredicateTermAt,
    restrictedPADerivationSoundnessAll4.
  repeat apply standardFormulaScoped_all.
  apply standardFormulaScoped_imp.
  - apply restrictedProofTermAt_scoped; raw_scope_term.
  - apply standardFormulaScoped_imp.
    + apply proofRuleValidTermAt_scoped; raw_scope_term.
    + apply standardFormulaScoped_imp.
      * apply fixedLevelTruthAdmissibleTermAt_scoped; raw_scope_term.
      * apply standardFormulaScoped_imp.
        -- apply contextAllSigmaTrueTermAt_scoped; raw_scope_term.
        -- apply fixedLevelSigmaTruthCertificateTermAt_scoped;
             raw_scope_term.
Qed.

Lemma restrictedPADerivationSoundnessPrefixTermAt_scoped : forall
    level scope current,
  StandardTermScoped scope current ->
  StandardFormulaScoped scope
    (restrictedPADerivationSoundnessPrefixTermAt level current).
Proof.
  intros level scope current hcurrent.
  unfold restrictedPADerivationSoundnessPrefixTermAt.
  apply standardFormulaScoped_all.
  apply standardFormulaScoped_imp.
  - apply standardFormulaScoped_ltTermAt; raw_scope_term.
  - apply restrictedPADerivationSoundnessPredicateTermAt_scoped.
    raw_scope_term.
Qed.

(** This is the syntactic premise left explicit by the proof-code induction
    module.  It now follows for every external fixed truth level, without a
    reflected computation specialized to any particular numeral. *)
Theorem restrictedPADerivationSoundnessPrefix_scoped : forall level,
  RestrictedPADerivationSoundnessPrefixScoped level.
Proof.
  intro level.
  unfold RestrictedPADerivationSoundnessPrefixScoped,
    restrictedPADerivationSoundnessInductionSourceFormula.
  apply restrictedPADerivationSoundnessPrefixTermAt_scoped.
  apply standardTermScoped_var. lia.
Qed.

End PABoundedRawCodedRestrictedPADerivationSoundnessScope.
