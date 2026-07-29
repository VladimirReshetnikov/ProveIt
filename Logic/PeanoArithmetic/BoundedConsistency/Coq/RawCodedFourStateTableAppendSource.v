(**
  One PA theorem extending all four synchronized traversal tables.

  The global truth certificate stores mode, formula, assignment-code, and
  assignment-step columns in four independent Goedel-beta tables.  The
  existing model theorem [raw_fixedLevelStateTablesAppend] extends all four
  columns at one common bound, but its proof-producing clients previously
  had only the one-column object-language append theorem.

  This module states the simultaneous operation as one closed formula with
  thirteen universal inputs and eight existential outputs.  Its de Bruijn
  layout deliberately agrees with the global traversal witness order.  Exact
  raw semantics reduce the formula to the existing four-table property, and
  raw-model completeness turns that already verified property into an
  ordinary PA derivation.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness
  RawCodedAssignment
  RawCodedFixedLevelTruth
  RawCodedFixedLevelTruthTotality.

Module PABoundedRawCodedFourStateTableAppendSource.

Import ListNotations.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTotality.

(** Thirteen outer inputs, from outermost to innermost:

      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep.

    At the body these occupy variables 12 down to 0. *)
Fixpoint fourStateTableAppendRepeatedAll
    (binderCount : nat) (body : formula) : formula :=
  match binderCount with
  | 0 => body
  | S smaller => pAll (fourStateTableAppendRepeatedAll smaller body)
  end.

(** Defined-through premise before the eight output witnesses are opened. *)
Definition fourStateTableAppendDefinedBody : formula :=
  fixedLevelAnd4
    (codedAssignmentDefinedThroughTermAt
      (tVar 12) (tVar 11) (tVar 4))
    (codedAssignmentDefinedThroughTermAt
      (tVar 10) (tVar 9) (tVar 4))
    (codedAssignmentDefinedThroughTermAt
      (tVar 8) (tVar 7) (tVar 4))
    (codedAssignmentDefinedThroughTermAt
      (tVar 6) (tVar 5) (tVar 4)).

(** Under the eight existential binders, variables 7 down to 0 are the new
    code/step pairs in the same column order as above.  Every old input has
    consequently moved up by eight slots. *)
Definition fourStateTableAppendExtensionBody : formula :=
  fixedLevelAnd4
    (codedAssignmentAppendPrefixTermAt
      (tSucc (tVar 12))
      (tVar 20) (tVar 19) (tVar 12) (tVar 11)
      (tVar 7) (tVar 6))
    (codedAssignmentAppendPrefixTermAt
      (tSucc (tVar 12))
      (tVar 18) (tVar 17) (tVar 12) (tVar 10)
      (tVar 5) (tVar 4))
    (codedAssignmentAppendPrefixTermAt
      (tSucc (tVar 12))
      (tVar 16) (tVar 15) (tVar 12) (tVar 9)
      (tVar 3) (tVar 2))
    (codedAssignmentAppendPrefixTermAt
      (tSucc (tVar 12))
      (tVar 14) (tVar 13) (tVar 12) (tVar 8)
      (tVar 1) (tVar 0)).

Definition codedFourStateTableAppendFormula : formula :=
  fourStateTableAppendRepeatedAll 13
    (pImp fourStateTableAppendDefinedBody
      (fixedLevelEx8 fourStateTableAppendExtensionBody)).

(** Carrier-level meaning of the new formula.  This is intentionally a
    four-way conjunction of [RawCodedAssignmentAppendPrefix] predicates: it
    is the exact interface needed by a proof-producing traversal client. *)
Definition RawFourStateTableAppendProperty (M : RawPAModel) : Prop :=
  forall modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound
    mode formula assignmentCode assignmentStep : M,
  RawCodedAssignmentDefinedThrough M modeCode modeStep bound /\
  RawCodedAssignmentDefinedThrough M formulaCode formulaStep bound /\
  RawCodedAssignmentDefinedThrough M
    assignmentCodeCode assignmentCodeStep bound /\
  RawCodedAssignmentDefinedThrough M
    assignmentStepCode assignmentStepStep bound ->
  exists newModeCode newModeStep newFormulaCode newFormulaStep
    newAssignmentCodeCode newAssignmentCodeStep
    newAssignmentStepCode newAssignmentStepStep : M,
    RawCodedAssignmentAppendPrefix M (raw_succ M bound)
      modeCode modeStep bound mode newModeCode newModeStep /\
    RawCodedAssignmentAppendPrefix M (raw_succ M bound)
      formulaCode formulaStep bound formula newFormulaCode newFormulaStep /\
    RawCodedAssignmentAppendPrefix M (raw_succ M bound)
      assignmentCodeCode assignmentCodeStep bound assignmentCode
      newAssignmentCodeCode newAssignmentCodeStep /\
    RawCodedAssignmentAppendPrefix M (raw_succ M bound)
      assignmentStepCode assignmentStepStep bound assignmentStep
      newAssignmentStepCode newAssignmentStepStep.

Arguments RawFourStateTableAppendProperty M : clear implicits.

(** The formula has the exact carrier semantics of the existing simultaneous
    append property.  This theorem is also the de Bruijn-index audit: a wrong
    old/new column slot makes the final [reflexivity] fail. *)
Theorem raw_sat_codedFourStateTableAppendFormula_iff : forall
    (M : RawPAModel) e,
  raw_formula_sat M e codedFourStateTableAppendFormula <->
  RawFourStateTableAppendProperty M.
Proof.
  intros M e.
  unfold codedFourStateTableAppendFormula,
    fourStateTableAppendDefinedBody,
    fourStateTableAppendExtensionBody,
    RawFourStateTableAppendProperty,
    fixedLevelAnd4, fixedLevelEx8.
  cbn [fourStateTableAppendRepeatedAll raw_formula_sat].
  repeat setoid_rewrite
    raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  repeat setoid_rewrite raw_sat_codedAssignmentAppendPrefixTermAt_iff.
  cbn [raw_term_eval scons].
  reflexivity.
Qed.

Theorem codedFourStateTableAppendFormula_sentence :
  Formula.Sentence codedFourStateTableAppendFormula.
Proof.
  intros index hfree.
  unfold codedFourStateTableAppendFormula,
    fourStateTableAppendDefinedBody,
    fourStateTableAppendExtensionBody,
    fixedLevelAnd4, fixedLevelEx8,
    codedAssignmentAppendPrefixTermAt,
    codedAssignmentDefinedThroughTermAt in hfree.
  cbn in hfree.
  lia.
Qed.

Theorem codedFourStateTableAppendFormula_raw_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e codedFourStateTableAppendFormula.
Proof.
  intros M hPA e.
  apply (proj2 (raw_sat_codedFourStateTableAppendFormula_iff M e)).
  intros modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound
    mode formula assignmentCode assignmentStep
    [hmodeDefined [hformulaDefined
      [hassignmentCodeDefined hassignmentStepDefined]]].
  destruct (raw_fixedLevelStateTablesAppend M hPA
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound
    mode formula assignmentCode assignmentStep
    hmodeDefined hformulaDefined
    hassignmentCodeDefined hassignmentStepDefined)
    as (newModeCode & newModeStep & newFormulaCode & newFormulaStep &
        newAssignmentCodeCode & newAssignmentCodeStep &
        newAssignmentStepCode & newAssignmentStepStep &
        hnewModeDefined & hnewFormulaDefined &
        hnewAssignmentCodeDefined & hnewAssignmentStepDefined &
        hmodePrefix & hformulaPrefix &
        hassignmentCodePrefix & hassignmentStepPrefix &
        hmodeLookup & hformulaLookup &
        hassignmentCodeLookup & hassignmentStepLookup).
  exists newModeCode, newModeStep, newFormulaCode, newFormulaStep,
    newAssignmentCodeCode, newAssignmentCodeStep,
    newAssignmentStepCode, newAssignmentStepStep.
  unfold RawCodedAssignmentAppendPrefix.
  repeat split; try assumption.
  - intros index value _ hbound hold.
    exact (hmodePrefix index value hbound hold).
  - intros _. exact hmodeLookup.
  - intros index value _ hbound hold.
    exact (hformulaPrefix index value hbound hold).
  - intros _. exact hformulaLookup.
  - intros index value _ hbound hold.
    exact (hassignmentCodePrefix index value hbound hold).
  - intros _. exact hassignmentCodeLookup.
  - intros index value _ hbound hold.
    exact (hassignmentStepPrefix index value hbound hold).
  - intros _. exact hassignmentStepLookup.
Qed.

Theorem PA_proves_codedFourStateTableAppendFormula :
  Formula.BProv Formula.Ax_s [] codedFourStateTableAppendFormula.
Proof.
  apply PA_BProv_of_raw_valid.
  - exact codedFourStateTableAppendFormula_sentence.
  - intros M hPA e.
    exact (codedFourStateTableAppendFormula_raw_valid M hPA e).
Qed.

End PABoundedRawCodedFourStateTableAppendSource.
