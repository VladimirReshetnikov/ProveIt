(** Concrete lower laws consumed by opaque ternary application.

    This module deliberately sits above the generic contract definitions in
    [RawCodedTemplateTernaryApplicationFunctionality].  The substantial
    represented induction lives in [RawCodedTermShiftProtection]; here we
    merely expose its one- and two-binder specializations through the exact
    record type expected by the ternary assembly theorem. *)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedFormulaOperations
  RawCodedTemplateTernaryApplicationFunctionality
  RawCodedTermShiftProtection
  RawCodedFormulaShiftSubstitutionInterchangeInduction.

Module PABoundedRawCodedFormulaOperationConcreteLaws.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTemplateTernaryApplicationFunctionality.
Import PABoundedRawCodedTermShiftProtection.
Import PABoundedRawCodedFormulaShiftSubstitutionInterchangeInduction.

Theorem raw_codedFormulaShiftAtom_protectiveShiftStable : forall
    (M : RawPAModel), RawPASatisfies M -> forall amount,
  RawCodedFormulaOperationProtectiveShiftStable M
    (RawCodedFormulaShiftAtom M) amount.
Proof.
  intros M hPA amount. constructor.
  - intros depth input transformedInput liftedInput
      liftedTransformedInput hoperation hleft hright.
    exact (raw_codedTermShift_protect_one M hPA
      depth amount input transformedInput liftedInput
      liftedTransformedInput hoperation hleft hright).
  - intros depth input transformedInput liftedInput
      liftedTransformedInput hoperation hleft hright.
    exact (raw_codedTermShift_protect_two M hPA
      depth amount input transformedInput liftedInput
      liftedTransformedInput hoperation hleft hright).
Qed.

(** A compact package for clients that need both lower shift laws. *)
Theorem raw_codedFormulaShiftAtom_concrete_laws : forall
    (M : RawPAModel), RawPASatisfies M -> forall amount,
  RawCodedFormulaOperationProtectiveShiftStable M
      (RawCodedFormulaShiftAtom M) amount /\
  RawCodedFormulaOperationSingleSubstitutionInterchange M
      (RawCodedFormulaShiftAtom M) amount.
Proof.
  intros M hPA amount. split.
  - exact (raw_codedFormulaShiftAtom_protectiveShiftStable M hPA amount).
  - exact (raw_codedFormulaShiftAtom_singleSubstitutionInterchange
      M hPA amount).
Qed.

End PABoundedRawCodedFormulaOperationConcreteLaws.
