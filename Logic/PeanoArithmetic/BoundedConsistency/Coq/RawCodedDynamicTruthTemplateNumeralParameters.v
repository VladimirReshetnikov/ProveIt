(**
  Concrete numeral parameters for the two dynamic-truth levels.

  The universal-leaf template reserves parameter name zero for its lower
  level and name one for its upper level.  In an arbitrary nonstandard model
  neither level can be externally converted into an ordinary Rocq numeral.
  The represented numeral-code totality theorem nevertheless supplies an
  internal term code for each carrier value.

  This module selects those two codes, packages them as the total named
  parameter interpretation expected by [RawCodedTemplateNumeralParameters],
  and immediately derives the exact term shift/open traces consumed by the
  direct structural translator.  Unused successor names share the upper
  code; this keeps the total-name contract minimal and is harmless because
  the concrete dynamic-truth template mentions only names zero and one.
*)

From Stdlib Require Import List Arith.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedNumeralTermCode RawCodedFormulaOperations
  RawCodedTemplateSyntax RawCodedTemplateStructuralTranslation
  RawCodedTemplateNumeralParameters
  RawCodedDynamicTruthUniversalLeafSourceTemplate.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthTemplateNumeralParameters.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.

(** ------------------------------------------------------------------
    The designated two-name interpretation. *)

(** Name zero denotes the lower object; every successor name denotes the
    upper object.  In particular, this agrees with the designated dynamic
    names zero and one. *)
Definition coqDynamicTruthParameterSelect {A : Type}
    (lower upper : A) (name : TemplateParameterName) : A :=
  match name with
  | 0 => lower
  | S _ => upper
  end.

Arguments coqDynamicTruthParameterSelect {A} _ _ _.

Lemma coqDynamicTruthParameterSelect_lower : forall
    (A : Type) (lower upper : A),
  coqDynamicTruthParameterSelect lower upper
    coqDynamicTruthLowerLevelParameterName = lower.
Proof. reflexivity. Qed.

Lemma coqDynamicTruthParameterSelect_upper : forall
    (A : Type) (lower upper : A),
  coqDynamicTruthParameterSelect lower upper
    coqDynamicTruthUpperLevelParameterName = upper.
Proof. reflexivity. Qed.

(** Explicit constructor used when a caller already has the two numeral
    codes.  The dependent validity field is discharged by the same case
    distinction as the bound/code selectors. *)
Definition rawCoqDynamicTruthTemplateNumeralParameters
    (M : RawPAModel)
    (lowerLevel upperLevel lowerCode upperCode : M)
    (lowerValid : RawNumeralTermCodeAt M lowerLevel lowerCode)
    (upperValid : RawNumeralTermCodeAt M upperLevel upperCode)
    : RawCodedTemplateNumeralParameters M.
Proof.
  refine
    {| rawNumeralTemplateParameterBound :=
         coqDynamicTruthParameterSelect lowerLevel upperLevel;
       rawNumeralTemplateParameterCode :=
         coqDynamicTruthParameterSelect lowerCode upperCode;
       rawNumeralTemplateParameter_valid := _ |}.
  intros [|name]; cbn [coqDynamicTruthParameterSelect]; assumption.
Defined.

Arguments rawCoqDynamicTruthTemplateNumeralParameters
  M _ _ _ _ _ _ : clear implicits.

Lemma rawCoqDynamicTruthTemplateNumeralParameters_lower_bound : forall
    M lowerLevel upperLevel lowerCode upperCode lowerValid upperValid,
  rawNumeralTemplateParameterBound
    (rawCoqDynamicTruthTemplateNumeralParameters M
      lowerLevel upperLevel lowerCode upperCode lowerValid upperValid)
    coqDynamicTruthLowerLevelParameterName = lowerLevel.
Proof. reflexivity. Qed.

Lemma rawCoqDynamicTruthTemplateNumeralParameters_upper_bound : forall
    M lowerLevel upperLevel lowerCode upperCode lowerValid upperValid,
  rawNumeralTemplateParameterBound
    (rawCoqDynamicTruthTemplateNumeralParameters M
      lowerLevel upperLevel lowerCode upperCode lowerValid upperValid)
    coqDynamicTruthUpperLevelParameterName = upperLevel.
Proof. reflexivity. Qed.

Lemma rawCoqDynamicTruthTemplateNumeralParameters_lower_code : forall
    M lowerLevel upperLevel lowerCode upperCode lowerValid upperValid,
  rawNumeralTemplateParameterCode
    (rawCoqDynamicTruthTemplateNumeralParameters M
      lowerLevel upperLevel lowerCode upperCode lowerValid upperValid)
    coqDynamicTruthLowerLevelParameterName = lowerCode.
Proof. reflexivity. Qed.

Lemma rawCoqDynamicTruthTemplateNumeralParameters_upper_code : forall
    M lowerLevel upperLevel lowerCode upperCode lowerValid upperValid,
  rawNumeralTemplateParameterCode
    (rawCoqDynamicTruthTemplateNumeralParameters M
      lowerLevel upperLevel lowerCode upperCode lowerValid upperValid)
    coqDynamicTruthUpperLevelParameterName = upperCode.
Proof. reflexivity. Qed.

(** Represented induction supplies both codes for arbitrary carrier values.
    The theorem remains in [Prop], so no choice principle is needed to
    eliminate a relational totality proof into a computational selector. *)
Theorem raw_coqDynamicTruthTemplateNumeralParameters_exists : forall
    (M : RawPAModel), RawPASatisfies M -> forall lowerLevel upperLevel,
  exists parameters : RawCodedTemplateNumeralParameters M,
    rawNumeralTemplateParameterBound parameters
      coqDynamicTruthLowerLevelParameterName = lowerLevel /\
    rawNumeralTemplateParameterBound parameters
      coqDynamicTruthUpperLevelParameterName = upperLevel.
Proof.
  intros M hPA lowerLevel upperLevel.
  destruct (raw_numeralTermCodeExists_all M hPA lowerLevel)
    as [lowerCode lowerValid].
  destruct (raw_numeralTermCodeExists_all M hPA upperLevel)
    as [upperCode upperValid].
  exists (rawCoqDynamicTruthTemplateNumeralParameters M
    lowerLevel upperLevel lowerCode upperCode lowerValid upperValid).
  split; reflexivity.
Qed.

(** ------------------------------------------------------------------
    Direct-translation term package. *)

(** The opaque formula interpretation is accepted as a function because it
    is part of the shared structural-symbol record.  No property of that
    function is assumed here; opaque formula traces remain the responsibility
    of the complementary atom package. *)
Record RawCodedDynamicTruthTemplateNumeralTermPackage
    (M : RawPAModel) (lowerLevel upperLevel : M)
    (opaqueCode : TemplatePredicateName -> list M -> M) : Type := {
  rawCoqDynamicTruthTermPackage_parameters :
    RawCodedTemplateNumeralParameters M;
  rawCoqDynamicTruthTermPackage_lower_bound :
    rawNumeralTemplateParameterBound
      rawCoqDynamicTruthTermPackage_parameters
      coqDynamicTruthLowerLevelParameterName = lowerLevel;
  rawCoqDynamicTruthTermPackage_upper_bound :
    rawNumeralTemplateParameterBound
      rawCoqDynamicTruthTermPackage_parameters
      coqDynamicTruthUpperLevelParameterName = upperLevel;
  rawCoqDynamicTruthTermPackage_traces :
    RawCodedTemplateTermTraceInputs M
      (rawNumeralTemplateSymbols M
        rawCoqDynamicTruthTermPackage_parameters opaqueCode)
}.

Arguments rawCoqDynamicTruthTermPackage_parameters
  {M lowerLevel upperLevel opaqueCode} _.
Arguments rawCoqDynamicTruthTermPackage_lower_bound
  {M lowerLevel upperLevel opaqueCode} _.
Arguments rawCoqDynamicTruthTermPackage_upper_bound
  {M lowerLevel upperLevel opaqueCode} _.
Arguments rawCoqDynamicTruthTermPackage_traces
  {M lowerLevel upperLevel opaqueCode} _.

Definition rawCoqDynamicTruthTemplateNumeralTermPackage
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (lowerLevel upperLevel : M)
    (opaqueCode : TemplatePredicateName -> list M -> M)
    (parameters : RawCodedTemplateNumeralParameters M)
    (lowerBound : rawNumeralTemplateParameterBound parameters
      coqDynamicTruthLowerLevelParameterName = lowerLevel)
    (upperBound : rawNumeralTemplateParameterBound parameters
      coqDynamicTruthUpperLevelParameterName = upperLevel)
    : RawCodedDynamicTruthTemplateNumeralTermPackage
        M lowerLevel upperLevel opaqueCode :=
  {| rawCoqDynamicTruthTermPackage_parameters := parameters;
     rawCoqDynamicTruthTermPackage_lower_bound := lowerBound;
     rawCoqDynamicTruthTermPackage_upper_bound := upperBound;
     rawCoqDynamicTruthTermPackage_traces :=
       rawNumeralTemplateTermTraceInputs M hPA parameters opaqueCode |}.

Arguments rawCoqDynamicTruthTemplateNumeralTermPackage
  M _ _ _ _ _ _ _ : clear implicits.

(** Totality therefore yields the complete term-side package for any two
    model elements and any chosen opaque interpretation. *)
Theorem raw_coqDynamicTruthTemplateNumeralTermPackage_exists : forall
    (M : RawPAModel), RawPASatisfies M ->
    forall lowerLevel upperLevel opaqueCode,
  exists package : RawCodedDynamicTruthTemplateNumeralTermPackage
      M lowerLevel upperLevel opaqueCode, True.
Proof.
  intros M hPA lowerLevel upperLevel opaqueCode.
  destruct (raw_coqDynamicTruthTemplateNumeralParameters_exists
    M hPA lowerLevel upperLevel)
    as [parameters [lowerBound upperBound]].
  exists (rawCoqDynamicTruthTemplateNumeralTermPackage
    M hPA lowerLevel upperLevel opaqueCode
    parameters lowerBound upperBound).
  exact I.
Qed.

(** ------------------------------------------------------------------
    Useful projections for the direct structural input record. *)

Definition rawCoqDynamicTruthTemplateNumeralSymbols
    {M lowerLevel upperLevel opaqueCode}
    (package : RawCodedDynamicTruthTemplateNumeralTermPackage
      M lowerLevel upperLevel opaqueCode)
    : RawCodedTemplateStructuralSymbols M :=
  rawNumeralTemplateSymbols M
    (rawCoqDynamicTruthTermPackage_parameters package) opaqueCode.

Arguments rawCoqDynamicTruthTemplateNumeralSymbols
  {M lowerLevel upperLevel opaqueCode} _.

Definition rawCoqDynamicTruthLowerNumeralCode
    {M lowerLevel upperLevel opaqueCode}
    (package : RawCodedDynamicTruthTemplateNumeralTermPackage
      M lowerLevel upperLevel opaqueCode) : M :=
  rawNumeralTemplateParameterCode
    (rawCoqDynamicTruthTermPackage_parameters package)
    coqDynamicTruthLowerLevelParameterName.

Definition rawCoqDynamicTruthUpperNumeralCode
    {M lowerLevel upperLevel opaqueCode}
    (package : RawCodedDynamicTruthTemplateNumeralTermPackage
      M lowerLevel upperLevel opaqueCode) : M :=
  rawNumeralTemplateParameterCode
    (rawCoqDynamicTruthTermPackage_parameters package)
    coqDynamicTruthUpperLevelParameterName.

Arguments rawCoqDynamicTruthLowerNumeralCode
  {M lowerLevel upperLevel opaqueCode} _.
Arguments rawCoqDynamicTruthUpperNumeralCode
  {M lowerLevel upperLevel opaqueCode} _.

Lemma rawCoqDynamicTruthLowerNumeralCode_valid : forall
    M lowerLevel upperLevel opaqueCode
    (package : RawCodedDynamicTruthTemplateNumeralTermPackage
      M lowerLevel upperLevel opaqueCode),
  RawNumeralTermCodeAt M lowerLevel
    (rawCoqDynamicTruthLowerNumeralCode package).
Proof.
  intros M lowerLevel upperLevel opaqueCode package.
  unfold rawCoqDynamicTruthLowerNumeralCode.
  pose proof (rawNumeralTemplateParameter_valid
    (rawCoqDynamicTruthTermPackage_parameters package)
    coqDynamicTruthLowerLevelParameterName) as hvalid.
  rewrite (rawCoqDynamicTruthTermPackage_lower_bound package) in hvalid.
  exact hvalid.
Qed.

Lemma rawCoqDynamicTruthUpperNumeralCode_valid : forall
    M lowerLevel upperLevel opaqueCode
    (package : RawCodedDynamicTruthTemplateNumeralTermPackage
      M lowerLevel upperLevel opaqueCode),
  RawNumeralTermCodeAt M upperLevel
    (rawCoqDynamicTruthUpperNumeralCode package).
Proof.
  intros M lowerLevel upperLevel opaqueCode package.
  unfold rawCoqDynamicTruthUpperNumeralCode.
  pose proof (rawNumeralTemplateParameter_valid
    (rawCoqDynamicTruthTermPackage_parameters package)
    coqDynamicTruthUpperLevelParameterName) as hvalid.
  rewrite (rawCoqDynamicTruthTermPackage_upper_bound package) in hvalid.
  exact hvalid.
Qed.

(** These two theorems have exactly the term-field types of
    [RawCodedTemplateDirectStructuralInputs]. *)
Theorem rawCoqDynamicTruthTemplateTermShiftAt : forall
    M lowerLevel upperLevel opaqueCode
    (package : RawCodedDynamicTruthTemplateNumeralTermPackage
      M lowerLevel upperLevel opaqueCode) depth input,
  RawCodedTermShift M
    (rawNumeralValue M depth) (rawNumeralValue M 1)
    (rawStructuralTemplateTermWith M
      (rawCoqDynamicTruthTemplateNumeralSymbols package) input)
    (rawStructuralTemplateTermWith M
      (rawCoqDynamicTruthTemplateNumeralSymbols package)
      (templateTermRename (templateShiftRenamingAt depth) input)).
Proof.
  intros. exact (rawTemplateTermTrace_shiftAt
    (rawCoqDynamicTruthTermPackage_traces package) depth input).
Qed.

Theorem rawCoqDynamicTruthTemplateTermOpeningAt : forall
    M lowerLevel upperLevel opaqueCode
    (package : RawCodedDynamicTruthTemplateNumeralTermPackage
      M lowerLevel upperLevel opaqueCode) depth replacement input,
  RawCodedFormulaSubstitutionAtom M
    (rawStructuralTemplateTermWith M
      (rawCoqDynamicTruthTemplateNumeralSymbols package) replacement)
    (rawNumeralValue M depth)
    (rawStructuralTemplateTermWith M
      (rawCoqDynamicTruthTemplateNumeralSymbols package) input)
    (rawStructuralTemplateTermWith M
      (rawCoqDynamicTruthTemplateNumeralSymbols package)
      (templateTermSubst
        (templateOpeningSubstAt depth replacement) input)).
Proof.
  intros. exact (rawTemplateTermTrace_openAt
    (rawCoqDynamicTruthTermPackage_traces package)
    depth replacement input).
Qed.

End PABoundedRawCodedDynamicTruthTemplateNumeralParameters.
