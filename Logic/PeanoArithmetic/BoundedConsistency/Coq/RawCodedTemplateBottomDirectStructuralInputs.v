(**
  A canonical direct structural translation for helper-only templates.

  The dependency-ordered native callback needs one template translation only
  to encode its fixed PA helper batch.  None of the callback interfaces gives
  semantic meaning to that translation's opaque leaves.  We may therefore
  interpret both five-argument opaque truth predicates as bottom.  Bottom is
  stable under every represented shift and opening, so the existing direct
  structural constructor supplies a completely concrete translation.

  This small construction is useful beyond the native callback: it proves
  that asking separately for a translation which agrees with embedded PA
  syntax is never a genuine proof-producing hypothesis.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedFormulaOperationTreeRealization
  RawCodedFormulaShiftTreeRealization
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateNumeralParameters
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedDynamicTruthTemplateNumeralParameters
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedTemplateDirectStructuralPAAgreement.

Module PABoundedRawCodedTemplateBottomDirectStructuralInputs.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaOperationTreeRealization.
Import PABoundedRawCodedFormulaShiftTreeRealization.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedDynamicTruthTemplateNumeralParameters.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.

(** A five-argument selector which deliberately forgets all arguments.  The
    two laws are represented operations, rather than metatheoretic code
    equalities; the one-node bottom tree realizes exactly those operations. *)
Definition rawBottomRestrictedPATruthDirectSelector
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (parameters : RawCodedTemplateNumeralParameters M)
    : RawCoqRestrictedPATruthDirectSelector M parameters.
Proof.
  refine
    {| rawCoqRestrictedPATruthDirectOutput :=
         fun _ _ _ _ _ => rawFormulaBotCode M |}.
  - intros depth first second third fourth fifth.
    exact (raw_codedFormulaShift_of_valid_tree M hPA
      (rawNumeralValue M 1) (RFSTBot M (rawNumeralValue M depth)) I).
  - intros depth replacement first second third fourth fifth.
    exact (raw_codedFormulaOperation_of_valid_tree M hPA
      (RawCodedFormulaSubstitutionAtom M)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters replacement)
      (RFSTBot M (rawNumeralValue M depth)) I).
Defined.

Arguments rawBottomRestrictedPATruthDirectSelector M hPA parameters
  : clear implicits.

(** At the standard value zero the numeral-term output is known explicitly,
    so no choice is needed to put the canonical input record in [Type]. *)
Definition rawBottomTemplateZeroNumeralParameters
    (M : RawPAModel) (hPA : RawPASatisfies M)
    : RawCodedTemplateNumeralParameters M :=
  rawCoqDynamicTruthTemplateNumeralParameters M
    (raw_zero M) (raw_zero M)
    (rawQuotedTermCode M (Term.numeral 0))
    (rawQuotedTermCode M (Term.numeral 0))
    (raw_numeralTermCodeAt_standard M hPA 0)
    (raw_numeralTermCodeAt_standard M hPA 0).

Arguments rawBottomTemplateZeroNumeralParameters M hPA : clear implicits.

Definition rawBottomTemplateDirectStructuralInputs
    (M : RawPAModel) (hPA : RawPASatisfies M)
    : RawCodedTemplateDirectStructuralInputs M :=
  rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
    M hPA (rawBottomTemplateZeroNumeralParameters M hPA)
    (rawBottomRestrictedPATruthDirectSelector M hPA
      (rawBottomTemplateZeroNumeralParameters M hPA))
    (rawBottomRestrictedPATruthDirectSelector M hPA
      (rawBottomTemplateZeroNumeralParameters M hPA)).

Arguments rawBottomTemplateDirectStructuralInputs M hPA : clear implicits.

Definition rawBottomDirectStructuralTemplateTranslation
    (M : RawPAModel) (hPA : RawPASatisfies M)
    : RawCodedTemplateTranslation M :=
  rawDirectStructuralTemplateTranslation M hPA
    (rawBottomTemplateDirectStructuralInputs M hPA).

Arguments rawBottomDirectStructuralTemplateTranslation M hPA
  : clear implicits.

Theorem rawBottomDirectStructuralTemplatePAAgreement : forall
    (M : RawPAModel) (hPA : RawPASatisfies M),
  RawCodedTemplatePAAgreement M
    (rawBottomDirectStructuralTemplateTranslation M hPA).
Proof.
  intros M hPA.
  exact (rawDirectStructuralTemplatePAAgreement M hPA
    (rawBottomTemplateDirectStructuralInputs M hPA)).
Qed.

(** The two parameter names can both denote zero.  Represented numeral-code
    totality chooses the required term codes inside [Prop], after which the
    bottom selectors give a direct structural input record. *)
Theorem raw_bottomTemplateDirectStructuralInputs_exists : forall
    (M : RawPAModel), RawPASatisfies M ->
  exists inputs : RawCodedTemplateDirectStructuralInputs M, True.
Proof.
  intros M hPA.
  exists (rawBottomTemplateDirectStructuralInputs M hPA).
  exact I.
Qed.

(** In particular, ordinary PA syntax has an agreeing template translation
    in every raw model of PA.  This is an existential statement only because
    represented numeral term codes are selected relationally. *)
Corollary raw_codedTemplatePAAgreement_exists : forall
    (M : RawPAModel), RawPASatisfies M ->
  exists translation : RawCodedTemplateTranslation M,
    RawCodedTemplatePAAgreement M translation.
Proof.
  intros M hPA.
  exists (rawBottomDirectStructuralTemplateTranslation M hPA).
  exact (rawBottomDirectStructuralTemplatePAAgreement M hPA).
Qed.

End PABoundedRawCodedTemplateBottomDirectStructuralInputs.
