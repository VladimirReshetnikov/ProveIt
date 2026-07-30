(**
  Compile simultaneous ternary application inside the direct PA template.

  A selected opaque predicate is applied by three successive de Bruijn
  openings.  The first two replacement terms must be protected from the
  openings which follow them: the first is shifted by two and the second by
  one.  [RawCodedTernaryApplication] records precisely that five-trace
  protocol.

  This file proves once, for every direct derivation-soundness translation,
  that carrying out the same operations in [TemplateFormula] compiles to a
  genuine represented ternary-application trace.  The result is deliberately
  independent of either truth selector.  In particular, later compilers may
  expose the structure of context truth, conclusion truth, or any other
  deeply closed ternary predicate without rebuilding the protective shifts.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateNumeralParameters
  RawCodedTemplateTernaryApplication
  RawCodedTemplateTernaryApplicationFunctionality
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.

Module
  PABoundedRawCodedRestrictedPATemplateTernaryApplicationCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTemplateTernaryApplicationFunctionality.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.

(** The exact template counterpart of [standardTernaryApplication].  Naming
    the two protected terms makes both the represented trace theorem and
    later normalization proofs substantially easier to read. *)
Definition coqRestrictedPATemplateTernaryFirstLifted
    (first : TemplateTerm) : TemplateTerm :=
  templateTermRename (templateShiftRenamingBy 0 2) first.

Definition coqRestrictedPATemplateTernarySecondLifted
    (second : TemplateTerm) : TemplateTerm :=
  templateTermRename (templateShiftRenamingBy 0 1) second.

Definition coqRestrictedPATemplateTernaryFirstResult
    (predicate : TemplateFormula) (first : TemplateTerm)
    : TemplateFormula :=
  templateFormulaOpen
    (coqRestrictedPATemplateTernaryFirstLifted first) predicate.

Definition coqRestrictedPATemplateTernarySecondResult
    (predicate : TemplateFormula) (first second : TemplateTerm)
    : TemplateFormula :=
  templateFormulaOpen
    (coqRestrictedPATemplateTernarySecondLifted second)
    (coqRestrictedPATemplateTernaryFirstResult predicate first).

Definition coqRestrictedPATemplateTernaryApplication
    (predicate : TemplateFormula) (first second third : TemplateTerm)
    : TemplateFormula :=
  templateFormulaOpen third
    (coqRestrictedPATemplateTernarySecondResult
      predicate first second).

(** The three formula openings are supplied by every template translation;
    only the two protective term shifts depend on the concrete term
    interpreter.  Factoring them as premises lets extended direct-input
    translations reuse the same five-trace application proof. *)
Theorem raw_codedTemplateTernaryApplication_trace_of_protected_shifts :
  forall (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
      predicate first second third,
  RawCodedTermShift M
    (raw_zero M) (rawNumeralValue M 2)
    (rawTemplateTerm translation first)
    (rawTemplateTerm translation
      (coqRestrictedPATemplateTernaryFirstLifted first)) ->
  RawCodedTermShift M
    (raw_zero M) (rawNumeralValue M 1)
    (rawTemplateTerm translation second)
    (rawTemplateTerm translation
      (coqRestrictedPATemplateTernarySecondLifted second)) ->
  RawCodedTernaryApplication M
    (rawTemplateFormula translation predicate)
    (rawTemplateTerm translation first)
    (rawTemplateTerm translation second)
    (rawTemplateTerm translation third)
    (rawTemplateFormula translation
      (coqRestrictedPATemplateTernaryApplication
        predicate first second third)).
Proof.
  intros M translation predicate first second third
    hfirstShift hsecondShift.
  unfold RawCodedTernaryApplication.
  exists
    (rawTemplateTerm translation
      (coqRestrictedPATemplateTernaryFirstLifted first)),
    (rawTemplateTerm translation
      (coqRestrictedPATemplateTernarySecondLifted second)),
    (rawTemplateFormula translation
      (coqRestrictedPATemplateTernaryFirstResult predicate first)),
    (rawTemplateFormula translation
      (coqRestrictedPATemplateTernarySecondResult
        predicate first second)).
  repeat split.
  - exact hfirstShift.
  - exact hsecondShift.
  - unfold coqRestrictedPATemplateTernaryFirstResult.
    exact (rawTemplateFormula_open translation
      predicate (coqRestrictedPATemplateTernaryFirstLifted first)).
  - unfold coqRestrictedPATemplateTernarySecondResult.
    exact (rawTemplateFormula_open translation
      (coqRestrictedPATemplateTernaryFirstResult predicate first)
      (coqRestrictedPATemplateTernarySecondLifted second)).
  - unfold coqRestrictedPATemplateTernaryApplication.
    exact (rawTemplateFormula_open translation
      (coqRestrictedPATemplateTernarySecondResult
        predicate first second) third).
Qed.

(** Direct term translation is selector-independent.  The numeral-template
    shift theorem therefore supplies the non-unit shift by two directly,
    rather than composing two independently represented unit-shift tables. *)
Lemma raw_coqRestrictedPATemplateTernary_first_shift : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (parameters : RawCodedTemplateNumeralParameters M)
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters),
  let inputs :=
    rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth in
  forall first,
  RawCodedTermShift M
    (raw_zero M) (rawNumeralValue M 2)
    (rawDirectTemplateTerm inputs first)
    (rawDirectTemplateTerm inputs
      (coqRestrictedPATemplateTernaryFirstLifted first)).
Proof.
  intros M hPA parameters contextTruth conclusionTruth inputs first.
  unfold inputs.
  unfold coqRestrictedPATemplateTernaryFirstLifted.
  rewrite !rawCoqRestrictedPADerivationSoundnessDirectTerm_view.
  unfold rawCoqRestrictedPADerivationSoundnessTemplateTermView,
    rawCoqRestrictedPADerivationSoundnessTermViewSymbols.
  change (RawCodedTermShift M
    (rawNumeralValue M 0) (rawNumeralValue M 2)
    (rawStructuralTemplateTermWith M
      (rawNumeralTemplateSymbols M parameters
        (fun _ _ => rawFormulaBotCode M)) first)
    (rawStructuralTemplateTermWith M
      (rawNumeralTemplateSymbols M parameters
        (fun _ _ => rawFormulaBotCode M))
      (templateTermRename (templateShiftRenamingBy 0 2) first))).
  apply raw_numeralTemplateTerm_shift_by. exact hPA.
Qed.

Lemma raw_coqRestrictedPATemplateTernary_second_shift : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (parameters : RawCodedTemplateNumeralParameters M)
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters),
  let inputs :=
    rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth in
  forall second,
  RawCodedTermShift M
    (raw_zero M) (rawNumeralValue M 1)
    (rawDirectTemplateTerm inputs second)
    (rawDirectTemplateTerm inputs
      (coqRestrictedPATemplateTernarySecondLifted second)).
Proof.
  intros M hPA parameters contextTruth conclusionTruth inputs second.
  unfold inputs.
  unfold coqRestrictedPATemplateTernarySecondLifted.
  rewrite !rawCoqRestrictedPADerivationSoundnessDirectTerm_view.
  unfold rawCoqRestrictedPADerivationSoundnessTemplateTermView,
    rawCoqRestrictedPADerivationSoundnessTermViewSymbols.
  change (RawCodedTermShift M
    (rawNumeralValue M 0) (rawNumeralValue M 1)
    (rawStructuralTemplateTermWith M
      (rawNumeralTemplateSymbols M parameters
        (fun _ _ => rawFormulaBotCode M)) second)
    (rawStructuralTemplateTermWith M
      (rawNumeralTemplateSymbols M parameters
        (fun _ _ => rawFormulaBotCode M))
      (templateTermRename (templateShiftRenamingBy 0 1) second))).
  apply raw_numeralTemplateTerm_shift_by. exact hPA.
Qed.

(** Complete five-trace application.  Formula opening is supplied by the
    public translation interface, so opaque leaves remain genuinely opaque
    throughout the construction. *)
Theorem raw_coqRestrictedPATemplateTernaryApplication_trace : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (parameters : RawCodedTemplateNumeralParameters M)
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters),
  let inputs :=
    rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth in
  forall predicate first second third,
  RawCodedTernaryApplication M
    (rawDirectTemplateFormula inputs predicate)
    (rawDirectTemplateTerm inputs first)
    (rawDirectTemplateTerm inputs second)
    (rawDirectTemplateTerm inputs third)
    (rawDirectTemplateFormula inputs
      (coqRestrictedPATemplateTernaryApplication
        predicate first second third)).
Proof.
  intros M hPA parameters contextTruth conclusionTruth inputs
    predicate first second third.
  unfold RawCodedTernaryApplication.
  exists
    (rawDirectTemplateTerm inputs
      (coqRestrictedPATemplateTernaryFirstLifted first)),
    (rawDirectTemplateTerm inputs
      (coqRestrictedPATemplateTernarySecondLifted second)),
    (rawDirectTemplateFormula inputs
      (coqRestrictedPATemplateTernaryFirstResult predicate first)),
    (rawDirectTemplateFormula inputs
      (coqRestrictedPATemplateTernarySecondResult
        predicate first second)).
  repeat split.
  - exact (raw_coqRestrictedPATemplateTernary_first_shift
      M hPA parameters contextTruth conclusionTruth first).
  - exact (raw_coqRestrictedPATemplateTernary_second_shift
      M hPA parameters contextTruth conclusionTruth second).
  - unfold coqRestrictedPATemplateTernaryFirstResult.
    exact (rawTemplateFormula_open
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      predicate (coqRestrictedPATemplateTernaryFirstLifted first)).
  - unfold coqRestrictedPATemplateTernarySecondResult.
    exact (rawTemplateFormula_open
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqRestrictedPATemplateTernaryFirstResult predicate first)
      (coqRestrictedPATemplateTernarySecondLifted second)).
  - unfold coqRestrictedPATemplateTernaryApplication.
    exact (rawTemplateFormula_open
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqRestrictedPATemplateTernarySecondResult
        predicate first second) third).
Qed.

(** Functional selection turns the relational compiler into the literal
    output equation needed for rerooting an opaque application at its
    transparent template expansion. *)
Corollary raw_coqRestrictedPATemplateTernaryApplication_output : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (parameters : RawCodedTemplateNumeralParameters M)
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters),
  let inputs :=
    rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth in
  forall predicate
    (selector : RawCodedTernaryApplicationSelector M
      (rawDirectTemplateFormula inputs predicate))
    first second third,
  rawTernaryApplicationOutput selector
    (rawDirectTemplateTerm inputs first)
    (rawDirectTemplateTerm inputs second)
    (rawDirectTemplateTerm inputs third) =
  rawDirectTemplateFormula inputs
    (coqRestrictedPATemplateTernaryApplication
      predicate first second third).
Proof.
  intros M hPA parameters contextTruth conclusionTruth inputs
    predicate selector first second third.
  unfold inputs in *.
  apply (rawTernaryApplicationOutput_unique M hPA
    (rawDirectTemplateFormula
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth) predicate)
    selector).
  - rewrite rawCoqRestrictedPADerivationSoundnessDirectTerm_view.
    apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax.
    exact hPA.
  - rewrite rawCoqRestrictedPADerivationSoundnessDirectTerm_view.
    apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax.
    exact hPA.
  - rewrite rawCoqRestrictedPADerivationSoundnessDirectTerm_view.
    apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax.
    exact hPA.
  - exact (raw_coqRestrictedPATemplateTernaryApplication_trace
      M hPA parameters contextTruth conclusionTruth
      predicate first second third).
Qed.

End
  PABoundedRawCodedRestrictedPATemplateTernaryApplicationCompilation.
