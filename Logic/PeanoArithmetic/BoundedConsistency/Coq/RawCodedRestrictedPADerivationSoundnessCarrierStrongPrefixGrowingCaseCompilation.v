(**
  Growing-base compilation of the two strong-prefix induction cases.

  The rigid case interface in the strong-prefix shell asks for proofs of
  [K(0)] and [forall d, K(d) -> K(S d)] in the caller's already fixed PA
  context.  That context may be empty (apart from the generated induction
  axiom), whereas both cases use ordinary arithmetic axioms.  The honest
  interface therefore grows the witnessed PA base by proofs of two closed
  arithmetic lemmas and transports the supplied strong-step proof into the
  resulting context.

  The successor proof deliberately avoids equality elimination.  From

      x < e,  e < S d

  PA proves [x < d].  Thus [K(d)] gives [K(e)], and the genuine recursive
  strong step [K(e) -> P(e)] supplies the desired endpoint.
*)

From Stdlib Require Import List Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedPAAxiomWitness
  RawCodedRestrictedPAProof
  RawCodedProofBinaryConstructors
  RawCodedProofAndEConstructors
  RawCodedPAProvability
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofConjunction
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofWitnessedContextMergeTransportComplete
  RawCodedPAAxiomContextSelfShift
  RawCodedPAInductionAxiomCertificate
  RawCodedPAClosureInductionCompiler
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateStructuralPAAgreement
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixInductionShell
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerCompilation.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixGrowingCaseCompilation.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedProof.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedProofAndEConstructors.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import
  PABoundedRawCodedPALocalProofWitnessedContextMergeTransportComplete.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedPAInductionAxiomCertificate.
Import PABoundedRawCodedPAClosureInductionCompiler.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateStructuralPAAgreement.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixInductionShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerCompilation.

(** ------------------------------------------------------------------
    The two closed arithmetic kernels. *)

Definition coqCarrierStrongPrefixNoLtZeroFormula : formula :=
  pAll (pImp
    (Formula.ltTermAt (tVar 0) tZero)
    pBot).

Definition coqCarrierStrongPrefixLtKernelBodyFormula : formula :=
  pImp
    (Formula.ltTermAt (tVar 0) (tVar 1))
    (pImp
      (Formula.ltTermAt (tVar 1) (tSucc (tVar 2)))
      (Formula.ltTermAt (tVar 0) (tVar 2))).

(** Quantifier order is [d], then [e], then [x], so that the body sees
    [x=#0], [e=#1], and [d=#2]. *)
Definition coqCarrierStrongPrefixLtKernelFormula : formula :=
  pAll (pAll (pAll coqCarrierStrongPrefixLtKernelBodyFormula)).

Lemma coqCarrierStrongPrefixNoLtZero_bprov :
  Formula.BProv Formula.Ax_s [] coqCarrierStrongPrefixNoLtZeroFormula.
Proof.
  unfold coqCarrierStrongPrefixNoLtZeroFormula.
  apply Formula.BProv_allI_of_sentences.
  - exact Formula.sentence_ax_s.
  - apply Formula.BProv_impI.
    apply (Formula.BProv_Ax_s_ltTermAt_leTermAt_bot
      [Formula.ltTermAt (tVar 0) tZero]
      (tVar 0) tZero).
    + apply Formula.BProv_ass_head.
    + apply Formula.BProv_Ax_s_leTermAt_zero_left.
Qed.

Lemma coqCarrierStrongPrefixLtKernel_bprov :
  Formula.BProv Formula.Ax_s [] coqCarrierStrongPrefixLtKernelFormula.
Proof.
  unfold coqCarrierStrongPrefixLtKernelFormula.
  apply Formula.BProv_allI_of_sentences.
  - exact Formula.sentence_ax_s.
  - apply Formula.BProv_allI_of_sentences.
    + exact Formula.sentence_ax_s.
    + apply Formula.BProv_allI_of_sentences.
      * exact Formula.sentence_ax_s.
      * unfold coqCarrierStrongPrefixLtKernelBodyFormula.
        apply Formula.BProv_impI.
        apply Formula.BProv_impI.
        apply (Formula.BProv_Ax_s_ltAt_leAt_trans
          [Formula.ltTermAt (tVar 1) (tSucc (tVar 2));
           Formula.ltTermAt (tVar 0) (tVar 1)] 0 1 2).
        -- apply Formula.BProv_ass. cbn. tauto.
        -- change (Formula.BProv Formula.Ax_s
             [Formula.ltTermAt (tVar 1) (tSucc (tVar 2));
              Formula.ltTermAt (tVar 0) (tVar 1)]
             (Formula.leTermAt (tVar 1) (tVar 2))).
           apply Formula.BProv_Ax_s_leTermAt_of_ltTermAt_succ_right.
           apply Formula.BProv_ass. cbn. tauto.
Qed.

Definition coqCarrierStrongPrefixCaseArithmeticFormula : formula :=
  pAnd coqCarrierStrongPrefixNoLtZeroFormula
    coqCarrierStrongPrefixLtKernelFormula.

Lemma coqCarrierStrongPrefixCaseArithmetic_bprov :
  Formula.BProv Formula.Ax_s []
    coqCarrierStrongPrefixCaseArithmeticFormula.
Proof.
  unfold coqCarrierStrongPrefixCaseArithmeticFormula.
  apply Formula.BProv_andI.
  - exact coqCarrierStrongPrefixNoLtZero_bprov.
  - exact coqCarrierStrongPrefixLtKernel_bprov.
Qed.

Definition coqCarrierStrongPrefixNoLtZeroTemplate : TemplateFormula :=
  embedPAFormula coqCarrierStrongPrefixNoLtZeroFormula.

Definition coqCarrierStrongPrefixLtKernelTemplate : TemplateFormula :=
  embedPAFormula coqCarrierStrongPrefixLtKernelFormula.

Definition coqCarrierStrongPrefixNoLtZeroBodyTemplate : TemplateFormula :=
  embedPAFormula
    (pImp (Formula.ltTermAt (tVar 0) tZero) pBot).

Definition coqCarrierStrongPrefixLtKernelBodyTemplate : TemplateFormula :=
  embedPAFormula coqCarrierStrongPrefixLtKernelBodyFormula.

(** ------------------------------------------------------------------
    Finite proof template over the three closed premises. *)

Definition coqCarrierStrongPrefixOrdinaryStepTemplate : TemplateFormula :=
  tfAll
    (tfImp
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixSuccessorTemplate).

Definition coqCarrierStrongPrefixZeroGuardTemplate : TemplateFormula :=
  embedPAFormula (Formula.ltTermAt (tVar 0) tZero).

Definition coqCarrierStrongPrefixZeroBodyTemplate : TemplateFormula :=
  tfImp coqCarrierStrongPrefixZeroGuardTemplate
    coqRestrictedPADerivationSoundnessCarrierPredicateTemplate.

Definition coqCarrierStrongPrefixSuccessorGuardTemplate : TemplateFormula :=
  embedPAFormula
    (Formula.ltTermAt (tVar 0) (tSucc (tVar 1))).

Definition coqCarrierStrongPrefixSuccessorGuardShiftedTemplate
    : TemplateFormula :=
  templateFormulaRename S coqCarrierStrongPrefixSuccessorGuardTemplate.

Definition coqCarrierStrongPrefixXLtETemplate : TemplateFormula :=
  embedPAFormula (Formula.ltTermAt (tVar 0) (tVar 1)).

Definition coqCarrierStrongPrefixXLtDTemplate : TemplateFormula :=
  embedPAFormula (Formula.ltTermAt (tVar 0) (tVar 2)).

Definition coqCarrierStrongPrefixKdUnderETemplate : TemplateFormula :=
  templateFormulaRename S
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate.

Definition coqCarrierStrongPrefixKdUnderXTemplate : TemplateFormula :=
  templateFormulaRename S coqCarrierStrongPrefixKdUnderETemplate.

Definition coqCarrierStrongPrefixKdUnderEBodyTemplate : TemplateFormula :=
  tfImp
    (embedPAFormula (Formula.ltTermAt (tVar 0) (tVar 2)))
    coqRestrictedPADerivationSoundnessCarrierPredicateTemplate.

Definition coqCarrierStrongPrefixKdUnderXBodyTemplate : TemplateFormula :=
  (** This is the body *under K's own member binder*.  At the surrounding
      [x,e,d] depth, [d] is [#2], hence beneath this additional binder it is
      [#3].  Opening the binder at [x=#0] lowers it back to [#2]. *)
  tfImp
    (embedPAFormula (Formula.ltTermAt (tVar 0) (tVar 3)))
    coqRestrictedPADerivationSoundnessCarrierPredicateTemplate.

Definition coqCarrierStrongPrefixKeBodyTemplate : TemplateFormula :=
  tfImp coqCarrierStrongPrefixXLtETemplate
    coqRestrictedPADerivationSoundnessCarrierPredicateTemplate.

(** Extracting bodies by pattern matching keeps the subsequent All-E tree
    tied definitionally to the advertised closed arithmetic formula. *)
Definition coqCarrierStrongPrefixNoLtZeroAllBodyTemplate : TemplateFormula :=
  match coqCarrierStrongPrefixNoLtZeroTemplate with
  | tfAll body => body
  | _ => tfBot
  end.

Definition coqCarrierStrongPrefixLtKernelAllDBodyTemplate : TemplateFormula :=
  match coqCarrierStrongPrefixLtKernelTemplate with
  | tfAll body => body
  | _ => tfBot
  end.

Definition coqCarrierStrongPrefixLtKernelAfterDTemplate : TemplateFormula :=
  templateFormulaOpen (embedPATerm (tVar 2))
    coqCarrierStrongPrefixLtKernelAllDBodyTemplate.

Definition coqCarrierStrongPrefixLtKernelAllEBodyTemplate : TemplateFormula :=
  match coqCarrierStrongPrefixLtKernelAfterDTemplate with
  | tfAll body => body
  | _ => tfBot
  end.

Definition coqCarrierStrongPrefixLtKernelAfterETemplate : TemplateFormula :=
  templateFormulaOpen (embedPATerm (tVar 1))
    coqCarrierStrongPrefixLtKernelAllEBodyTemplate.

Definition coqCarrierStrongPrefixLtKernelAllXBodyTemplate : TemplateFormula :=
  match coqCarrierStrongPrefixLtKernelAfterETemplate with
  | tfAll body => body
  | _ => tfBot
  end.

Definition coqCarrierStrongPrefixLtKernelInstanceTemplate : TemplateFormula :=
  templateFormulaOpen (embedPATerm (tVar 0))
    coqCarrierStrongPrefixLtKernelAllXBodyTemplate.

Definition coqCarrierStrongPrefixStrongStepAllBodyTemplate : TemplateFormula :=
  match coqRestrictedPADerivationSoundnessCarrierStrongStepTemplate with
  | tfAll body => body
  | _ => tfBot
  end.

Definition coqCarrierStrongPrefixStrongStepAtETemplate : TemplateFormula :=
  templateFormulaOpen (embedPATerm (tVar 0))
    coqCarrierStrongPrefixStrongStepAllBodyTemplate.

Lemma coqCarrierStrongPrefixNoLtZeroTemplate_shape :
  coqCarrierStrongPrefixNoLtZeroTemplate =
  tfAll coqCarrierStrongPrefixNoLtZeroAllBodyTemplate.
Proof. reflexivity. Qed.

Lemma coqCarrierStrongPrefixNoLtZeroInstanceTemplate_shape :
  templateFormulaOpen (embedPATerm (tVar 0))
    coqCarrierStrongPrefixNoLtZeroAllBodyTemplate =
  tfImp coqCarrierStrongPrefixZeroGuardTemplate tfBot.
Proof. reflexivity. Qed.

Lemma coqCarrierStrongPrefixLtKernelTemplate_shape :
  coqCarrierStrongPrefixLtKernelTemplate =
  tfAll coqCarrierStrongPrefixLtKernelAllDBodyTemplate.
Proof. reflexivity. Qed.

Lemma coqCarrierStrongPrefixLtKernelAfterDTemplate_shape :
  coqCarrierStrongPrefixLtKernelAfterDTemplate =
  tfAll coqCarrierStrongPrefixLtKernelAllEBodyTemplate.
Proof. reflexivity. Qed.

Lemma coqCarrierStrongPrefixLtKernelAfterETemplate_shape :
  coqCarrierStrongPrefixLtKernelAfterETemplate =
  tfAll coqCarrierStrongPrefixLtKernelAllXBodyTemplate.
Proof. reflexivity. Qed.

Lemma coqCarrierStrongPrefixLtKernelInstanceTemplate_shape :
  coqCarrierStrongPrefixLtKernelInstanceTemplate =
  coqCarrierStrongPrefixLtKernelBodyTemplate.
Proof. reflexivity. Qed.

Lemma coqCarrierStrongPrefixStrongStepTemplate_shape :
  coqRestrictedPADerivationSoundnessCarrierStrongStepTemplate =
  tfAll coqCarrierStrongPrefixStrongStepAllBodyTemplate.
Proof. reflexivity. Qed.

(** Opening the carrier predicate with the variable itself is an identity.
    Asking conversion to establish this directly expands the very large
    soundness predicate.  The already checked finalizer shape contains the
    same identity as its implication consequent, so project that consequent
    from the opaque theorem instead.  Kernel conversion then exposes only
    the outer implication constructor. *)
Definition coqCarrierTemplateImpConsequent
    (input : TemplateFormula) : TemplateFormula :=
  match input with
  | tfImp _ consequent => consequent
  | _ => tfBot
  end.

Lemma coqCarrierPredicate_open_variable_identity :
  templateFormulaOpen (embedPATerm (tVar 0))
    coqRestrictedPADerivationSoundnessCarrierPredicateTemplate =
  coqRestrictedPADerivationSoundnessCarrierPredicateTemplate.
Proof.
  pose proof
    coqRestrictedPADerivationSoundnessCarrierFinalizerGuardedPredicateTemplate_shape
    as hshape.
  exact (f_equal coqCarrierTemplateImpConsequent hshape).
Qed.

(** [templateOpeningSubstAt depth #0] fixes indices through [depth] and
    lowers every larger index once.  Its fixed points therefore remain fixed
    when the protected prefix grows by one.  The following structural lemmas
    package that elementary fact once, so later uses stay opaque and never
    traverse the very large carrier predicate during conversion. *)
Fixpoint coqCarrierLowerIndexAt (depth index : nat) : nat :=
  match depth, index with
  | 0, 0 => 0
  | 0, S outerIndex => outerIndex
  | S _, 0 => 0
  | S outerDepth, S outerIndex =>
      S (coqCarrierLowerIndexAt outerDepth outerIndex)
  end.

Lemma coqCarrierOpeningSubstAt_variable : forall depth index,
  templateOpeningSubstAt depth (ttVar 0) index =
  ttVar (coqCarrierLowerIndexAt depth index).
Proof.
  induction depth as [|depth ih]; intros [|index]; cbn.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - now rewrite ih.
Qed.

Lemma coqCarrierLowerIndexAt_fixed_succ : forall depth index,
  coqCarrierLowerIndexAt depth index = index ->
  coqCarrierLowerIndexAt (S depth) index = index.
Proof.
  induction depth as [|depth ih]; intros [|index] hfixed; cbn in *.
  - reflexivity.
  - lia.
  - reflexivity.
  - f_equal. apply ih. lia.
Qed.

Lemma coqCarrierLowerIndexAt_fixed_shift : forall depth index,
  coqCarrierLowerIndexAt depth index = index ->
  templateShiftRenamingAt (S depth) index = index.
Proof.
  induction depth as [|depth ih]; intros [|index] hfixed;
    cbn in hfixed |- *; try reflexivity.
  - lia.
  - f_equal. apply ih. now injection hfixed.
Qed.

Lemma coqCarrierOpeningSubstAt_above_fixed_index : forall
    depth index replacement,
  coqCarrierLowerIndexAt depth index = index ->
  templateOpeningSubstAt (S depth) replacement index = ttVar index.
Proof.
  induction depth as [|depth ih]; intros [|index] replacement hfixed.
  - reflexivity.
  - cbn in hfixed. lia.
  - reflexivity.
  - change
      (templateTermRename S
        (templateOpeningSubstAt (S depth) replacement index) =
       ttVar (S index)).
    rewrite (ih index replacement).
    + reflexivity.
    + cbn in hfixed. now injection hfixed.
Qed.

Lemma coqCarrierTemplateTerm_opening_fixed_succ : forall input depth,
  templateTermSubst (templateOpeningSubstAt depth (ttVar 0)) input = input ->
  templateTermSubst (templateOpeningSubstAt (S depth) (ttVar 0)) input = input.
Proof.
  induction input; intros depth hfixed; cbn in hfixed |- *.
  - change
      (templateOpeningSubstAt depth (ttVar 0) n = ttVar n) in hfixed.
    change
      (templateOpeningSubstAt (S depth) (ttVar 0) n = ttVar n).
    rewrite !coqCarrierOpeningSubstAt_variable in hfixed |- *.
    f_equal. apply coqCarrierLowerIndexAt_fixed_succ.
    now injection hfixed.
  - reflexivity.
  - reflexivity.
  - injection hfixed as hchild. f_equal. now apply IHinput.
  - injection hfixed as hleft hright. f_equal.
    + now apply IHinput1.
    + now apply IHinput2.
  - injection hfixed as hleft hright. f_equal.
    + now apply IHinput1.
    + now apply IHinput2.
Qed.

Lemma coqCarrierTemplateTerms_opening_fixed_succ : forall inputs depth,
  templateTermsSubst (templateOpeningSubstAt depth (ttVar 0)) inputs = inputs ->
  templateTermsSubst (templateOpeningSubstAt (S depth) (ttVar 0)) inputs =
    inputs.
Proof.
  induction inputs as [|input inputs ih]; intros depth hfixed;
    cbn in hfixed |- *; [reflexivity |].
  injection hfixed as hhead htail. f_equal.
  - now apply coqCarrierTemplateTerm_opening_fixed_succ.
  - now apply ih.
Qed.

Lemma coqCarrierTemplateFormula_opening_fixed_succ : forall input depth,
  templateFormulaSubst (templateOpeningSubstAt depth (ttVar 0)) input =
    input ->
  templateFormulaSubst (templateOpeningSubstAt (S depth) (ttVar 0)) input =
    input.
Proof.
  induction input; intros depth hfixed; cbn in hfixed |- *.
  - injection hfixed as hleft hright. f_equal.
    + now apply coqCarrierTemplateTerm_opening_fixed_succ.
    + now apply coqCarrierTemplateTerm_opening_fixed_succ.
  - reflexivity.
  - injection hfixed as hleft hright. f_equal.
    + now apply IHinput1.
    + now apply IHinput2.
  - injection hfixed as hleft hright. f_equal.
    + now apply IHinput1.
    + now apply IHinput2.
  - injection hfixed as hleft hright. f_equal.
    + now apply IHinput1.
    + now apply IHinput2.
  - injection hfixed as hbody. f_equal.
    change
      (templateFormulaSubst
        (templateOpeningSubstAt (S (S depth)) (ttVar 0)) input = input).
    apply IHinput with (depth := S depth).
    exact hbody.
  - injection hfixed as hbody. f_equal.
    change
      (templateFormulaSubst
        (templateOpeningSubstAt (S (S depth)) (ttVar 0)) input = input).
    apply IHinput with (depth := S depth).
    exact hbody.
  - injection hfixed as harguments. f_equal.
    now apply coqCarrierTemplateTerms_opening_fixed_succ.
Qed.

(** A formula fixed by zero-opening below [depth] uses no variable above
    that protected prefix.  Consequently opening the next variable with an
    arbitrary replacement still leaves it unchanged. *)
Lemma coqCarrierTemplateTerm_opening_fixed_above : forall
    input depth replacement,
  templateTermSubst
    (templateOpeningSubstAt depth (ttVar 0)) input = input ->
  templateTermSubst
    (templateOpeningSubstAt (S depth) replacement) input = input.
Proof.
  induction input; intros depth replacement hfixed; cbn in hfixed |- *.
  - change
      (templateOpeningSubstAt depth (ttVar 0) n = ttVar n) in hfixed.
    rewrite coqCarrierOpeningSubstAt_variable in hfixed.
    apply coqCarrierOpeningSubstAt_above_fixed_index.
    now injection hfixed.
  - reflexivity.
  - reflexivity.
  - injection hfixed as hchild. f_equal. now apply IHinput.
  - injection hfixed as hleft hright. f_equal.
    + now apply IHinput1.
    + now apply IHinput2.
  - injection hfixed as hleft hright. f_equal.
    + now apply IHinput1.
    + now apply IHinput2.
Qed.

Lemma coqCarrierTemplateTerms_opening_fixed_above : forall
    inputs depth replacement,
  templateTermsSubst
    (templateOpeningSubstAt depth (ttVar 0)) inputs = inputs ->
  templateTermsSubst
    (templateOpeningSubstAt (S depth) replacement) inputs = inputs.
Proof.
  induction inputs as [|input inputs ih]; intros depth replacement hfixed;
    cbn in hfixed |- *; [reflexivity |].
  injection hfixed as hhead htail. f_equal.
  - now apply coqCarrierTemplateTerm_opening_fixed_above.
  - now apply ih.
Qed.

Lemma coqCarrierTemplateFormula_opening_fixed_above : forall
    input depth replacement,
  templateFormulaSubst
    (templateOpeningSubstAt depth (ttVar 0)) input = input ->
  templateFormulaSubst
    (templateOpeningSubstAt (S depth) replacement) input = input.
Proof.
  induction input; intros depth replacement hfixed; cbn in hfixed |- *.
  - injection hfixed as hleft hright. f_equal.
    + now apply coqCarrierTemplateTerm_opening_fixed_above.
    + now apply coqCarrierTemplateTerm_opening_fixed_above.
  - reflexivity.
  - injection hfixed as hleft hright. f_equal.
    + now apply IHinput1.
    + now apply IHinput2.
  - injection hfixed as hleft hright. f_equal.
    + now apply IHinput1.
    + now apply IHinput2.
  - injection hfixed as hleft hright. f_equal.
    + now apply IHinput1.
    + now apply IHinput2.
  - injection hfixed as hbody. f_equal.
    change
      (templateFormulaSubst
        (templateOpeningSubstAt (S (S depth)) replacement) input = input).
    apply IHinput with (depth := S depth).
    exact hbody.
  - injection hfixed as hbody. f_equal.
    change
      (templateFormulaSubst
        (templateOpeningSubstAt (S (S depth)) replacement) input = input).
    apply IHinput with (depth := S depth).
    exact hbody.
  - injection hfixed as harguments. f_equal.
    now apply coqCarrierTemplateTerms_opening_fixed_above.
Qed.

Lemma coqCarrierPredicate_opening_above_root_identity : forall replacement,
  templateFormulaSubst (templateOpeningSubstAt 1 replacement)
    coqRestrictedPADerivationSoundnessCarrierPredicateTemplate =
  coqRestrictedPADerivationSoundnessCarrierPredicateTemplate.
Proof.
  intro replacement.
  apply coqCarrierTemplateFormula_opening_fixed_above with (depth := 0).
  pose proof coqCarrierPredicate_open_variable_identity as hpredicate.
  unfold templateFormulaOpen in hpredicate.
  exact hpredicate.
Qed.

Lemma coqCarrierTemplateTerm_opening_fixed_shift : forall input depth,
  templateTermSubst
    (templateOpeningSubstAt depth (ttVar 0)) input = input ->
  templateTermRename (templateShiftRenamingAt (S depth)) input = input.
Proof.
  induction input; intros depth hfixed; cbn in hfixed |- *.
  - rewrite coqCarrierOpeningSubstAt_variable in hfixed.
    f_equal. apply coqCarrierLowerIndexAt_fixed_shift.
    now injection hfixed.
  - reflexivity.
  - reflexivity.
  - injection hfixed as hchild. f_equal. now apply IHinput.
  - injection hfixed as hleft hright. f_equal.
    + now apply IHinput1.
    + now apply IHinput2.
  - injection hfixed as hleft hright. f_equal.
    + now apply IHinput1.
    + now apply IHinput2.
Qed.

Lemma coqCarrierTemplateTerms_opening_fixed_shift : forall inputs depth,
  templateTermsSubst
    (templateOpeningSubstAt depth (ttVar 0)) inputs = inputs ->
  templateTermsRename (templateShiftRenamingAt (S depth)) inputs = inputs.
Proof.
  induction inputs as [|input inputs ih]; intros depth hfixed;
    cbn in hfixed |- *; [reflexivity |].
  injection hfixed as hhead htail. f_equal.
  - now apply coqCarrierTemplateTerm_opening_fixed_shift.
  - now apply ih.
Qed.

Lemma coqCarrierTemplateFormula_opening_fixed_shift : forall input depth,
  templateFormulaSubst
    (templateOpeningSubstAt depth (ttVar 0)) input = input ->
  templateFormulaRename (templateShiftRenamingAt (S depth)) input = input.
Proof.
  induction input; intros depth hfixed; cbn in hfixed |- *.
  - injection hfixed as hleft hright. f_equal.
    + now apply coqCarrierTemplateTerm_opening_fixed_shift.
    + now apply coqCarrierTemplateTerm_opening_fixed_shift.
  - reflexivity.
  - injection hfixed as hleft hright. f_equal.
    + now apply IHinput1.
    + now apply IHinput2.
  - injection hfixed as hleft hright. f_equal.
    + now apply IHinput1.
    + now apply IHinput2.
  - injection hfixed as hleft hright. f_equal.
    + now apply IHinput1.
    + now apply IHinput2.
  - injection hfixed as hbody. f_equal.
    transitivity
      (templateFormulaRename
        (templateShiftRenamingAt (S (S depth))) input).
    + apply templateFormulaRename_ext. intros [|index]; reflexivity.
    + apply IHinput with (depth := S depth).
      exact hbody.
  - injection hfixed as hbody. f_equal.
    transitivity
      (templateFormulaRename
        (templateShiftRenamingAt (S (S depth))) input).
    + apply templateFormulaRename_ext. intros [|index]; reflexivity.
    + apply IHinput with (depth := S depth).
      exact hbody.
  - injection hfixed as harguments. f_equal.
    now apply coqCarrierTemplateTerms_opening_fixed_shift.
Qed.

Lemma coqCarrierPredicate_rename_above_root_identity :
  templateFormulaRename (templateShiftRenamingAt 1)
    coqRestrictedPADerivationSoundnessCarrierPredicateTemplate =
  coqRestrictedPADerivationSoundnessCarrierPredicateTemplate.
Proof.
  pose proof coqCarrierPredicate_open_variable_identity as hpredicate.
  unfold templateFormulaOpen in hpredicate.
  change
    (templateFormulaSubst
      (templateOpeningSubstAt 0 (ttVar 0))
      coqRestrictedPADerivationSoundnessCarrierPredicateTemplate =
     coqRestrictedPADerivationSoundnessCarrierPredicateTemplate)
    in hpredicate.
  exact (coqCarrierTemplateFormula_opening_fixed_shift
    coqRestrictedPADerivationSoundnessCarrierPredicateTemplate
    0 hpredicate).
Qed.

(** The same opening fixes [K].  Once its member quantifier is crossed, the
    predicate's depth-zero fixed point remains fixed at depth one. *)
Lemma coqCarrierStrongPrefix_open_variable_identity :
  templateFormulaOpen (embedPATerm (tVar 0))
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate =
  coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate.
Proof.
  pose proof coqCarrierPredicate_open_variable_identity as hpredicateZero.
  unfold templateFormulaOpen in hpredicateZero.
  change
    (templateFormulaSubst
      (templateOpeningSubstAt 0 (ttVar 0))
      coqRestrictedPADerivationSoundnessCarrierPredicateTemplate =
     coqRestrictedPADerivationSoundnessCarrierPredicateTemplate)
    in hpredicateZero.
  pose proof
    (coqCarrierTemplateFormula_opening_fixed_succ
      coqRestrictedPADerivationSoundnessCarrierPredicateTemplate
      0 hpredicateZero) as hpredicateOne.
  unfold templateFormulaOpen,
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate.
  change
    (tfAll
      (templateFormulaSubst
        (templateOpeningSubstAt 1 (ttVar 0))
        (tfImp
          (embedPAFormula (Formula.ltTermAt (tVar 0) (tVar 1)))
          coqRestrictedPADerivationSoundnessCarrierPredicateTemplate)) =
     tfAll
      (tfImp
        (embedPAFormula (Formula.ltTermAt (tVar 0) (tVar 1)))
        coqRestrictedPADerivationSoundnessCarrierPredicateTemplate)).
  assert (hbody :
    templateFormulaSubst
      (templateOpeningSubstAt 1 (ttVar 0))
      (tfImp
        (embedPAFormula (Formula.ltTermAt (tVar 0) (tVar 1)))
        coqRestrictedPADerivationSoundnessCarrierPredicateTemplate) =
    tfImp
      (embedPAFormula (Formula.ltTermAt (tVar 0) (tVar 1)))
      coqRestrictedPADerivationSoundnessCarrierPredicateTemplate).
  {
    change
      (tfImp
        (templateFormulaSubst
          (templateOpeningSubstAt 1 (ttVar 0))
          (embedPAFormula (Formula.ltTermAt (tVar 0) (tVar 1))))
        (templateFormulaSubst
          (templateOpeningSubstAt 1 (ttVar 0))
          coqRestrictedPADerivationSoundnessCarrierPredicateTemplate) =
       tfImp
        (embedPAFormula (Formula.ltTermAt (tVar 0) (tVar 1)))
        coqRestrictedPADerivationSoundnessCarrierPredicateTemplate).
    change
      (templateFormulaSubst
        (templateOpeningSubstAt 1 (ttVar 0))
        coqRestrictedPADerivationSoundnessCarrierPredicateTemplate =
       coqRestrictedPADerivationSoundnessCarrierPredicateTemplate)
      in hpredicateOne.
    now rewrite hpredicateOne.
  }
  exact (f_equal tfAll hbody).
Qed.

Lemma coqCarrierStrongPrefix_rename_above_root_identity :
  templateFormulaRename (templateShiftRenamingAt 1)
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate =
  coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate.
Proof.
  apply coqCarrierTemplateFormula_opening_fixed_shift with (depth := 0).
  pose proof coqCarrierStrongPrefix_open_variable_identity as hprefix.
  unfold templateFormulaOpen in hprefix.
  exact hprefix.
Qed.

Lemma coqCarrierStrongPrefixShiftedTemplate_identity :
  coqRestrictedPADerivationSoundnessCarrierStrongPrefixShiftedTemplate =
  coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate.
Proof.
  unfold
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixShiftedTemplate.
  exact coqCarrierStrongPrefix_rename_above_root_identity.
Qed.

Lemma coqCarrierStrongPrefixStrongStepAtETemplate_shape :
  coqCarrierStrongPrefixStrongStepAtETemplate =
  tfImp coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate
    coqRestrictedPADerivationSoundnessCarrierPredicateTemplate.
Proof.
  unfold coqCarrierStrongPrefixStrongStepAtETemplate,
    coqCarrierStrongPrefixStrongStepAllBodyTemplate.
  change
    (tfImp
      (templateFormulaOpen (embedPATerm (tVar 0))
        coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate)
      (templateFormulaOpen (embedPATerm (tVar 0))
        coqRestrictedPADerivationSoundnessCarrierPredicateTemplate) =
     tfImp coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate
       coqRestrictedPADerivationSoundnessCarrierPredicateTemplate).
  now rewrite coqCarrierStrongPrefix_open_variable_identity,
    coqCarrierPredicate_open_variable_identity.
Qed.

Lemma coqCarrierStrongPrefixKdUnderETemplate_shape :
  coqCarrierStrongPrefixKdUnderETemplate =
  tfAll coqCarrierStrongPrefixKdUnderEBodyTemplate.
Proof.
  unfold coqCarrierStrongPrefixKdUnderETemplate,
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate,
    coqCarrierStrongPrefixKdUnderEBodyTemplate.
  change
    (tfAll
      (tfImp
        (embedPAFormula (Formula.ltTermAt (tVar 0) (tVar 2)))
        (templateFormulaRename (templateShiftRenamingAt 1)
          coqRestrictedPADerivationSoundnessCarrierPredicateTemplate)) =
     tfAll
      (tfImp
        (embedPAFormula (Formula.ltTermAt (tVar 0) (tVar 2)))
        coqRestrictedPADerivationSoundnessCarrierPredicateTemplate)).
  now rewrite coqCarrierPredicate_rename_above_root_identity.
Qed.

Lemma coqCarrierStrongPrefixKdUnderXTemplate_shape :
  coqCarrierStrongPrefixKdUnderXTemplate =
  tfAll coqCarrierStrongPrefixKdUnderXBodyTemplate.
Proof.
  unfold coqCarrierStrongPrefixKdUnderXTemplate.
  rewrite coqCarrierStrongPrefixKdUnderETemplate_shape.
  unfold coqCarrierStrongPrefixKdUnderXBodyTemplate,
    coqCarrierStrongPrefixKdUnderEBodyTemplate.
  change
    (tfAll
      (tfImp
        (embedPAFormula (Formula.ltTermAt (tVar 0) (tVar 3)))
        (templateFormulaRename (templateShiftRenamingAt 1)
          coqRestrictedPADerivationSoundnessCarrierPredicateTemplate)) =
     tfAll
      (tfImp
        (embedPAFormula (Formula.ltTermAt (tVar 0) (tVar 3)))
        coqRestrictedPADerivationSoundnessCarrierPredicateTemplate)).
  now rewrite coqCarrierPredicate_rename_above_root_identity.
Qed.

Lemma coqCarrierStrongPrefixKdUnderX_open_shape :
  templateFormulaOpen (embedPATerm (tVar 0))
    coqCarrierStrongPrefixKdUnderXBodyTemplate =
  tfImp coqCarrierStrongPrefixXLtDTemplate
    coqRestrictedPADerivationSoundnessCarrierPredicateTemplate.
Proof.
  change
    (tfImp coqCarrierStrongPrefixXLtDTemplate
      (templateFormulaOpen (embedPATerm (tVar 0))
        coqRestrictedPADerivationSoundnessCarrierPredicateTemplate) =
     tfImp coqCarrierStrongPrefixXLtDTemplate
       coqRestrictedPADerivationSoundnessCarrierPredicateTemplate).
  now rewrite coqCarrierPredicate_open_variable_identity.
Qed.

Lemma coqCarrierStrongPrefixZeroTemplate_shape :
  coqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroTemplate =
  tfAll coqCarrierStrongPrefixZeroBodyTemplate.
Proof.
  unfold
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroTemplate,
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate,
    coqCarrierStrongPrefixZeroBodyTemplate,
    coqCarrierStrongPrefixZeroGuardTemplate,
    templateFormulaOpen.
  change
    (tfAll
      (tfImp
        (embedPAFormula (Formula.ltTermAt (tVar 0) tZero))
        (templateFormulaSubst
          (templateOpeningSubstAt 1 (embedPATerm tZero))
          coqRestrictedPADerivationSoundnessCarrierPredicateTemplate)) =
     tfAll
      (tfImp
        (embedPAFormula (Formula.ltTermAt (tVar 0) tZero))
        coqRestrictedPADerivationSoundnessCarrierPredicateTemplate)).
  now rewrite coqCarrierPredicate_opening_above_root_identity.
Qed.

Lemma coqCarrierStrongPrefixSuccessorTemplate_shape :
  coqRestrictedPADerivationSoundnessCarrierStrongPrefixSuccessorTemplate =
  tfAll
    (tfImp coqCarrierStrongPrefixSuccessorGuardTemplate
      coqRestrictedPADerivationSoundnessCarrierPredicateTemplate).
Proof.
  unfold
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixSuccessorTemplate.
  rewrite coqCarrierStrongPrefixShiftedTemplate_identity.
  unfold
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate,
    coqCarrierStrongPrefixSuccessorGuardTemplate,
    templateFormulaOpen.
  change
    (tfAll
      (tfImp
        (embedPAFormula
          (Formula.ltTermAt (tVar 0) (tSucc (tVar 1))))
        (templateFormulaSubst
          (templateOpeningSubstAt 1
            (embedPATerm (tSucc (tVar 0))))
          coqRestrictedPADerivationSoundnessCarrierPredicateTemplate)) =
     tfAll
      (tfImp
        (embedPAFormula
          (Formula.ltTermAt (tVar 0) (tSucc (tVar 1))))
        coqRestrictedPADerivationSoundnessCarrierPredicateTemplate)).
  now rewrite coqCarrierPredicate_opening_above_root_identity.
Qed.

Lemma coqCarrierStrongPrefixKeTemplate_shape :
  coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate =
  tfAll coqCarrierStrongPrefixKeBodyTemplate.
Proof. reflexivity. Qed.

(** All three outer premises are closed, so repeated eigenvariable shifts
    leave their finite template context literally unchanged. *)
Definition coqCarrierStrongPrefixCasePremiseContext : TemplateContext :=
  [coqRestrictedPADerivationSoundnessCarrierStrongStepTemplate;
   coqCarrierStrongPrefixLtKernelTemplate;
   coqCarrierStrongPrefixNoLtZeroTemplate].

Lemma coqCarrierStrongStepTemplate_shift_closed :
  templateFormulaRename S
    coqRestrictedPADerivationSoundnessCarrierStrongStepTemplate =
  coqRestrictedPADerivationSoundnessCarrierStrongStepTemplate.
Proof.
  unfold coqRestrictedPADerivationSoundnessCarrierStrongStepTemplate.
  change
    (tfAll
      (tfImp
        (templateFormulaRename (templateShiftRenamingAt 1)
          coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate)
        (templateFormulaRename (templateShiftRenamingAt 1)
          coqRestrictedPADerivationSoundnessCarrierPredicateTemplate)) =
     tfAll
      (tfImp coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate
        coqRestrictedPADerivationSoundnessCarrierPredicateTemplate)).
  now rewrite coqCarrierStrongPrefix_rename_above_root_identity,
    coqCarrierPredicate_rename_above_root_identity.
Qed.

Lemma coqCarrierStrongPrefixCasePremiseContext_shift_closed :
  templateContextShift coqCarrierStrongPrefixCasePremiseContext =
  coqCarrierStrongPrefixCasePremiseContext.
Proof.
  unfold templateContextShift, templateContextRename,
    coqCarrierStrongPrefixCasePremiseContext.
  change
    ([templateFormulaRename S
       coqRestrictedPADerivationSoundnessCarrierStrongStepTemplate;
     templateFormulaRename S coqCarrierStrongPrefixLtKernelTemplate;
     templateFormulaRename S coqCarrierStrongPrefixNoLtZeroTemplate] =
    [coqRestrictedPADerivationSoundnessCarrierStrongStepTemplate;
     coqCarrierStrongPrefixLtKernelTemplate;
     coqCarrierStrongPrefixNoLtZeroTemplate]).
  rewrite coqCarrierStrongStepTemplate_shift_closed.
  reflexivity.
Qed.

(** Expose only the two freshly shifted heads before reusing closure of the
    shared premise tail.  In particular, do not compute [templateContextShift]
    over that tail: it contains the large strong-step predicate template. *)
Lemma coqCarrierStrongPrefixSuccessorAllContext_shift :
  templateContextShift
    (coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate ::
      coqCarrierStrongPrefixCasePremiseContext) =
  coqCarrierStrongPrefixKdUnderETemplate ::
    coqCarrierStrongPrefixCasePremiseContext.
Proof.
  change
    (coqCarrierStrongPrefixKdUnderETemplate ::
      templateContextShift coqCarrierStrongPrefixCasePremiseContext =
     coqCarrierStrongPrefixKdUnderETemplate ::
      coqCarrierStrongPrefixCasePremiseContext).
  now rewrite coqCarrierStrongPrefixCasePremiseContext_shift_closed.
Qed.

Lemma coqCarrierStrongPrefixKeAllContext_shift :
  templateContextShift
    (coqCarrierStrongPrefixSuccessorGuardTemplate ::
     coqCarrierStrongPrefixKdUnderETemplate ::
     coqCarrierStrongPrefixCasePremiseContext) =
  coqCarrierStrongPrefixSuccessorGuardShiftedTemplate ::
    coqCarrierStrongPrefixKdUnderXTemplate ::
    coqCarrierStrongPrefixCasePremiseContext.
Proof.
  change
    (coqCarrierStrongPrefixSuccessorGuardShiftedTemplate ::
     coqCarrierStrongPrefixKdUnderXTemplate ::
     templateContextShift coqCarrierStrongPrefixCasePremiseContext =
     coqCarrierStrongPrefixSuccessorGuardShiftedTemplate ::
     coqCarrierStrongPrefixKdUnderXTemplate ::
     coqCarrierStrongPrefixCasePremiseContext).
  now rewrite coqCarrierStrongPrefixCasePremiseContext_shift_closed.
Qed.

(** Zero case. *)
Definition coqCarrierStrongPrefixZeroArithmeticAllRoot : TemplateRawProof :=
  trpAss
    (coqCarrierStrongPrefixZeroGuardTemplate ::
      coqCarrierStrongPrefixCasePremiseContext)
    coqCarrierStrongPrefixNoLtZeroTemplate.

Definition coqCarrierStrongPrefixZeroArithmeticRoot : TemplateRawProof :=
  trpAllE
    (coqCarrierStrongPrefixZeroGuardTemplate ::
      coqCarrierStrongPrefixCasePremiseContext)
    coqCarrierStrongPrefixNoLtZeroAllBodyTemplate
    (embedPATerm (tVar 0))
    coqCarrierStrongPrefixZeroArithmeticAllRoot.

Definition coqCarrierStrongPrefixZeroGuardRoot : TemplateRawProof :=
  trpAss
    (coqCarrierStrongPrefixZeroGuardTemplate ::
      coqCarrierStrongPrefixCasePremiseContext)
    coqCarrierStrongPrefixZeroGuardTemplate.

Definition coqCarrierStrongPrefixZeroBottomRoot : TemplateRawProof :=
  trpImpE
    (coqCarrierStrongPrefixZeroGuardTemplate ::
      coqCarrierStrongPrefixCasePremiseContext)
    coqCarrierStrongPrefixZeroGuardTemplate tfBot
    coqCarrierStrongPrefixZeroArithmeticRoot
    coqCarrierStrongPrefixZeroGuardRoot.

Definition coqCarrierStrongPrefixZeroPredicateRoot : TemplateRawProof :=
  trpBotE
    (coqCarrierStrongPrefixZeroGuardTemplate ::
      coqCarrierStrongPrefixCasePremiseContext)
    coqRestrictedPADerivationSoundnessCarrierPredicateTemplate
    coqCarrierStrongPrefixZeroBottomRoot.

Definition coqCarrierStrongPrefixZeroBodyRoot : TemplateRawProof :=
  trpImpI coqCarrierStrongPrefixCasePremiseContext
    coqCarrierStrongPrefixZeroGuardTemplate
    coqRestrictedPADerivationSoundnessCarrierPredicateTemplate
    coqCarrierStrongPrefixZeroPredicateRoot.

Definition coqCarrierStrongPrefixZeroRoot : TemplateRawProof :=
  trpAllI coqCarrierStrongPrefixCasePremiseContext
    coqCarrierStrongPrefixZeroBodyTemplate
    coqCarrierStrongPrefixZeroBodyRoot.

(** Successor case: deepest arithmetic and prefix instances. *)
Definition coqCarrierStrongPrefixDeepContext : TemplateContext :=
  coqCarrierStrongPrefixXLtETemplate ::
  coqCarrierStrongPrefixSuccessorGuardShiftedTemplate ::
  coqCarrierStrongPrefixKdUnderXTemplate ::
  coqCarrierStrongPrefixCasePremiseContext.

Definition coqCarrierStrongPrefixLtKernelAllRoot : TemplateRawProof :=
  trpAss coqCarrierStrongPrefixDeepContext
    coqCarrierStrongPrefixLtKernelTemplate.

Definition coqCarrierStrongPrefixLtKernelAfterDRoot : TemplateRawProof :=
  trpAllE coqCarrierStrongPrefixDeepContext
    coqCarrierStrongPrefixLtKernelAllDBodyTemplate
    (embedPATerm (tVar 2))
    coqCarrierStrongPrefixLtKernelAllRoot.

Definition coqCarrierStrongPrefixLtKernelAfterERoot : TemplateRawProof :=
  trpAllE coqCarrierStrongPrefixDeepContext
    coqCarrierStrongPrefixLtKernelAllEBodyTemplate
    (embedPATerm (tVar 1))
    coqCarrierStrongPrefixLtKernelAfterDRoot.

Definition coqCarrierStrongPrefixLtKernelInstanceRoot : TemplateRawProof :=
  trpAllE coqCarrierStrongPrefixDeepContext
    coqCarrierStrongPrefixLtKernelAllXBodyTemplate
    (embedPATerm (tVar 0))
    coqCarrierStrongPrefixLtKernelAfterERoot.

Definition coqCarrierStrongPrefixXLtEAssumptionRoot : TemplateRawProof :=
  trpAss coqCarrierStrongPrefixDeepContext
    coqCarrierStrongPrefixXLtETemplate.

Definition coqCarrierStrongPrefixGuardShiftedAssumptionRoot
    : TemplateRawProof :=
  trpAss coqCarrierStrongPrefixDeepContext
    coqCarrierStrongPrefixSuccessorGuardShiftedTemplate.

Definition coqCarrierStrongPrefixLtKernelAfterXLtERoot : TemplateRawProof :=
  trpImpE coqCarrierStrongPrefixDeepContext
    coqCarrierStrongPrefixXLtETemplate
    (tfImp coqCarrierStrongPrefixSuccessorGuardShiftedTemplate
      coqCarrierStrongPrefixXLtDTemplate)
    coqCarrierStrongPrefixLtKernelInstanceRoot
    coqCarrierStrongPrefixXLtEAssumptionRoot.

Definition coqCarrierStrongPrefixXLtDRoot : TemplateRawProof :=
  trpImpE coqCarrierStrongPrefixDeepContext
    coqCarrierStrongPrefixSuccessorGuardShiftedTemplate
    coqCarrierStrongPrefixXLtDTemplate
    coqCarrierStrongPrefixLtKernelAfterXLtERoot
    coqCarrierStrongPrefixGuardShiftedAssumptionRoot.

Definition coqCarrierStrongPrefixKdUnderXAssumptionRoot : TemplateRawProof :=
  trpAss coqCarrierStrongPrefixDeepContext
    coqCarrierStrongPrefixKdUnderXTemplate.

Definition coqCarrierStrongPrefixKdAtXRoot : TemplateRawProof :=
  trpAllE coqCarrierStrongPrefixDeepContext
    coqCarrierStrongPrefixKdUnderXBodyTemplate
    (embedPATerm (tVar 0))
    coqCarrierStrongPrefixKdUnderXAssumptionRoot.

Definition coqCarrierStrongPrefixPredicateAtXRoot : TemplateRawProof :=
  trpImpE coqCarrierStrongPrefixDeepContext
    coqCarrierStrongPrefixXLtDTemplate
    coqRestrictedPADerivationSoundnessCarrierPredicateTemplate
    coqCarrierStrongPrefixKdAtXRoot
    coqCarrierStrongPrefixXLtDRoot.

Definition coqCarrierStrongPrefixKeBodyRoot : TemplateRawProof :=
  trpImpI
    (coqCarrierStrongPrefixSuccessorGuardShiftedTemplate ::
      coqCarrierStrongPrefixKdUnderXTemplate ::
      coqCarrierStrongPrefixCasePremiseContext)
    coqCarrierStrongPrefixXLtETemplate
    coqRestrictedPADerivationSoundnessCarrierPredicateTemplate
    coqCarrierStrongPrefixPredicateAtXRoot.

Definition coqCarrierStrongPrefixKeRoot : TemplateRawProof :=
  trpAllI
    (coqCarrierStrongPrefixSuccessorGuardTemplate ::
      coqCarrierStrongPrefixKdUnderETemplate ::
      coqCarrierStrongPrefixCasePremiseContext)
    coqCarrierStrongPrefixKeBodyTemplate
    coqCarrierStrongPrefixKeBodyRoot.

(** Apply the genuine strong step at [e]. *)
Definition coqCarrierStrongPrefixStrongStepAllRoot : TemplateRawProof :=
  trpAss
    (coqCarrierStrongPrefixSuccessorGuardTemplate ::
      coqCarrierStrongPrefixKdUnderETemplate ::
      coqCarrierStrongPrefixCasePremiseContext)
    coqRestrictedPADerivationSoundnessCarrierStrongStepTemplate.

Definition coqCarrierStrongPrefixStrongStepAtERoot : TemplateRawProof :=
  trpAllE
    (coqCarrierStrongPrefixSuccessorGuardTemplate ::
      coqCarrierStrongPrefixKdUnderETemplate ::
      coqCarrierStrongPrefixCasePremiseContext)
    coqCarrierStrongPrefixStrongStepAllBodyTemplate
    (embedPATerm (tVar 0))
    coqCarrierStrongPrefixStrongStepAllRoot.

Definition coqCarrierStrongPrefixPredicateAtERoot : TemplateRawProof :=
  trpImpE
    (coqCarrierStrongPrefixSuccessorGuardTemplate ::
      coqCarrierStrongPrefixKdUnderETemplate ::
      coqCarrierStrongPrefixCasePremiseContext)
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate
    coqRestrictedPADerivationSoundnessCarrierPredicateTemplate
    coqCarrierStrongPrefixStrongStepAtERoot
    coqCarrierStrongPrefixKeRoot.

Definition coqCarrierStrongPrefixSuccessorBodyRoot : TemplateRawProof :=
  trpImpI
    (coqCarrierStrongPrefixKdUnderETemplate ::
      coqCarrierStrongPrefixCasePremiseContext)
    coqCarrierStrongPrefixSuccessorGuardTemplate
    coqRestrictedPADerivationSoundnessCarrierPredicateTemplate
    coqCarrierStrongPrefixPredicateAtERoot.

Definition coqCarrierStrongPrefixSuccessorPrefixRoot : TemplateRawProof :=
  trpAllI
    (coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate ::
      coqCarrierStrongPrefixCasePremiseContext)
    (tfImp coqCarrierStrongPrefixSuccessorGuardTemplate
      coqRestrictedPADerivationSoundnessCarrierPredicateTemplate)
    coqCarrierStrongPrefixSuccessorBodyRoot.

Definition coqCarrierStrongPrefixStepBodyRoot : TemplateRawProof :=
  trpImpI coqCarrierStrongPrefixCasePremiseContext
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixSuccessorTemplate
    coqCarrierStrongPrefixSuccessorPrefixRoot.

Definition coqCarrierStrongPrefixStepRoot : TemplateRawProof :=
  trpAllI coqCarrierStrongPrefixCasePremiseContext
    (tfImp
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixSuccessorTemplate)
    coqCarrierStrongPrefixStepBodyRoot.

(** Pair the two cases and discharge the three closed premises. *)
Definition coqCarrierStrongPrefixCasePairRoot : TemplateRawProof :=
  trpAndI coqCarrierStrongPrefixCasePremiseContext
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroTemplate
    coqCarrierStrongPrefixOrdinaryStepTemplate
    coqCarrierStrongPrefixZeroRoot
    coqCarrierStrongPrefixStepRoot.

Definition coqCarrierStrongPrefixCaseFromStrongStepRoot : TemplateRawProof :=
  trpImpI
    [coqCarrierStrongPrefixLtKernelTemplate;
     coqCarrierStrongPrefixNoLtZeroTemplate]
    coqRestrictedPADerivationSoundnessCarrierStrongStepTemplate
    (tfAnd
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroTemplate
      coqCarrierStrongPrefixOrdinaryStepTemplate)
    coqCarrierStrongPrefixCasePairRoot.

Definition coqCarrierStrongPrefixCaseFromLtKernelRoot : TemplateRawProof :=
  trpImpI [coqCarrierStrongPrefixNoLtZeroTemplate]
    coqCarrierStrongPrefixLtKernelTemplate
    (tfImp
      coqRestrictedPADerivationSoundnessCarrierStrongStepTemplate
      (tfAnd
        coqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroTemplate
        coqCarrierStrongPrefixOrdinaryStepTemplate))
    coqCarrierStrongPrefixCaseFromStrongStepRoot.

Definition coqCarrierStrongPrefixCaseCompilationRoot : TemplateRawProof :=
  trpImpI [] coqCarrierStrongPrefixNoLtZeroTemplate
    (tfImp coqCarrierStrongPrefixLtKernelTemplate
      (tfImp
        coqRestrictedPADerivationSoundnessCarrierStrongStepTemplate
        (tfAnd
          coqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroTemplate
          coqCarrierStrongPrefixOrdinaryStepTemplate)))
    coqCarrierStrongPrefixCaseFromLtKernelRoot.

Definition coqCarrierStrongPrefixCaseCompilationTemplate : TemplateFormula :=
  tfImp coqCarrierStrongPrefixNoLtZeroTemplate
    (tfImp coqCarrierStrongPrefixLtKernelTemplate
      (tfImp
        coqRestrictedPADerivationSoundnessCarrierStrongStepTemplate
        (tfAnd
          coqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroTemplate
          coqCarrierStrongPrefixOrdinaryStepTemplate))).

(** Small compositional rules keep validity checking linear in the finite
    proof tree.  Reducing the entire nested [TemplateRawProofValid] term in
    one computation duplicates its large structural formulae at every parent
    and is unnecessarily expensive. *)
Lemma coqCarrier_templateRawDerives_impI : forall
    context antecedent consequent child,
  TemplateRawDerives (antecedent :: context) consequent child ->
  TemplateRawDerives context (tfImp antecedent consequent)
    (trpImpI context antecedent consequent child).
Proof.
  intros context antecedent consequent child
    [hvalid [hcontext hconclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; try assumption; reflexivity.
Qed.

Lemma coqCarrier_templateRawDerives_impE : forall
    context antecedent consequent implicationChild antecedentChild,
  TemplateRawDerives context (tfImp antecedent consequent)
    implicationChild ->
  TemplateRawDerives context antecedent antecedentChild ->
  TemplateRawDerives context consequent
    (trpImpE context antecedent consequent
      implicationChild antecedentChild).
Proof.
  intros context antecedent consequent implicationChild antecedentChild
    [himpValid [himpContext himpConclusion]]
    [hantecedentValid [hantecedentContext hantecedentConclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; try assumption; reflexivity.
Qed.

Lemma coqCarrier_templateRawDerives_botE : forall
    context conclusion child,
  TemplateRawDerives context tfBot child ->
  TemplateRawDerives context conclusion
    (trpBotE context conclusion child).
Proof.
  intros context conclusion child [hvalid [hcontext hconclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; try assumption; reflexivity.
Qed.

Lemma coqCarrier_templateRawDerives_andI : forall
    context lhs rhs leftChild rightChild,
  TemplateRawDerives context lhs leftChild ->
  TemplateRawDerives context rhs rightChild ->
  TemplateRawDerives context (tfAnd lhs rhs)
    (trpAndI context lhs rhs leftChild rightChild).
Proof.
  intros context lhs rhs leftChild rightChild
    [hleftValid [hleftContext hleftConclusion]]
    [hrightValid [hrightContext hrightConclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; try assumption; reflexivity.
Qed.

Lemma coqCarrier_templateRawDerives_allI : forall context body child,
  TemplateRawDerives (templateContextShift context) body child ->
  TemplateRawDerives context (tfAll body)
    (trpAllI context body child).
Proof.
  intros context body child [hvalid [hcontext hconclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; try assumption; reflexivity.
Qed.

Lemma coqCarrier_templateRawDerives_allE : forall
    context body replacement child,
  TemplateRawDerives context (tfAll body) child ->
  TemplateRawDerives context (templateFormulaOpen replacement body)
    (trpAllE context body replacement child).
Proof.
  intros context body replacement child
    [hvalid [hcontext hconclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; try assumption; reflexivity.
Qed.

Lemma coqCarrierStrongPrefixCaseCompilationRoot_valid :
  TemplateRawDerives [] coqCarrierStrongPrefixCaseCompilationTemplate
    coqCarrierStrongPrefixCaseCompilationRoot.
Proof.
  (** Keep every intermediate judgement opaque to the next one.  Unfolding
      the whole proof tree at once asks conversion to duplicate the large
      carrier predicate at every parent and consumes gigabytes of memory. *)
  assert (hZeroArithmeticAll :
    TemplateRawDerives
      (coqCarrierStrongPrefixZeroGuardTemplate ::
        coqCarrierStrongPrefixCasePremiseContext)
      coqCarrierStrongPrefixNoLtZeroTemplate
      coqCarrierStrongPrefixZeroArithmeticAllRoot).
  {
    unfold coqCarrierStrongPrefixZeroArithmeticAllRoot.
    apply templateRawDerives_assumption.
    unfold coqCarrierStrongPrefixCasePremiseContext.
    do 3 apply in_cons. apply in_eq.
  }
  assert (hZeroArithmetic :
    TemplateRawDerives
      (coqCarrierStrongPrefixZeroGuardTemplate ::
        coqCarrierStrongPrefixCasePremiseContext)
      (tfImp coqCarrierStrongPrefixZeroGuardTemplate tfBot)
      coqCarrierStrongPrefixZeroArithmeticRoot).
  {
    unfold coqCarrierStrongPrefixZeroArithmeticRoot.
    rewrite <- coqCarrierStrongPrefixNoLtZeroInstanceTemplate_shape.
    apply coqCarrier_templateRawDerives_allE.
    rewrite <- coqCarrierStrongPrefixNoLtZeroTemplate_shape.
    exact hZeroArithmeticAll.
  }
  assert (hZeroGuard :
    TemplateRawDerives
      (coqCarrierStrongPrefixZeroGuardTemplate ::
        coqCarrierStrongPrefixCasePremiseContext)
      coqCarrierStrongPrefixZeroGuardTemplate
      coqCarrierStrongPrefixZeroGuardRoot).
  {
    unfold coqCarrierStrongPrefixZeroGuardRoot.
    apply templateRawDerives_assumption. apply in_eq.
  }
  assert (hZeroBottom :
    TemplateRawDerives
      (coqCarrierStrongPrefixZeroGuardTemplate ::
        coqCarrierStrongPrefixCasePremiseContext)
      tfBot coqCarrierStrongPrefixZeroBottomRoot).
  {
    unfold coqCarrierStrongPrefixZeroBottomRoot.
    now apply coqCarrier_templateRawDerives_impE.
  }
  assert (hZeroPredicate :
    TemplateRawDerives
      (coqCarrierStrongPrefixZeroGuardTemplate ::
        coqCarrierStrongPrefixCasePremiseContext)
      coqRestrictedPADerivationSoundnessCarrierPredicateTemplate
      coqCarrierStrongPrefixZeroPredicateRoot).
  {
    unfold coqCarrierStrongPrefixZeroPredicateRoot.
    now apply coqCarrier_templateRawDerives_botE.
  }
  assert (hZeroBody :
    TemplateRawDerives coqCarrierStrongPrefixCasePremiseContext
      coqCarrierStrongPrefixZeroBodyTemplate
      coqCarrierStrongPrefixZeroBodyRoot).
  {
    unfold coqCarrierStrongPrefixZeroBodyTemplate,
      coqCarrierStrongPrefixZeroBodyRoot.
    now apply coqCarrier_templateRawDerives_impI.
  }
  assert (hZero :
    TemplateRawDerives coqCarrierStrongPrefixCasePremiseContext
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroTemplate
      coqCarrierStrongPrefixZeroRoot).
  {
    unfold coqCarrierStrongPrefixZeroRoot.
    rewrite coqCarrierStrongPrefixZeroTemplate_shape.
    apply coqCarrier_templateRawDerives_allI.
    rewrite coqCarrierStrongPrefixCasePremiseContext_shift_closed.
    exact hZeroBody.
  }

  assert (hLtKernelAll :
    TemplateRawDerives coqCarrierStrongPrefixDeepContext
      coqCarrierStrongPrefixLtKernelTemplate
      coqCarrierStrongPrefixLtKernelAllRoot).
  {
    unfold coqCarrierStrongPrefixLtKernelAllRoot.
    apply templateRawDerives_assumption.
    unfold coqCarrierStrongPrefixDeepContext,
      coqCarrierStrongPrefixCasePremiseContext.
    do 4 apply in_cons. apply in_eq.
  }
  assert (hLtKernelAfterD :
    TemplateRawDerives coqCarrierStrongPrefixDeepContext
      coqCarrierStrongPrefixLtKernelAfterDTemplate
      coqCarrierStrongPrefixLtKernelAfterDRoot).
  {
    unfold coqCarrierStrongPrefixLtKernelAfterDRoot,
      coqCarrierStrongPrefixLtKernelAfterDTemplate.
    apply coqCarrier_templateRawDerives_allE.
    rewrite <- coqCarrierStrongPrefixLtKernelTemplate_shape.
    exact hLtKernelAll.
  }
  assert (hLtKernelAfterE :
    TemplateRawDerives coqCarrierStrongPrefixDeepContext
      coqCarrierStrongPrefixLtKernelAfterETemplate
      coqCarrierStrongPrefixLtKernelAfterERoot).
  {
    unfold coqCarrierStrongPrefixLtKernelAfterERoot,
      coqCarrierStrongPrefixLtKernelAfterETemplate.
    apply coqCarrier_templateRawDerives_allE.
    rewrite <- coqCarrierStrongPrefixLtKernelAfterDTemplate_shape.
    exact hLtKernelAfterD.
  }
  assert (hLtKernelInstance :
    TemplateRawDerives coqCarrierStrongPrefixDeepContext
      coqCarrierStrongPrefixLtKernelInstanceTemplate
      coqCarrierStrongPrefixLtKernelInstanceRoot).
  {
    unfold coqCarrierStrongPrefixLtKernelInstanceRoot,
      coqCarrierStrongPrefixLtKernelInstanceTemplate.
    apply coqCarrier_templateRawDerives_allE.
    rewrite <- coqCarrierStrongPrefixLtKernelAfterETemplate_shape.
    exact hLtKernelAfterE.
  }
  assert (hXLtE :
    TemplateRawDerives coqCarrierStrongPrefixDeepContext
      coqCarrierStrongPrefixXLtETemplate
      coqCarrierStrongPrefixXLtEAssumptionRoot).
  {
    unfold coqCarrierStrongPrefixXLtEAssumptionRoot.
    apply templateRawDerives_assumption.
    unfold coqCarrierStrongPrefixDeepContext. apply in_eq.
  }
  assert (hGuardShifted :
    TemplateRawDerives coqCarrierStrongPrefixDeepContext
      coqCarrierStrongPrefixSuccessorGuardShiftedTemplate
      coqCarrierStrongPrefixGuardShiftedAssumptionRoot).
  {
    unfold coqCarrierStrongPrefixGuardShiftedAssumptionRoot.
    apply templateRawDerives_assumption.
    unfold coqCarrierStrongPrefixDeepContext.
    apply in_cons. apply in_eq.
  }
  assert (hLtKernelAfterXLtE :
    TemplateRawDerives coqCarrierStrongPrefixDeepContext
      (tfImp coqCarrierStrongPrefixSuccessorGuardShiftedTemplate
        coqCarrierStrongPrefixXLtDTemplate)
      coqCarrierStrongPrefixLtKernelAfterXLtERoot).
  {
    unfold coqCarrierStrongPrefixLtKernelAfterXLtERoot.
    apply coqCarrier_templateRawDerives_impE.
    - change
        (TemplateRawDerives coqCarrierStrongPrefixDeepContext
          coqCarrierStrongPrefixLtKernelBodyTemplate
          coqCarrierStrongPrefixLtKernelInstanceRoot).
      rewrite <- coqCarrierStrongPrefixLtKernelInstanceTemplate_shape.
      exact hLtKernelInstance.
    - exact hXLtE.
  }
  assert (hXLtD :
    TemplateRawDerives coqCarrierStrongPrefixDeepContext
      coqCarrierStrongPrefixXLtDTemplate
      coqCarrierStrongPrefixXLtDRoot).
  {
    unfold coqCarrierStrongPrefixXLtDRoot.
    now apply coqCarrier_templateRawDerives_impE.
  }
  assert (hKdUnderX :
    TemplateRawDerives coqCarrierStrongPrefixDeepContext
      coqCarrierStrongPrefixKdUnderXTemplate
      coqCarrierStrongPrefixKdUnderXAssumptionRoot).
  {
    unfold coqCarrierStrongPrefixKdUnderXAssumptionRoot.
    apply templateRawDerives_assumption.
    unfold coqCarrierStrongPrefixDeepContext.
    do 2 apply in_cons. apply in_eq.
  }
  assert (hKdAtX :
    TemplateRawDerives coqCarrierStrongPrefixDeepContext
      (tfImp coqCarrierStrongPrefixXLtDTemplate
        coqRestrictedPADerivationSoundnessCarrierPredicateTemplate)
      coqCarrierStrongPrefixKdAtXRoot).
  {
    unfold coqCarrierStrongPrefixKdAtXRoot.
    rewrite <- coqCarrierStrongPrefixKdUnderX_open_shape.
    apply coqCarrier_templateRawDerives_allE.
    rewrite <- coqCarrierStrongPrefixKdUnderXTemplate_shape.
    exact hKdUnderX.
  }
  assert (hPredicateAtX :
    TemplateRawDerives coqCarrierStrongPrefixDeepContext
      coqRestrictedPADerivationSoundnessCarrierPredicateTemplate
      coqCarrierStrongPrefixPredicateAtXRoot).
  {
    unfold coqCarrierStrongPrefixPredicateAtXRoot.
    now apply coqCarrier_templateRawDerives_impE.
  }
  assert (hKeBody :
    TemplateRawDerives
      (coqCarrierStrongPrefixSuccessorGuardShiftedTemplate ::
       coqCarrierStrongPrefixKdUnderXTemplate ::
       coqCarrierStrongPrefixCasePremiseContext)
      coqCarrierStrongPrefixKeBodyTemplate
      coqCarrierStrongPrefixKeBodyRoot).
  {
    unfold coqCarrierStrongPrefixKeBodyTemplate,
      coqCarrierStrongPrefixKeBodyRoot.
    apply coqCarrier_templateRawDerives_impI.
    exact hPredicateAtX.
  }
  assert (hKe :
    TemplateRawDerives
      (coqCarrierStrongPrefixSuccessorGuardTemplate ::
       coqCarrierStrongPrefixKdUnderETemplate ::
       coqCarrierStrongPrefixCasePremiseContext)
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate
      coqCarrierStrongPrefixKeRoot).
  {
    unfold coqCarrierStrongPrefixKeRoot.
    rewrite coqCarrierStrongPrefixKeTemplate_shape.
    apply coqCarrier_templateRawDerives_allI.
    rewrite coqCarrierStrongPrefixKeAllContext_shift.
    exact hKeBody.
  }
  assert (hStrongStepAll :
    TemplateRawDerives
      (coqCarrierStrongPrefixSuccessorGuardTemplate ::
       coqCarrierStrongPrefixKdUnderETemplate ::
       coqCarrierStrongPrefixCasePremiseContext)
      coqRestrictedPADerivationSoundnessCarrierStrongStepTemplate
      coqCarrierStrongPrefixStrongStepAllRoot).
  {
    unfold coqCarrierStrongPrefixStrongStepAllRoot.
    apply templateRawDerives_assumption.
    unfold coqCarrierStrongPrefixCasePremiseContext.
    do 2 apply in_cons. apply in_eq.
  }
  assert (hStrongStepAtE :
    TemplateRawDerives
      (coqCarrierStrongPrefixSuccessorGuardTemplate ::
       coqCarrierStrongPrefixKdUnderETemplate ::
       coqCarrierStrongPrefixCasePremiseContext)
      (tfImp
        coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate
        coqRestrictedPADerivationSoundnessCarrierPredicateTemplate)
      coqCarrierStrongPrefixStrongStepAtERoot).
  {
    unfold coqCarrierStrongPrefixStrongStepAtERoot.
    rewrite <- coqCarrierStrongPrefixStrongStepAtETemplate_shape.
    unfold coqCarrierStrongPrefixStrongStepAtETemplate.
    apply coqCarrier_templateRawDerives_allE.
    rewrite <- coqCarrierStrongPrefixStrongStepTemplate_shape.
    exact hStrongStepAll.
  }
  assert (hPredicateAtE :
    TemplateRawDerives
      (coqCarrierStrongPrefixSuccessorGuardTemplate ::
       coqCarrierStrongPrefixKdUnderETemplate ::
       coqCarrierStrongPrefixCasePremiseContext)
      coqRestrictedPADerivationSoundnessCarrierPredicateTemplate
      coqCarrierStrongPrefixPredicateAtERoot).
  {
    unfold coqCarrierStrongPrefixPredicateAtERoot.
    now apply coqCarrier_templateRawDerives_impE.
  }
  assert (hSuccessorBody :
    TemplateRawDerives
      (coqCarrierStrongPrefixKdUnderETemplate ::
       coqCarrierStrongPrefixCasePremiseContext)
      (tfImp coqCarrierStrongPrefixSuccessorGuardTemplate
        coqRestrictedPADerivationSoundnessCarrierPredicateTemplate)
      coqCarrierStrongPrefixSuccessorBodyRoot).
  {
    unfold coqCarrierStrongPrefixSuccessorBodyRoot.
    now apply coqCarrier_templateRawDerives_impI.
  }
  assert (hSuccessorPrefix :
    TemplateRawDerives
      (coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate ::
       coqCarrierStrongPrefixCasePremiseContext)
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixSuccessorTemplate
      coqCarrierStrongPrefixSuccessorPrefixRoot).
  {
    unfold coqCarrierStrongPrefixSuccessorPrefixRoot.
    rewrite coqCarrierStrongPrefixSuccessorTemplate_shape.
    apply coqCarrier_templateRawDerives_allI.
    rewrite coqCarrierStrongPrefixSuccessorAllContext_shift.
    exact hSuccessorBody.
  }
  assert (hStepBody :
    TemplateRawDerives coqCarrierStrongPrefixCasePremiseContext
      (tfImp
        coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate
        coqRestrictedPADerivationSoundnessCarrierStrongPrefixSuccessorTemplate)
      coqCarrierStrongPrefixStepBodyRoot).
  {
    unfold coqCarrierStrongPrefixStepBodyRoot.
    now apply coqCarrier_templateRawDerives_impI.
  }
  assert (hStep :
    TemplateRawDerives coqCarrierStrongPrefixCasePremiseContext
      coqCarrierStrongPrefixOrdinaryStepTemplate
      coqCarrierStrongPrefixStepRoot).
  {
    unfold coqCarrierStrongPrefixOrdinaryStepTemplate,
      coqCarrierStrongPrefixStepRoot.
    apply coqCarrier_templateRawDerives_allI.
    rewrite coqCarrierStrongPrefixCasePremiseContext_shift_closed.
    exact hStepBody.
  }
  assert (hPair :
    TemplateRawDerives coqCarrierStrongPrefixCasePremiseContext
      (tfAnd
        coqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroTemplate
        coqCarrierStrongPrefixOrdinaryStepTemplate)
      coqCarrierStrongPrefixCasePairRoot).
  {
    unfold coqCarrierStrongPrefixCasePairRoot.
    now apply coqCarrier_templateRawDerives_andI.
  }
  assert (hFromStrongStep :
    TemplateRawDerives
      [coqCarrierStrongPrefixLtKernelTemplate;
       coqCarrierStrongPrefixNoLtZeroTemplate]
      (tfImp coqRestrictedPADerivationSoundnessCarrierStrongStepTemplate
        (tfAnd
          coqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroTemplate
          coqCarrierStrongPrefixOrdinaryStepTemplate))
      coqCarrierStrongPrefixCaseFromStrongStepRoot).
  {
    unfold coqCarrierStrongPrefixCaseFromStrongStepRoot.
    now apply coqCarrier_templateRawDerives_impI.
  }
  assert (hFromLtKernel :
    TemplateRawDerives [coqCarrierStrongPrefixNoLtZeroTemplate]
      (tfImp coqCarrierStrongPrefixLtKernelTemplate
        (tfImp coqRestrictedPADerivationSoundnessCarrierStrongStepTemplate
          (tfAnd
            coqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroTemplate
            coqCarrierStrongPrefixOrdinaryStepTemplate)))
      coqCarrierStrongPrefixCaseFromLtKernelRoot).
  {
    unfold coqCarrierStrongPrefixCaseFromLtKernelRoot.
    now apply coqCarrier_templateRawDerives_impI.
  }
  unfold coqCarrierStrongPrefixCaseCompilationTemplate,
    coqCarrierStrongPrefixCaseCompilationRoot.
  now apply coqCarrier_templateRawDerives_impI.
Qed.

(** ------------------------------------------------------------------
    Checked same-context specialization of the finite template. *)

Definition rawCoqCarrierStrongPrefixNoLtZeroCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawStructuralTemplateFormula inputs
    coqCarrierStrongPrefixNoLtZeroTemplate.

Definition rawCoqCarrierStrongPrefixLtKernelCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawStructuralTemplateFormula inputs
    coqCarrierStrongPrefixLtKernelTemplate.

Definition rawCoqCarrierStrongPrefixOrdinaryStepCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawStructuralTemplateFormula inputs
    coqCarrierStrongPrefixOrdinaryStepTemplate.

Definition rawCoqCarrierStrongPrefixCasePairCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawFormulaAndCode M
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllCode
      M inputs).

Arguments rawCoqCarrierStrongPrefixNoLtZeroCode M inputs
  : clear implicits.
Arguments rawCoqCarrierStrongPrefixLtKernelCode M inputs
  : clear implicits.
Arguments rawCoqCarrierStrongPrefixOrdinaryStepCode M inputs
  : clear implicits.
Arguments rawCoqCarrierStrongPrefixCasePairCode M inputs
  : clear implicits.

Lemma raw_coqCarrierStrongPrefixOrdinaryStepCode_view : forall
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M),
  rawCoqCarrierStrongPrefixOrdinaryStepCode M inputs =
  rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllCode
    M inputs.
Proof. reflexivity. Qed.

Definition rawCoqCarrierStrongPrefixCaseCompilationRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateStructuralInputs M) (context : M) : M :=
  rawTemplateProofCodeOnTail
    (rawStructuralTemplateTranslation M hPA inputs)
    context coqCarrierStrongPrefixCaseCompilationRoot.

Arguments rawCoqCarrierStrongPrefixCaseCompilationRoot
  M hPA inputs context : clear implicits.

Theorem raw_codedPALocalProofOf_coqCarrierStrongPrefixCaseCompilation :
    forall (M : RawPAModel) (hPA : RawPASatisfies M)
      (inputs : RawCodedTemplateStructuralInputs M)
      witnessList context,
  RawCodedPAAxiomWitnessContext M witnessList context ->
  RawCodedPALocalProofOf M context
    (rawStructuralTemplateFormula inputs
      coqCarrierStrongPrefixCaseCompilationTemplate)
    (rawCoqCarrierStrongPrefixCaseCompilationRoot
      M hPA inputs context).
Proof.
  intros M hPA inputs witnessList context hwitnessed.
  unfold rawCoqCarrierStrongPrefixCaseCompilationRoot.
  apply (raw_templateProofOnPAAxiomContext_localProof M hPA
    (rawStructuralTemplateTranslation M hPA inputs)
    witnessList context coqCarrierStrongPrefixCaseCompilationRoot).
  - exact hwitnessed.
  - exact (proj1 coqCarrierStrongPrefixCaseCompilationRoot_valid).
Qed.

(** Applying the compiled implication consumes only actual local proof
    roots in the same witnessed context.  It returns the exact two formulas
    expected by the closure-induction shell. *)
Theorem raw_codedPALocalProofOf_coqCarrierStrongPrefixCases_from_roots :
    forall (M : RawPAModel) (hPA : RawPASatisfies M)
      (inputs : RawCodedTemplateStructuralInputs M)
      witnessList context noLtZeroRoot ltKernelRoot strongStepRoot,
  RawCodedPAAxiomWitnessContext M witnessList context ->
  RawCodedPALocalProofOf M context
    (rawCoqCarrierStrongPrefixNoLtZeroCode M inputs) noLtZeroRoot ->
  RawCodedPALocalProofOf M context
    (rawCoqCarrierStrongPrefixLtKernelCode M inputs) ltKernelRoot ->
  RawCodedPALocalProofOf M context
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepCode M inputs)
    strongStepRoot ->
  exists zeroChild stepChild : M,
    RawCodedPALocalProofOf M context
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroCode
        M inputs) zeroChild /\
    RawCodedPALocalProofOf M context
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllCode
        M inputs) stepChild.
Proof.
  intros M hPA inputs witnessList context
    noLtZeroRoot ltKernelRoot strongStepRoot
    hwitnessed hnoZero hkernel hstrong.
  pose proof
    (raw_codedPALocalProofOf_coqCarrierStrongPrefixCaseCompilation
      M hPA inputs witnessList context hwitnessed) as hcompiled.
  unfold coqCarrierStrongPrefixCaseCompilationTemplate in hcompiled.
  cbn [rawStructuralTemplateFormula
    rawStructuralTemplateFormulaWith] in hcompiled.
  set (afterNoZero := rawProofImpERoot M context
    (rawCoqCarrierStrongPrefixNoLtZeroCode M inputs)
    (rawFormulaImpCode M
      (rawCoqCarrierStrongPrefixLtKernelCode M inputs)
      (rawFormulaImpCode M
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepCode M inputs)
        (rawCoqCarrierStrongPrefixCasePairCode M inputs)))
    (rawCoqCarrierStrongPrefixCaseCompilationRoot
      M hPA inputs context) noLtZeroRoot).
  assert (hafterNoZero : RawCodedPALocalProofOf M context
      (rawFormulaImpCode M
        (rawCoqCarrierStrongPrefixLtKernelCode M inputs)
        (rawFormulaImpCode M
          (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepCode
            M inputs)
          (rawCoqCarrierStrongPrefixCasePairCode M inputs)))
      afterNoZero).
  {
    apply (raw_codedPALocalProofOf_impE M hPA context
      (rawCoqCarrierStrongPrefixNoLtZeroCode M inputs)
      (rawFormulaImpCode M
        (rawCoqCarrierStrongPrefixLtKernelCode M inputs)
        (rawFormulaImpCode M
          (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepCode
            M inputs)
          (rawCoqCarrierStrongPrefixCasePairCode M inputs)))
      (rawCoqCarrierStrongPrefixCaseCompilationRoot
        M hPA inputs context) noLtZeroRoot).
    - exact hcompiled.
    - exact hnoZero.
  }
  set (afterKernel := rawProofImpERoot M context
    (rawCoqCarrierStrongPrefixLtKernelCode M inputs)
    (rawFormulaImpCode M
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepCode M inputs)
      (rawCoqCarrierStrongPrefixCasePairCode M inputs))
    afterNoZero ltKernelRoot).
  assert (hafterKernel : RawCodedPALocalProofOf M context
      (rawFormulaImpCode M
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepCode M inputs)
        (rawCoqCarrierStrongPrefixCasePairCode M inputs))
      afterKernel).
  {
    exact (raw_codedPALocalProofOf_impE M hPA context
      (rawCoqCarrierStrongPrefixLtKernelCode M inputs)
      (rawFormulaImpCode M
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepCode M inputs)
        (rawCoqCarrierStrongPrefixCasePairCode M inputs))
      afterNoZero ltKernelRoot hafterNoZero hkernel).
  }
  set (pairRoot := rawProofImpERoot M context
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepCode M inputs)
    (rawCoqCarrierStrongPrefixCasePairCode M inputs)
    afterKernel strongStepRoot).
  assert (hpair : RawCodedPALocalProofOf M context
      (rawCoqCarrierStrongPrefixCasePairCode M inputs) pairRoot).
  {
    exact (raw_codedPALocalProofOf_impE M hPA context
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepCode M inputs)
      (rawCoqCarrierStrongPrefixCasePairCode M inputs)
      afterKernel strongStepRoot hafterKernel hstrong).
  }
  exists
    (rawProofAndERoot M RawAndLeft context
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllCode
        M inputs) pairRoot),
    (rawProofAndERoot M RawAndRight context
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllCode
        M inputs) pairRoot).
  split.
  - exact (raw_codedPALocalProofOf_andE1 M hPA context
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllCode
        M inputs) pairRoot hpair).
  - exact (raw_codedPALocalProofOf_andE2 M hPA context
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroCode
        M inputs)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllCode
        M inputs) pairRoot hpair).
Qed.

(** ------------------------------------------------------------------
    Ordinary proof certificates for the arithmetic premises. *)

Theorem raw_codedPAProofOf_coqCarrierStrongPrefixNoLtZero : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateStructuralInputs M),
  exists certificate : M,
    RawCodedPAProofOf M
      (rawCoqCarrierStrongPrefixNoLtZeroCode M inputs) certificate.
Proof.
  intros M hPA inputs.
  destruct (raw_codedPAProofOf_of_BProv M hPA
    coqCarrierStrongPrefixNoLtZeroFormula
    coqCarrierStrongPrefixNoLtZero_bprov) as
    [certificate hcertificate].
  exists certificate.
  unfold rawCoqCarrierStrongPrefixNoLtZeroCode,
    coqCarrierStrongPrefixNoLtZeroTemplate.
  rewrite rawStructuralTemplateFormula_embedPA.
  rewrite rawQuotedFormulaCode_standard by exact hPA.
  exact hcertificate.
Qed.

Theorem raw_codedPAProofOf_coqCarrierStrongPrefixLtKernel : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateStructuralInputs M),
  exists certificate : M,
    RawCodedPAProofOf M
      (rawCoqCarrierStrongPrefixLtKernelCode M inputs) certificate.
Proof.
  intros M hPA inputs.
  destruct (raw_codedPAProofOf_of_BProv M hPA
    coqCarrierStrongPrefixLtKernelFormula
    coqCarrierStrongPrefixLtKernel_bprov) as
    [certificate hcertificate].
  exists certificate.
  unfold rawCoqCarrierStrongPrefixLtKernelCode,
    coqCarrierStrongPrefixLtKernelTemplate.
  rewrite rawStructuralTemplateFormula_embedPA.
  rewrite rawQuotedFormulaCode_standard by exact hPA.
  exact hcertificate.
Qed.

(** ------------------------------------------------------------------
    The honest growing-prefix endpoint. *)

Definition rawCoqCarrierStrongPrefixGrowingCaseWitnessList
    (M : RawPAModel) (prefix : StandardPAAxiomWitnessPrefix)
    (baseWitnessList : M) : M :=
  rawStandardPAAxiomWitnessPrefixWitnessListCode
    M prefix baseWitnessList.

Definition rawCoqCarrierStrongPrefixGrowingCaseContext
    (M : RawPAModel) (prefix : StandardPAAxiomWitnessPrefix)
    (baseContext : M) : M :=
  rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext.

Arguments rawCoqCarrierStrongPrefixGrowingCaseWitnessList
  M prefix baseWitnessList : clear implicits.
Arguments rawCoqCarrierStrongPrefixGrowingCaseContext
  M prefix baseContext : clear implicits.

Lemma raw_contextListIncluded_coqCarrierStrongPrefixGrowingCase_base :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (prefix : StandardPAAxiomWitnessPrefix) baseContext,
  RawContextListIncluded M baseContext
    (rawCoqCarrierStrongPrefixGrowingCaseContext
      M prefix baseContext).
Proof.
  intros M hPA prefix.
  induction prefix as [| witness tail ih]; intro baseContext.
  - exact (raw_contextListIncluded_refl M baseContext).
  - cbn [rawCoqCarrierStrongPrefixGrowingCaseContext
      rawStandardPAAxiomWitnessPrefixContextCode].
    exact (raw_contextListIncluded_cons_target M hPA
      baseContext
      (rawStandardPAAxiomWitnessPrefixContextCode M tail baseContext)
      (rawQuotedFormulaCode M (witnessedAxiom witness))
      (ih baseContext)).
Qed.

(** Every root exposed by this package has a literal context.  A later
    growing finalizer may use [growingWitnessList/growingContext] as its new
    base and prepend another standard arithmetic prefix without recovering
    any hidden certificate fields. *)
Definition RawCoqCarrierStrongPrefixGrowingCasePackageOf
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    (baseWitnessList baseContext axiom : M)
    (prefix : StandardPAAxiomWitnessPrefix)
    (noLtZeroBaseRoot ltKernelBaseRoot prefixedStrongStepRoot
      noLtZeroExtendedRoot ltKernelExtendedRoot zeroChild stepChild : M)
    : Prop :=
  let growingWitnessList :=
    rawCoqCarrierStrongPrefixGrowingCaseWitnessList
      M prefix baseWitnessList in
  let growingContext :=
    rawCoqCarrierStrongPrefixGrowingCaseContext
      M prefix baseContext in
  let extendedWitnessList :=
    rawPAInductionExtendedWitnessList M growingWitnessList
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode
        M inputs) in
  let extendedContext :=
    rawPAInductionExtendedContext M growingContext axiom in
  RawCodedPAAxiomWitnessContext M growingWitnessList growingContext /\
  RawCodedPALocalProofOf M growingContext
    (rawCoqCarrierStrongPrefixNoLtZeroCode M inputs)
    noLtZeroBaseRoot /\
  RawCodedPALocalProofOf M growingContext
    (rawCoqCarrierStrongPrefixLtKernelCode M inputs)
    ltKernelBaseRoot /\
  RawCodedPAAxiomWitnessContext M extendedWitnessList extendedContext /\
  RawCodedPALocalProofOf M extendedContext
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepCode M inputs)
    prefixedStrongStepRoot /\
  RawCodedPALocalProofOf M extendedContext
    (rawCoqCarrierStrongPrefixNoLtZeroCode M inputs)
    noLtZeroExtendedRoot /\
  RawCodedPALocalProofOf M extendedContext
    (rawCoqCarrierStrongPrefixLtKernelCode M inputs)
    ltKernelExtendedRoot /\
  RawCodedPALocalProofOf M extendedContext
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroCode
      M inputs) zeroChild /\
  RawCodedPALocalProofOf M extendedContext
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllCode
      M inputs) stepChild.

Arguments RawCoqCarrierStrongPrefixGrowingCasePackageOf
  M inputs baseWitnessList baseContext axiom prefix
  noLtZeroBaseRoot ltKernelBaseRoot prefixedStrongStepRoot
  noLtZeroExtendedRoot ltKernelExtendedRoot zeroChild stepChild
  : clear implicits.

(** Unlike the shell's rigid case compiler, this theorem is unconditional.
    The selected [prefix] contains exactly the finitely many standard PA
    axioms used by the conjunction of the two arithmetic kernels. *)
Theorem raw_coqCarrierStrongPrefixGrowingCasePackage : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateStructuralInputs M)
    replacement axiom closureCount baseWitnessList baseContext
    strongStepRoot,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCoqRestrictedPADerivationSoundnessStrongPrefixClosureRemainder
    M inputs replacement axiom closureCount ->
  RawCodedPALocalProofOf M
    (rawPAInductionExtendedContext M baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepCode M inputs)
    strongStepRoot ->
  exists (prefix : StandardPAAxiomWitnessPrefix)
      (noLtZeroBaseRoot ltKernelBaseRoot prefixedStrongStepRoot
        noLtZeroExtendedRoot ltKernelExtendedRoot zeroChild stepChild : M),
    RawCoqCarrierStrongPrefixGrowingCasePackageOf
      M inputs baseWitnessList baseContext axiom prefix
      noLtZeroBaseRoot ltKernelBaseRoot prefixedStrongStepRoot
      noLtZeroExtendedRoot ltKernelExtendedRoot zeroChild stepChild.
Proof.
  intros M hPA inputs replacement axiom closureCount
    baseWitnessList baseContext strongStepRoot
    hbase hremainder hstrongStep.

  (* Compile both closed arithmetic kernels at once.  This selects one
     finite standard prefix and, importantly, keeps its literal list shape. *)
  destruct
    (raw_codedTemplatePALocalProofOf_of_BProv_on_witnessed_tail
      M hPA (rawStructuralTemplateTranslation M hPA inputs)
      (rawStructuralTemplatePAAgreement M hPA inputs)
      baseWitnessList baseContext
      coqCarrierStrongPrefixCaseArithmeticFormula
      hbase coqCarrierStrongPrefixCaseArithmetic_bprov)
    as (prefix & arithmeticPairRoot & hprefixed & harithmeticPair).
  change (RawCodedPALocalProofOf M
    (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
    (rawFormulaAndCode M
      (rawCoqCarrierStrongPrefixNoLtZeroCode M inputs)
      (rawCoqCarrierStrongPrefixLtKernelCode M inputs))
    arithmeticPairRoot) in harithmeticPair.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA
    (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
    (rawCoqCarrierStrongPrefixNoLtZeroCode M inputs)
    (rawCoqCarrierStrongPrefixLtKernelCode M inputs)
    arithmeticPairRoot harithmeticPair) as hnoLtZeroBase.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA
    (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
    (rawCoqCarrierStrongPrefixNoLtZeroCode M inputs)
    (rawCoqCarrierStrongPrefixLtKernelCode M inputs)
    arithmeticPairRoot harithmeticPair) as hltKernelBase.
  set (noLtZeroBaseRoot := rawProofAndERoot M RawAndLeft
    (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
    (rawCoqCarrierStrongPrefixNoLtZeroCode M inputs)
    (rawCoqCarrierStrongPrefixLtKernelCode M inputs)
    arithmeticPairRoot) in hnoLtZeroBase |- *.
  set (ltKernelBaseRoot := rawProofAndERoot M RawAndRight
    (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
    (rawCoqCarrierStrongPrefixNoLtZeroCode M inputs)
    (rawCoqCarrierStrongPrefixLtKernelCode M inputs)
    arithmeticPairRoot) in hltKernelBase |- *.

  (* The closure remainder fixes one genuine induction axiom.  Adjoin that
     same axiom above both the original and the enlarged arithmetic base. *)
  pose proof
    (raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixClosureInductionData
      M hPA inputs replacement axiom closureCount hremainder) as hdata.
  pose proof (raw_codedPAClosureInductionData_axiom M
    replacement
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode M inputs)
    axiom
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixShiftedCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixSuccessorCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixAllCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepImpCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixStepAllCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixPremiseCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyCode
      M inputs)
    closureCount hdata) as hinduction.
  pose proof (raw_codedPAAxiomWitnessContext_add_induction M hPA
    baseWitnessList baseContext
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode M inputs)
    axiom hbase hinduction) as hbaseExtended.
  pose proof (raw_codedPAAxiomWitnessContext_add_induction M hPA
    (rawCoqCarrierStrongPrefixGrowingCaseWitnessList
      M prefix baseWitnessList)
    (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode M inputs)
    axiom hprefixed hinduction) as hprefixedExtended.

  pose proof (raw_codedPAAxiomWitnessContext_context_realizable M
    baseWitnessList baseContext hbase) as hbaseRealizable.
  pose proof (raw_codedPAAxiomWitnessContext_context_realizable M
    (rawCoqCarrierStrongPrefixGrowingCaseWitnessList
      M prefix baseWitnessList)
    (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
    hprefixed) as hprefixedRealizable.
  assert (hextendedInclusion : RawContextListIncluded M
      (rawPAInductionExtendedContext M baseContext axiom)
      (rawPAInductionExtendedContext M
        (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
        axiom)).
  {
    unfold rawPAInductionExtendedContext.
    exact (raw_contextListIncluded_cons M hPA
      baseContext
      (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
      axiom axiom hbaseRealizable hprefixedRealizable eq_refl
      (raw_contextListIncluded_coqCarrierStrongPrefixGrowingCase_base
        M hPA prefix baseContext)).
  }
  destruct
    (raw_codedPALocalProofWitnessedContextInclusionWeakening_complete
      M hPA
      (rawPAInductionExtendedWitnessList M baseWitnessList
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode
          M inputs))
      (rawPAInductionExtendedContext M baseContext axiom)
      (rawPAInductionExtendedWitnessList M
        (rawCoqCarrierStrongPrefixGrowingCaseWitnessList
          M prefix baseWitnessList)
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode
          M inputs))
      (rawPAInductionExtendedContext M
        (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
        axiom)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepCode M inputs)
      strongStepRoot hbaseExtended hprefixedExtended
      hextendedInclusion hstrongStep) as
    [prefixedStrongStepRoot hprefixedStrongStep].

  assert (harithmeticExtendedInclusion : RawContextListIncluded M
      (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
      (rawPAInductionExtendedContext M
        (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
        axiom)).
  {
    unfold rawPAInductionExtendedContext.
    exact (raw_contextListIncluded_cons_target M hPA
      (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
      (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
      axiom
      (raw_contextListIncluded_refl M
        (rawCoqCarrierStrongPrefixGrowingCaseContext
          M prefix baseContext))).
  }
  destruct
    (raw_codedPALocalProofWitnessedContextInclusionWeakening_complete
      M hPA
      (rawCoqCarrierStrongPrefixGrowingCaseWitnessList
        M prefix baseWitnessList)
      (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
      (rawPAInductionExtendedWitnessList M
        (rawCoqCarrierStrongPrefixGrowingCaseWitnessList
          M prefix baseWitnessList)
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode
          M inputs))
      (rawPAInductionExtendedContext M
        (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
        axiom)
      (rawCoqCarrierStrongPrefixNoLtZeroCode M inputs)
      noLtZeroBaseRoot hprefixed hprefixedExtended
      harithmeticExtendedInclusion hnoLtZeroBase) as
    [noLtZeroExtendedRoot hnoLtZeroExtended].
  destruct
    (raw_codedPALocalProofWitnessedContextInclusionWeakening_complete
      M hPA
      (rawCoqCarrierStrongPrefixGrowingCaseWitnessList
        M prefix baseWitnessList)
      (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
      (rawPAInductionExtendedWitnessList M
        (rawCoqCarrierStrongPrefixGrowingCaseWitnessList
          M prefix baseWitnessList)
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode
          M inputs))
      (rawPAInductionExtendedContext M
        (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
        axiom)
      (rawCoqCarrierStrongPrefixLtKernelCode M inputs)
      ltKernelBaseRoot hprefixed hprefixedExtended
      harithmeticExtendedInclusion hltKernelBase) as
    [ltKernelExtendedRoot hltKernelExtended].

  destruct
    (raw_codedPALocalProofOf_coqCarrierStrongPrefixCases_from_roots
      M hPA inputs
      (rawPAInductionExtendedWitnessList M
        (rawCoqCarrierStrongPrefixGrowingCaseWitnessList
          M prefix baseWitnessList)
        (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixCode
          M inputs))
      (rawPAInductionExtendedContext M
        (rawCoqCarrierStrongPrefixGrowingCaseContext M prefix baseContext)
        axiom)
      noLtZeroExtendedRoot ltKernelExtendedRoot prefixedStrongStepRoot
      hprefixedExtended hnoLtZeroExtended hltKernelExtended
      hprefixedStrongStep) as
    (zeroChild & stepChild & hzero & hstep).
  exists prefix, noLtZeroBaseRoot, ltKernelBaseRoot,
    prefixedStrongStepRoot, noLtZeroExtendedRoot,
    ltKernelExtendedRoot, zeroChild, stepChild.
  unfold RawCoqCarrierStrongPrefixGrowingCasePackageOf.
  split.
  - exact hprefixed.
  - split.
    + exact hnoLtZeroBase.
    + split.
      * exact hltKernelBase.
      * split.
        -- exact hprefixedExtended.
        -- split.
           ++ exact hprefixedStrongStep.
           ++ split.
              ** exact hnoLtZeroExtended.
              ** split.
                 --- exact hltKernelExtended.
                 --- split.
                     +++ exact hzero.
                     +++ exact hstep.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixGrowingCaseCompilation.
