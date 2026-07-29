(**
  Ordinary deep closure for the direct strong-prefix soundness body.

  The direct template translator permits genuinely nonstandard formula codes
  at opaque leaves, so its finite, standard-depth operation fields do not by
  themselves establish closure at arbitrary carrier-valued cutoffs.  The
  finite scoping judgment and term identities developed for the diagonal
  frontier do supply exactly what is needed for transparent equality atoms.
  Ordinary formula-operation compositionality then propagates those identities
  through every connective and binder.

  Unlike the stronger diagonal theorem, this argument needs only ordinary
  deep closure at opaque leaves.  Its substitution traces may use unrelated
  internal traversal tables at different depths.  That is sufficient for the
  ordinary universal-closure invariant and avoids the shared-table diagonal
  callback entirely.
*)

From Stdlib Require Import List Arith.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedTermEvaluationRealization
  RawCodedFormulaRankTotality
  RawCodedFormulaShiftSubstitutionInterchange
  RawCodedFormulaSubstitutionAtomInterchange
  RawCodedFixedLevelTruthTotality
  RawCodedDynamicTruthPairedSuccessorAdequacy
  RawCodedDynamicTruthTemplateDirectInputs
  RawCodedDynamicTruthGlobalSuccessorDeepClosure
  RawCodedTemplateSyntax
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateNumeralParameters
  RawCodedTemplateTernaryApplication
  RawCodedTernaryPredicateDeepClosure
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell
  RawCodedFormulaBoundAllCarrierBoundary
  RawCodedUniversalClosureOrdinarySubstitution
  RawCodedRestrictedPADerivationSoundnessDirectDiagonalClosure.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrdinaryClosure.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTermEvaluationRealization.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedFormulaShiftSubstitutionInterchange.
Import PABoundedRawCodedFormulaSubstitutionAtomInterchange.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedDynamicTruthPairedSuccessorAdequacy.
Import PABoundedRawCodedDynamicTruthTemplateDirectInputs.
Import PABoundedRawCodedDynamicTruthGlobalSuccessorDeepClosure.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTernaryPredicateDeepClosure.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.
Import PABoundedRawCodedFormulaBoundAllCarrierBoundary.
Import PABoundedRawCodedUniversalClosureOrdinarySubstitution.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectDiagonalClosure.

(** Bottom is deeply closed from every carrier root.  Keeping this one-node
    case explicit is useful both for the transparent [tfBot] constructor and
    for malformed opaque names/arities in concrete selector dispatch. *)
Lemma raw_formulaBotCode_deep_closed_from : forall
    (M : RawPAModel), RawPASatisfies M -> forall root,
  RawCodedFormulaDeepClosedFrom M root (rawFormulaBotCode M).
Proof.
  intros M hPA root.
  split.
  - exact (raw_formulaBotCode_atomically_adequate M hPA).
  - split.
    + intros cutoff amount _.
      exact (raw_codedFormulaShift_bottom M hPA cutoff amount).
    + intros replacement assignmentCode assignmentStep depth _ _.
      exact (raw_codedFormulaSubstitution_bottom
        M hPA replacement depth).
Qed.

(** Structural ordinary closure of an arbitrary scoped direct template.
    Equality atoms are the only transparent case that is not already covered
    by a formula-level constructor lemma.  Their two term payloads are fixed
    at every carrier cutoff/depth by the scoped term identities. *)
Theorem raw_coqRestrictedPADirectTemplateFormula_deep_closed_from_scope :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (parameters : RawCodedTemplateNumeralParameters M)
      (contextTruth conclusionTruth :
        RawCoqRestrictedPATruthDirectSelector M parameters)
      scope input,
  RawCoqRestrictedPAOpaqueDeepClosedFromTemplateScopes M
    (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth) ->
  CoqRestrictedPATemplateFormulaScoped scope input ->
  RawCodedFormulaDeepClosedFrom M (rawNumeralValue M scope)
    (rawDirectTemplateFormula
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth)
      input).
Proof.
  intros M hPA parameters contextTruth conclusionTruth scope input
    hopaque.
  revert scope.
  induction input as
      [left right | | left IHleft right IHright
      | left IHleft right IHright | left IHleft right IHright
      | body IHbody | body IHbody | predicate arguments];
    intros scope hscoped;
    cbn [CoqRestrictedPATemplateFormulaScoped rawDirectTemplateFormula
      rawStructuralTemplateFormulaWith] in *.
  - destruct hscoped as [hleft hright].
    split.
    + change (RawCodedFormulaAtomicallyAdequate M
        (rawDirectTemplateFormula
          (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
            M hPA parameters contextTruth conclusionTruth)
          (tfEq left right))).
      exact (rawDirectTemplateFormula_atomically_adequate M hPA _ _).
    + split.
      * intros cutoff amount hcutoff.
        change (RawCodedFormulaShift M cutoff amount
          (rawFormulaEqCode M
            (rawStructuralTemplateTermWith M
              (rawCoqRestrictedPADerivationSoundnessTemplateSymbols
                M parameters contextTruth conclusionTruth) left)
            (rawStructuralTemplateTermWith M
              (rawCoqRestrictedPADerivationSoundnessTemplateSymbols
                M parameters contextTruth conclusionTruth) right))
          (rawFormulaEqCode M
            (rawStructuralTemplateTermWith M
              (rawCoqRestrictedPADerivationSoundnessTemplateSymbols
                M parameters contextTruth conclusionTruth) left)
            (rawStructuralTemplateTermWith M
              (rawCoqRestrictedPADerivationSoundnessTemplateSymbols
                M parameters contextTruth conclusionTruth) right))).
        rewrite !rawCoqRestrictedPADerivationSoundnessTemplateTerm_symbols.
        apply (raw_codedFormulaShift_eq_of_term_shifts M hPA).
        -- exact
             (raw_coqRestrictedPATemplateTerm_shift_identity_from_scope
               M hPA parameters scope cutoff amount left
               hleft hcutoff).
        -- exact
             (raw_coqRestrictedPATemplateTerm_shift_identity_from_scope
               M hPA parameters scope cutoff amount right
               hright hcutoff).
      * intros replacement assignmentCode assignmentStep depth
          hreplacement hdepth.
        change (RawCodedFormulaOperation M
          (RawCodedFormulaSubstitutionAtom M) replacement depth
          (rawFormulaEqCode M
            (rawStructuralTemplateTermWith M
              (rawCoqRestrictedPADerivationSoundnessTemplateSymbols
                M parameters contextTruth conclusionTruth) left)
            (rawStructuralTemplateTermWith M
              (rawCoqRestrictedPADerivationSoundnessTemplateSymbols
                M parameters contextTruth conclusionTruth) right))
          (rawFormulaEqCode M
            (rawStructuralTemplateTermWith M
              (rawCoqRestrictedPADerivationSoundnessTemplateSymbols
                M parameters contextTruth conclusionTruth) left)
            (rawStructuralTemplateTermWith M
              (rawCoqRestrictedPADerivationSoundnessTemplateSymbols
                M parameters contextTruth conclusionTruth) right))).
        rewrite !rawCoqRestrictedPADerivationSoundnessTemplateTerm_symbols.
        apply (raw_codedFormulaSubstitution_eq_of_term_atoms M hPA).
        -- exact
             (raw_coqRestrictedPATemplateTerm_substitution_identity_from_scope
               M hPA parameters replacement assignmentCode assignmentStep
               scope depth left hreplacement hleft hdepth).
        -- exact
             (raw_coqRestrictedPATemplateTerm_substitution_identity_from_scope
               M hPA parameters replacement assignmentCode assignmentStep
               scope depth right hreplacement hright hdepth).
  - exact (raw_formulaBotCode_deep_closed_from
      M hPA (rawNumeralValue M scope)).
  - destruct hscoped as [hleft hright].
    apply (rawFormulaImpCode_deep_closed_from M hPA).
    + exact (IHleft scope hleft).
    + exact (IHright scope hright).
  - destruct hscoped as [hleft hright].
    apply (rawFormulaAndCode_deep_closed_from M hPA).
    + exact (IHleft scope hleft).
    + exact (IHright scope hright).
  - destruct hscoped as [hleft hright].
    apply (rawFormulaOrCode_deep_closed_from M hPA).
    + exact (IHleft scope hleft).
    + exact (IHright scope hright).
  - apply (rawFormulaAllCode_deep_closed_from M hPA).
    change (RawCodedFormulaDeepClosedFrom M
      (rawNumeralValue M (S scope))
      (rawDirectTemplateFormula
        (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
          M hPA parameters contextTruth conclusionTruth) body)).
    exact (IHbody (S scope) hscoped).
  - apply (rawFormulaExCode_deep_closed_from M hPA).
    change (RawCodedFormulaDeepClosedFrom M
      (rawNumeralValue M (S scope))
      (rawDirectTemplateFormula
        (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
          M hPA parameters contextTruth conclusionTruth) body)).
    exact (IHbody (S scope) hscoped).
  - exact (hopaque scope predicate arguments hscoped).
Qed.

(** Concrete discharge of the opaque callback from the two ternary
    predicates used by the native truth construction.  The exact leaf
    equations deliberately form part of the hypotheses: they are the
    auditable bridge tying the abstract five-argument direct selectors to
    their underlying ternary applications.  All other predicate names and
    every arity other than five reduce definitionally to bottom. *)
Theorem
    raw_coqRestrictedPAOpaqueDeepClosedFromTemplateScopes_of_ternary_leaf_equations :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (parameters : RawCodedTemplateNumeralParameters M)
      (contextTruth conclusionTruth :
        RawCoqRestrictedPATruthDirectSelector M parameters)
      contextPredicate conclusionPredicate
      (contextApplicationSelector :
        RawCodedTernaryApplicationSelector M contextPredicate)
      (conclusionApplicationSelector :
        RawCodedTernaryApplicationSelector M conclusionPredicate),
  RawCodedTernaryPredicateDeepClosed M contextPredicate ->
  RawCodedTernaryPredicateDeepClosed M conclusionPredicate ->
  (forall first second third fourth fifth,
    rawDirectTemplateFormula
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth)
      (tfOpaque coqRestrictedPAContextTruthPredicateName
        [first; second; third; fourth; fifth]) =
    rawTernaryApplicationOutput contextApplicationSelector
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fifth)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fourth)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters third)) ->
  (forall first second third fourth fifth,
    rawDirectTemplateFormula
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth)
      (tfOpaque coqRestrictedPAConclusionTruthPredicateName
        [first; second; third; fourth; fifth]) =
    rawTernaryApplicationOutput conclusionApplicationSelector
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters third)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fourth)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fifth)) ->
  RawCoqRestrictedPAOpaqueDeepClosedFromTemplateScopes M
    (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth).
Proof.
  intros M hPA parameters contextTruth conclusionTruth
    contextPredicate conclusionPredicate
    contextApplicationSelector conclusionApplicationSelector
    hcontextDeep hconclusionDeep hcontextLeaf hconclusionLeaf
    scope [|[|predicate]] arguments hscoped.
  - destruct arguments as
      [|first [|second [|third [|fourth [|fifth [|sixth rest]]]]]].
    all: try
      (change (RawCodedFormulaDeepClosedFrom M (rawNumeralValue M scope)
        (rawFormulaBotCode M));
       exact (raw_formulaBotCode_deep_closed_from
         M hPA (rawNumeralValue M scope))).
    cbn [CoqRestrictedPATemplateTermsScoped] in hscoped.
    destruct hscoped as
      [hfirst [hsecond [hthird [hfourth [hfifth _]]]]].
    change (RawCodedFormulaDeepClosedFrom M (rawNumeralValue M scope)
      (rawDirectTemplateFormula
        (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
          M hPA parameters contextTruth conclusionTruth)
        (tfOpaque coqRestrictedPAContextTruthPredicateName
          [first; second; third; fourth; fifth]))).
    rewrite (hcontextLeaf first second third fourth fifth).
    exact
      (raw_coqRestrictedPATernaryApplication_deep_closed_from_template_scope
        M hPA parameters scope contextPredicate contextApplicationSelector
        fifth fourth third hcontextDeep hfifth hfourth hthird).
  - destruct arguments as
      [|first [|second [|third [|fourth [|fifth [|sixth rest]]]]]].
    all: try
      (change (RawCodedFormulaDeepClosedFrom M (rawNumeralValue M scope)
        (rawFormulaBotCode M));
       exact (raw_formulaBotCode_deep_closed_from
         M hPA (rawNumeralValue M scope))).
    cbn [CoqRestrictedPATemplateTermsScoped] in hscoped.
    destruct hscoped as
      [hfirst [hsecond [hthird [hfourth [hfifth _]]]]].
    change (RawCodedFormulaDeepClosedFrom M (rawNumeralValue M scope)
      (rawDirectTemplateFormula
        (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
          M hPA parameters contextTruth conclusionTruth)
        (tfOpaque coqRestrictedPAConclusionTruthPredicateName
          [first; second; third; fourth; fifth]))).
    rewrite (hconclusionLeaf first second third fourth fifth).
    exact
      (raw_coqRestrictedPATernaryApplication_deep_closed_from_template_scope
        M hPA parameters scope conclusionPredicate
        conclusionApplicationSelector third fourth fifth
        hconclusionDeep hthird hfourth hfifth).
  - change (RawCodedFormulaDeepClosedFrom M (rawNumeralValue M scope)
      (rawFormulaBotCode M)).
    exact (raw_formulaBotCode_deep_closed_from
      M hPA (rawNumeralValue M scope)).
Qed.

(** The complete induction body is closed at its root.  The scope proof is
    computed only for the finite metatheoretic template; no carrier value is
    reduced or decoded. *)
Lemma
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyTemplate_scoped :
  CoqRestrictedPATemplateFormulaScoped 0
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyTemplate.
Proof.
  apply (proj1 (coqRestrictedPATemplateFormulaScopedBool_iff 0 _)).
  vm_compute. reflexivity.
Qed.

Theorem
    raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirect_deep_closed_of_opaque_deep :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (parameters : RawCodedTemplateNumeralParameters M)
      (contextTruth conclusionTruth :
        RawCoqRestrictedPATruthDirectSelector M parameters),
  RawCoqRestrictedPAOpaqueDeepClosedFromTemplateScopes M
    (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth) ->
  RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 0)
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode
      M
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth)).
Proof.
  intros M hPA parameters contextTruth conclusionTruth hopaque.
  rewrite
    raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode_view.
  exact
    (raw_coqRestrictedPADirectTemplateFormula_deep_closed_from_scope
      M hPA parameters contextTruth conclusionTruth 0
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyTemplate
      hopaque
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyTemplate_scoped).
Qed.

(** Project the substitution half of deep closure at every depth.  The only
    use of the replacement's represented syntax is the explicit realizability
    witness accepted by [RawCodedFormulaDeepOperationallyClosedFrom]. *)
Corollary
    raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirect_substitution_identity_of_opaque_deep :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (parameters : RawCodedTemplateNumeralParameters M)
      (contextTruth conclusionTruth :
        RawCoqRestrictedPATruthDirectSelector M parameters)
      replacement assignmentCode assignmentStep,
  RawTermSyntaxRealizable M replacement assignmentCode assignmentStep ->
  RawCoqRestrictedPAOpaqueDeepClosedFromTemplateScopes M
    (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth) ->
  RawCodedFormulaSubstitutionIdentityAtAllDepths M replacement
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode
      M
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth)).
Proof.
  intros M hPA parameters contextTruth conclusionTruth
    replacement assignmentCode assignmentStep hreplacement hopaque depth.
  pose proof
    (raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirect_deep_closed_of_opaque_deep
      M hPA parameters contextTruth conclusionTruth hopaque) as hdeep.
  exact ((proj2 (proj2 hdeep)) replacement assignmentCode assignmentStep
    depth hreplacement (raw_rank_zero_le M hPA depth)).
Qed.

(** End-to-end ordinary identity for the two native-style ternary leaves.
    This packages the exact leaf equations with their deep predicate facts,
    while remaining independent of how a particular native trace chooses the
    selectors. *)
Corollary
    raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirect_substitution_identity_of_ternary_leaf_equations :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (parameters : RawCodedTemplateNumeralParameters M)
      (contextTruth conclusionTruth :
        RawCoqRestrictedPATruthDirectSelector M parameters)
      contextPredicate conclusionPredicate
      (contextApplicationSelector :
        RawCodedTernaryApplicationSelector M contextPredicate)
      (conclusionApplicationSelector :
        RawCodedTernaryApplicationSelector M conclusionPredicate)
      replacement assignmentCode assignmentStep,
  RawTermSyntaxRealizable M replacement assignmentCode assignmentStep ->
  RawCodedTernaryPredicateDeepClosed M contextPredicate ->
  RawCodedTernaryPredicateDeepClosed M conclusionPredicate ->
  (forall first second third fourth fifth,
    rawDirectTemplateFormula
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth)
      (tfOpaque coqRestrictedPAContextTruthPredicateName
        [first; second; third; fourth; fifth]) =
    rawTernaryApplicationOutput contextApplicationSelector
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fifth)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fourth)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters third)) ->
  (forall first second third fourth fifth,
    rawDirectTemplateFormula
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth)
      (tfOpaque coqRestrictedPAConclusionTruthPredicateName
        [first; second; third; fourth; fifth]) =
    rawTernaryApplicationOutput conclusionApplicationSelector
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters third)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fourth)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fifth)) ->
  RawCodedFormulaSubstitutionIdentityAtAllDepths M replacement
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode
      M
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth)).
Proof.
  intros M hPA parameters contextTruth conclusionTruth
    contextPredicate conclusionPredicate
    contextApplicationSelector conclusionApplicationSelector
    replacement assignmentCode assignmentStep hreplacement
    hcontextDeep hconclusionDeep hcontextLeaf hconclusionLeaf.
  apply
    (raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirect_substitution_identity_of_opaque_deep
      M hPA parameters contextTruth conclusionTruth
      replacement assignmentCode assignmentStep hreplacement).
  exact
    (raw_coqRestrictedPAOpaqueDeepClosedFromTemplateScopes_of_ternary_leaf_equations
      M hPA parameters contextTruth conclusionTruth
      contextPredicate conclusionPredicate
      contextApplicationSelector conclusionApplicationSelector
      hcontextDeep hconclusionDeep hcontextLeaf hconclusionLeaf).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrdinaryClosure.
