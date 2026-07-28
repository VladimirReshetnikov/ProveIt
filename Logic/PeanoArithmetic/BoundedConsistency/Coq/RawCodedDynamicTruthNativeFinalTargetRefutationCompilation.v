(**
  Structural refutation of the graph-selected final consistency target.

  The native final staged compiler works in the canonical context obtained
  after opening the three existential witnesses of a putative restricted PA
  proof.  That context already contains the three-times shifted form of the
  original restricted-proof assumption.  Consequently a proof of the next
  restricted-consistency target can be refuted without reconstructing the
  existential package:

    1. eliminate the target's redundant [sealPA] universal prefix;
    2. instantiate its genuine certificate quantifier with object variable 3;
    3. use the shifted restricted-proof assumption already present in the
       canonical context; and
    4. discharge the temporary target assumption by implication introduction.

  The two substitution facts needed by those eliminations are proved below
  as represented raw operation traces.  In particular, no carrier element is
  decoded and no semantic truth-to-proof conversion, dynamic-soundness
  producer, or consistency-certificate successor is used.
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedFormulaRankTotality
  RawCodedFormulaOperationsStandardRealization
  RawCodedFormulaOperationCompositionality
  RawCodedFormulaShiftTreeRealization
  RawCodedFormulaDiagonalOperation
  RawCodedFormulaDiagonalOperationComposition
  RawCodedScopedFormulaDiagonalSubstitution
  RawCodedFormulaSubstitutionAtomInterchange
  RawCodedTermOperationsStandardAdequacy
  RawCodedFormulaOperationsStandardAdequacy
  RawCodedStandardFormulaScopeDecision
  RawCodedStandardFormulaScopeCombinators
  RawCodedRestrictedTargetContextScopes
  RawCodedRestrictedTargetProofContextScopes
  RawCodedRestrictedPADynamicSoundnessFieldScopes
  RawCodedRestrictedPADynamicSoundnessRemainingFieldScopes
  RawCodedNumeralTermCode
  RawCodedNumeralTermShift
  RawCodedNumeralTermOpening
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedContextShift
  RawCodedProofAssumptionLeaf
  RawCodedProofAllEConstructor
  RawCodedProofBinaryConstructors
  RawCodedProofImpIConstructor
  RawCodedPALocalProofExistential
  RawCodedPALocalProofUniversalElimination
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofComposition
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedRestrictedPAConsistencyOpenCompiler
  RawCodedRestrictedPAConsistencyOpenDescent
  RawCodedRestrictedPAConsistencyTripleExDescent
  RawCodedRestrictedTargetFormulaShift
  RawCodedRestrictedPAConsistencyShiftOrbit
  RawCodedRestrictedPAConsistencyShiftRealization
  RawCodedRestrictedPAProjectedFieldRefutation
  RawCodedPAAxiomContextSelfShift
  RawCodedDynamicTruthNativeFinalStagedRootCompilation.

Module PABoundedRawCodedDynamicTruthNativeFinalTargetRefutationCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedFormulaOperationsStandardRealization.
Import PABoundedRawCodedFormulaOperationCompositionality.
Import PABoundedRawCodedFormulaShiftTreeRealization.
Import PABoundedRawCodedFormulaDiagonalOperation.
Import PABoundedRawCodedFormulaDiagonalOperationComposition.
Import PABoundedRawCodedScopedFormulaDiagonalSubstitution.
Import PABoundedRawCodedFormulaSubstitutionAtomInterchange.
Import PABoundedRawCodedTermOperationsStandardAdequacy.
Import PABoundedRawCodedFormulaOperationsStandardAdequacy.
Import PABoundedRawCodedStandardFormulaScopeDecision.
Import PABoundedRawCodedStandardFormulaScopeCombinators.
Import PABoundedRawCodedRestrictedTargetContextScopes.
Import PABoundedRawCodedRestrictedTargetProofContextScopes.
Import PABoundedRawCodedRestrictedPADynamicSoundnessFieldScopes.
Import PABoundedRawCodedRestrictedPADynamicSoundnessRemainingFieldScopes.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedNumeralTermShift.
Import PABoundedRawCodedNumeralTermOpening.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedProofAllEConstructor.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofUniversalElimination.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedRestrictedPAConsistencyOpenCompiler.
Import PABoundedRawCodedRestrictedPAConsistencyOpenDescent.
Import PABoundedRawCodedRestrictedPAConsistencyTripleExDescent.
Import PABoundedRawCodedRestrictedTargetFormulaShift.
Import PABoundedRawCodedRestrictedPAConsistencyShiftOrbit.
Import PABoundedRawCodedRestrictedPAConsistencyShiftRealization.
Import PABoundedRawCodedRestrictedPAProjectedFieldRefutation.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.

(** A scope judgment for the finite restricted-target syntax.  The numeral
    hole is closed at every scope.  Compound term contexts and nested seals
    are not used by the proof assumption, so they are deliberately excluded
    instead of claiming an unnecessary operation theorem for them. *)
Definition RestrictedTargetTermContextDiagonalScoped (scope : nat)
    (context : RestrictedTargetTermContext) : Prop :=
  match context with
  | RTTCFixed fixed => StandardTermScoped scope fixed
  | RTTCHole => True
  | RTTCSucc _ | RTTCAdd _ _ | RTTCMul _ _ => False
  end.

Fixpoint RestrictedTargetFormulaContextDiagonalScoped (scope : nat)
    (context : RestrictedTargetFormulaContext) : Prop :=
  match context with
  | RTFCFixed fixed => StandardFormulaScoped scope fixed
  | RTFCBot => True
  | RTFCEq lhs rhs =>
      RestrictedTargetTermContextDiagonalScoped scope lhs /\
      RestrictedTargetTermContextDiagonalScoped scope rhs
  | RTFCImp lhs rhs | RTFCAnd lhs rhs | RTFCOr lhs rhs =>
      RestrictedTargetFormulaContextDiagonalScoped scope lhs /\
      RestrictedTargetFormulaContextDiagonalScoped scope rhs
  | RTFCAll child | RTFCEx child =>
      RestrictedTargetFormulaContextDiagonalScoped (S scope) child
  | RTFCSeal _ => False
  end.

Arguments RestrictedTargetTermContextDiagonalScoped scope context
  : clear implicits.
Arguments RestrictedTargetFormulaContextDiagonalScoped scope context
  : clear implicits.

(** The existing scope library handles every target-context constructor.  In
    the present proof assumption, the independent shift-support certificate
    rules out precisely the compound term/seal cases omitted by the smaller
    diagonal judgment above.  This conversion keeps the large checker fields
    opaque. *)
Lemma restrictedTargetTermContextDiagonalScoped_of_shift_scope : forall
    scope context,
  RestrictedTargetTermContextShiftSupported context ->
  RestrictedTargetTermContextScoped scope context ->
  RestrictedTargetTermContextDiagonalScoped scope context.
Proof.
  intros scope context hshift hscope.
  destruct context; cbn
    [RestrictedTargetTermContextShiftSupported
      RestrictedTargetTermContextScoped
      RestrictedTargetTermContextDiagonalScoped] in *;
    try contradiction; assumption || exact I.
Qed.

Lemma restrictedTargetFormulaContextDiagonalScoped_of_shift_scope : forall
    scope context,
  RestrictedTargetFormulaContextShiftSupported context ->
  RestrictedTargetFormulaContextScoped scope context ->
  RestrictedTargetFormulaContextDiagonalScoped scope context.
Proof.
  intros scope context. revert scope.
  induction context as [fixed | | lhs rhs | lhs IHlhs rhs IHrhs |
      lhs IHlhs rhs IHrhs | lhs IHlhs rhs IHrhs |
      child IHchild | child IHchild | child IHchild];
    intros scope hshift hscope;
    cbn [RestrictedTargetFormulaContextShiftSupported
      RestrictedTargetFormulaContextScoped
      RestrictedTargetFormulaContextDiagonalScoped] in *.
  - exact hscope.
  - exact I.
  - destruct hshift as [hshiftL hshiftR].
    destruct hscope as [hscopeL hscopeR]. split.
    + exact (restrictedTargetTermContextDiagonalScoped_of_shift_scope
        scope lhs hshiftL hscopeL).
    + exact (restrictedTargetTermContextDiagonalScoped_of_shift_scope
        scope rhs hshiftR hscopeR).
  - destruct hshift as [hshiftL hshiftR].
    destruct hscope as [hscopeL hscopeR]. split.
    + exact (IHlhs scope hshiftL hscopeL).
    + exact (IHrhs scope hshiftR hscopeR).
  - destruct hshift as [hshiftL hshiftR].
    destruct hscope as [hscopeL hscopeR]. split.
    + exact (IHlhs scope hshiftL hscopeL).
    + exact (IHrhs scope hshiftR hscopeR).
  - destruct hshift as [hshiftL hshiftR].
    destruct hscope as [hscopeL hscopeR]. split.
    + exact (IHlhs scope hshiftL hscopeL).
    + exact (IHrhs scope hshiftR hscopeR).
  - exact (IHchild (S scope) hshift hscope).
  - exact (IHchild (S scope) hshift hscope).
  - contradiction.
Qed.

(** A standard scoped term is fixed by substitution below its scope; the
    nonstandard numeral hole is fixed by its own numeral traversal. *)
Lemma raw_codedRestrictedTargetTermContext_substitutionAtom_scoped : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      replacementBound replacement numeralBound numeralCode
      scope depth context,
  RawNumeralTermCodeAt M replacementBound replacement ->
  RawNumeralTermCodeAt M numeralBound numeralCode ->
  RestrictedTargetTermContextDiagonalScoped scope context ->
  rawLe M (rawNumeralValue M scope) depth ->
  RawCodedFormulaSubstitutionAtom M replacement depth
    (rawRestrictedTargetTermContextCode M numeralCode context)
    (rawRestrictedTargetTermContextCode M numeralCode context).
Proof.
  intros M hPA replacementBound replacement numeralBound numeralCode
    scope depth context hreplacement hnumeral hscope hdepth.
  destruct context; cbn
    [RestrictedTargetTermContextDiagonalScoped
      rawRestrictedTargetTermContextCode] in *;
    try contradiction.
  - exact (raw_codedFormulaSubstitutionAtom_standard_identity_below
      M hPA replacementBound replacement scope depth t
      hreplacement hscope hdepth).
  - exact (raw_codedFormulaSubstitutionAtom_numeral_identity
      M hPA replacementBound replacement numeralBound numeralCode depth
      hreplacement hnumeral).
Qed.

(** Structural diagonal substitution for a scoped restricted-target context.
    The represented depth remains carrier-valued; only the finite context
    shape and its metatheoretic scope are inspected here. *)
Theorem raw_codedRestrictedTargetFormulaContext_diagonal_scoped : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      replacementBound replacement numeralBound numeralCode
      scope depth context,
  RawNumeralTermCodeAt M replacementBound replacement ->
  RawNumeralTermCodeAt M numeralBound numeralCode ->
  RestrictedTargetFormulaContextDiagonalScoped scope context ->
  rawLe M (rawNumeralValue M scope) depth ->
  RawCodedFormulaDiagonalSubstitution M replacement depth
    (rawRestrictedTargetFormulaContextCode M numeralCode context).
Proof.
  intros M hPA replacementBound replacement numeralBound numeralCode
    scope depth context.
  revert scope depth.
  induction context as [fixed | | lhs rhs | lhs IHlhs rhs IHrhs |
      lhs IHlhs rhs IHrhs | lhs IHlhs rhs IHrhs |
      child IHchild | child IHchild | child IHchild];
    intros scope depth hreplacement hnumeral hscope hdepth;
    cbn [RestrictedTargetFormulaContextDiagonalScoped
      rawRestrictedTargetFormulaContextCode] in *.
  - exact (raw_codedFormulaDiagonalSubstitution_standard_scoped
      M hPA replacementBound replacement scope depth fixed
      hreplacement hscope hdepth).
  - exact (raw_codedFormulaDiagonalSubstitution_bot
      M hPA replacement depth).
  - destruct hscope as [hlhs hrhs].
    apply (raw_codedFormulaDiagonalSubstitution_eq M hPA).
    + exact (raw_codedRestrictedTargetTermContext_substitutionAtom_scoped
        M hPA replacementBound replacement numeralBound numeralCode
        scope depth lhs hreplacement hnumeral hlhs hdepth).
    + exact (raw_codedRestrictedTargetTermContext_substitutionAtom_scoped
        M hPA replacementBound replacement numeralBound numeralCode
        scope depth rhs hreplacement hnumeral hrhs hdepth).
  - destruct hscope as [hlhs hrhs].
    apply (raw_codedFormulaDiagonalSubstitution_imp M hPA).
    + exact (IHlhs scope depth hreplacement hnumeral hlhs hdepth).
    + exact (IHrhs scope depth hreplacement hnumeral hrhs hdepth).
  - destruct hscope as [hlhs hrhs].
    apply (raw_codedFormulaDiagonalSubstitution_and M hPA).
    + exact (IHlhs scope depth hreplacement hnumeral hlhs hdepth).
    + exact (IHrhs scope depth hreplacement hnumeral hrhs hdepth).
  - destruct hscope as [hlhs hrhs].
    apply (raw_codedFormulaDiagonalSubstitution_or M hPA).
    + exact (IHlhs scope depth hreplacement hnumeral hlhs hdepth).
    + exact (IHrhs scope depth hreplacement hnumeral hrhs hdepth).
  - apply (raw_codedFormulaDiagonalSubstitution_all M hPA).
    apply (IHchild (S scope) (raw_succ M depth)
      hreplacement hnumeral hscope).
    change (rawLe M (raw_succ M (rawNumeralValue M scope))
      (raw_succ M depth)).
    exact (raw_rank_succ_le M hPA _ _ hdepth).
  - apply (raw_codedFormulaDiagonalSubstitution_ex M hPA).
    apply (IHchild (S scope) (raw_succ M depth)
      hreplacement hnumeral hscope).
    change (rawLe M (raw_succ M (rawNumeralValue M scope))
      (raw_succ M depth)).
    exact (raw_rank_succ_le M hPA _ _ hdepth).
  - contradiction.
Qed.

(** The sole free variable of the proof assumption is the candidate
    certificate.  All fixed leaves below its three existential binders have
    the corresponding increased scopes. *)
Lemma restrictedPAProofAssumptionFormulaContext_standard_scoped_one :
  RestrictedTargetFormulaContextScoped 1
    restrictedPAProofAssumptionFormulaContext.
Proof.
  unfold restrictedPAProofAssumptionFormulaContext,
    restrictedTargetCodedRestrictedPAProofContext.
  cbn [restrictedTargetExN RestrictedTargetFormulaContextScoped].
  split.
  - raw_scope_formula.
  - split.
    + raw_scope_formula.
    + split.
      * apply restrictedTargetProofContext_scoped; raw_scope_term.
      * split.
        -- eapply standardFormulaScoped_weaken.
           ++ exact proofAtomicallyAdequateTermAt_scoped_three.
           ++ lia.
        -- split.
           ++ eapply standardFormulaScoped_weaken.
              ** exact proofHasFormulaCoverageTermAt_scoped_three.
              ** lia.
           ++ split.
              ** eapply standardFormulaScoped_weaken.
                 --- exact proofRuleCoverageTermAt_scoped_three.
                 --- lia.
              ** eapply standardFormulaScoped_weaken.
                 --- exact proofRuleValidTermAt_scoped_three.
                 --- lia.
Qed.

Lemma restrictedPAProofAssumptionFormulaContext_diagonal_scoped_one :
  RestrictedTargetFormulaContextDiagonalScoped 1
    restrictedPAProofAssumptionFormulaContext.
Proof.
  exact (restrictedTargetFormulaContextDiagonalScoped_of_shift_scope
    1 restrictedPAProofAssumptionFormulaContext
    restrictedPAProofAssumptionFormulaContext_shift_supported
    restrictedPAProofAssumptionFormulaContext_standard_scoped_one).
Qed.

(** The actual consistency body is closed.  This operational statement is
    stronger than a semantic sentence lemma: it supplies the represented
    identity substitution trace consumed by raw [RP_allE]. *)
Lemma raw_restrictedPAConsistencyBody_diagonal : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      replacementBound replacement numeralBound numeralCode depth,
  RawNumeralTermCodeAt M replacementBound replacement ->
  RawNumeralTermCodeAt M numeralBound numeralCode ->
  RawCodedFormulaDiagonalSubstitution M replacement depth
    (rawFormulaAllCode M
      (rawFormulaImpCode M
        (rawRestrictedPAProofAssumptionCode M numeralCode)
        (rawFormulaBotCode M))).
Proof.
  intros M hPA replacementBound replacement numeralBound numeralCode
    depth hreplacement hnumeral.
  apply (raw_codedFormulaDiagonalSubstitution_all M hPA).
  apply (raw_codedFormulaDiagonalSubstitution_imp M hPA).
  - unfold rawRestrictedPAProofAssumptionCode.
    apply (raw_codedRestrictedTargetFormulaContext_diagonal_scoped
      M hPA replacementBound replacement numeralBound numeralCode
      1 (raw_succ M depth) restrictedPAProofAssumptionFormulaContext
      hreplacement hnumeral
      restrictedPAProofAssumptionFormulaContext_diagonal_scoped_one).
    apply raw_rank_one_le_succ. exact hPA.
  - exact (raw_codedFormulaDiagonalSubstitution_bot
      M hPA replacement (raw_succ M depth)).
Qed.

(** Closing a diagonally substitution-stable formula by any fixed number of
    universal binders preserves stability.  This induction follows the
    implementation order of [rawRestrictedTargetCloseNFormulaCode]. *)
Lemma raw_restrictedTargetCloseNFormulaCode_diagonal : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      replacement count body,
  (forall depth,
    RawCodedFormulaDiagonalSubstitution M replacement depth body) ->
  forall depth,
    RawCodedFormulaDiagonalSubstitution M replacement depth
      (rawRestrictedTargetCloseNFormulaCode M count body).
Proof.
  intros M hPA replacement count.
  induction count as [|count IH]; intros body hbody depth.
  - exact (hbody depth).
  - cbn [rawRestrictedTargetCloseNFormulaCode].
    apply IH. intro currentDepth.
    apply (raw_codedFormulaDiagonalSubstitution_all M hPA).
    exact (hbody (raw_succ M currentDepth)).
Qed.

Lemma raw_restrictedPAConsistencyClosedPrefix_singleSubstitution : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      replacementBound replacement numeralBound numeralCode count,
  RawNumeralTermCodeAt M replacementBound replacement ->
  RawNumeralTermCodeAt M numeralBound numeralCode ->
  RawCodedFormulaSingleSubstitution M replacement
    (rawRestrictedTargetCloseNFormulaCode M count
      (rawFormulaAllCode M
        (rawFormulaImpCode M
          (rawRestrictedPAProofAssumptionCode M numeralCode)
          (rawFormulaBotCode M))))
    (rawRestrictedTargetCloseNFormulaCode M count
      (rawFormulaAllCode M
        (rawFormulaImpCode M
          (rawRestrictedPAProofAssumptionCode M numeralCode)
          (rawFormulaBotCode M)))).
Proof.
  intros M hPA replacementBound replacement numeralBound numeralCode count
    hreplacement hnumeral.
  apply (raw_codedFormulaSingleSubstitution_of_diagonal M hPA).
  apply (raw_restrictedTargetCloseNFormulaCode_diagonal M hPA).
  intro depth.
  exact (raw_restrictedPAConsistencyBody_diagonal M hPA
    replacementBound replacement numeralBound numeralCode depth
    hreplacement hnumeral).
Qed.

(** Constructor equality needed to expose the outermost quantifier of a
    nonempty fixed closure. *)
Lemma rawRestrictedTargetCloseNFormulaCode_succ_outside : forall
    (M : RawPAModel) count body,
  rawRestrictedTargetCloseNFormulaCode M (S count) body =
  rawFormulaAllCode M
    (rawRestrictedTargetCloseNFormulaCode M count body).
Proof.
  intros M count. induction count as [|count IH]; intro body.
  - reflexivity.
  - exact (IH (rawFormulaAllCode M body)).
Qed.

(** Explicit chain of [RP_allE] nodes removing the fixed seal prefix. *)
Fixpoint rawProofRestrictedPAConsistencyCloseNERoot
    (M : RawPAModel) (count : nat)
    (context body replacement child : M) : M :=
  match count with
  | 0 => child
  | S count' =>
      rawProofRestrictedPAConsistencyCloseNERoot M count'
        context body replacement
        (rawProofAllERoot M context
          (rawRestrictedTargetCloseNFormulaCode M count' body)
          replacement child)
  end.

Arguments rawProofRestrictedPAConsistencyCloseNERoot
  M count context body replacement child : clear implicits.

Theorem raw_codedPALocalProofOf_restrictedPAConsistency_closeN_eliminate :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      replacementBound replacement numeralBound numeralCode
      count context child,
  RawNumeralTermCodeAt M replacementBound replacement ->
  RawNumeralTermCodeAt M numeralBound numeralCode ->
  RawCodedPALocalProofOf M context
    (rawRestrictedTargetCloseNFormulaCode M count
      (rawFormulaAllCode M
        (rawFormulaImpCode M
          (rawRestrictedPAProofAssumptionCode M numeralCode)
          (rawFormulaBotCode M)))) child ->
  RawCodedPALocalProofOf M context
    (rawFormulaAllCode M
      (rawFormulaImpCode M
        (rawRestrictedPAProofAssumptionCode M numeralCode)
        (rawFormulaBotCode M)))
    (rawProofRestrictedPAConsistencyCloseNERoot M count context
      (rawFormulaAllCode M
        (rawFormulaImpCode M
          (rawRestrictedPAProofAssumptionCode M numeralCode)
          (rawFormulaBotCode M)))
      replacement child).
Proof.
  intros M hPA replacementBound replacement numeralBound numeralCode
    count.
  induction count as [|count IH]; intros context child
    hreplacement hnumeral hchild.
  - exact hchild.
  - rewrite rawRestrictedTargetCloseNFormulaCode_succ_outside in hchild.
    assert (hprefix : RawCodedPALocalProofOf M context
        (rawRestrictedTargetCloseNFormulaCode M count
          (rawFormulaAllCode M
            (rawFormulaImpCode M
              (rawRestrictedPAProofAssumptionCode M numeralCode)
              (rawFormulaBotCode M))))
        (rawProofAllERoot M context
          (rawRestrictedTargetCloseNFormulaCode M count
            (rawFormulaAllCode M
              (rawFormulaImpCode M
                (rawRestrictedPAProofAssumptionCode M numeralCode)
                (rawFormulaBotCode M))))
          replacement child)).
    {
      exact (raw_codedPALocalProofOf_allE M hPA context
        (rawRestrictedTargetCloseNFormulaCode M count
          (rawFormulaAllCode M
            (rawFormulaImpCode M
              (rawRestrictedPAProofAssumptionCode M numeralCode)
              (rawFormulaBotCode M))))
        replacement
        (rawRestrictedTargetCloseNFormulaCode M count
          (rawFormulaAllCode M
            (rawFormulaImpCode M
              (rawRestrictedPAProofAssumptionCode M numeralCode)
              (rawFormulaBotCode M))))
        child hchild
        (raw_restrictedPAConsistencyClosedPrefix_singleSubstitution
          M hPA replacementBound replacement numeralBound numeralCode count
          hreplacement hnumeral)).
    }
    cbn [rawProofRestrictedPAConsistencyCloseNERoot].
    exact (IH context
      (rawProofAllERoot M context
        (rawRestrictedTargetCloseNFormulaCode M count
          (rawFormulaAllCode M
            (rawFormulaImpCode M
              (rawRestrictedPAProofAssumptionCode M numeralCode)
              (rawFormulaBotCode M))))
        replacement child)
      hreplacement hnumeral hprefix).
Qed.

(** ------------------------------------------------------------------
    The genuine candidate quantifier. *)

(** Substituting object variable 3 at [depth] has the same effect on a
    standard leaf as shifting its active variable by three.  We retain these
    equations as an executable support judgment, because they are needed
    only for the fixed proof-assumption template. *)
Lemma standardTermOpening_candidateThree_of_scoped : forall depth input,
  StandardTermScoped (S depth) input ->
  standardTermOpening depth
    (standardTermShift 0 depth (tVar 3))
    (standardTermShift depth 0 input) =
  standardTermShift depth 3 input.
Proof.
  intros depth input. induction input as
      [index | | child IH | lhs IHlhs rhs IHrhs |
       lhs IHlhs rhs IHrhs]; intro hscope;
    cbn [standardTermShift standardTermOpening].
  - assert (hindex : index < S depth).
    { apply hscope. reflexivity. }
    destruct (index <? depth) eqn:hbelow.
    + cbn [standardTermOpening]. rewrite hbelow. reflexivity.
    + apply Nat.ltb_ge in hbelow.
      assert (hindexEq : index = depth) by lia. subst index.
      cbn [standardTermShift standardTermOpening].
      rewrite Nat.add_0_r.
      rewrite Nat.ltb_irrefl, Nat.eqb_refl.
      cbn.
      f_equal. change (3 + depth = depth + 3). apply Nat.add_comm.
  - reflexivity.
  - f_equal. apply IH. intros index hfree.
    exact (hscope index hfree).
  - f_equal.
    + apply IHlhs. intros index hfree.
      exact (hscope index (or_introl hfree)).
    + apply IHrhs. intros index hfree.
      exact (hscope index (or_intror hfree)).
  - f_equal.
    + apply IHlhs. intros index hfree.
      exact (hscope index (or_introl hfree)).
    + apply IHrhs. intros index hfree.
      exact (hscope index (or_intror hfree)).
Qed.

Lemma standardFormulaSubstitution_candidateThree_of_scoped :
    forall depth input,
  StandardFormulaScoped (S depth) input ->
  standardFormulaSingleSubstitution (tVar 3) depth
    (standardFormulaShift depth 0 input) =
  standardFormulaShift depth 3 input.
Proof.
  intros depth input. revert depth.
  induction input as [lhs rhs | | lhs IHlhs rhs IHrhs |
      lhs IHlhs rhs IHrhs | lhs IHlhs rhs IHrhs |
      child IHchild | child IHchild]; intros depth hscope;
    cbn [standardFormulaSingleSubstitution standardFormulaShift].
  - f_equal.
    + apply standardTermOpening_candidateThree_of_scoped.
      intros index hfree. exact (hscope index (or_introl hfree)).
    + apply standardTermOpening_candidateThree_of_scoped.
      intros index hfree. exact (hscope index (or_intror hfree)).
  - reflexivity.
  - f_equal.
    + apply IHlhs. intros index hfree.
      exact (hscope index (or_introl hfree)).
    + apply IHrhs. intros index hfree.
      exact (hscope index (or_intror hfree)).
  - f_equal.
    + apply IHlhs. intros index hfree.
      exact (hscope index (or_introl hfree)).
    + apply IHrhs. intros index hfree.
      exact (hscope index (or_intror hfree)).
  - f_equal.
    + apply IHlhs. intros index hfree.
      exact (hscope index (or_introl hfree)).
    + apply IHrhs. intros index hfree.
      exact (hscope index (or_intror hfree)).
  - f_equal. apply IHchild.
    exact (StandardFormulaScoped_binder (S depth) child hscope).
  - f_equal. apply IHchild.
    exact (StandardFormulaScoped_ex_binder (S depth) child hscope).
Qed.

Definition RestrictedTargetTermContextCandidateThreeSupported (depth : nat)
    (context : RestrictedTargetTermContext) : Prop :=
  match context with
  | RTTCFixed fixed =>
      standardTermOpening depth
        (standardTermShift 0 depth (tVar 3))
        (standardTermShift depth 0 fixed) =
      standardTermShift depth 3 fixed
  | RTTCHole => True
  | RTTCSucc _ | RTTCAdd _ _ | RTTCMul _ _ => False
  end.

Fixpoint RestrictedTargetFormulaContextCandidateThreeSupported
    (depth : nat) (context : RestrictedTargetFormulaContext) : Prop :=
  match context with
  | RTFCFixed fixed =>
      standardFormulaSingleSubstitution (tVar 3) depth
        (standardFormulaShift depth 0 fixed) =
      standardFormulaShift depth 3 fixed
  | RTFCBot => True
  | RTFCEq lhs rhs =>
      RestrictedTargetTermContextCandidateThreeSupported depth lhs /\
      RestrictedTargetTermContextCandidateThreeSupported depth rhs
  | RTFCImp lhs rhs | RTFCAnd lhs rhs | RTFCOr lhs rhs =>
      RestrictedTargetFormulaContextCandidateThreeSupported depth lhs /\
      RestrictedTargetFormulaContextCandidateThreeSupported depth rhs
  | RTFCAll child | RTFCEx child =>
      RestrictedTargetFormulaContextCandidateThreeSupported (S depth) child
  | RTFCSeal _ => False
  end.

Lemma restrictedTargetTermContextCandidateThreeSupported_of_shift_scope :
    forall depth context,
  RestrictedTargetTermContextShiftSupported context ->
  RestrictedTargetTermContextScoped (S depth) context ->
  RestrictedTargetTermContextCandidateThreeSupported depth context.
Proof.
  intros depth context hshift hscope.
  destruct context; cbn
    [RestrictedTargetTermContextShiftSupported
      RestrictedTargetTermContextScoped
      RestrictedTargetTermContextCandidateThreeSupported] in *;
    try contradiction.
  - exact (standardTermOpening_candidateThree_of_scoped
      depth t hscope).
  - exact I.
Qed.

Lemma restrictedTargetFormulaContextCandidateThreeSupported_of_shift_scope :
    forall depth context,
  RestrictedTargetFormulaContextShiftSupported context ->
  RestrictedTargetFormulaContextScoped (S depth) context ->
  RestrictedTargetFormulaContextCandidateThreeSupported depth context.
Proof.
  intros depth context. revert depth.
  induction context as [fixed | | lhs rhs | lhs IHlhs rhs IHrhs |
      lhs IHlhs rhs IHrhs | lhs IHlhs rhs IHrhs |
      child IHchild | child IHchild | child IHchild];
    intros depth hshift hscope;
    cbn [RestrictedTargetFormulaContextShiftSupported
      RestrictedTargetFormulaContextScoped
      RestrictedTargetFormulaContextCandidateThreeSupported] in *.
  - exact (standardFormulaSubstitution_candidateThree_of_scoped
      depth fixed hscope).
  - exact I.
  - destruct hshift as [hshiftL hshiftR].
    destruct hscope as [hscopeL hscopeR]. split.
    + exact
        (restrictedTargetTermContextCandidateThreeSupported_of_shift_scope
          depth lhs hshiftL hscopeL).
    + exact
        (restrictedTargetTermContextCandidateThreeSupported_of_shift_scope
          depth rhs hshiftR hscopeR).
  - destruct hshift as [hshiftL hshiftR].
    destruct hscope as [hscopeL hscopeR]. split.
    + exact (IHlhs depth hshiftL hscopeL).
    + exact (IHrhs depth hshiftR hscopeR).
  - destruct hshift as [hshiftL hshiftR].
    destruct hscope as [hscopeL hscopeR]. split.
    + exact (IHlhs depth hshiftL hscopeL).
    + exact (IHrhs depth hshiftR hscopeR).
  - destruct hshift as [hshiftL hshiftR].
    destruct hscope as [hscopeL hscopeR]. split.
    + exact (IHlhs depth hshiftL hscopeL).
    + exact (IHrhs depth hshiftR hscopeR).
  - exact (IHchild (S depth) hshift hscope).
  - exact (IHchild (S depth) hshift hscope).
  - contradiction.
Qed.

(** Atomic realization for a fixed term or for the nonstandard numeral hole.
    The replacement itself is standard syntax, but the numeral remains an
    arbitrary carrier-valued term code. *)
Lemma raw_codedRestrictedTargetTermContext_candidateThree : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      numeralBound numeralCode depth context,
  RawNumeralTermCodeAt M numeralBound numeralCode ->
  RestrictedTargetTermContextCandidateThreeSupported depth context ->
  RawCodedFormulaSubstitutionAtom M
    (rawTermVarCode M (rawNumeralValue M 3))
    (rawNumeralValue M depth)
    (rawRestrictedTargetTermContextIteratedShiftCode
      M numeralCode depth 0 context)
    (rawRestrictedTargetTermContextIteratedShiftCode
      M numeralCode depth 3 context).
Proof.
  intros M hPA numeralBound numeralCode depth context
    hnumeral hsupport.
  destruct context; cbn
    [RestrictedTargetTermContextCandidateThreeSupported
      rawRestrictedTargetTermContextIteratedShiftCode] in *;
    try contradiction.
  - exists (rawQuotedTermCode M
      (standardTermShift 0 depth (tVar 3))).
    split.
    + change (RawCodedTermShift M
        (rawNumeralValue M 0) (rawNumeralValue M depth)
        (rawQuotedTermCode M (tVar 3))
        (rawQuotedTermCode M
          (standardTermShift 0 depth (tVar 3)))).
      exact (raw_codedTermShift_standard M hPA 0 depth (tVar 3)).
    + pose proof (raw_codedTermOpening_standard M hPA depth
        (standardTermShift 0 depth (tVar 3))
        (standardTermShift depth 0 t)) as hopening.
      rewrite hsupport in hopening. exact hopening.
  - exists (rawQuotedTermCode M
      (standardTermShift 0 depth (tVar 3))).
    split.
    + change (RawCodedTermShift M
        (rawNumeralValue M 0) (rawNumeralValue M depth)
        (rawQuotedTermCode M (tVar 3))
        (rawQuotedTermCode M
          (standardTermShift 0 depth (tVar 3)))).
      exact (raw_codedTermShift_standard M hPA 0 depth (tVar 3)).
    + exact (raw_codedTermOpening_numeral_identity M hPA
        numeralBound numeralCode (rawNumeralValue M depth)
        (rawQuotedTermCode M
          (standardTermShift 0 depth (tVar 3))) hnumeral).
Qed.

(** Formula-level realization of candidate instantiation across the finite
    restricted-target context. *)
Theorem raw_codedRestrictedTargetFormulaContext_candidateThree : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      numeralBound numeralCode depth context,
  RawNumeralTermCodeAt M numeralBound numeralCode ->
  RestrictedTargetFormulaContextCandidateThreeSupported depth context ->
  RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
    (rawTermVarCode M (rawNumeralValue M 3))
    (rawNumeralValue M depth)
    (rawRestrictedTargetFormulaContextIteratedShiftCode
      M numeralCode depth 0 context)
    (rawRestrictedTargetFormulaContextIteratedShiftCode
      M numeralCode depth 3 context).
Proof.
  intros M hPA numeralBound numeralCode depth context.
  revert depth.
  induction context as [fixed | | lhs rhs | lhs IHlhs rhs IHrhs |
      lhs IHlhs rhs IHrhs | lhs IHlhs rhs IHrhs |
      child IHchild | child IHchild | child IHchild];
    intros depth hnumeral hsupport;
    cbn [RestrictedTargetFormulaContextCandidateThreeSupported
      rawRestrictedTargetFormulaContextIteratedShiftCode] in *.
  - pose proof (raw_standardFormulaSingleSubstitution_at M hPA
      (tVar 3) depth (standardFormulaShift depth 0 fixed)) as hop.
    rewrite hsupport in hop. exact hop.
  - exact (raw_standardFormulaSingleSubstitution_at M hPA
      (tVar 3) depth pBot).
  - destruct hsupport as [hlhs hrhs].
    apply (raw_codedFormulaSubstitution_eq_of_term_atoms M hPA).
    + exact (raw_codedRestrictedTargetTermContext_candidateThree
        M hPA numeralBound numeralCode depth lhs hnumeral hlhs).
    + exact (raw_codedRestrictedTargetTermContext_candidateThree
        M hPA numeralBound numeralCode depth rhs hnumeral hrhs).
  - destruct hsupport as [hlhs hrhs].
    exact (raw_codedFormulaSubstitution_binary_composition M hPA
      (rawTermVarCode M (rawNumeralValue M 3)) RFSBImp
      (rawNumeralValue M depth) _ _ _ _
      (IHlhs depth hnumeral hlhs) (IHrhs depth hnumeral hrhs)).
  - destruct hsupport as [hlhs hrhs].
    exact (raw_codedFormulaSubstitution_binary_composition M hPA
      (rawTermVarCode M (rawNumeralValue M 3)) RFSBAnd
      (rawNumeralValue M depth) _ _ _ _
      (IHlhs depth hnumeral hlhs) (IHrhs depth hnumeral hrhs)).
  - destruct hsupport as [hlhs hrhs].
    exact (raw_codedFormulaSubstitution_binary_composition M hPA
      (rawTermVarCode M (rawNumeralValue M 3)) RFSBOr
      (rawNumeralValue M depth) _ _ _ _
      (IHlhs depth hnumeral hlhs) (IHrhs depth hnumeral hrhs)).
  - apply (raw_codedFormulaSubstitution_unary_composition M hPA
      (rawTermVarCode M (rawNumeralValue M 3)) RFSUAll
      (rawNumeralValue M depth)).
    change (RawCodedFormulaOperation M
      (RawCodedFormulaSubstitutionAtom M)
      (rawTermVarCode M (rawNumeralValue M 3))
      (rawNumeralValue M (S depth))
      (rawRestrictedTargetFormulaContextIteratedShiftCode
        M numeralCode (S depth) 0 child)
      (rawRestrictedTargetFormulaContextIteratedShiftCode
        M numeralCode (S depth) 3 child)).
    exact (IHchild (S depth) hnumeral hsupport).
  - apply (raw_codedFormulaSubstitution_unary_composition M hPA
      (rawTermVarCode M (rawNumeralValue M 3)) RFSUEx
      (rawNumeralValue M depth)).
    change (RawCodedFormulaOperation M
      (RawCodedFormulaSubstitutionAtom M)
      (rawTermVarCode M (rawNumeralValue M 3))
      (rawNumeralValue M (S depth))
      (rawRestrictedTargetFormulaContextIteratedShiftCode
        M numeralCode (S depth) 0 child)
      (rawRestrictedTargetFormulaContextIteratedShiftCode
        M numeralCode (S depth) 3 child)).
    exact (IHchild (S depth) hnumeral hsupport).
  - contradiction.
Qed.

Lemma restrictedPAProofAssumptionFormulaContext_candidateThree_supported :
  RestrictedTargetFormulaContextCandidateThreeSupported 0
    restrictedPAProofAssumptionFormulaContext.
Proof.
  exact
    (restrictedTargetFormulaContextCandidateThreeSupported_of_shift_scope
      0 restrictedPAProofAssumptionFormulaContext
      restrictedPAProofAssumptionFormulaContext_shift_supported
      restrictedPAProofAssumptionFormulaContext_standard_scoped_one).
Qed.

(** Instantiating the candidate variable with object variable 3 yields
    exactly the three-step shift already stored in the canonical context. *)
Lemma raw_restrictedPAProofAssumption_candidateThree_substitution : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      numeralBound numeralCode,
  RawNumeralTermCodeAt M numeralBound numeralCode ->
  RawCodedFormulaSingleSubstitution M
    (rawTermVarCode M (rawNumeralValue M 3))
    (rawRestrictedPAProofAssumptionCode M numeralCode)
    (rawRestrictedPAProofAssumptionIteratedShiftCode M numeralCode 3).
Proof.
  intros M hPA numeralBound numeralCode hnumeral.
  pose proof (raw_codedRestrictedTargetFormulaContext_candidateThree
    M hPA numeralBound numeralCode 0
    restrictedPAProofAssumptionFormulaContext hnumeral
    restrictedPAProofAssumptionFormulaContext_candidateThree_supported)
    as hsubstitution.
  unfold RawCodedFormulaSingleSubstitution,
    rawRestrictedPAProofAssumptionIteratedShiftCode.
  cbn [rawNumeralValue].
  rewrite <- (raw_restrictedPAProofAssumptionFormulaContext_view
    M numeralCode).
  rewrite <- (rawRestrictedTargetFormulaContextIteratedShiftCode_zero
    M numeralCode 0 restrictedPAProofAssumptionFormulaContext
    restrictedPAProofAssumptionFormulaContext_shift_supported).
  exact hsubstitution.
Qed.

Lemma raw_restrictedPAConsistencyCandidateImplication_substitution : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      numeralBound numeralCode,
  RawNumeralTermCodeAt M numeralBound numeralCode ->
  RawCodedFormulaSingleSubstitution M
    (rawTermVarCode M (rawNumeralValue M 3))
    (rawFormulaImpCode M
      (rawRestrictedPAProofAssumptionCode M numeralCode)
      (rawFormulaBotCode M))
    (rawFormulaImpCode M
      (rawRestrictedPAProofAssumptionIteratedShiftCode M numeralCode 3)
      (rawFormulaBotCode M)).
Proof.
  intros M hPA numeralBound numeralCode hnumeral.
  unfold RawCodedFormulaSingleSubstitution.
  change (RawCodedFormulaOperation M
    (RawCodedFormulaSubstitutionAtom M)
    (rawTermVarCode M (rawNumeralValue M 3)) (raw_zero M)
    (rawFormulaImpCode M
      (rawRestrictedPAProofAssumptionCode M numeralCode)
      (rawFormulaBotCode M))
    (rawFormulaImpCode M
      (rawRestrictedPAProofAssumptionIteratedShiftCode M numeralCode 3)
      (rawFormulaBotCode M))).
  apply (raw_codedFormulaSubstitution_binary_composition M hPA
    (rawTermVarCode M (rawNumeralValue M 3)) RFSBImp (raw_zero M)).
  - exact (raw_restrictedPAProofAssumption_candidateThree_substitution
      M hPA numeralBound numeralCode hnumeral).
  - apply (raw_codedFormulaOperation_of_diagonal M hPA).
    exact (raw_codedFormulaDiagonalSubstitution_bot M hPA
      (rawTermVarCode M (rawNumeralValue M 3)) (raw_zero M)).
Qed.

(** ------------------------------------------------------------------
    Same-context proof root and the final staged adapter. *)

Definition rawDynamicTruthNativeFinalTargetRefutationRoot
    (M : RawPAModel) (nextFinal successorNumeralCode baseContext : M) : M :=
  let shiftedProofContext :=
    rawRestrictedPACanonicalShiftedProofContextCode
      M baseContext successorNumeralCode in
  let fieldsContext :=
    rawRestrictedPAFieldsContextCode M successorNumeralCode
      shiftedProofContext in
  let targetContext := rawListNode M nextFinal fieldsContext in
  let nextFinalRoot :=
    rawProofAssumptionRoot M targetContext nextFinal in
  let unsealedRoot :=
    rawProofRestrictedPAConsistencyCloseNERoot M
      (restrictedTargetFormulaContextBound
        restrictedPAConsistencyBodyFormulaContext)
      targetContext
      (rawFormulaAllCode M
        (rawFormulaImpCode M
          (rawRestrictedPAProofAssumptionCode M successorNumeralCode)
          (rawFormulaBotCode M)))
      successorNumeralCode nextFinalRoot in
  let candidateImplicationRoot :=
    rawProofAllERoot M targetContext
      (rawFormulaImpCode M
        (rawRestrictedPAProofAssumptionCode M successorNumeralCode)
        (rawFormulaBotCode M))
      (rawTermVarCode M (rawNumeralValue M 3)) unsealedRoot in
  let shiftedAssumption :=
    rawRestrictedPAProofAssumptionIteratedShiftCode
      M successorNumeralCode 3 in
  let shiftedAssumptionRoot :=
    rawProofAssumptionRoot M targetContext shiftedAssumption in
  let bottomRoot :=
    rawProofImpERoot M targetContext shiftedAssumption
      (rawFormulaBotCode M) candidateImplicationRoot
      shiftedAssumptionRoot in
  rawProofImpIRoot M fieldsContext nextFinal
    (rawFormulaBotCode M) bottomRoot.

Arguments rawDynamicTruthNativeFinalTargetRefutationRoot
  M nextFinal successorNumeralCode baseContext : clear implicits.

(** Exact pointwise component expected as the third root of
    [RawDynamicTruthNativeFinalUniversalSoundnessCompositionCompiler]. *)
Definition RawDynamicTruthNativeFinalTargetRefutationRootCompiler
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode witnessList baseContext,
    RawDynamicTruthNativeFinalStagedGraphTraceAt M tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode ->
    RawDynamicTruthNativeFinalStagedPrerequisitesOn M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness ->
    RawCodedPALocalProofOf M
      (rawRestrictedPAFieldsContextCode M successorNumeralCode
        (rawRestrictedPACanonicalShiftedProofContextCode
          M baseContext successorNumeralCode))
      (rawFormulaImpCode M nextFinal (rawFormulaBotCode M))
      (rawDynamicTruthNativeFinalTargetRefutationRoot
        M nextFinal successorNumeralCode baseContext).

Arguments RawDynamicTruthNativeFinalTargetRefutationRootCompiler M
  : clear implicits.

Theorem raw_dynamicTruthNativeFinalTargetRefutationRootCompiler : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeFinalTargetRefutationRootCompiler M.
Proof.
  intros M hPA tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    htrace hprerequisites.
  pose proof htrace as htraceCopy.
  destruct htraceCopy as
    [_ _ _ _ _ _ _ hsource].
  destruct hsource as
    [_ hnumeral hnextTarget _].
  rewrite raw_restrictedPAConsistencyTargetCode_view in hnextTarget.
  subst nextFinal.
  pose proof hprerequisites as hprerequisitesCopy.
  destruct hprerequisitesCopy as
    (currentLocalRoot & currentCrossLevelRoot & currentShiftRoot &
      currentSubstitutionRoot & currentAxiomSoundnessRoot & currentFinalRoot &
      nextLocalRoot & nextCrossLevelRoot & nextShiftRoot &
      nextSubstitutionRoot & nextAxiomSoundnessRoot &
      [hprefix _]).
  destruct hprefix as
    [hwitness _ _ _ _ _ _ _ _ _ _].
  assert (hbaseRealizable : RawContextListRealizable M baseContext).
  {
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      witnessList baseContext hwitness).
  }
  assert (hbaseShift : RawContextShift M baseContext baseContext).
  {
    exact (raw_codedPAAxiomWitnessContext_selfShift M hPA
      witnessList baseContext hwitness).
  }
  set (shiftedRootContext :=
    rawRestrictedPACanonicalShiftedRootContextCode
      M baseContext successorNumeralCode).
  set (shiftedWitnessContext :=
    rawRestrictedPACanonicalShiftedWitnessContextCode
      M baseContext successorNumeralCode).
  set (shiftedProofContext :=
    rawRestrictedPACanonicalShiftedProofContextCode
      M baseContext successorNumeralCode).
  assert (hcontexts : RawRestrictedPAExistentialDescentContexts M
      successorNumeralCode baseContext shiftedRootContext
      shiftedWitnessContext shiftedProofContext).
  {
    unfold shiftedRootContext, shiftedWitnessContext, shiftedProofContext.
    exact (raw_restrictedPAExistentialDescentContexts_realized
      M hPA (raw_succ M level) successorNumeralCode baseContext
      hnumeral hbaseShift).
  }
  destruct hcontexts as [_ [_ hproofShift]].
  assert (hshiftedProofRealizable :
      RawContextListRealizable M shiftedProofContext).
  {
    exact (raw_contextShift_target_realizable M
      (rawRestrictedPAAfterProofContextCode M successorNumeralCode
        shiftedWitnessContext)
      shiftedProofContext hproofShift).
  }
  set (fieldsContext := rawRestrictedPAFieldsContextCode
    M successorNumeralCode shiftedProofContext).
  assert (hfieldsRealizable : RawContextListRealizable M fieldsContext).
  {
    unfold fieldsContext, rawRestrictedPAFieldsContextCode.
    exact (raw_contextList_cons_realizable M hPA shiftedProofContext
      (rawRestrictedPAProofFieldsCode M successorNumeralCode)
      hshiftedProofRealizable).
  }
  set (target :=
    rawRestrictedTargetCloseNFormulaCode M
      (restrictedTargetFormulaContextBound
        restrictedPAConsistencyBodyFormulaContext)
      (rawFormulaAllCode M
        (rawFormulaImpCode M
          (rawRestrictedPAProofAssumptionCode M successorNumeralCode)
          (rawFormulaBotCode M)))).
  set (targetContext := rawListNode M target fieldsContext).
  assert (htargetRealizable : RawContextListRealizable M targetContext).
  {
    unfold targetContext.
    exact (raw_contextList_cons_realizable M hPA fieldsContext target
      hfieldsRealizable).
  }
  assert (htargetAssumption : RawCodedPALocalProofOf M targetContext target
      (rawProofAssumptionRoot M targetContext target)).
  {
    unfold targetContext.
    exact (raw_codedPALocalProofOf_assumption M hPA
      fieldsContext target hfieldsRealizable).
  }
  pose proof
    (raw_codedPALocalProofOf_restrictedPAConsistency_closeN_eliminate
      M hPA (raw_succ M level) successorNumeralCode
      (raw_succ M level) successorNumeralCode
      (restrictedTargetFormulaContextBound
        restrictedPAConsistencyBodyFormulaContext)
      targetContext (rawProofAssumptionRoot M targetContext target)
      hnumeral hnumeral htargetAssumption) as hunsealed.
  set (unsealedRoot :=
    rawProofRestrictedPAConsistencyCloseNERoot M
      (restrictedTargetFormulaContextBound
        restrictedPAConsistencyBodyFormulaContext)
      targetContext
      (rawFormulaAllCode M
        (rawFormulaImpCode M
          (rawRestrictedPAProofAssumptionCode M successorNumeralCode)
          (rawFormulaBotCode M)))
      successorNumeralCode
      (rawProofAssumptionRoot M targetContext target)).
  change (RawCodedPALocalProofOf M targetContext
    (rawFormulaAllCode M
      (rawFormulaImpCode M
        (rawRestrictedPAProofAssumptionCode M successorNumeralCode)
        (rawFormulaBotCode M))) unsealedRoot) in hunsealed.
  set (shiftedAssumption :=
    rawRestrictedPAProofAssumptionIteratedShiftCode
      M successorNumeralCode 3).
  set (candidateImplicationRoot := rawProofAllERoot M targetContext
    (rawFormulaImpCode M
      (rawRestrictedPAProofAssumptionCode M successorNumeralCode)
      (rawFormulaBotCode M))
    (rawTermVarCode M (rawNumeralValue M 3)) unsealedRoot).
  assert (hcandidateImplication : RawCodedPALocalProofOf M targetContext
      (rawFormulaImpCode M shiftedAssumption (rawFormulaBotCode M))
      candidateImplicationRoot).
  {
    unfold candidateImplicationRoot, shiftedAssumption.
    exact (raw_codedPALocalProofOf_allE M hPA targetContext
      (rawFormulaImpCode M
        (rawRestrictedPAProofAssumptionCode M successorNumeralCode)
        (rawFormulaBotCode M))
      (rawTermVarCode M (rawNumeralValue M 3))
      (rawFormulaImpCode M
        (rawRestrictedPAProofAssumptionIteratedShiftCode
          M successorNumeralCode 3)
        (rawFormulaBotCode M))
      unsealedRoot hunsealed
      (raw_restrictedPAConsistencyCandidateImplication_substitution
        M hPA (raw_succ M level) successorNumeralCode hnumeral)).
  }
  assert (hshiftedAssumptionMember :
      RawContextListMember M targetContext shiftedAssumption).
  {
    assert (hmember0 : RawContextListMember M
        (rawListNode M shiftedAssumption baseContext) shiftedAssumption).
    {
      exact (raw_contextList_cons_head_member M hPA
        baseContext shiftedAssumption hbaseRealizable).
    }
    assert (hmember1 : RawContextListMember M
        (rawListNode M
          (rawRestrictedPAProofAfterWitnessIteratedShiftCode
            M successorNumeralCode 2)
          (rawListNode M shiftedAssumption baseContext))
        shiftedAssumption).
    {
      exact (raw_contextList_cons_tail_member M hPA _ _ _ hmember0).
    }
    assert (hmember2 : RawContextListMember M shiftedProofContext
        shiftedAssumption).
    {
      unfold shiftedProofContext,
        rawRestrictedPACanonicalShiftedProofContextCode,
        rawRestrictedPAShiftedProofContextCode.
      exact (raw_contextList_cons_tail_member M hPA _ _ _ hmember1).
    }
    assert (hmember3 : RawContextListMember M fieldsContext
        shiftedAssumption).
    {
      unfold fieldsContext, rawRestrictedPAFieldsContextCode.
      exact (raw_contextList_cons_tail_member M hPA _ _ _ hmember2).
    }
    unfold targetContext.
    exact (raw_contextList_cons_tail_member M hPA _ _ _ hmember3).
  }
  set (shiftedAssumptionRoot :=
    rawProofAssumptionRoot M targetContext shiftedAssumption).
  assert (hshiftedAssumption : RawCodedPALocalProofOf M targetContext
      shiftedAssumption shiftedAssumptionRoot).
  {
    split.
    - exact (raw_proofAssumption_ruleCoverage M hPA
        targetContext shiftedAssumption hshiftedAssumptionMember).
    - exact (raw_proofAssumption_endpoint M
        targetContext shiftedAssumption).
  }
  set (bottomRoot := rawProofImpERoot M targetContext shiftedAssumption
    (rawFormulaBotCode M) candidateImplicationRoot shiftedAssumptionRoot).
  assert (hbottom : RawCodedPALocalProofOf M targetContext
      (rawFormulaBotCode M) bottomRoot).
  {
    unfold bottomRoot.
    exact (raw_codedPALocalProofOf_impE M hPA targetContext
      shiftedAssumption (rawFormulaBotCode M)
      candidateImplicationRoot shiftedAssumptionRoot
      hcandidateImplication hshiftedAssumption).
  }
  unfold rawDynamicTruthNativeFinalTargetRefutationRoot.
  fold shiftedProofContext fieldsContext targetContext target
    unsealedRoot candidateImplicationRoot shiftedAssumption
    shiftedAssumptionRoot bottomRoot.
  exact (raw_codedPALocalProofOf_impI M hPA fieldsContext target
    (rawFormulaBotCode M) bottomRoot hbottom).
Qed.

End PABoundedRawCodedDynamicTruthNativeFinalTargetRefutationCompilation.
