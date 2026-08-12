(**
  Atomic adequacy of the final bridge's restricted-proof field head.

  Six of the seven checker fields are ordinary quoted PA formulae.  The
  occurrence-bound field is the sole exception: it contains the arbitrary
  carrier code of the successor numeral term.  We do not decode that code.
  Instead, the existing restricted-target shift tree realizes the field as
  the target of a represented shift.  At cutoff three the field is scoped,
  so this shift is syntactically the identity; the numeral hole is fixed by
  [RawNumeralTermCodeAt].  Shift-target adequacy then supplies the desired
  certificate for the nonstandard field.

  Constructor closure assembles the seven fields into their exact
  right-associated conjunction.  The final theorem projects only the
  numeral trace from the staged graph and ignores the semantic proof roots:
  this compiler is therefore purely syntactic.
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedTermOperationsStandardAdequacy
  RawCodedFormulaOperationsStandardAdequacy
  RawCodedNumeralTermCode
  RawCodedScopedFormulaDiagonalSubstitution
  RawCodedFixedLevelTruthTotality
  RawCodedProofAtomicAdequacyStandard
  RawCodedFormulaShiftAtomicAdequacy
  RawCodedDynamicTruthPairedSuccessorAdequacy
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedRestrictedTargetFormulaShift
  RawCodedRestrictedTargetContextScopes
  RawCodedRestrictedTargetProofContextScopes
  RawCodedRestrictedPADynamicSoundnessSource
  RawCodedRestrictedPAConsistencyOpenDescent
  RawCodedDynamicTruthNativeFinalSelectedAxiomSupportTransport.

Module
  PABoundedRawCodedDynamicTruthNativeFinalBridgeFieldsHeadAdequacy.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedTermOperationsStandardAdequacy.
Import PABoundedRawCodedFormulaOperationsStandardAdequacy.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedScopedFormulaDiagonalSubstitution.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedFormulaShiftAtomicAdequacy.
Import PABoundedRawCodedDynamicTruthPairedSuccessorAdequacy.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedRestrictedTargetFormulaShift.
Import PABoundedRawCodedRestrictedTargetContextScopes.
Import PABoundedRawCodedRestrictedTargetProofContextScopes.
Import PABoundedRawCodedRestrictedPADynamicSoundnessSource.
Import PABoundedRawCodedRestrictedPAConsistencyOpenDescent.
Import
  PABoundedRawCodedDynamicTruthNativeFinalSelectedAxiomSupportTransport.

(** Host-level scope makes a shift at the scope cutoff an identity.  The
    formula analogue is included locally as well, keeping the raw-code
    argument below independent of any ternary-truth application module. *)
Lemma restrictedFields_standardTermShift_identity_of_scoped :
    forall scope amount input,
  StandardTermScoped scope input ->
  standardTermShift scope amount input = input.
Proof.
  intros scope amount input hscope.
  rewrite standardTermShift_as_rename.
  transitivity (Term.rename (fun index => index) input).
  - apply Term.rename_ext_free.
    intros index hfree.
    specialize (hscope index hfree).
    unfold standardShiftRenaming.
    assert (hbelow : (index <? scope) = true)
      by (apply Nat.ltb_lt; exact hscope).
    rewrite hbelow. reflexivity.
  - apply Term.rename_id.
Qed.

Lemma restrictedFields_standardFormulaShift_identity_of_scoped :
    forall scope amount input,
  StandardFormulaScoped scope input ->
  standardFormulaShift scope amount input = input.
Proof.
  intros scope amount input hscope.
  rewrite standardFormulaShift_as_rename.
  transitivity (Formula.rename (fun index => index) input).
  - apply Formula.rename_ext_free.
    intros index hfree.
    specialize (hscope index hfree).
    unfold standardShiftRenaming.
    assert (hbelow : (index <? scope) = true)
      by (apply Nat.ltb_lt; exact hscope).
    rewrite hbelow. reflexivity.
  - apply Formula.rename_id.
Qed.

(** The shift-supported restricted target uses only fixed terms and the
    numeral hole.  Consequently its iterated-shift code is literally fixed
    whenever all fixed terms are scoped below the root cutoff. *)
Lemma
    rawRestrictedTargetTermContextIteratedShiftCode_scoped_identity :
    forall (M : RawPAModel) numeralCode scope prior context,
  RestrictedTargetTermContextShiftSupported context ->
  RestrictedTargetTermContextScoped scope context ->
  rawRestrictedTargetTermContextIteratedShiftCode
    M numeralCode scope prior context =
  rawRestrictedTargetTermContextCode M numeralCode context.
Proof.
  intros M numeralCode scope prior context hshift hscope.
  destruct context;
    cbn [RestrictedTargetTermContextShiftSupported
      RestrictedTargetTermContextScoped
      rawRestrictedTargetTermContextIteratedShiftCode
      rawRestrictedTargetTermContextCode] in *;
    try contradiction; try reflexivity.
  now rewrite restrictedFields_standardTermShift_identity_of_scoped.
Qed.

(** Structural lifting of the preceding identity through every supported
    formula constructor.  [RTFCSeal] is excluded by the existing shift-
    support predicate, exactly as in the restricted-target shift theorem. *)
Lemma
    rawRestrictedTargetFormulaContextIteratedShiftCode_scoped_identity :
    forall (M : RawPAModel) numeralCode scope prior context,
  RestrictedTargetFormulaContextShiftSupported context ->
  RestrictedTargetFormulaContextScoped scope context ->
  rawRestrictedTargetFormulaContextIteratedShiftCode
    M numeralCode scope prior context =
  rawRestrictedTargetFormulaContextCode M numeralCode context.
Proof.
  intros M numeralCode scope prior context.
  revert scope.
  induction context as [fixed | | lhs rhs | lhs IHlhs rhs IHrhs |
      lhs IHlhs rhs IHrhs | lhs IHlhs rhs IHrhs |
      child IHchild | child IHchild | child IHchild];
    intros scope hshift hscope;
    cbn [RestrictedTargetFormulaContextShiftSupported
      RestrictedTargetFormulaContextScoped
      rawRestrictedTargetFormulaContextIteratedShiftCode
      rawRestrictedTargetFormulaContextCode] in *.
  - now rewrite restrictedFields_standardFormulaShift_identity_of_scoped.
  - reflexivity.
  - destruct hshift as [hshiftL hshiftR].
    destruct hscope as [hscopeL hscopeR].
    now rewrite
      (rawRestrictedTargetTermContextIteratedShiftCode_scoped_identity
        M numeralCode scope prior lhs hshiftL hscopeL),
      (rawRestrictedTargetTermContextIteratedShiftCode_scoped_identity
        M numeralCode scope prior rhs hshiftR hscopeR).
  - destruct hshift as [hshiftL hshiftR].
    destruct hscope as [hscopeL hscopeR].
    now rewrite (IHlhs scope hshiftL hscopeL),
      (IHrhs scope hshiftR hscopeR).
  - destruct hshift as [hshiftL hshiftR].
    destruct hscope as [hscopeL hscopeR].
    now rewrite (IHlhs scope hshiftL hscopeL),
      (IHrhs scope hshiftR hscopeR).
  - destruct hshift as [hshiftL hshiftR].
    destruct hscope as [hscopeL hscopeR].
    now rewrite (IHlhs scope hshiftL hscopeL),
      (IHrhs scope hshiftR hscopeR).
  - now rewrite (IHchild (S scope) hshift hscope).
  - now rewrite (IHchild (S scope) hshift hscope).
  - contradiction.
Qed.

(** The one nonstandard field.  Its three free checker witnesses are
    indices 0, 1, and 2, hence cutoff three protects every free variable. *)
Theorem raw_restrictedPAOccurrenceBoundFieldCode_atomically_adequate :
    forall (M : RawPAModel), RawPASatisfies M -> forall
    level successorNumeralCode,
  RawNumeralTermCodeAt M level successorNumeralCode ->
  RawCodedFormulaAtomicallyAdequate M
    (rawRestrictedPAOccurrenceBoundFieldCode M successorNumeralCode).
Proof.
  intros M hPA level successorNumeralCode hnumeral.
  assert (hsupport : RestrictedTargetFormulaContextShiftSupported
      (restrictedTargetProofContext (tVar 1))).
  { exact restrictedPADynamicOccurrenceContext_shift_supported. }
  assert (hscope : RestrictedTargetFormulaContextScoped 3
      (restrictedTargetProofContext (tVar 1))).
  {
    apply restrictedTargetProofContext_scoped.
    intros index hfree. cbn [Term.Free] in hfree.
    subst index. lia.
  }
  pose proof
    (raw_codedFormulaShift_restrictedTargetContext_iterated
      M hPA level successorNumeralCode 3 0
      (restrictedTargetProofContext (tVar 1)) hnumeral hsupport)
    as hshift.
  pose proof (raw_codedFormulaShift_target_atomically_adequate
    M hPA (rawNumeralValue M 3) (rawNumeralValue M 1)
    (rawRestrictedTargetFormulaContextIteratedShiftCode
      M successorNumeralCode 3 0
      (restrictedTargetProofContext (tVar 1)))
    (rawRestrictedTargetFormulaContextIteratedShiftCode
      M successorNumeralCode 3 1
      (restrictedTargetProofContext (tVar 1)))
    hshift) as hadequate.
  rewrite
    (rawRestrictedTargetFormulaContextIteratedShiftCode_scoped_identity
      M successorNumeralCode 3 1
      (restrictedTargetProofContext (tVar 1)) hsupport hscope)
    in hadequate.
  unfold rawRestrictedPAOccurrenceBoundFieldCode.
  exact hadequate.
Qed.

(** Atomic adequacy of the complete seven-field head.  No field is obtained
    from a semantic truth hypothesis: quoted adequacy handles the six fixed
    leaves and the preceding shift-target theorem handles the numeral leaf. *)
Theorem raw_restrictedPAProofFieldsCode_atomically_adequate :
    forall (M : RawPAModel), RawPASatisfies M -> forall
    level successorNumeralCode,
  RawNumeralTermCodeAt M level successorNumeralCode ->
  RawCodedFormulaAtomicallyAdequate M
    (rawRestrictedPAProofFieldsCode M successorNumeralCode).
Proof.
  intros M hPA level successorNumeralCode hnumeral.
  unfold rawRestrictedPAProofFieldsCode.
  apply (raw_formulaAndCode_atomically_adequate M hPA).
  - unfold rawRestrictedPACertificateTupleFieldCode.
    apply raw_quotedFormula_atomically_adequate. exact hPA.
  - unfold rawRestrictedPAProofFieldsSuffix6Code.
    apply (raw_formulaAndCode_atomically_adequate M hPA).
    + unfold rawRestrictedPAAxiomContextFieldCode.
      apply raw_quotedFormula_atomically_adequate. exact hPA.
    + apply (raw_formulaAndCode_atomically_adequate M hPA).
      * exact
          (raw_restrictedPAOccurrenceBoundFieldCode_atomically_adequate
            M hPA level successorNumeralCode hnumeral).
      * apply (raw_formulaAndCode_atomically_adequate M hPA).
        -- unfold rawRestrictedPAAtomicAdequacyFieldCode.
           apply raw_quotedFormula_atomically_adequate. exact hPA.
        -- apply (raw_formulaAndCode_atomically_adequate M hPA).
           ++ unfold rawRestrictedPAFormulaCoverageFieldCode.
              apply raw_quotedFormula_atomically_adequate. exact hPA.
           ++ apply (raw_formulaAndCode_atomically_adequate M hPA).
              ** unfold rawRestrictedPARuleCoverageFieldCode.
                 apply raw_quotedFormula_atomically_adequate. exact hPA.
              ** unfold rawRestrictedPABottomEndpointFieldCode.
                 apply raw_quotedFormula_atomically_adequate. exact hPA.
Qed.

(** Instantiate the pointwise compiler required by final selected-axiom
    support transport.  Staged prerequisites are irrelevant to this syntax
    fact; the graph trace is used solely for its numeral-term witness. *)
Theorem raw_dynamicTruthNativeFinalBridgeFieldsHeadAdequacyCompiler :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeFinalBridgeFieldsHeadAdequacyCompiler M.
Proof.
  intros M hPA tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    htrace _.
  destruct htrace as [_ _ _ _ _ _ _ hsource].
  destruct hsource as [_ hnumeral _ _].
  exact (raw_restrictedPAProofFieldsCode_atomically_adequate
    M hPA (raw_succ M level) successorNumeralCode hnumeral).
Qed.

End PABoundedRawCodedDynamicTruthNativeFinalBridgeFieldsHeadAdequacy.
