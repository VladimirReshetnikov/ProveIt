(**
  Add the native quantifier-free Ex8 collision helper to a six-field master
  common context.

  The generic fixed-helper extension produces a translated quotation of an
  ordinary PA theorem.  Here that theorem is the exact Ex8 branch-collision
  implication from [RawCodedDynamicTruthQFBranchExclusivity].  Agreement with
  ordinary PA quotation, followed by the native-code quotation equation,
  changes only the displayed conclusion of the seventh local proof; its root
  and its synchronized prefixed context are retained verbatim.

  The final theorem has no translation premise.  It constructs a harmless
  structural translation whose named parameters denote the represented zero
  term and whose opaque formula leaves denote bottom.  Embedded ordinary PA
  syntax contains neither kind of leaf, so the standard structural agreement
  theorem applies.  Existing numeral-term traces and one-node bottom trees
  discharge all operation fields; no new shift or substitution machinery is
  introduced here.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFormulaShiftTreeRealization
  RawCodedNumeralTermCode
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateStructuralPAAgreement
  RawCodedTemplateNumeralParameters
  RawCodedTruthCertificateMasterBaseBridge
  RawCodedTruthCertificateMasterFixedHelperExtension
  RawCodedDynamicTruthQFBranchExclusivity.

Import ListNotations.

Module PABoundedRawCodedTruthCertificateMasterQFHelperExtension.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaShiftTreeRealization.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateStructuralPAAgreement.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTruthCertificateMasterBaseBridge.
Import PABoundedRawCodedTruthCertificateMasterFixedHelperExtension.
Import PABoundedRawCodedDynamicTruthQFBranchExclusivity.

(** The native seven-root interface.  Its seventh conclusion is literally
    [rawDynamicTruthQFEx8BranchExclusivityCode M], rather than a translated
    template expression or merely an extensionally equivalent formula code. *)
Definition RawSixFieldMasterCommonContextProofsWithQFHelperOf
    (M : RawPAModel)
    (field1 field2 field3 field4 field5 finalField : M) : Prop :=
  exists witnessList context
      root1 root2 root3 root4 root5 finalRoot qfHelperRoot : M,
    RawCodedPAAxiomWitnessContext M witnessList context /\
    RawCodedPALocalProofOf M context field1 root1 /\
    RawCodedPALocalProofOf M context field2 root2 /\
    RawCodedPALocalProofOf M context field3 root3 /\
    RawCodedPALocalProofOf M context field4 root4 /\
    RawCodedPALocalProofOf M context field5 root5 /\
    RawCodedPALocalProofOf M context finalField finalRoot /\
    RawCodedPALocalProofOf M context
      (rawDynamicTruthQFEx8BranchExclusivityCode M) qfHelperRoot.

Arguments RawSixFieldMasterCommonContextProofsWithQFHelperOf
  M field1 field2 field3 field4 field5 finalField : clear implicits.

(** Any PA-agreeing translation suffices for the native specialization.
    This intermediate theorem isolates the only two target equalities used
    after invoking the generic fixed-helper extension. *)
Theorem
    raw_sixFieldMasterCommonContextProofsWithQFHelper_of_agreement : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall field1 field2 field3 field4 field5 finalField,
  RawSixFieldMasterCommonContextProofsOf M
    field1 field2 field3 field4 field5 finalField ->
  RawSixFieldMasterCommonContextProofsWithQFHelperOf M
    field1 field2 field3 field4 field5 finalField.
Proof.
  intros M hPA translation hagreement
    field1 field2 field3 field4 field5 finalField hmaster.
  pose proof
    (raw_sixFieldMasterCommonContextProofsWithFixedPAHelper_of_BProv
      M hPA translation hagreement
      field1 field2 field3 field4 field5 finalField
      dynamicTruthQFEx8BranchExclusivityFormula
      hmaster PA_proves_dynamicTruthQFEx8BranchExclusivityFormula)
    as hextended.
  unfold RawSixFieldMasterCommonContextProofsWithFixedPAHelperOf
    in hextended.
  destruct hextended as
    (witnessList & context & root1 & root2 & root3 & root4 & root5 &
      finalRoot & qfHelperRoot & hwitnessed & hfield1 & hfield2 & hfield3 &
      hfield4 & hfield5 & hfinal & hqfHelper).

  (* First expose the ordinary quotation selected by template agreement;
     then orient the native-code equation toward that quotation. *)
  rewrite (rawTemplateFormula_embedPA hagreement
    dynamicTruthQFEx8BranchExclusivityFormula) in hqfHelper.
  rewrite <- (rawDynamicTruthQFEx8BranchExclusivityCode_eq_quoted
    M hPA) in hqfHelper.

  unfold RawSixFieldMasterCommonContextProofsWithQFHelperOf.
  exists witnessList, context,
    root1, root2, root3, root4, root5, finalRoot, qfHelperRoot.
  split; [exact hwitnessed |].
  split; [exact hfield1 |].
  split; [exact hfield2 |].
  split; [exact hfield3 |].
  split; [exact hfield4 |].
  split; [exact hfield5 |].
  split; [exact hfinal |].
  exact hqfHelper.
Qed.

(** ------------------------------------------------------------------
    A concrete PA-agreeing translation for the unconditional endpoint. *)

(** Every named parameter denotes one already witnessed code of the zero
    numeral term.  The same trace may be reused for every metasyntactic name. *)
Local Definition rawQFHelperZeroNumeralParameters
    (M : RawPAModel) (zeroTermCode : M)
    (hzeroTermCode :
      RawNumeralTermCodeAt M (raw_zero M) zeroTermCode)
    : RawCodedTemplateNumeralParameters M :=
  {| rawNumeralTemplateParameterBound := fun _ => raw_zero M;
     rawNumeralTemplateParameterCode := fun _ => zeroTermCode;
     rawNumeralTemplateParameter_valid := fun _ => hzeroTermCode |}.

(** All opaque applications map to bottom.  Their shift/open trees are the
    corresponding one-node bottom trees at the requested depth.  The term
    fields are exactly the reusable numeral-parameter trace theorems. *)
Local Definition rawQFHelperBottomStructuralInputs
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (parameters : RawCodedTemplateNumeralParameters M)
    : RawCodedTemplateStructuralInputs M.
Proof.
  pose (opaqueCode :=
    fun (_ : TemplatePredicateName) (_ : list M) => rawFormulaBotCode M).
  refine
    {| rawStructuralTemplateSymbols :=
         rawNumeralTemplateSymbols M parameters opaqueCode;
       rawStructuralTemplateTermShiftAt := _;
       rawStructuralTemplateTermOpeningAt := _;
       rawStructuralTemplateOpaqueShiftTree :=
         fun depth _ _ => RFSTBot M (rawNumeralValue M depth);
       rawStructuralTemplateOpaqueShiftTree_depth := _;
       rawStructuralTemplateOpaqueShiftTree_source := _;
       rawStructuralTemplateOpaqueShiftTree_target := _;
       rawStructuralTemplateOpaqueShiftTree_valid := _;
       rawStructuralTemplateOpaqueOpenTree :=
         fun depth _ _ _ => RFSTBot M (rawNumeralValue M depth);
       rawStructuralTemplateOpaqueOpenTree_depth := _;
       rawStructuralTemplateOpaqueOpenTree_source := _;
       rawStructuralTemplateOpaqueOpenTree_target := _;
       rawStructuralTemplateOpaqueOpenTree_valid := _ |}.
  - exact (raw_numeralTemplateTerm_shift M hPA parameters opaqueCode).
  - exact (raw_numeralTemplateTerm_substitutionAtom
      M hPA parameters opaqueCode).
  - intros. reflexivity.
  - intros. reflexivity.
  - intros. reflexivity.
  - intros. exact I.
  - intros. reflexivity.
  - intros. reflexivity.
  - intros. reflexivity.
  - intros. exact I.
Defined.

(** Translation-free public specialization.  Represented induction supplies
    one honest zero-term code; the structural realizer turns the finite
    bottom-fallback syntax above into a complete template translation. *)
Theorem raw_sixFieldMasterCommonContextProofsWithQFHelper : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall field1 field2 field3 field4 field5 finalField,
  RawSixFieldMasterCommonContextProofsOf M
    field1 field2 field3 field4 field5 finalField ->
  RawSixFieldMasterCommonContextProofsWithQFHelperOf M
    field1 field2 field3 field4 field5 finalField.
Proof.
  intros M hPA field1 field2 field3 field4 field5 finalField hmaster.
  destruct (raw_numeralTermCodeExists_zero M hPA)
    as [zeroTermCode hzeroTermCode].
  set (parameters := rawQFHelperZeroNumeralParameters
    M zeroTermCode hzeroTermCode).
  set (inputs := rawQFHelperBottomStructuralInputs M hPA parameters).
  set (translation := rawStructuralTemplateTranslation M hPA inputs).
  apply
    (raw_sixFieldMasterCommonContextProofsWithQFHelper_of_agreement
      M hPA translation).
  - unfold translation.
    exact (rawStructuralTemplatePAAgreement M hPA inputs).
  - exact hmaster.
Qed.

End PABoundedRawCodedTruthCertificateMasterQFHelperExtension.
