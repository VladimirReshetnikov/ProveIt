(**
  Extend a six-field master common context by a finite batch of fixed PA
  theorems.

  A batch entry packages an ordinary PA formula together with its closed
  [BProv] derivation.  The target seen by the raw model is always the
  translated quotation of that formula under one caller-supplied,
  PA-agreeing template translation.

  The construction deliberately compiles the batch one theorem at a time.
  Each compiler invocation may select its own finite standard PA-axiom
  prefix.  After that choice, all six master roots and all helper roots built
  earlier are transplanted through that *same* prefix.  Consequently the
  final package contains one literal carrier-coded context shared by every
  root, rather than merely extensionally equivalent contexts.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedContextLists
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedRestrictedPAProof
  RawCodedTruthCertificateMasterBaseBridge
  RawCodedDynamicTruthQFBranchExclusivity
  RawCodedDynamicTruthImpBranchExclusivity.

Import ListNotations.

Module PABoundedRawCodedTruthCertificateMasterFixedHelperBatchExtension.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedTruthCertificateMasterBaseBridge.
Import PABoundedRawCodedDynamicTruthQFBranchExclusivity.
Import PABoundedRawCodedDynamicTruthImpBranchExclusivity.

(** A dependent batch entry: the second field proves precisely the formula
    stored in the first field.  Thus a list of entries cannot silently lose
    the ordinary derivations needed by the compiler. *)
Record RawFixedPAHelper : Type := {
  rawFixedPAHelperFormula : formula;
  rawFixedPAHelperBProv :
    Formula.BProv Formula.Ax_s [] rawFixedPAHelperFormula
}.

(** The carrier target attached to one helper.  Keeping this as a named
    definition makes it explicit that the complete batch uses one and the
    same translation, while allowing formulas in different entries. *)
Definition rawFixedPAHelperTranslatedTargetCode
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M)
    (helper : RawFixedPAHelper) : M :=
  rawTemplateFormula translation
    (embedPAFormula (rawFixedPAHelperFormula helper)).

Arguments rawFixedPAHelperTranslatedTargetCode
  M translation helper : clear implicits.

Definition rawFixedPAHelperBatchTranslatedTargetCodes
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M)
    (helpers : list RawFixedPAHelper) : list M :=
  map (rawFixedPAHelperTranslatedTargetCode M translation) helpers.

Arguments rawFixedPAHelperBatchTranslatedTargetCodes
  M translation helpers : clear implicits.

(** A length-indexed-by-construction family of local proof assertions.  Its
    two list arguments must have the same shape; at every position the root
    proves exactly that helper's translated target over the shared context.
    Defining the relation structurally, instead of with an uncorrelated
    membership predicate, preserves multiplicity and order. *)
Fixpoint RawFixedPAHelperBatchLocalProofs
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M)
    (context : M)
    (helpers : list RawFixedPAHelper)
    (roots : list M) : Prop :=
  match helpers, roots with
  | [], [] => True
  | helper :: helperTail, root :: rootTail =>
      RawCodedPALocalProofOf M context
        (rawFixedPAHelperTranslatedTargetCode M translation helper) root /\
      RawFixedPAHelperBatchLocalProofs M translation context
        helperTail rootTail
  | _, _ => False
  end.

Arguments RawFixedPAHelperBatchLocalProofs
  M translation context helpers roots : clear implicits.

(** The structural family really does contain one root per helper. *)
Lemma raw_fixedPAHelperBatchLocalProofs_length : forall
    (M : RawPAModel) translation context helpers roots,
  RawFixedPAHelperBatchLocalProofs M translation context helpers roots ->
  length roots = length helpers.
Proof.
  intros M translation context helpers.
  induction helpers as [| helper helperTail ih]; intros roots hproofs.
  - destruct roots as [| root rootTail].
    + reflexivity.
    + contradiction.
  - destruct roots as [| root rootTail].
    + contradiction.
    + cbn [RawFixedPAHelperBatchLocalProofs] in hproofs.
      destruct hproofs as [_ htail].
      cbn. rewrite (ih rootTail htail). reflexivity.
Qed.

(** Transplant a complete helper family through one chosen standard prefix.
    Each returned root mentions the same explicit prefixed context.  This is
    the induction step needed after compiling the next fixed theorem. *)
Theorem raw_fixedPAHelperBatchLocalProofs_standardPrefix : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall translation prefix baseContext helpers roots,
  RawContextListRealizable M baseContext ->
  RawFixedPAHelperBatchLocalProofs
    M translation baseContext helpers roots ->
  exists prefixedRoots,
    RawFixedPAHelperBatchLocalProofs M translation
      (rawStandardPAAxiomWitnessPrefixContextCode
        M prefix baseContext)
      helpers prefixedRoots.
Proof.
  intros M hPA translation prefix baseContext helpers.
  induction helpers as [| helper helperTail ih]; intros roots hbase hproofs.
  - destruct roots as [| root rootTail].
    + exists []. exact I.
    + contradiction.
  - destruct roots as [| root rootTail].
    + contradiction.
    + cbn [RawFixedPAHelperBatchLocalProofs] in hproofs.
      destruct hproofs as [hroot htail].
      destruct (raw_codedPALocalProofOf_standardPAAxiomWitnessPrefix
        M hPA prefix baseContext
        (rawFixedPAHelperTranslatedTargetCode M translation helper)
        root hbase hroot) as [prefixedRoot hprefixedRoot].
      destruct (ih rootTail hbase htail)
        as [prefixedTail hprefixedTail].
      exists (prefixedRoot :: prefixedTail).
      cbn [RawFixedPAHelperBatchLocalProofs].
      split; [exact hprefixedRoot | exact hprefixedTail].
Qed.

(** The exact common-context interface for six master fields and an ordered
    finite helper batch.  There is one existential [context], and both the
    six individual assertions and the entire helper family refer to it
    syntactically. *)
Definition RawSixFieldMasterCommonContextProofsWithFixedPAHelperBatchOf
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M)
    (field1 field2 field3 field4 field5 finalField : M)
    (helpers : list RawFixedPAHelper) : Prop :=
  exists witnessList context
      root1 root2 root3 root4 root5 finalRoot : M,
    exists helperRoots : list M,
      RawCodedPAAxiomWitnessContext M witnessList context /\
      RawCodedPALocalProofOf M context field1 root1 /\
      RawCodedPALocalProofOf M context field2 root2 /\
      RawCodedPALocalProofOf M context field3 root3 /\
      RawCodedPALocalProofOf M context field4 root4 /\
      RawCodedPALocalProofOf M context field5 root5 /\
      RawCodedPALocalProofOf M context finalField finalRoot /\
      RawFixedPAHelperBatchLocalProofs
        M translation context helpers helperRoots.

Arguments RawSixFieldMasterCommonContextProofsWithFixedPAHelperBatchOf
  M translation field1 field2 field3 field4 field5 finalField helpers
    : clear implicits.

(** Add an arbitrary finite metatheoretic batch of fixed ordinary PA
    theorems.  The recursive call first places the tail in a common context.
    Compiling the head selects one new witness prefix above that context;
    every tail root and all six master roots are then rebuilt through exactly
    that selected prefix.  Consing the freshly compiled head root restores
    the caller's original helper order. *)
Theorem
    raw_sixFieldMasterCommonContextProofsWithFixedPAHelperBatch : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall field1 field2 field3 field4 field5 finalField helpers,
  RawSixFieldMasterCommonContextProofsOf M
    field1 field2 field3 field4 field5 finalField ->
  RawSixFieldMasterCommonContextProofsWithFixedPAHelperBatchOf
    M translation field1 field2 field3 field4 field5 finalField helpers.
Proof.
  intros M hPA translation hagreement
    field1 field2 field3 field4 field5 finalField helpers.
  induction helpers as [| helper helperTail ih]; intro hmaster.
  - unfold RawSixFieldMasterCommonContextProofsOf in hmaster.
    destruct hmaster as
      (witnessList & context & root1 & root2 & root3 & root4 & root5 &
        finalRoot & hwitnessed & hfield1 & hfield2 & hfield3 & hfield4 &
        hfield5 & hfinal).
    unfold RawSixFieldMasterCommonContextProofsWithFixedPAHelperBatchOf.
    exists witnessList, context,
      root1, root2, root3, root4, root5, finalRoot, [].
    split; [exact hwitnessed |].
    split; [exact hfield1 |].
    split; [exact hfield2 |].
    split; [exact hfield3 |].
    split; [exact hfield4 |].
    split; [exact hfield5 |].
    split; [exact hfinal |].
    exact I.
  - pose proof (ih hmaster) as htailPackage.
    unfold RawSixFieldMasterCommonContextProofsWithFixedPAHelperBatchOf
      in htailPackage.
    destruct htailPackage as
      (baseWitnessList & baseContext & root1 & root2 & root3 & root4 &
        root5 & finalRoot & helperRoots & hbaseWitnessed & hfield1 &
        hfield2 & hfield3 & hfield4 & hfield5 & hfinal & hhelperTail).

    pose proof
      (raw_codedPAAxiomWitnessPrefix_context_realizable_of_witnessed
        M baseWitnessList baseContext hbaseWitnessed)
      as hbaseRealizable.

    (* The head compiler alone chooses [prefix].  Its context is subsequently
       reused literally by every transplantation below. *)
    destruct
      (raw_codedTemplatePALocalProofOf_of_BProv_on_witnessed_tail
        M hPA translation hagreement
        baseWitnessList baseContext
        (rawFixedPAHelperFormula helper) hbaseWitnessed
        (rawFixedPAHelperBProv helper))
      as (prefix & helperRoot & hprefixedWitnessed & hhelperProof).

    destruct (raw_codedPALocalProofOf_standardPAAxiomWitnessPrefix
      M hPA prefix baseContext field1 root1
      hbaseRealizable hfield1) as [prefixedRoot1 hprefixed1].
    destruct (raw_codedPALocalProofOf_standardPAAxiomWitnessPrefix
      M hPA prefix baseContext field2 root2
      hbaseRealizable hfield2) as [prefixedRoot2 hprefixed2].
    destruct (raw_codedPALocalProofOf_standardPAAxiomWitnessPrefix
      M hPA prefix baseContext field3 root3
      hbaseRealizable hfield3) as [prefixedRoot3 hprefixed3].
    destruct (raw_codedPALocalProofOf_standardPAAxiomWitnessPrefix
      M hPA prefix baseContext field4 root4
      hbaseRealizable hfield4) as [prefixedRoot4 hprefixed4].
    destruct (raw_codedPALocalProofOf_standardPAAxiomWitnessPrefix
      M hPA prefix baseContext field5 root5
      hbaseRealizable hfield5) as [prefixedRoot5 hprefixed5].
    destruct (raw_codedPALocalProofOf_standardPAAxiomWitnessPrefix
      M hPA prefix baseContext finalField finalRoot
      hbaseRealizable hfinal) as [prefixedFinalRoot hprefixedFinal].
    destruct (raw_fixedPAHelperBatchLocalProofs_standardPrefix
      M hPA translation prefix baseContext helperTail helperRoots
      hbaseRealizable hhelperTail)
      as [prefixedHelperRoots hprefixedHelperTail].

    unfold RawSixFieldMasterCommonContextProofsWithFixedPAHelperBatchOf.
    exists
      (rawStandardPAAxiomWitnessPrefixWitnessListCode
        M prefix baseWitnessList),
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext),
      prefixedRoot1, prefixedRoot2, prefixedRoot3, prefixedRoot4,
      prefixedRoot5, prefixedFinalRoot,
      (helperRoot :: prefixedHelperRoots).
    split; [exact hprefixedWitnessed |].
    split; [exact hprefixed1 |].
    split; [exact hprefixed2 |].
    split; [exact hprefixed3 |].
    split; [exact hprefixed4 |].
    split; [exact hprefixed5 |].
    split; [exact hprefixedFinal |].
    cbn [RawFixedPAHelperBatchLocalProofs].
    split; [exact hhelperProof | exact hprefixedHelperTail].
Qed.

(** A singleton wrapper makes the relation to the one-helper construction
    transparent while retaining the batch API used by later matrix cells. *)
Corollary
    raw_sixFieldMasterCommonContextProofsWithFixedPAHelperSingleton : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall field1 field2 field3 field4 field5 finalField helper,
  RawSixFieldMasterCommonContextProofsOf M
    field1 field2 field3 field4 field5 finalField ->
  RawSixFieldMasterCommonContextProofsWithFixedPAHelperBatchOf
    M translation field1 field2 field3 field4 field5 finalField [helper].
Proof.
  intros M hPA translation hagreement
    field1 field2 field3 field4 field5 finalField helper hmaster.
  exact (raw_sixFieldMasterCommonContextProofsWithFixedPAHelperBatch
    M hPA translation hagreement
    field1 field2 field3 field4 field5 finalField [helper] hmaster).
Qed.

(** ------------------------------------------------------------------
    The first three native collision helpers.

    These entries do not claim that the conditional implication cells have
    discharged their predecessor-state premise.  They package exactly the
    ordinary PA theorems proved by the native QF and implication-cell
    modules: one unconditional QF collision and two conditional implication
    collisions. *)

Definition rawDynamicTruthQFCollisionFixedPAHelper : RawFixedPAHelper :=
  {| rawFixedPAHelperFormula :=
       dynamicTruthQFEx8BranchExclusivityFormula;
     rawFixedPAHelperBProv :=
       PA_proves_dynamicTruthQFEx8BranchExclusivityFormula |}.

Definition rawDynamicTruthImpFalseLeftCollisionFixedPAHelper
    : RawFixedPAHelper :=
  {| rawFixedPAHelperFormula :=
       dynamicTruthImpFalseLeftConditionalCellFormula;
     rawFixedPAHelperBProv :=
       PA_proves_dynamicTruthImpFalseLeftConditionalCellFormula |}.

Definition rawDynamicTruthImpTrueRightCollisionFixedPAHelper
    : RawFixedPAHelper :=
  {| rawFixedPAHelperFormula :=
       dynamicTruthImpTrueRightConditionalCellFormula;
     rawFixedPAHelperBProv :=
       PA_proves_dynamicTruthImpTrueRightConditionalCellFormula |}.

Definition rawDynamicTruthFirstThreeCollisionFixedPAHelpers
    : list RawFixedPAHelper :=
  [ rawDynamicTruthQFCollisionFixedPAHelper;
    rawDynamicTruthImpFalseLeftCollisionFixedPAHelper;
    rawDynamicTruthImpTrueRightCollisionFixedPAHelper ].

(** All three carrier targets are translated by the same value
    [translation].  Agreement exposes them simultaneously as ordinary PA
    quotations; later native-code equations may rewrite these quotations
    without changing their common proof context. *)
Lemma rawDynamicTruthFirstThreeCollisionFixedPAHelperTargets_eq_quoted :
    forall (M : RawPAModel)
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  rawFixedPAHelperBatchTranslatedTargetCodes M translation
    rawDynamicTruthFirstThreeCollisionFixedPAHelpers =
  [ rawQuotedFormulaCode M
      dynamicTruthQFEx8BranchExclusivityFormula;
    rawQuotedFormulaCode M
      dynamicTruthImpFalseLeftConditionalCellFormula;
    rawQuotedFormulaCode M
      dynamicTruthImpTrueRightConditionalCellFormula ].
Proof.
  intros M translation hagreement.
  unfold rawFixedPAHelperBatchTranslatedTargetCodes,
    rawDynamicTruthFirstThreeCollisionFixedPAHelpers,
    rawDynamicTruthQFCollisionFixedPAHelper,
    rawDynamicTruthImpFalseLeftCollisionFixedPAHelper,
    rawDynamicTruthImpTrueRightCollisionFixedPAHelper,
    rawFixedPAHelperTranslatedTargetCode.
  cbn [map rawFixedPAHelperFormula].
  repeat rewrite (rawTemplateFormula_embedPA hagreement).
  reflexivity.
Qed.

(** Concrete three-helper interface.  It is a direct instance of the generic
    batch theorem, so all nine roots share one literal synchronized context. *)
Corollary
    raw_sixFieldMasterCommonContextProofsWithFirstThreeCollisionHelpers :
    forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall field1 field2 field3 field4 field5 finalField,
  RawSixFieldMasterCommonContextProofsOf M
    field1 field2 field3 field4 field5 finalField ->
  RawSixFieldMasterCommonContextProofsWithFixedPAHelperBatchOf
    M translation field1 field2 field3 field4 field5 finalField
    rawDynamicTruthFirstThreeCollisionFixedPAHelpers.
Proof.
  intros M hPA translation hagreement
    field1 field2 field3 field4 field5 finalField hmaster.
  exact (raw_sixFieldMasterCommonContextProofsWithFixedPAHelperBatch
    M hPA translation hagreement
    field1 field2 field3 field4 field5 finalField
    rawDynamicTruthFirstThreeCollisionFixedPAHelpers hmaster).
Qed.

End PABoundedRawCodedTruthCertificateMasterFixedHelperBatchExtension.
