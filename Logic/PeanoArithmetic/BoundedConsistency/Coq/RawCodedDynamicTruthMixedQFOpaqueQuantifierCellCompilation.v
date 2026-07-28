(**
  Transparent compilation of the two lower-dependent mixed-QF cells.

  The ordinary fixed-bottom instances of these cells are PA theorems.  The
  only new logical observation needed at an opaque lower application is
  monotonicity of the negative binder side:

      exists^8 (P and not (exists^3 (Q and opaque)))
        -> exists^8 (P and not (exists^3 (Q and bottom))).

  The proof below preserves the eight witnesses and rebuilds the negative
  component without inspecting the opaque atom.  Consequently it can be
  translated directly at an arbitrary carrier code whenever the exact
  shift/open trace for that atom is supplied.  No carrier code is decoded,
  and no semantic validity or completeness principle is used by the
  transport compiler.

  For synchronized master clients, the two fixed-bottom collision theorems
  are appended as explicit [RawFixedPAHelper] seeds after the established
  thirty-eight-helper batch.  Both transported roots then inhabit literally
  the same witnessed PA context as all six master roots and all forty helper
  roots.
*)

From Stdlib Require Import List Arith.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedContextShift
  RawCodedRestrictedPAProof
  RawCodedPAProvability
  RawCodedPAProofImpICertificates
  RawCodedPAAxiomContextSelfShift
  RawCodedProofBinaryConstructors
  RawCodedPALocalProofExistential
  RawCodedPAProofBinaryCertificates
  RawCodedPALocalProofComposition
  RawCodedTemplateSyntax
  RawCodedTemplateLogicalSchemas
  RawCodedTemplateProjectionSchemas
  RawCodedTemplateProofCompiler
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedFixedLevelTruthTotality
  RawCodedTruthCertificateMasterBaseBridge
  RawCodedTruthCertificateMasterFixedHelperBatchExtension
  RawCodedTruthCertificateMasterMixedQFHelperBatch
  RawCodedDynamicTruthQFBranchExclusivity
  RawCodedDynamicTruthUniversalLeafSourceTemplate
  RawCodedDynamicTruthPiUniversalLeafSourceTemplate
  RawCodedDynamicTruthQuantifierBranchExclusivity
  RawCodedDynamicTruthQuantifierConditionalCellCompilation
  RawCodedDynamicTruthMixedQFBranchExclusivity.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthMixedQFOpaqueQuantifierCellCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPAProofImpICertificates.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPAProofBinaryCertificates.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateLogicalSchemas.
Import PABoundedRawCodedTemplateProjectionSchemas.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedTruthCertificateMasterBaseBridge.
Import PABoundedRawCodedTruthCertificateMasterFixedHelperBatchExtension.
Import PABoundedRawCodedTruthCertificateMasterMixedQFHelperBatch.
Import PABoundedRawCodedDynamicTruthQFBranchExclusivity.
Import PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthPiUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthQuantifierBranchExclusivity.
Import PABoundedRawCodedDynamicTruthQuantifierConditionalCellCompilation.
Import PABoundedRawCodedDynamicTruthMixedQFBranchExclusivity.

(** ------------------------------------------------------------------
    Pure logical transport through two existential towers. *)

(** Eliminate an existential tower whose innermost conjunction contains
    bottom.  At a successor step the conclusion is bottom, so the eigenbody
    endpoint is invariant under the mandatory one-variable renaming. *)
Fixpoint templateRepeatedExistsBottomFrom
    (binderCount : nat) (context : TemplateContext)
    (prefix : TemplateFormula) (sourceProof : TemplateRawProof)
    : TemplateRawProof :=
  match binderCount with
  | 0 =>
      trpAndE2 context prefix tfBot sourceProof
  | S smaller =>
      let sourceBody :=
        templateRepeatedExists smaller (tfAnd prefix tfBot) in
      let eigenContext := sourceBody :: templateContextShift context in
      trpExE context sourceBody tfBot sourceProof
        (templateRepeatedExistsBottomFrom smaller eigenContext prefix
          (trpAss eigenContext sourceBody))
  end.

Theorem templateRepeatedExistsBottomFrom_derives : forall
    binderCount context prefix sourceProof,
  TemplateRawDerives context
    (templateRepeatedExists binderCount (tfAnd prefix tfBot)) sourceProof ->
  TemplateRawDerives context tfBot
    (templateRepeatedExistsBottomFrom
      binderCount context prefix sourceProof).
Proof.
  induction binderCount as [| smaller ih];
    intros context prefix sourceProof hsource.
  - cbn [templateRepeatedExistsBottomFrom templateRepeatedExists].
    destruct hsource as [hvalid [hcontext hconclusion]].
    unfold TemplateRawDerives.
    cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
    repeat split; assumption.
  - cbn [templateRepeatedExistsBottomFrom templateRepeatedExists].
    set (sourceBody :=
      templateRepeatedExists smaller (tfAnd prefix tfBot)).
    set (eigenContext := sourceBody :: templateContextShift context).
    assert (hassumption : TemplateRawDerives eigenContext sourceBody
        (trpAss eigenContext sourceBody)).
    { apply templateRawDerives_assumption. left. reflexivity. }
    pose proof (ih eigenContext prefix
      (trpAss eigenContext sourceBody) hassumption) as hbottom.
    destruct hsource as [hsourceValid [hsourceContext hsourceConclusion]].
    destruct hbottom as
      [hbottomValid [hbottomContext hbottomConclusion]].
    unfold TemplateRawDerives.
    cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
    repeat split; try assumption; try reflexivity.
Qed.

(** The negative fixed-bottom counterexample is derivable in every context.
    Keeping the context as an argument is essential: the proof is later
    rebuilt under the eight successive eigenvariable contexts. *)
Definition templateNoBottomCounterexampleProof
    (binderCount : nat) (context : TemplateContext)
    (prefix : TemplateFormula) : TemplateRawProof :=
  let counterexample :=
    templateRepeatedExists binderCount (tfAnd prefix tfBot) in
  let assumptionContext := counterexample :: context in
  trpImpI context counterexample tfBot
    (templateRepeatedExistsBottomFrom binderCount assumptionContext prefix
      (trpAss assumptionContext counterexample)).

Theorem templateNoBottomCounterexampleProof_derives : forall
    binderCount context prefix,
  TemplateRawDerives context
    (tfImp
      (templateRepeatedExists binderCount (tfAnd prefix tfBot)) tfBot)
    (templateNoBottomCounterexampleProof binderCount context prefix).
Proof.
  intros binderCount context prefix.
  unfold templateNoBottomCounterexampleProof.
  set (counterexample :=
    templateRepeatedExists binderCount (tfAnd prefix tfBot)).
  assert (hassumption : TemplateRawDerives
      (counterexample :: context) counterexample
      (trpAss (counterexample :: context) counterexample)).
  { apply templateRawDerives_assumption. left. reflexivity. }
  pose proof (templateRepeatedExistsBottomFrom_derives binderCount
    (counterexample :: context) prefix
    (trpAss (counterexample :: context) counterexample) hassumption)
    as hbottom.
  destruct hbottom as [hvalid [hcontext hconclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; assumption.
Qed.

(** Preserve every outer witness while replacing an arbitrary negative
    component by the fixed-bottom negative component.  The source negative
    formula is deliberately opaque to this construction. *)
Fixpoint templateRepeatedExistsFixBottomNegativeFrom
    (outerBinders innerBinders : nat)
    (context : TemplateContext)
    (outerPrefix sourceNegative innerPrefix : TemplateFormula)
    (sourceProof : TemplateRawProof) : TemplateRawProof :=
  match outerBinders with
  | 0 =>
      trpAndI context outerPrefix
        (tfImp
          (templateRepeatedExists innerBinders
            (tfAnd innerPrefix tfBot)) tfBot)
        (trpAndE1 context outerPrefix sourceNegative sourceProof)
        (templateNoBottomCounterexampleProof
          innerBinders context innerPrefix)
  | S smaller =>
      let sourceBody := templateRepeatedExists smaller
        (tfAnd outerPrefix sourceNegative) in
      let fixedNegative := tfImp
        (templateRepeatedExists innerBinders
          (tfAnd innerPrefix tfBot)) tfBot in
      let targetBody := templateRepeatedExists smaller
        (tfAnd outerPrefix fixedNegative) in
      let eigenContext := sourceBody :: templateContextShift context in
      let transportedBody :=
        templateRepeatedExistsFixBottomNegativeFrom
          smaller innerBinders eigenContext
          outerPrefix sourceNegative innerPrefix
          (trpAss eigenContext sourceBody) in
      let preservedWitness :=
        trpExI eigenContext
          (templateFormulaRename (templateUpRenaming S) targetBody)
          (ttVar 0) transportedBody in
      trpExE context sourceBody (tfEx targetBody)
        sourceProof preservedWitness
  end.

Theorem templateRepeatedExistsFixBottomNegativeFrom_derives : forall
    outerBinders innerBinders context
    outerPrefix sourceNegative innerPrefix sourceProof,
  TemplateRawDerives context
    (templateRepeatedExists outerBinders
      (tfAnd outerPrefix sourceNegative)) sourceProof ->
  TemplateRawDerives context
    (templateRepeatedExists outerBinders
      (tfAnd outerPrefix
        (tfImp
          (templateRepeatedExists innerBinders
            (tfAnd innerPrefix tfBot)) tfBot)))
    (templateRepeatedExistsFixBottomNegativeFrom
      outerBinders innerBinders context
      outerPrefix sourceNegative innerPrefix sourceProof).
Proof.
  induction outerBinders as [| smaller ih];
    intros innerBinders context outerPrefix sourceNegative
      innerPrefix sourceProof hsource.
  - cbn [templateRepeatedExistsFixBottomNegativeFrom
      templateRepeatedExists].
    pose proof (templateNoBottomCounterexampleProof_derives
      innerBinders context innerPrefix) as hnegative.
    destruct hsource as [hsourceValid [hsourceContext hsourceConclusion]].
    destruct hnegative as
      [hnegativeValid [hnegativeContext hnegativeConclusion]].
    unfold templateNoBottomCounterexampleProof in
      hnegativeValid, hnegativeContext, hnegativeConclusion.
    cbn [TemplateRawProofValid templateRawContext templateRawConclusion]
      in hnegativeValid, hnegativeContext, hnegativeConclusion.
    destruct hnegativeValid as
      [hbottomValid [hbottomContext hbottomConclusion]].
    unfold TemplateRawDerives.
    cbn [TemplateRawProofValid templateRawContext templateRawConclusion]
      in hsourceValid, hsourceContext, hsourceConclusion,
        hnegativeContext, hnegativeConclusion |-.
    repeat split; try assumption; try reflexivity.
  - cbn [templateRepeatedExistsFixBottomNegativeFrom
      templateRepeatedExists].
    set (sourceBody := templateRepeatedExists smaller
      (tfAnd outerPrefix sourceNegative)).
    set (fixedNegative := tfImp
      (templateRepeatedExists innerBinders
        (tfAnd innerPrefix tfBot)) tfBot).
    set (targetBody := templateRepeatedExists smaller
      (tfAnd outerPrefix fixedNegative)).
    set (eigenContext := sourceBody :: templateContextShift context).
    assert (hassumption : TemplateRawDerives eigenContext sourceBody
        (trpAss eigenContext sourceBody)).
    { apply templateRawDerives_assumption. left. reflexivity. }
    pose proof (ih innerBinders eigenContext outerPrefix sourceNegative
      innerPrefix (trpAss eigenContext sourceBody) hassumption)
      as htransported.
    destruct hsource as [hsourceValid [hsourceContext hsourceConclusion]].
    destruct htransported as
      [htransportedValid [htransportedContext htransportedConclusion]].
    unfold TemplateRawDerives.
    cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
    rewrite templateFormulaOpen_binderShift_zero.
    repeat split; try assumption; try reflexivity.
Qed.

(** ------------------------------------------------------------------
    Concrete branch and cell transports. *)

Definition coqDynamicTruthPiExistentialFixedBottomCounterexampleTemplate
    : TemplateFormula :=
  templateRepeatedExists 3
    (tfAnd coqDynamicTruthPiBinderPrependTemplate tfBot).

Definition coqDynamicTruthPiExistentialFixedBottomEx8BranchTemplate
    : TemplateFormula :=
  templateRepeatedExists 8
    (tfAnd coqDynamicTruthPiExistentialPrefixTemplate
      (tfImp
        coqDynamicTruthPiExistentialFixedBottomCounterexampleTemplate
        tfBot)).

Definition coqDynamicTruthSigmaUniversalFixedBottomCounterexampleTemplate
    : TemplateFormula :=
  templateRepeatedExists 3
    (tfAnd coqDynamicTruthSigmaBinderPrependTemplate tfBot).

Definition coqDynamicTruthSigmaUniversalFixedBottomEx8BranchTemplate
    : TemplateFormula :=
  templateRepeatedExists 8
    (tfAnd coqDynamicTruthSigmaUniversalPrefixTemplate
      (tfImp
        coqDynamicTruthSigmaUniversalFixedBottomCounterexampleTemplate
        tfBot)).

Definition coqDynamicTruthSigmaQFEx8BranchTemplate : TemplateFormula :=
  embedPAFormula dynamicTruthSigmaQFEx8BranchFormula.

Definition coqDynamicTruthPiQFEx8BranchTemplate : TemplateFormula :=
  embedPAFormula dynamicTruthPiQFEx8BranchFormula.

Definition coqDynamicTruthSigmaQFPiExFixedBottomCellTemplate
    : TemplateFormula :=
  tfImp coqDynamicTruthSigmaQFEx8BranchTemplate
    (tfImp coqDynamicTruthPiExistentialFixedBottomEx8BranchTemplate tfBot).

Definition coqDynamicTruthSigmaQFPiExOpaqueCellTemplate
    : TemplateFormula :=
  tfImp coqDynamicTruthSigmaQFEx8BranchTemplate
    (tfImp coqDynamicTruthPiExistentialEx8BranchTemplate tfBot).

Definition coqDynamicTruthSigmaAllPiQFFixedBottomCellTemplate
    : TemplateFormula :=
  tfImp coqDynamicTruthSigmaUniversalFixedBottomEx8BranchTemplate
    (tfImp coqDynamicTruthPiQFEx8BranchTemplate tfBot).

Definition coqDynamicTruthSigmaAllPiQFOpaqueCellTemplate
    : TemplateFormula :=
  tfImp coqDynamicTruthSigmaUniversalEx8BranchTemplate
    (tfImp coqDynamicTruthPiQFEx8BranchTemplate tfBot).

(** A source branch proves its fixed-bottom sibling. *)
Definition coqDynamicTruthPiExistentialOpaqueToFixedFrom
    (context : TemplateContext) (sourceProof : TemplateRawProof)
    : TemplateRawProof :=
  templateRepeatedExistsFixBottomNegativeFrom 8 3 context
    coqDynamicTruthPiExistentialPrefixTemplate
    (tfImp coqDynamicTruthPiExistentialCounterexampleTemplate tfBot)
    coqDynamicTruthPiBinderPrependTemplate sourceProof.

Definition coqDynamicTruthSigmaUniversalOpaqueToFixedFrom
    (context : TemplateContext) (sourceProof : TemplateRawProof)
    : TemplateRawProof :=
  templateRepeatedExistsFixBottomNegativeFrom 8 3 context
    coqDynamicTruthSigmaUniversalPrefixTemplate
    (tfImp coqDynamicTruthSigmaUniversalCounterexampleTemplate tfBot)
    coqDynamicTruthSigmaBinderPrependTemplate sourceProof.

Theorem coqDynamicTruthPiExistentialOpaqueToFixedFrom_derives : forall
    context sourceProof,
  TemplateRawDerives context
    coqDynamicTruthPiExistentialEx8BranchTemplate sourceProof ->
  TemplateRawDerives context
    coqDynamicTruthPiExistentialFixedBottomEx8BranchTemplate
    (coqDynamicTruthPiExistentialOpaqueToFixedFrom context sourceProof).
Proof.
  intros context sourceProof hsource.
  unfold coqDynamicTruthPiExistentialOpaqueToFixedFrom,
    coqDynamicTruthPiExistentialEx8BranchTemplate,
    coqDynamicTruthPiExistentialCounterexampleTemplate,
    coqDynamicTruthPiExistentialFixedBottomEx8BranchTemplate,
    coqDynamicTruthPiExistentialFixedBottomCounterexampleTemplate.
  exact (templateRepeatedExistsFixBottomNegativeFrom_derives
    8 3 context coqDynamicTruthPiExistentialPrefixTemplate
    (tfImp
      (templateRepeatedExists 3
        (tfAnd coqDynamicTruthPiBinderPrependTemplate
          coqDynamicTruthLowerSigmaAtomTemplate)) tfBot)
    coqDynamicTruthPiBinderPrependTemplate sourceProof hsource).
Qed.

Theorem coqDynamicTruthSigmaUniversalOpaqueToFixedFrom_derives : forall
    context sourceProof,
  TemplateRawDerives context
    coqDynamicTruthSigmaUniversalEx8BranchTemplate sourceProof ->
  TemplateRawDerives context
    coqDynamicTruthSigmaUniversalFixedBottomEx8BranchTemplate
    (coqDynamicTruthSigmaUniversalOpaqueToFixedFrom context sourceProof).
Proof.
  intros context sourceProof hsource.
  unfold coqDynamicTruthSigmaUniversalOpaqueToFixedFrom,
    coqDynamicTruthSigmaUniversalEx8BranchTemplate,
    coqDynamicTruthSigmaUniversalCounterexampleTemplate,
    coqDynamicTruthSigmaUniversalFixedBottomEx8BranchTemplate,
    coqDynamicTruthSigmaUniversalFixedBottomCounterexampleTemplate.
  exact (templateRepeatedExistsFixBottomNegativeFrom_derives
    8 3 context coqDynamicTruthSigmaUniversalPrefixTemplate
    (tfImp
      (templateRepeatedExists 3
        (tfAnd coqDynamicTruthSigmaBinderPrependTemplate
          coqDynamicTruthLowerPiAtomTemplate)) tfBot)
    coqDynamicTruthSigmaBinderPrependTemplate sourceProof hsource).
Qed.

(** From the fixed collision, consume the opaque branch only after replacing
    it by its fixed-bottom sibling. *)
Definition coqDynamicTruthSigmaQFPiExOpaqueCellTransportProof
    : TemplateRawProof :=
  let fixedCell := coqDynamicTruthSigmaQFPiExFixedBottomCellTemplate in
  let sigmaBranch := coqDynamicTruthSigmaQFEx8BranchTemplate in
  let opaqueBranch := coqDynamicTruthPiExistentialEx8BranchTemplate in
  let fixedBranch :=
    coqDynamicTruthPiExistentialFixedBottomEx8BranchTemplate in
  let fixedContext := [fixedCell] in
  let sigmaContext := sigmaBranch :: fixedContext in
  let opaqueContext := opaqueBranch :: sigmaContext in
  let fixedProof := trpAss opaqueContext fixedCell in
  let sigmaProof := trpAss opaqueContext sigmaBranch in
  let opaqueProof := trpAss opaqueContext opaqueBranch in
  let fixedBranchProof :=
    coqDynamicTruthPiExistentialOpaqueToFixedFrom
      opaqueContext opaqueProof in
  let fixedTailProof :=
    trpImpE opaqueContext sigmaBranch
      (tfImp fixedBranch tfBot) fixedProof sigmaProof in
  let bottomProof :=
    trpImpE opaqueContext fixedBranch tfBot
      fixedTailProof fixedBranchProof in
  trpImpI [] fixedCell coqDynamicTruthSigmaQFPiExOpaqueCellTemplate
    (trpImpI fixedContext sigmaBranch
      (tfImp opaqueBranch tfBot)
      (trpImpI sigmaContext opaqueBranch tfBot bottomProof)).

Theorem coqDynamicTruthSigmaQFPiExOpaqueCellTransportProof_derives :
  TemplateRawDerives []
    (tfImp coqDynamicTruthSigmaQFPiExFixedBottomCellTemplate
      coqDynamicTruthSigmaQFPiExOpaqueCellTemplate)
    coqDynamicTruthSigmaQFPiExOpaqueCellTransportProof.
Proof.
  unfold coqDynamicTruthSigmaQFPiExOpaqueCellTransportProof.
  set (fixedCell := coqDynamicTruthSigmaQFPiExFixedBottomCellTemplate).
  set (sigmaBranch := coqDynamicTruthSigmaQFEx8BranchTemplate).
  set (opaqueBranch := coqDynamicTruthPiExistentialEx8BranchTemplate).
  set (fixedBranch :=
    coqDynamicTruthPiExistentialFixedBottomEx8BranchTemplate).
  set (fixedContext := [fixedCell]).
  set (sigmaContext := sigmaBranch :: fixedContext).
  set (opaqueContext := opaqueBranch :: sigmaContext).
  assert (hopaque : TemplateRawDerives opaqueContext opaqueBranch
      (trpAss opaqueContext opaqueBranch)).
  { apply templateRawDerives_assumption. left. reflexivity. }
  pose proof (coqDynamicTruthPiExistentialOpaqueToFixedFrom_derives
    opaqueContext (trpAss opaqueContext opaqueBranch) hopaque)
    as hfixedBranch.
  destruct hfixedBranch as
    [hfixedBranchValid [hfixedBranchContext hfixedBranchConclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; try assumption; try reflexivity; auto.
  all: unfold opaqueContext, sigmaContext, fixedContext;
    cbn; auto.
Qed.

Definition coqDynamicTruthSigmaAllPiQFOpaqueCellTransportProof
    : TemplateRawProof :=
  let fixedCell := coqDynamicTruthSigmaAllPiQFFixedBottomCellTemplate in
  let opaqueBranch := coqDynamicTruthSigmaUniversalEx8BranchTemplate in
  let fixedBranch :=
    coqDynamicTruthSigmaUniversalFixedBottomEx8BranchTemplate in
  let piBranch := coqDynamicTruthPiQFEx8BranchTemplate in
  let fixedContext := [fixedCell] in
  let opaqueContext := opaqueBranch :: fixedContext in
  let piContext := piBranch :: opaqueContext in
  let fixedProof := trpAss piContext fixedCell in
  let opaqueProof := trpAss piContext opaqueBranch in
  let piProof := trpAss piContext piBranch in
  let fixedBranchProof :=
    coqDynamicTruthSigmaUniversalOpaqueToFixedFrom
      piContext opaqueProof in
  let fixedTailProof :=
    trpImpE piContext fixedBranch (tfImp piBranch tfBot)
      fixedProof fixedBranchProof in
  let bottomProof :=
    trpImpE piContext piBranch tfBot fixedTailProof piProof in
  trpImpI [] fixedCell coqDynamicTruthSigmaAllPiQFOpaqueCellTemplate
    (trpImpI fixedContext opaqueBranch (tfImp piBranch tfBot)
      (trpImpI opaqueContext piBranch tfBot bottomProof)).

Theorem coqDynamicTruthSigmaAllPiQFOpaqueCellTransportProof_derives :
  TemplateRawDerives []
    (tfImp coqDynamicTruthSigmaAllPiQFFixedBottomCellTemplate
      coqDynamicTruthSigmaAllPiQFOpaqueCellTemplate)
    coqDynamicTruthSigmaAllPiQFOpaqueCellTransportProof.
Proof.
  unfold coqDynamicTruthSigmaAllPiQFOpaqueCellTransportProof.
  set (fixedCell := coqDynamicTruthSigmaAllPiQFFixedBottomCellTemplate).
  set (opaqueBranch := coqDynamicTruthSigmaUniversalEx8BranchTemplate).
  set (fixedBranch :=
    coqDynamicTruthSigmaUniversalFixedBottomEx8BranchTemplate).
  set (piBranch := coqDynamicTruthPiQFEx8BranchTemplate).
  set (fixedContext := [fixedCell]).
  set (opaqueContext := opaqueBranch :: fixedContext).
  set (piContext := piBranch :: opaqueContext).
  assert (hopaque : TemplateRawDerives piContext opaqueBranch
      (trpAss piContext opaqueBranch)).
  { apply templateRawDerives_assumption. right. left. reflexivity. }
  pose proof (coqDynamicTruthSigmaUniversalOpaqueToFixedFrom_derives
    piContext (trpAss piContext opaqueBranch) hopaque)
    as hfixedBranch.
  destruct hfixedBranch as
    [hfixedBranchValid [hfixedBranchContext hfixedBranchConclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; try assumption; try reflexivity; auto.
  all: unfold piContext, opaqueContext, fixedContext;
    cbn; auto.
Qed.

(** ------------------------------------------------------------------
    Direct translation equations. *)

Theorem rawDirect_dynamicTruthSigmaQFPiExFixedBottomCellTemplate_identified :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      lowerApplication
      (trace : RawDynamicTruthQuantifierLowerApplicationDirectTrace
        M lowerApplication),
  rawDirectTemplateFormula
    (rawDynamicTruthQuantifierLowerApplication_inputs trace)
    coqDynamicTruthSigmaQFPiExFixedBottomCellTemplate =
  rawDynamicTruthMixedQFCellCode M DTMQFSigmaQFPiEx
    (rawFormulaBotCode M) (rawFormulaBotCode M).
Proof.
  intros M hPA lowerApplication trace.
  unfold coqDynamicTruthSigmaQFPiExFixedBottomCellTemplate,
    coqDynamicTruthSigmaQFEx8BranchTemplate,
    coqDynamicTruthPiExistentialFixedBottomEx8BranchTemplate,
    coqDynamicTruthPiExistentialFixedBottomCounterexampleTemplate,
    coqDynamicTruthPiExistentialPrefixTemplate,
    coqDynamicTruthPiBinderPrependTemplate,
    rawDynamicTruthMixedQFCellCode,
    rawDynamicTruthMixedQFCollisionCode,
    rawDynamicTruthMixedQFSigmaBranchCode,
    rawDynamicTruthMixedQFPiBranchCode,
    rawDynamicTruthPiExistentialEx8BranchCode,
    rawCoqDynamicTruthPiExistentialLeafTemplateCode.
  cbn [templateRepeatedExists rawDirectTemplateFormula
    rawStructuralTemplateFormulaWith].
  repeat rewrite rawDirectTemplateFormula_quantifier_embedPA.
  rewrite rawDynamicTruthMixedSigmaQFEx8BranchCode_eq_quoted
    by exact hPA.
  try rewrite !rawFixedFormulaNumeralCode_eq_quoted by exact hPA.
  try rewrite !rawDynamicTruthPiFixedFormulaNumeralCode_eq_quoted
    by exact hPA.
  reflexivity.
Qed.

Theorem rawDirect_dynamicTruthSigmaQFPiExOpaqueCellTemplate_identified :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      lowerApplication
      (trace : RawDynamicTruthQuantifierLowerApplicationDirectTrace
        M lowerApplication),
  rawDirectTemplateFormula
    (rawDynamicTruthQuantifierLowerApplication_inputs trace)
    coqDynamicTruthSigmaQFPiExOpaqueCellTemplate =
  rawDynamicTruthMixedQFCellCode M DTMQFSigmaQFPiEx
    (rawFormulaBotCode M) lowerApplication.
Proof.
  intros M hPA lowerApplication trace.
  unfold coqDynamicTruthSigmaQFPiExOpaqueCellTemplate,
    coqDynamicTruthSigmaQFEx8BranchTemplate,
    coqDynamicTruthPiExistentialEx8BranchTemplate,
    coqDynamicTruthPiExistentialCounterexampleTemplate,
    coqDynamicTruthPiExistentialPrefixTemplate,
    coqDynamicTruthPiBinderPrependTemplate,
    rawDynamicTruthMixedQFCellCode,
    rawDynamicTruthMixedQFCollisionCode,
    rawDynamicTruthMixedQFSigmaBranchCode,
    rawDynamicTruthMixedQFPiBranchCode,
    rawDynamicTruthPiExistentialEx8BranchCode,
    rawCoqDynamicTruthPiExistentialLeafTemplateCode.
  cbn [templateRepeatedExists rawDirectTemplateFormula
    rawStructuralTemplateFormulaWith].
  repeat rewrite rawDirectTemplateFormula_quantifier_embedPA.
  rewrite rawDynamicTruthQuantifierLowerApplication_sigma_designated.
  rewrite rawDynamicTruthMixedSigmaQFEx8BranchCode_eq_quoted
    by exact hPA.
  try rewrite !rawFixedFormulaNumeralCode_eq_quoted by exact hPA.
  try rewrite !rawDynamicTruthPiFixedFormulaNumeralCode_eq_quoted
    by exact hPA.
  reflexivity.
Qed.

Theorem
    rawDirect_dynamicTruthSigmaAllPiQFFixedBottomCellTemplate_identified :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      lowerApplication
      (trace : RawDynamicTruthQuantifierLowerApplicationDirectTrace
        M lowerApplication),
  rawDirectTemplateFormula
    (rawDynamicTruthQuantifierLowerApplication_inputs trace)
    coqDynamicTruthSigmaAllPiQFFixedBottomCellTemplate =
  rawDynamicTruthMixedQFCellCode M DTMQFSigmaAllPiQF
    (rawFormulaBotCode M) (rawFormulaBotCode M).
Proof.
  intros M hPA lowerApplication trace.
  unfold coqDynamicTruthSigmaAllPiQFFixedBottomCellTemplate,
    coqDynamicTruthPiQFEx8BranchTemplate,
    coqDynamicTruthSigmaUniversalFixedBottomEx8BranchTemplate,
    coqDynamicTruthSigmaUniversalFixedBottomCounterexampleTemplate,
    coqDynamicTruthSigmaUniversalPrefixTemplate,
    coqDynamicTruthSigmaBinderPrependTemplate,
    rawDynamicTruthMixedQFCellCode,
    rawDynamicTruthMixedQFCollisionCode,
    rawDynamicTruthMixedQFSigmaBranchCode,
    rawDynamicTruthMixedQFPiBranchCode,
    rawDynamicTruthSigmaUniversalEx8BranchCode,
    rawCoqDynamicTruthSigmaUniversalLeafTemplateCode.
  cbn [templateRepeatedExists rawDirectTemplateFormula
    rawStructuralTemplateFormulaWith].
  repeat rewrite rawDirectTemplateFormula_quantifier_embedPA.
  rewrite rawDynamicTruthMixedPiQFEx8BranchCode_eq_quoted
    by exact hPA.
  try rewrite !rawFixedFormulaNumeralCode_eq_quoted by exact hPA.
  try rewrite !rawDynamicTruthPiFixedFormulaNumeralCode_eq_quoted
    by exact hPA.
  reflexivity.
Qed.

Theorem rawDirect_dynamicTruthSigmaAllPiQFOpaqueCellTemplate_identified :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      lowerApplication
      (trace : RawDynamicTruthQuantifierLowerApplicationDirectTrace
        M lowerApplication),
  rawDirectTemplateFormula
    (rawDynamicTruthQuantifierLowerApplication_inputs trace)
    coqDynamicTruthSigmaAllPiQFOpaqueCellTemplate =
  rawDynamicTruthMixedQFCellCode M DTMQFSigmaAllPiQF
    lowerApplication (rawFormulaBotCode M).
Proof.
  intros M hPA lowerApplication trace.
  unfold coqDynamicTruthSigmaAllPiQFOpaqueCellTemplate,
    coqDynamicTruthPiQFEx8BranchTemplate,
    coqDynamicTruthSigmaUniversalEx8BranchTemplate,
    coqDynamicTruthSigmaUniversalCounterexampleTemplate,
    coqDynamicTruthSigmaUniversalPrefixTemplate,
    coqDynamicTruthSigmaBinderPrependTemplate,
    rawDynamicTruthMixedQFCellCode,
    rawDynamicTruthMixedQFCollisionCode,
    rawDynamicTruthMixedQFSigmaBranchCode,
    rawDynamicTruthMixedQFPiBranchCode,
    rawDynamicTruthSigmaUniversalEx8BranchCode,
    rawCoqDynamicTruthSigmaUniversalLeafTemplateCode.
  cbn [templateRepeatedExists rawDirectTemplateFormula
    rawStructuralTemplateFormulaWith].
  repeat rewrite rawDirectTemplateFormula_quantifier_embedPA.
  rewrite rawDynamicTruthQuantifierLowerApplication_designated.
  rewrite rawDynamicTruthMixedPiQFEx8BranchCode_eq_quoted
    by exact hPA.
  try rewrite !rawFixedFormulaNumeralCode_eq_quoted by exact hPA.
  try rewrite !rawDynamicTruthPiFixedFormulaNumeralCode_eq_quoted
    by exact hPA.
  reflexivity.
Qed.

Corollary rawDirect_dynamicTruthSigmaQFPiExOpaqueCellTransport_identified :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      lowerApplication
      (trace : RawDynamicTruthQuantifierLowerApplicationDirectTrace
        M lowerApplication),
  rawDirectTemplateFormula
    (rawDynamicTruthQuantifierLowerApplication_inputs trace)
    (tfImp coqDynamicTruthSigmaQFPiExFixedBottomCellTemplate
      coqDynamicTruthSigmaQFPiExOpaqueCellTemplate) =
  rawFormulaImpCode M
    (rawDynamicTruthMixedQFCellCode M DTMQFSigmaQFPiEx
      (rawFormulaBotCode M) (rawFormulaBotCode M))
    (rawDynamicTruthMixedQFCellCode M DTMQFSigmaQFPiEx
      (rawFormulaBotCode M) lowerApplication).
Proof.
  intros M hPA lowerApplication trace.
  cbn [rawDirectTemplateFormula rawStructuralTemplateFormulaWith].
  rewrite
    (rawDirect_dynamicTruthSigmaQFPiExFixedBottomCellTemplate_identified
      M hPA lowerApplication trace).
  rewrite (rawDirect_dynamicTruthSigmaQFPiExOpaqueCellTemplate_identified
    M hPA lowerApplication trace).
  reflexivity.
Qed.

Corollary
    rawDirect_dynamicTruthSigmaAllPiQFOpaqueCellTransport_identified :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      lowerApplication
      (trace : RawDynamicTruthQuantifierLowerApplicationDirectTrace
        M lowerApplication),
  rawDirectTemplateFormula
    (rawDynamicTruthQuantifierLowerApplication_inputs trace)
    (tfImp coqDynamicTruthSigmaAllPiQFFixedBottomCellTemplate
      coqDynamicTruthSigmaAllPiQFOpaqueCellTemplate) =
  rawFormulaImpCode M
    (rawDynamicTruthMixedQFCellCode M DTMQFSigmaAllPiQF
      (rawFormulaBotCode M) (rawFormulaBotCode M))
    (rawDynamicTruthMixedQFCellCode M DTMQFSigmaAllPiQF
      lowerApplication (rawFormulaBotCode M)).
Proof.
  intros M hPA lowerApplication trace.
  cbn [rawDirectTemplateFormula rawStructuralTemplateFormulaWith].
  rewrite
    (rawDirect_dynamicTruthSigmaAllPiQFFixedBottomCellTemplate_identified
      M hPA lowerApplication trace).
  rewrite (rawDirect_dynamicTruthSigmaAllPiQFOpaqueCellTemplate_identified
    M hPA lowerApplication trace).
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Same-context compilation and modus ponens with a fixed seed root. *)

Definition rawDynamicTruthSigmaQFPiExOpaqueCellTransportLocalRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (context lowerApplication : M)
    (trace : RawDynamicTruthQuantifierLowerApplicationDirectTrace
      M lowerApplication) : M :=
  rawTemplateProofCodeOnTail
    (rawDynamicTruthQuantifierDirectTranslation
      M hPA lowerApplication trace)
    context coqDynamicTruthSigmaQFPiExOpaqueCellTransportProof.

Definition rawDynamicTruthSigmaAllPiQFOpaqueCellTransportLocalRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (context lowerApplication : M)
    (trace : RawDynamicTruthQuantifierLowerApplicationDirectTrace
      M lowerApplication) : M :=
  rawTemplateProofCodeOnTail
    (rawDynamicTruthQuantifierDirectTranslation
      M hPA lowerApplication trace)
    context coqDynamicTruthSigmaAllPiQFOpaqueCellTransportProof.

Arguments rawDynamicTruthSigmaQFPiExOpaqueCellTransportLocalRoot
  M hPA context lowerApplication trace : clear implicits.
Arguments rawDynamicTruthSigmaAllPiQFOpaqueCellTransportLocalRoot
  M hPA context lowerApplication trace : clear implicits.

Theorem raw_codedPALocalProofOf_dynamicTruthSigmaQFPiExOpaqueTransport :
    forall (M : RawPAModel) (hPA : RawPASatisfies M)
      context lowerApplication
      (trace : RawDynamicTruthQuantifierLowerApplicationDirectTrace
        M lowerApplication),
  RawContextListRealizable M context ->
  RawContextShift M context context ->
  RawCodedPALocalProofOf M context
    (rawFormulaImpCode M
      (rawDynamicTruthMixedQFCellCode M DTMQFSigmaQFPiEx
        (rawFormulaBotCode M) (rawFormulaBotCode M))
      (rawDynamicTruthMixedQFCellCode M DTMQFSigmaQFPiEx
        (rawFormulaBotCode M) lowerApplication))
    (rawDynamicTruthSigmaQFPiExOpaqueCellTransportLocalRoot
      M hPA context lowerApplication trace).
Proof.
  intros M hPA context lowerApplication trace
    hcontext hselfShift.
  rewrite <-
    (rawDirect_dynamicTruthSigmaQFPiExOpaqueCellTransport_identified
      M hPA lowerApplication trace).
  unfold rawDynamicTruthSigmaQFPiExOpaqueCellTransportLocalRoot,
    rawDynamicTruthQuantifierDirectTranslation.
  pose proof (raw_templateProofOnTail_localProof M hPA
    (rawDirectStructuralTemplateTranslation M hPA
      (rawDynamicTruthQuantifierLowerApplication_inputs trace))
    context coqDynamicTruthSigmaQFPiExOpaqueCellTransportProof
    hcontext hselfShift
    (proj1
      coqDynamicTruthSigmaQFPiExOpaqueCellTransportProof_derives))
    as hcompiled.
  cbn [templateRawContext rawTemplateContextCodeOnTail] in hcompiled.
  exact hcompiled.
Qed.

Theorem raw_codedPALocalProofOf_dynamicTruthSigmaAllPiQFOpaqueTransport :
    forall (M : RawPAModel) (hPA : RawPASatisfies M)
      context lowerApplication
      (trace : RawDynamicTruthQuantifierLowerApplicationDirectTrace
        M lowerApplication),
  RawContextListRealizable M context ->
  RawContextShift M context context ->
  RawCodedPALocalProofOf M context
    (rawFormulaImpCode M
      (rawDynamicTruthMixedQFCellCode M DTMQFSigmaAllPiQF
        (rawFormulaBotCode M) (rawFormulaBotCode M))
      (rawDynamicTruthMixedQFCellCode M DTMQFSigmaAllPiQF
        lowerApplication (rawFormulaBotCode M)))
    (rawDynamicTruthSigmaAllPiQFOpaqueCellTransportLocalRoot
      M hPA context lowerApplication trace).
Proof.
  intros M hPA context lowerApplication trace
    hcontext hselfShift.
  rewrite <-
    (rawDirect_dynamicTruthSigmaAllPiQFOpaqueCellTransport_identified
      M hPA lowerApplication trace).
  unfold rawDynamicTruthSigmaAllPiQFOpaqueCellTransportLocalRoot,
    rawDynamicTruthQuantifierDirectTranslation.
  pose proof (raw_templateProofOnTail_localProof M hPA
    (rawDirectStructuralTemplateTranslation M hPA
      (rawDynamicTruthQuantifierLowerApplication_inputs trace))
    context coqDynamicTruthSigmaAllPiQFOpaqueCellTransportProof
    hcontext hselfShift
    (proj1
      coqDynamicTruthSigmaAllPiQFOpaqueCellTransportProof_derives))
    as hcompiled.
  cbn [templateRawContext rawTemplateContextCodeOnTail] in hcompiled.
  exact hcompiled.
Qed.

Definition rawDynamicTruthSigmaQFPiExOpaqueCellLocalRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (context lowerApplication fixedRoot : M)
    (trace : RawDynamicTruthQuantifierLowerApplicationDirectTrace
      M lowerApplication) : M :=
  rawProofImpERoot M context
    (rawDynamicTruthMixedQFCellCode M DTMQFSigmaQFPiEx
      (rawFormulaBotCode M) (rawFormulaBotCode M))
    (rawDynamicTruthMixedQFCellCode M DTMQFSigmaQFPiEx
      (rawFormulaBotCode M) lowerApplication)
    (rawDynamicTruthSigmaQFPiExOpaqueCellTransportLocalRoot
      M hPA context lowerApplication trace)
    fixedRoot.

Definition rawDynamicTruthSigmaAllPiQFOpaqueCellLocalRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (context lowerApplication fixedRoot : M)
    (trace : RawDynamicTruthQuantifierLowerApplicationDirectTrace
      M lowerApplication) : M :=
  rawProofImpERoot M context
    (rawDynamicTruthMixedQFCellCode M DTMQFSigmaAllPiQF
      (rawFormulaBotCode M) (rawFormulaBotCode M))
    (rawDynamicTruthMixedQFCellCode M DTMQFSigmaAllPiQF
      lowerApplication (rawFormulaBotCode M))
    (rawDynamicTruthSigmaAllPiQFOpaqueCellTransportLocalRoot
      M hPA context lowerApplication trace)
    fixedRoot.

Arguments rawDynamicTruthSigmaQFPiExOpaqueCellLocalRoot
  M hPA context lowerApplication fixedRoot trace : clear implicits.
Arguments rawDynamicTruthSigmaAllPiQFOpaqueCellLocalRoot
  M hPA context lowerApplication fixedRoot trace : clear implicits.

Theorem raw_codedPALocalProofOf_dynamicTruthSigmaQFPiExOpaqueCell_direct :
    forall (M : RawPAModel) (hPA : RawPASatisfies M)
      context lowerApplication fixedRoot
      (trace : RawDynamicTruthQuantifierLowerApplicationDirectTrace
        M lowerApplication),
  RawContextListRealizable M context ->
  RawContextShift M context context ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthMixedQFCellCode M DTMQFSigmaQFPiEx
      (rawFormulaBotCode M) (rawFormulaBotCode M)) fixedRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthMixedQFCellCode M DTMQFSigmaQFPiEx
      (rawFormulaBotCode M) lowerApplication)
    (rawDynamicTruthSigmaQFPiExOpaqueCellLocalRoot
      M hPA context lowerApplication fixedRoot trace).
Proof.
  intros M hPA context lowerApplication fixedRoot trace
    hcontext hselfShift hfixed.
  unfold rawDynamicTruthSigmaQFPiExOpaqueCellLocalRoot.
  apply (raw_codedPALocalProofOf_impE M hPA context
    (rawDynamicTruthMixedQFCellCode M DTMQFSigmaQFPiEx
      (rawFormulaBotCode M) (rawFormulaBotCode M))
    (rawDynamicTruthMixedQFCellCode M DTMQFSigmaQFPiEx
      (rawFormulaBotCode M) lowerApplication)).
  - exact
      (raw_codedPALocalProofOf_dynamicTruthSigmaQFPiExOpaqueTransport
        M hPA context lowerApplication trace hcontext hselfShift).
  - exact hfixed.
Qed.

Theorem raw_codedPALocalProofOf_dynamicTruthSigmaAllPiQFOpaqueCell_direct :
    forall (M : RawPAModel) (hPA : RawPASatisfies M)
      context lowerApplication fixedRoot
      (trace : RawDynamicTruthQuantifierLowerApplicationDirectTrace
        M lowerApplication),
  RawContextListRealizable M context ->
  RawContextShift M context context ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthMixedQFCellCode M DTMQFSigmaAllPiQF
      (rawFormulaBotCode M) (rawFormulaBotCode M)) fixedRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthMixedQFCellCode M DTMQFSigmaAllPiQF
      lowerApplication (rawFormulaBotCode M))
    (rawDynamicTruthSigmaAllPiQFOpaqueCellLocalRoot
      M hPA context lowerApplication fixedRoot trace).
Proof.
  intros M hPA context lowerApplication fixedRoot trace
    hcontext hselfShift hfixed.
  unfold rawDynamicTruthSigmaAllPiQFOpaqueCellLocalRoot.
  apply (raw_codedPALocalProofOf_impE M hPA context
    (rawDynamicTruthMixedQFCellCode M DTMQFSigmaAllPiQF
      (rawFormulaBotCode M) (rawFormulaBotCode M))
    (rawDynamicTruthMixedQFCellCode M DTMQFSigmaAllPiQF
      lowerApplication (rawFormulaBotCode M))).
  - exact
      (raw_codedPALocalProofOf_dynamicTruthSigmaAllPiQFOpaqueTransport
        M hPA context lowerApplication trace hcontext hselfShift).
  - exact hfixed.
Qed.

Corollary
    raw_codedPALocalProofOf_dynamicTruthSigmaQFPiExOpaqueCell_witnessed :
    forall (M : RawPAModel) (hPA : RawPASatisfies M)
      witnessList context lowerApplication fixedRoot
      (trace : RawDynamicTruthQuantifierLowerApplicationDirectTrace
        M lowerApplication),
  RawCodedPAAxiomWitnessContext M witnessList context ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthMixedQFCellCode M DTMQFSigmaQFPiEx
      (rawFormulaBotCode M) (rawFormulaBotCode M)) fixedRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthMixedQFCellCode M DTMQFSigmaQFPiEx
      (rawFormulaBotCode M) lowerApplication)
    (rawDynamicTruthSigmaQFPiExOpaqueCellLocalRoot
      M hPA context lowerApplication fixedRoot trace).
Proof.
  intros M hPA witnessList context lowerApplication fixedRoot trace
    hwitness hfixed.
  apply (raw_codedPALocalProofOf_dynamicTruthSigmaQFPiExOpaqueCell_direct
    M hPA context lowerApplication fixedRoot trace).
  - exact (raw_codedPAAxiomWitnessContext_context_realizable
      M witnessList context hwitness).
  - exact (raw_codedPAAxiomWitnessContext_selfShift
      M hPA witnessList context hwitness).
  - exact hfixed.
Qed.

Corollary
    raw_codedPALocalProofOf_dynamicTruthSigmaAllPiQFOpaqueCell_witnessed :
    forall (M : RawPAModel) (hPA : RawPASatisfies M)
      witnessList context lowerApplication fixedRoot
      (trace : RawDynamicTruthQuantifierLowerApplicationDirectTrace
        M lowerApplication),
  RawCodedPAAxiomWitnessContext M witnessList context ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthMixedQFCellCode M DTMQFSigmaAllPiQF
      (rawFormulaBotCode M) (rawFormulaBotCode M)) fixedRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthMixedQFCellCode M DTMQFSigmaAllPiQF
      lowerApplication (rawFormulaBotCode M))
    (rawDynamicTruthSigmaAllPiQFOpaqueCellLocalRoot
      M hPA context lowerApplication fixedRoot trace).
Proof.
  intros M hPA witnessList context lowerApplication fixedRoot trace
    hwitness hfixed.
  apply (raw_codedPALocalProofOf_dynamicTruthSigmaAllPiQFOpaqueCell_direct
    M hPA context lowerApplication fixedRoot trace).
  - exact (raw_codedPAAxiomWitnessContext_context_realizable
      M witnessList context hwitness).
  - exact (raw_codedPAAxiomWitnessContext_selfShift
      M hPA witnessList context hwitness).
  - exact hfixed.
Qed.

(** ------------------------------------------------------------------
    The synchronized thirty-eight-plus-two fixed-helper batch. *)

Definition rawDynamicTruthSigmaQFPiExTransportSeedPAHelper
    : RawFixedPAHelper :=
  {| rawFixedPAHelperFormula :=
       dynamicTruthMixedQFCellFormula DTMQFSigmaQFPiEx pBot pBot;
     rawFixedPAHelperBProv :=
       PA_proves_dynamicTruthMixedQFCellFormula
         DTMQFSigmaQFPiEx pBot pBot |}.

Definition rawDynamicTruthSigmaAllPiQFTransportSeedPAHelper
    : RawFixedPAHelper :=
  {| rawFixedPAHelperFormula :=
       dynamicTruthMixedQFCellFormula DTMQFSigmaAllPiQF pBot pBot;
     rawFixedPAHelperBProv :=
       PA_proves_dynamicTruthMixedQFCellFormula
         DTMQFSigmaAllPiQF pBot pBot |}.

Definition rawDynamicTruthMixedQFOpaqueTransportSeedPAHelpers
    : list RawFixedPAHelper :=
  [ rawDynamicTruthSigmaQFPiExTransportSeedPAHelper;
    rawDynamicTruthSigmaAllPiQFTransportSeedPAHelper ].

Definition rawDynamicTruthReadyAndAllMixedQFPAHelpers
    : list RawFixedPAHelper :=
  rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers ++
  rawDynamicTruthMixedQFOpaqueTransportSeedPAHelpers.

Lemma rawDynamicTruthMixedQFOpaqueTransportSeedPAHelpers_length :
  length rawDynamicTruthMixedQFOpaqueTransportSeedPAHelpers = 2.
Proof. reflexivity. Qed.

Lemma rawDynamicTruthReadyAndAllMixedQFPAHelpers_length :
  length rawDynamicTruthReadyAndAllMixedQFPAHelpers = 40.
Proof.
  unfold rawDynamicTruthReadyAndAllMixedQFPAHelpers.
  rewrite length_app,
    rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers_length,
    rawDynamicTruthMixedQFOpaqueTransportSeedPAHelpers_length.
  reflexivity.
Qed.

(** This literal equality audits the precise 38+2 order.  The final entries
    are fixed-bottom seeds; it deliberately makes no claim that either seed
    target is already an arbitrary native lower-application code. *)
Lemma rawDynamicTruthReadyAndAllMixedQFPAHelpers_order :
  rawDynamicTruthReadyAndAllMixedQFPAHelpers =
  rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers ++
  [ rawDynamicTruthSigmaQFPiExTransportSeedPAHelper;
    rawDynamicTruthSigmaAllPiQFTransportSeedPAHelper ].
Proof. reflexivity. Qed.

Lemma rawDynamicTruthSigmaQFPiExTransportSeedTarget_eq_fixed : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  rawFixedPAHelperTranslatedTargetCode M translation
    rawDynamicTruthSigmaQFPiExTransportSeedPAHelper =
  rawDynamicTruthMixedQFCellCode M DTMQFSigmaQFPiEx
    (rawFormulaBotCode M) (rawFormulaBotCode M).
Proof.
  intros M hPA translation hagreement.
  unfold rawFixedPAHelperTranslatedTargetCode,
    rawDynamicTruthSigmaQFPiExTransportSeedPAHelper.
  cbn [rawFixedPAHelperFormula].
  rewrite (rawTemplateFormula_embedPA hagreement).
  symmetry.
  exact (rawDynamicTruthMixedQFCellCode_eq_quoted
    M hPA DTMQFSigmaQFPiEx pBot pBot).
Qed.

Lemma rawDynamicTruthSigmaAllPiQFTransportSeedTarget_eq_fixed : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  rawFixedPAHelperTranslatedTargetCode M translation
    rawDynamicTruthSigmaAllPiQFTransportSeedPAHelper =
  rawDynamicTruthMixedQFCellCode M DTMQFSigmaAllPiQF
    (rawFormulaBotCode M) (rawFormulaBotCode M).
Proof.
  intros M hPA translation hagreement.
  unfold rawFixedPAHelperTranslatedTargetCode,
    rawDynamicTruthSigmaAllPiQFTransportSeedPAHelper.
  cbn [rawFixedPAHelperFormula].
  rewrite (rawTemplateFormula_embedPA hagreement).
  symmetry.
  exact (rawDynamicTruthMixedQFCellCode_eq_quoted
    M hPA DTMQFSigmaAllPiQF pBot pBot).
Qed.

Lemma rawDynamicTruthReadyAndAllMixedQFPAHelperTargets_order : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  rawFixedPAHelperBatchTranslatedTargetCodes M translation
    rawDynamicTruthReadyAndAllMixedQFPAHelpers =
  rawFixedPAHelperBatchTranslatedTargetCodes M translation
    rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers ++
  [ rawDynamicTruthMixedQFCellCode M DTMQFSigmaQFPiEx
      (rawFormulaBotCode M) (rawFormulaBotCode M);
    rawDynamicTruthMixedQFCellCode M DTMQFSigmaAllPiQF
      (rawFormulaBotCode M) (rawFormulaBotCode M) ].
Proof.
  intros M hPA translation hagreement.
  unfold rawDynamicTruthReadyAndAllMixedQFPAHelpers,
    rawDynamicTruthMixedQFOpaqueTransportSeedPAHelpers,
    rawFixedPAHelperBatchTranslatedTargetCodes.
  rewrite map_app. cbn [map].
  rewrite (rawDynamicTruthSigmaQFPiExTransportSeedTarget_eq_fixed
    M hPA translation hagreement).
  rewrite (rawDynamicTruthSigmaAllPiQFTransportSeedTarget_eq_fixed
    M hPA translation hagreement).
  reflexivity.
Qed.

(** Split a structurally indexed helper-root family at a list append.  This
    avoids any untyped [nth] lookup and preserves the exact helper/root
    correspondence on both sides of the split. *)
Lemma raw_fixedPAHelperBatchLocalProofs_app_split : forall
    (M : RawPAModel) translation context prefix suffix roots,
  RawFixedPAHelperBatchLocalProofs M translation context
    (prefix ++ suffix) roots ->
  exists prefixRoots suffixRoots,
    roots = prefixRoots ++ suffixRoots /\
    RawFixedPAHelperBatchLocalProofs M translation context
      prefix prefixRoots /\
    RawFixedPAHelperBatchLocalProofs M translation context
      suffix suffixRoots.
Proof.
  intros M translation context prefix.
  induction prefix as [| helper prefixTail ih];
    intros suffix roots hproofs.
  - exists [], roots. cbn. repeat split; assumption.
  - destruct roots as [| root rootsTail].
    + contradiction.
    + cbn [RawFixedPAHelperBatchLocalProofs] in hproofs.
      destruct hproofs as [hroot htail].
      destruct (ih suffix rootsTail htail)
        as (prefixRoots & suffixRoots & hroots & hprefix & hsuffix).
      exists (root :: prefixRoots), suffixRoots.
      split.
      * cbn. now rewrite hroots.
      * split.
        -- cbn [RawFixedPAHelperBatchLocalProofs].
           split; assumption.
        -- exact hsuffix.
Qed.

(** Recover the two suffix roots and rewrite only their fixed-bottom targets.
    The thirty-eight-prefix root list is returned unchanged. *)
Theorem raw_mixedQFOpaqueTransportSeedRoots_of_40helper_roots : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall context roots,
  RawFixedPAHelperBatchLocalProofs M translation context
    rawDynamicTruthReadyAndAllMixedQFPAHelpers roots ->
  exists prefixRoots sigmaQFPiExSeedRoot sigmaAllPiQFSeedRoot,
    roots = prefixRoots ++
      [sigmaQFPiExSeedRoot; sigmaAllPiQFSeedRoot] /\
    RawFixedPAHelperBatchLocalProofs M translation context
      rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers prefixRoots /\
    RawCodedPALocalProofOf M context
      (rawDynamicTruthMixedQFCellCode M DTMQFSigmaQFPiEx
        (rawFormulaBotCode M) (rawFormulaBotCode M))
      sigmaQFPiExSeedRoot /\
    RawCodedPALocalProofOf M context
      (rawDynamicTruthMixedQFCellCode M DTMQFSigmaAllPiQF
        (rawFormulaBotCode M) (rawFormulaBotCode M))
      sigmaAllPiQFSeedRoot.
Proof.
  intros M hPA translation hagreement context roots hroots.
  unfold rawDynamicTruthReadyAndAllMixedQFPAHelpers in hroots.
  destruct (raw_fixedPAHelperBatchLocalProofs_app_split M translation
    context rawDynamicTruthReadyBinderPrincipalAndMixedQFPAHelpers
    rawDynamicTruthMixedQFOpaqueTransportSeedPAHelpers roots hroots)
    as (prefixRoots & suffixRoots & hsplit & hprefix & hsuffix).
  unfold rawDynamicTruthMixedQFOpaqueTransportSeedPAHelpers in hsuffix.
  destruct suffixRoots as [| sigmaQFPiExSeedRoot suffixTail].
  { contradiction. }
  destruct suffixTail as [| sigmaAllPiQFSeedRoot suffixTail].
  { cbn [RawFixedPAHelperBatchLocalProofs] in hsuffix.
    intuition. }
  destruct suffixTail as [| extraRoot suffixTail].
  2:{ cbn [RawFixedPAHelperBatchLocalProofs] in hsuffix.
      intuition. }
  cbn [RawFixedPAHelperBatchLocalProofs] in hsuffix.
  destruct hsuffix as [hsigmaQFPiEx [hsigmaAllPiQF _]].
  rewrite (rawDynamicTruthSigmaQFPiExTransportSeedTarget_eq_fixed
    M hPA translation hagreement) in hsigmaQFPiEx.
  rewrite (rawDynamicTruthSigmaAllPiQFTransportSeedTarget_eq_fixed
    M hPA translation hagreement) in hsigmaAllPiQF.
  exists prefixRoots, sigmaQFPiExSeedRoot, sigmaAllPiQFSeedRoot.
  split.
  - exact hsplit.
  - split.
    + exact hprefix.
    + split; assumption.
Qed.

(** Compile all forty fixed helpers around the same six-field master. *)
Corollary raw_sixFieldMasterCommonContextProofsWithAllMixedQFHelpers :
    forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall field1 field2 field3 field4 field5 finalField,
  RawSixFieldMasterCommonContextProofsOf M
    field1 field2 field3 field4 field5 finalField ->
  RawSixFieldMasterCommonContextProofsWithFixedPAHelperBatchOf
    M translation field1 field2 field3 field4 field5 finalField
    rawDynamicTruthReadyAndAllMixedQFPAHelpers.
Proof.
  intros M hPA translation hagreement
    field1 field2 field3 field4 field5 finalField hmaster.
  exact (raw_sixFieldMasterCommonContextProofsWithFixedPAHelperBatch
    M hPA translation hagreement
    field1 field2 field3 field4 field5 finalField
    rawDynamicTruthReadyAndAllMixedQFPAHelpers hmaster).
Qed.

(** The exact synchronized result: six master roots, forty ordered helper
    roots, and the two arbitrary lower-application collision roots all share
    one literal witnessed context. *)
Definition
    RawSixFieldMasterCommonContextProofsWithAllMixedQFOpaqueRootsOf
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M)
    (field1 field2 field3 field4 field5 finalField : M)
    (lowerPiApplication lowerSigmaApplication : M) : Prop :=
  exists witnessList context
      root1 root2 root3 root4 root5 finalRoot : M,
    exists helperRoots : list M,
    exists sigmaQFPiExRoot sigmaAllPiQFRoot : M,
      RawCodedPAAxiomWitnessContext M witnessList context /\
      RawCodedPALocalProofOf M context field1 root1 /\
      RawCodedPALocalProofOf M context field2 root2 /\
      RawCodedPALocalProofOf M context field3 root3 /\
      RawCodedPALocalProofOf M context field4 root4 /\
      RawCodedPALocalProofOf M context field5 root5 /\
      RawCodedPALocalProofOf M context finalField finalRoot /\
      RawFixedPAHelperBatchLocalProofs M translation context
        rawDynamicTruthReadyAndAllMixedQFPAHelpers helperRoots /\
      RawCodedPALocalProofOf M context
        (rawDynamicTruthMixedQFCellCode M DTMQFSigmaQFPiEx
          (rawFormulaBotCode M) lowerSigmaApplication)
        sigmaQFPiExRoot /\
      RawCodedPALocalProofOf M context
        (rawDynamicTruthMixedQFCellCode M DTMQFSigmaAllPiQF
          lowerPiApplication (rawFormulaBotCode M))
        sigmaAllPiQFRoot.

Arguments
  RawSixFieldMasterCommonContextProofsWithAllMixedQFOpaqueRootsOf
    M translation field1 field2 field3 field4 field5 finalField
    lowerPiApplication lowerSigmaApplication : clear implicits.

Theorem raw_sixFieldMasterCommonContextProofsWithAllMixedQFOpaqueRoots :
    forall (M : RawPAModel) (hPA : RawPASatisfies M)
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall field1 field2 field3 field4 field5 finalField,
  RawSixFieldMasterCommonContextProofsOf M
    field1 field2 field3 field4 field5 finalField ->
  forall lowerPiApplication lowerSigmaApplication,
  RawDynamicTruthQuantifierLowerApplicationDirectTrace
    M lowerPiApplication ->
  RawDynamicTruthQuantifierLowerApplicationDirectTrace
    M lowerSigmaApplication ->
  RawSixFieldMasterCommonContextProofsWithAllMixedQFOpaqueRootsOf
    M translation field1 field2 field3 field4 field5 finalField
    lowerPiApplication lowerSigmaApplication.
Proof.
  intros M hPA translation hagreement
    field1 field2 field3 field4 field5 finalField hmaster
    lowerPiApplication lowerSigmaApplication piTrace sigmaTrace.
  pose proof
    (raw_sixFieldMasterCommonContextProofsWithAllMixedQFHelpers
      M hPA translation hagreement
      field1 field2 field3 field4 field5 finalField hmaster)
    as hpackage.
  unfold RawSixFieldMasterCommonContextProofsWithFixedPAHelperBatchOf
    in hpackage.
  destruct hpackage as
    (witnessList & context & root1 & root2 & root3 & root4 & root5 &
      finalRoot & helperRoots & hwitness & hfield1 & hfield2 & hfield3 &
      hfield4 & hfield5 & hfinal & hhelpers).
  destruct (raw_mixedQFOpaqueTransportSeedRoots_of_40helper_roots
    M hPA translation hagreement context helperRoots hhelpers)
    as (prefixRoots & sigmaQFPiExSeedRoot & sigmaAllPiQFSeedRoot &
      hrootOrder & hprefix & hsigmaQFPiExSeed & hsigmaAllPiQFSeed).
  pose proof
    (raw_codedPALocalProofOf_dynamicTruthSigmaQFPiExOpaqueCell_witnessed
      M hPA witnessList context lowerSigmaApplication
      sigmaQFPiExSeedRoot sigmaTrace hwitness hsigmaQFPiExSeed)
    as hsigmaQFPiEx.
  pose proof
    (raw_codedPALocalProofOf_dynamicTruthSigmaAllPiQFOpaqueCell_witnessed
      M hPA witnessList context lowerPiApplication
      sigmaAllPiQFSeedRoot piTrace hwitness hsigmaAllPiQFSeed)
    as hsigmaAllPiQF.
  unfold
    RawSixFieldMasterCommonContextProofsWithAllMixedQFOpaqueRootsOf.
  exists witnessList, context,
    root1, root2, root3, root4, root5, finalRoot, helperRoots,
    (rawDynamicTruthSigmaQFPiExOpaqueCellLocalRoot
      M hPA context lowerSigmaApplication sigmaQFPiExSeedRoot sigmaTrace),
    (rawDynamicTruthSigmaAllPiQFOpaqueCellLocalRoot
      M hPA context lowerPiApplication sigmaAllPiQFSeedRoot piTrace).
  split; [exact hwitness |].
  split; [exact hfield1 |].
  split; [exact hfield2 |].
  split; [exact hfield3 |].
  split; [exact hfield4 |].
  split; [exact hfield5 |].
  split; [exact hfinal |].
  split; [exact hhelpers |].
  split; [exact hsigmaQFPiEx | exact hsigmaAllPiQF].
Qed.

(** ------------------------------------------------------------------
    Ordinary certificates and total compiler interfaces. *)

Theorem raw_codedPAProofOf_dynamicTruthSigmaQFPiExOpaqueCell_direct :
    forall (M : RawPAModel) (hPA : RawPASatisfies M)
      lowerApplication
      (trace : RawDynamicTruthQuantifierLowerApplicationDirectTrace
        M lowerApplication),
  exists certificate : M,
    RawCodedPAProofOf M
      (rawDynamicTruthMixedQFCellCode M DTMQFSigmaQFPiEx
        (rawFormulaBotCode M) lowerApplication) certificate.
Proof.
  intros M hPA lowerApplication trace.
  destruct (raw_codedPAProofOf_dynamicTruthMixedQFCell
    M hPA DTMQFSigmaQFPiEx pBot pBot)
    as [fixedCertificate hfixed].
  change (RawCodedPAProofOf M
    (rawDynamicTruthMixedQFCellCode M DTMQFSigmaQFPiEx
      (rawFormulaBotCode M) (rawFormulaBotCode M)) fixedCertificate)
    in hfixed.
  destruct hfixed as
    (witnessList & fixedRoot & context & hcertificate & hwitness &
      hfixedCoverage & hfixedEndpoint).
  pose proof
    (raw_codedPALocalProofOf_dynamicTruthSigmaQFPiExOpaqueTransport
      M hPA context lowerApplication trace
      (raw_codedPAAxiomWitnessContext_context_realizable
        M witnessList context hwitness)
      (raw_codedPAAxiomWitnessContext_selfShift
        M hPA witnessList context hwitness))
    as htransport.
  destruct htransport as [htransportCoverage htransportEndpoint].
  exists (rawProofImpECertificate M witnessList context
    (rawDynamicTruthMixedQFCellCode M DTMQFSigmaQFPiEx
      (rawFormulaBotCode M) (rawFormulaBotCode M))
    (rawDynamicTruthMixedQFCellCode M DTMQFSigmaQFPiEx
      (rawFormulaBotCode M) lowerApplication)
    (rawDynamicTruthSigmaQFPiExOpaqueCellTransportLocalRoot
      M hPA context lowerApplication trace)
    fixedRoot).
  exact (raw_codedPAProofOf_impE_from_fields M hPA
    witnessList context
    (rawDynamicTruthMixedQFCellCode M DTMQFSigmaQFPiEx
      (rawFormulaBotCode M) (rawFormulaBotCode M))
    (rawDynamicTruthMixedQFCellCode M DTMQFSigmaQFPiEx
      (rawFormulaBotCode M) lowerApplication)
    (rawDynamicTruthSigmaQFPiExOpaqueCellTransportLocalRoot
      M hPA context lowerApplication trace)
    fixedRoot hwitness
    htransportCoverage htransportEndpoint
    hfixedCoverage hfixedEndpoint).
Qed.

Theorem raw_codedPAProofOf_dynamicTruthSigmaAllPiQFOpaqueCell_direct :
    forall (M : RawPAModel) (hPA : RawPASatisfies M)
      lowerApplication
      (trace : RawDynamicTruthQuantifierLowerApplicationDirectTrace
        M lowerApplication),
  exists certificate : M,
    RawCodedPAProofOf M
      (rawDynamicTruthMixedQFCellCode M DTMQFSigmaAllPiQF
        lowerApplication (rawFormulaBotCode M)) certificate.
Proof.
  intros M hPA lowerApplication trace.
  destruct (raw_codedPAProofOf_dynamicTruthMixedQFCell
    M hPA DTMQFSigmaAllPiQF pBot pBot)
    as [fixedCertificate hfixed].
  change (RawCodedPAProofOf M
    (rawDynamicTruthMixedQFCellCode M DTMQFSigmaAllPiQF
      (rawFormulaBotCode M) (rawFormulaBotCode M)) fixedCertificate)
    in hfixed.
  destruct hfixed as
    (witnessList & fixedRoot & context & hcertificate & hwitness &
      hfixedCoverage & hfixedEndpoint).
  pose proof
    (raw_codedPALocalProofOf_dynamicTruthSigmaAllPiQFOpaqueTransport
      M hPA context lowerApplication trace
      (raw_codedPAAxiomWitnessContext_context_realizable
        M witnessList context hwitness)
      (raw_codedPAAxiomWitnessContext_selfShift
        M hPA witnessList context hwitness))
    as htransport.
  destruct htransport as [htransportCoverage htransportEndpoint].
  exists (rawProofImpECertificate M witnessList context
    (rawDynamicTruthMixedQFCellCode M DTMQFSigmaAllPiQF
      (rawFormulaBotCode M) (rawFormulaBotCode M))
    (rawDynamicTruthMixedQFCellCode M DTMQFSigmaAllPiQF
      lowerApplication (rawFormulaBotCode M))
    (rawDynamicTruthSigmaAllPiQFOpaqueCellTransportLocalRoot
      M hPA context lowerApplication trace)
    fixedRoot).
  exact (raw_codedPAProofOf_impE_from_fields M hPA
    witnessList context
    (rawDynamicTruthMixedQFCellCode M DTMQFSigmaAllPiQF
      (rawFormulaBotCode M) (rawFormulaBotCode M))
    (rawDynamicTruthMixedQFCellCode M DTMQFSigmaAllPiQF
      lowerApplication (rawFormulaBotCode M))
    (rawDynamicTruthSigmaAllPiQFOpaqueCellTransportLocalRoot
      M hPA context lowerApplication trace)
    fixedRoot hwitness
    htransportCoverage htransportEndpoint
    hfixedCoverage hfixedEndpoint).
Qed.

(** Existing adequacy-indexed trace totality is enough for the exact
    adequacy-indexed compiler. *)
Definition RawDynamicTruthMixedQFOpaqueQuantifierAdequateCellProofCompiler
    (M : RawPAModel) : Prop :=
  (forall lowerSigmaApplication : M,
    RawCodedFormulaAtomicallyAdequate M lowerSigmaApplication ->
    exists certificate : M,
      RawCodedPAProofOf M
        (rawDynamicTruthMixedQFCellCode M DTMQFSigmaQFPiEx
          (rawFormulaBotCode M) lowerSigmaApplication) certificate) /\
  (forall lowerPiApplication : M,
    RawCodedFormulaAtomicallyAdequate M lowerPiApplication ->
    exists certificate : M,
      RawCodedPAProofOf M
        (rawDynamicTruthMixedQFCellCode M DTMQFSigmaAllPiQF
          lowerPiApplication (rawFormulaBotCode M)) certificate).

Theorem
    rawDynamicTruthMixedQFOpaqueQuantifierAdequateCellProofCompiler_of_trace
    : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthQuantifierLowerApplicationDirectTraceTotal M ->
  RawDynamicTruthMixedQFOpaqueQuantifierAdequateCellProofCompiler M.
Proof.
  intros M hPA htrace. split.
  - intros lowerSigmaApplication hadequate.
    destruct (htrace lowerSigmaApplication hadequate) as [trace].
    exact (raw_codedPAProofOf_dynamicTruthSigmaQFPiExOpaqueCell_direct
      M hPA lowerSigmaApplication trace).
  - intros lowerPiApplication hadequate.
    destruct (htrace lowerPiApplication hadequate) as [trace].
    exact (raw_codedPAProofOf_dynamicTruthSigmaAllPiQFOpaqueCell_direct
      M hPA lowerPiApplication trace).
Qed.

(** The original opaque compiler quantifies over every carrier element, not
    merely adequate formula codes.  Its smallest honest trace premise is
    therefore the corresponding all-carrier direct-trace totality. *)
Definition RawDynamicTruthMixedQFLowerApplicationDirectTraceTotal
    (M : RawPAModel) : Prop :=
  forall lowerApplication : M,
    inhabited
      (RawDynamicTruthQuantifierLowerApplicationDirectTrace
        M lowerApplication).

Arguments RawDynamicTruthMixedQFLowerApplicationDirectTraceTotal M
  : clear implicits.

Theorem rawDynamicTruthMixedQFOpaqueQuantifierCellProofCompiler_of_trace :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthMixedQFLowerApplicationDirectTraceTotal M ->
  RawDynamicTruthMixedQFOpaqueQuantifierCellProofCompiler M.
Proof.
  intros M hPA htrace. split.
  - intro lowerSigmaApplication.
    destruct (htrace lowerSigmaApplication) as [trace].
    exact (raw_codedPAProofOf_dynamicTruthSigmaQFPiExOpaqueCell_direct
      M hPA lowerSigmaApplication trace).
  - intro lowerPiApplication.
    destruct (htrace lowerPiApplication) as [trace].
    exact (raw_codedPAProofOf_dynamicTruthSigmaAllPiQFOpaqueCell_direct
      M hPA lowerPiApplication trace).
Qed.

Corollary raw_dynamicTruthMixedQFCellProofCompilerTotal_of_trace :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthMixedQFLowerApplicationDirectTraceTotal M ->
  RawDynamicTruthMixedQFCellProofCompilerTotal M.
Proof.
  intros M hPA htrace.
  apply (raw_dynamicTruthMixedQFCellProofCompilerTotal_of_opaque M hPA).
  exact (rawDynamicTruthMixedQFOpaqueQuantifierCellProofCompiler_of_trace
    M hPA htrace).
Qed.

End PABoundedRawCodedDynamicTruthMixedQFOpaqueQuantifierCellCompilation.
