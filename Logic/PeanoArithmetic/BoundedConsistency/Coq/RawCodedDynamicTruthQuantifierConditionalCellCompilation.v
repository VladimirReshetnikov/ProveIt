(**
  Structural compilation of the two conditional quantifier cells.

  The cells in [RawCodedDynamicTruthQuantifierBranchExclusivity] were first
  proved for each standard lower-application formula.  Such a theorem cannot
  simply be quoted at a nonstandard carrier code.  Here the same proof is
  expressed as a finite [TemplateRawProof].  Its sole opaque atom is the
  selected lower application, and the direct structural translation carries
  every shift and opening trace needed by the eight existential eliminations.

  Atomic adequacy of one carrier formula does not by itself manufacture those
  operation traces.  The exact remaining premise is therefore packaged as a
  direct template input whose designated atom translates to that carrier
  formula.  Under that premise this file constructs ordinary represented PA
  certificates and, independently, compiles the same trees directly in any
  realizable self-shifting common context.  No object proof is obtained from
  semantic validity.
*)

From Stdlib Require Import List Arith.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedPAProvability
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedContextShift
  RawCodedPALocalProofExistential
  RawCodedTemplateSyntax
  RawCodedFixedLevelTruthTotality
  RawCodedTemplateLogicalSchemas
  RawCodedTemplateProjectionSchemas
  RawCodedTemplateProofCompiler
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateTernaryApplication
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateClosedProofCompilation
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedDynamicTruthTemplateNumeralParameters
  RawCodedDynamicTruthTemplateDirectInputs
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthUniversalLeafSourceTemplate
  RawCodedDynamicTruthPiUniversalLeafSourceTemplate
  RawCodedDynamicTruthQuantifierBranchExclusivity.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthQuantifierConditionalCellCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedTemplateLogicalSchemas.
Import PABoundedRawCodedTemplateProjectionSchemas.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateClosedProofCompilation.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedDynamicTruthTemplateNumeralParameters.
Import PABoundedRawCodedDynamicTruthTemplateDirectInputs.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthPiUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthQuantifierBranchExclusivity.

(** ------------------------------------------------------------------
    A generic direct proof of

      (forall^n (P -> C)) -> (exists^n (P and (C -> bottom))) -> bottom.

    At a successor binder, existential elimination introduces its witness.
    The shifted universal assumption is specialized at that same witness;
    the recursive implication then handles the remaining binders.  Building
    an implication in every ambient context avoids any hidden weakening. *)

Fixpoint templateRepeatedAllExistsCollisionProof
    (binderCount : nat) (ambient : TemplateContext)
    (prefix counterexample : TemplateFormula) : TemplateRawProof :=
  let universal := templateRepeatedForall binderCount
    (tfImp prefix counterexample) in
  let existential := templateRepeatedExists binderCount
    (tfAnd prefix (tfImp counterexample tfBot)) in
  match binderCount with
  | 0 =>
      let universalContext := universal :: ambient in
      let collisionContext := existential :: universalContext in
      let existentialProof := trpAss collisionContext existential in
      let prefixProof := trpAndE1 collisionContext prefix
        (tfImp counterexample tfBot) existentialProof in
      let negativeProof := trpAndE2 collisionContext prefix
        (tfImp counterexample tfBot) existentialProof in
      let counterexampleProof := trpImpE collisionContext prefix
        counterexample
        (trpAss collisionContext universal) prefixProof in
      trpImpI ambient universal (tfImp existential tfBot)
        (trpImpI universalContext existential tfBot
          (trpImpE collisionContext counterexample tfBot
            negativeProof counterexampleProof))
  | S smaller =>
      let universalBody := templateRepeatedForall smaller
        (tfImp prefix counterexample) in
      let existentialBody := templateRepeatedExists smaller
        (tfAnd prefix (tfImp counterexample tfBot)) in
      let universalContext := universal :: ambient in
      let collisionContext := existential :: universalContext in
      let eigenContext :=
        existentialBody :: templateContextShift collisionContext in
      let shiftedUniversalBody :=
        templateFormulaRename (templateUpRenaming S) universalBody in
      let universalBodyProof :=
        trpAllE eigenContext shiftedUniversalBody (ttVar 0)
          (trpAss eigenContext (tfAll shiftedUniversalBody)) in
      let recursiveImplication :=
        templateRepeatedAllExistsCollisionProof smaller eigenContext
          prefix counterexample in
      let afterUniversal := trpImpE eigenContext universalBody
        (tfImp existentialBody tfBot)
        recursiveImplication universalBodyProof in
      let bottomProof := trpImpE eigenContext existentialBody tfBot
        afterUniversal (trpAss eigenContext existentialBody) in
      trpImpI ambient universal (tfImp existential tfBot)
        (trpImpI universalContext existential tfBot
          (trpExE collisionContext existentialBody tfBot
            (trpAss collisionContext existential) bottomProof))
  end.

Arguments templateRepeatedAllExistsCollisionProof
  binderCount ambient prefix counterexample : clear implicits.

Theorem templateRepeatedAllExistsCollisionProof_derives : forall
    binderCount ambient prefix counterexample,
  TemplateRawDerives ambient
    (tfImp
      (templateRepeatedForall binderCount (tfImp prefix counterexample))
      (tfImp
        (templateRepeatedExists binderCount
          (tfAnd prefix (tfImp counterexample tfBot)))
        tfBot))
    (templateRepeatedAllExistsCollisionProof binderCount ambient
      prefix counterexample).
Proof.
  induction binderCount as [|smaller ih];
    intros ambient prefix counterexample.
  - unfold templateRepeatedAllExistsCollisionProof.
    unfold TemplateRawDerives.
    cbn [templateRepeatedForall templateRepeatedExists
      TemplateRawProofValid templateRawContext templateRawConclusion].
    repeat split; auto.
    all: cbn; auto.
  - cbn [templateRepeatedAllExistsCollisionProof
      templateRepeatedForall templateRepeatedExists].
    set (universalBody := templateRepeatedForall smaller
      (tfImp prefix counterexample)).
    set (existentialBody := templateRepeatedExists smaller
      (tfAnd prefix (tfImp counterexample tfBot))).
    set (universal := tfAll universalBody).
    set (existential := tfEx existentialBody).
    set (universalContext := universal :: ambient).
    set (collisionContext := existential :: universalContext).
    set (eigenContext :=
      existentialBody :: templateContextShift collisionContext).
    set (shiftedUniversalBody :=
      templateFormulaRename (templateUpRenaming S) universalBody).
    pose proof (ih eigenContext prefix counterexample) as hrecursive.
    destruct hrecursive as
      [hrecursiveValid [hrecursiveContext hrecursiveConclusion]].
    unfold shiftedUniversalBody.
    unfold TemplateRawDerives.
    cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
    rewrite templateFormulaOpen_binderShift_zero.
    repeat split; try assumption; try reflexivity; auto.
    all: unfold eigenContext, collisionContext, universalContext,
      universal, existential in *;
      cbn [templateContextShift templateContextRename] in *;
      try assumption; try reflexivity; auto.
    all: try (left; reflexivity).
    all: try (right; right; left; reflexivity).
Qed.

(** Curry a branch-to-universal bridge ahead of the collision theorem. *)
Definition templateQuantifierConditionalCellProof
    (binderCount : nat) (bridgeBranch prefix counterexample : TemplateFormula)
    : TemplateRawProof :=
  let universal := templateRepeatedForall binderCount
    (tfImp prefix counterexample) in
  let existential := templateRepeatedExists binderCount
    (tfAnd prefix (tfImp counterexample tfBot)) in
  let bridge := tfImp bridgeBranch universal in
  let bridgeContext := [bridge] in
  let branchContext := [bridgeBranch; bridge] in
  let existentialContext := [existential; bridgeBranch; bridge] in
  let universalProof := trpImpE existentialContext bridgeBranch universal
    (trpAss existentialContext bridge)
    (trpAss existentialContext bridgeBranch) in
  let collisionImplication :=
    templateRepeatedAllExistsCollisionProof binderCount
      existentialContext prefix counterexample in
  let afterUniversal := trpImpE existentialContext universal
    (tfImp existential tfBot) collisionImplication universalProof in
  trpImpI [] bridge (tfImp bridgeBranch (tfImp existential tfBot))
    (trpImpI bridgeContext bridgeBranch (tfImp existential tfBot)
      (trpImpI branchContext existential tfBot
        (trpImpE existentialContext existential tfBot afterUniversal
          (trpAss existentialContext existential)))).

Theorem templateQuantifierConditionalCellProof_derives : forall
    binderCount bridgeBranch prefix counterexample,
  TemplateRawDerives []
    (tfImp
      (tfImp bridgeBranch
        (templateRepeatedForall binderCount
          (tfImp prefix counterexample)))
      (tfImp bridgeBranch
        (tfImp
          (templateRepeatedExists binderCount
            (tfAnd prefix (tfImp counterexample tfBot)))
          tfBot)))
    (templateQuantifierConditionalCellProof binderCount
      bridgeBranch prefix counterexample).
Proof.
  intros binderCount bridgeBranch prefix counterexample.
  unfold templateQuantifierConditionalCellProof.
  pose proof (templateRepeatedAllExistsCollisionProof_derives
    binderCount
    [templateRepeatedExists binderCount
       (tfAnd prefix (tfImp counterexample tfBot));
     bridgeBranch;
     tfImp bridgeBranch
       (templateRepeatedForall binderCount
         (tfImp prefix counterexample))]
    prefix counterexample) as hcollision.
  destruct hcollision as [hvalid [hcontext hconclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; try assumption; try reflexivity; auto.
  all: try (left; reflexivity).
  all: try (right; left; reflexivity).
  all: try (right; right; left; reflexivity).
Qed.

(** The universal diagonal has the two final branch assumptions in the
    opposite order: the Sigma universal branch comes before the Pi-all
    bridge branch. *)
Definition templateQuantifierConditionalCellReversedProof
    (binderCount : nat) (bridgeBranch prefix counterexample : TemplateFormula)
    : TemplateRawProof :=
  let universal := templateRepeatedForall binderCount
    (tfImp prefix counterexample) in
  let existential := templateRepeatedExists binderCount
    (tfAnd prefix (tfImp counterexample tfBot)) in
  let bridge := tfImp bridgeBranch universal in
  let bridgeContext := [bridge] in
  let existentialContext := [existential; bridge] in
  let branchContext := [bridgeBranch; existential; bridge] in
  let universalProof := trpImpE branchContext bridgeBranch universal
    (trpAss branchContext bridge) (trpAss branchContext bridgeBranch) in
  let collisionImplication :=
    templateRepeatedAllExistsCollisionProof binderCount branchContext
      prefix counterexample in
  let afterUniversal := trpImpE branchContext universal
    (tfImp existential tfBot) collisionImplication universalProof in
  trpImpI [] bridge (tfImp existential (tfImp bridgeBranch tfBot))
    (trpImpI bridgeContext existential (tfImp bridgeBranch tfBot)
      (trpImpI existentialContext bridgeBranch tfBot
        (trpImpE branchContext existential tfBot afterUniversal
          (trpAss branchContext existential)))).

Theorem templateQuantifierConditionalCellReversedProof_derives : forall
    binderCount bridgeBranch prefix counterexample,
  TemplateRawDerives []
    (tfImp
      (tfImp bridgeBranch
        (templateRepeatedForall binderCount
          (tfImp prefix counterexample)))
      (tfImp
        (templateRepeatedExists binderCount
          (tfAnd prefix (tfImp counterexample tfBot)))
        (tfImp bridgeBranch tfBot)))
    (templateQuantifierConditionalCellReversedProof binderCount
      bridgeBranch prefix counterexample).
Proof.
  intros binderCount bridgeBranch prefix counterexample.
  unfold templateQuantifierConditionalCellReversedProof.
  pose proof (templateRepeatedAllExistsCollisionProof_derives
    binderCount
    [bridgeBranch;
     templateRepeatedExists binderCount
       (tfAnd prefix (tfImp counterexample tfBot));
     tfImp bridgeBranch
       (templateRepeatedForall binderCount
         (tfImp prefix counterexample))]
    prefix counterexample) as hcollision.
  destruct hcollision as [hvalid [hcontext hconclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; try assumption; try reflexivity; auto.
  all: try (left; reflexivity).
  all: try (right; left; reflexivity).
  all: try (right; right; left; reflexivity).
Qed.

(** ------------------------------------------------------------------
    The two native template instances. *)

Definition coqDynamicTruthSigmaEx8BranchTemplate : TemplateFormula :=
  templateRepeatedExists 8 coqDynamicTruthSigmaExLeafTemplate.

Definition coqDynamicTruthPiExistentialCounterexampleTemplate
    : TemplateFormula :=
  templateRepeatedExists 3
    (tfAnd coqDynamicTruthPiBinderPrependTemplate
      coqDynamicTruthLowerSigmaAtomTemplate).

Definition coqDynamicTruthPiExistentialEx8BranchTemplate
    : TemplateFormula :=
  templateRepeatedExists 8
    (tfAnd coqDynamicTruthPiExistentialPrefixTemplate
      (tfImp coqDynamicTruthPiExistentialCounterexampleTemplate tfBot)).

Definition coqDynamicTruthSigmaExPiExConditionalCellTemplate
    : TemplateFormula :=
  tfImp
    (tfImp coqDynamicTruthSigmaEx8BranchTemplate
      (templateRepeatedForall 8
        (tfImp coqDynamicTruthPiExistentialPrefixTemplate
          coqDynamicTruthPiExistentialCounterexampleTemplate)))
    (tfImp coqDynamicTruthSigmaEx8BranchTemplate
      (tfImp coqDynamicTruthPiExistentialEx8BranchTemplate tfBot)).

Definition coqDynamicTruthSigmaExPiExConditionalCellTemplateProof
    : TemplateRawProof :=
  templateQuantifierConditionalCellProof 8
    coqDynamicTruthSigmaEx8BranchTemplate
    coqDynamicTruthPiExistentialPrefixTemplate
    coqDynamicTruthPiExistentialCounterexampleTemplate.

Theorem coqDynamicTruthSigmaExPiExConditionalCellTemplateProof_derives :
  TemplateRawDerives []
    coqDynamicTruthSigmaExPiExConditionalCellTemplate
    coqDynamicTruthSigmaExPiExConditionalCellTemplateProof.
Proof.
  unfold coqDynamicTruthSigmaExPiExConditionalCellTemplate,
    coqDynamicTruthSigmaExPiExConditionalCellTemplateProof,
    coqDynamicTruthPiExistentialEx8BranchTemplate.
  apply templateQuantifierConditionalCellProof_derives.
Qed.

Definition coqDynamicTruthSigmaUniversalCounterexampleTemplate
    : TemplateFormula :=
  templateRepeatedExists 3
    (tfAnd coqDynamicTruthSigmaBinderPrependTemplate
      coqDynamicTruthLowerPiAtomTemplate).

Definition coqDynamicTruthSigmaUniversalEx8BranchTemplate
    : TemplateFormula :=
  templateRepeatedExists 8
    (tfAnd coqDynamicTruthSigmaUniversalPrefixTemplate
      (tfImp coqDynamicTruthSigmaUniversalCounterexampleTemplate tfBot)).

Definition coqDynamicTruthPiAllEx8BranchTemplate : TemplateFormula :=
  templateRepeatedExists 8 coqDynamicTruthPiAllLeafTemplate.

Definition coqDynamicTruthSigmaAllPiAllConditionalCellTemplate
    : TemplateFormula :=
  tfImp
    (tfImp coqDynamicTruthPiAllEx8BranchTemplate
      (templateRepeatedForall 8
        (tfImp coqDynamicTruthSigmaUniversalPrefixTemplate
          coqDynamicTruthSigmaUniversalCounterexampleTemplate)))
    (tfImp coqDynamicTruthSigmaUniversalEx8BranchTemplate
      (tfImp coqDynamicTruthPiAllEx8BranchTemplate tfBot)).

Definition coqDynamicTruthSigmaAllPiAllConditionalCellTemplateProof
    : TemplateRawProof :=
  templateQuantifierConditionalCellReversedProof 8
    coqDynamicTruthPiAllEx8BranchTemplate
    coqDynamicTruthSigmaUniversalPrefixTemplate
    coqDynamicTruthSigmaUniversalCounterexampleTemplate.

Theorem coqDynamicTruthSigmaAllPiAllConditionalCellTemplateProof_derives :
  TemplateRawDerives []
    coqDynamicTruthSigmaAllPiAllConditionalCellTemplate
    coqDynamicTruthSigmaAllPiAllConditionalCellTemplateProof.
Proof.
  unfold coqDynamicTruthSigmaAllPiAllConditionalCellTemplate,
    coqDynamicTruthSigmaAllPiAllConditionalCellTemplateProof,
    coqDynamicTruthSigmaUniversalEx8BranchTemplate.
  apply templateQuantifierConditionalCellReversedProof_derives.
Qed.

(** ------------------------------------------------------------------
    Narrow carrier trace premise and exact translation equations. *)

Record RawDynamicTruthQuantifierLowerApplicationDirectTrace
    (M : RawPAModel) (lowerApplication : M) : Type := {
  rawDynamicTruthQuantifierLowerApplication_inputs :
    RawCodedTemplateDirectStructuralInputs M;
  rawDynamicTruthQuantifierLowerApplication_designated :
    rawDirectTemplateFormula
      rawDynamicTruthQuantifierLowerApplication_inputs
      coqDynamicTruthLowerPiAtomTemplate = lowerApplication
}.

Arguments rawDynamicTruthQuantifierLowerApplication_inputs
  {M lowerApplication} _.
Arguments rawDynamicTruthQuantifierLowerApplication_designated
  {M lowerApplication} _.

Definition RawDynamicTruthQuantifierLowerApplicationDirectTraceTotal
    (M : RawPAModel) : Prop :=
  forall lowerApplication : M,
    RawCodedFormulaAtomicallyAdequate M lowerApplication ->
    inhabited
      (RawDynamicTruthQuantifierLowerApplicationDirectTrace
        M lowerApplication).

Arguments RawDynamicTruthQuantifierLowerApplicationDirectTraceTotal M
  : clear implicits.

Lemma rawDynamicTruthQuantifierLowerApplication_sigma_designated : forall
    (M : RawPAModel) lowerApplication
    (trace : RawDynamicTruthQuantifierLowerApplicationDirectTrace
      M lowerApplication),
  rawDirectTemplateFormula
    (rawDynamicTruthQuantifierLowerApplication_inputs trace)
    coqDynamicTruthLowerSigmaAtomTemplate = lowerApplication.
Proof.
  intros M lowerApplication trace.
  change (rawDirectTemplateFormula
    (rawDynamicTruthQuantifierLowerApplication_inputs trace)
    coqDynamicTruthLowerPiAtomTemplate = lowerApplication).
  apply rawDynamicTruthQuantifierLowerApplication_designated.
Qed.

(** Native predecessor selectors furnish the exact direct trace package.
    This adapter shows that the premise above is not a second application
    semantics: it is precisely the selector's represented shift/open
    commutation plus the native three-substitution application trace. *)
Theorem rawDynamicTruthQuantifierLowerApplicationDirectTrace_of_native :
    forall (M : RawPAModel) (hPA : RawPASatisfies M)
      (lowerLevel upperLevel lowerPredicate lowerApplication : M)
      (selector : RawCodedTernaryApplicationSelector M lowerPredicate),
  RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax
    M lowerPredicate selector ->
  RawDynamicTruthCoqLowerApplication M
    lowerPredicate lowerApplication ->
  inhabited
    (RawDynamicTruthQuantifierLowerApplicationDirectTrace
      M lowerApplication).
Proof.
  intros M hPA lowerLevel upperLevel lowerPredicate lowerApplication
    selector commutingOnSyntax hlowerApplication.
  destruct (raw_coqDynamicTruthTemplateNumeralTermPackage_exists
    M hPA lowerLevel upperLevel
    (rawCoqDynamicTruthTemplateOpaqueCode selector))
    as [package _].
  pose (inputs := rawCoqDynamicTruthTemplateDirectStructuralInputs
    M hPA lowerLevel upperLevel lowerPredicate selector
    commutingOnSyntax package).
  constructor.
  refine {| rawDynamicTruthQuantifierLowerApplication_inputs := inputs |}.
  exact (rawCoqDynamicTruthLowerPiAtom_identifies_native_application
    M hPA lowerLevel upperLevel lowerPredicate selector
    commutingOnSyntax package lowerApplication hlowerApplication).
Qed.

Corollary rawDynamicTruthQuantifierLowerApplicationDirectTrace_of_native_pi :
    forall (M : RawPAModel) (hPA : RawPASatisfies M)
      (lowerLevel upperLevel lowerPredicate lowerApplication : M)
      (selector : RawCodedTernaryApplicationSelector M lowerPredicate),
  RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax
    M lowerPredicate selector ->
  RawDynamicTruthPiCoqLowerApplication M
    lowerPredicate lowerApplication ->
  inhabited
    (RawDynamicTruthQuantifierLowerApplicationDirectTrace
      M lowerApplication).
Proof.
  intros M hPA lowerLevel upperLevel lowerPredicate lowerApplication
    selector commutingOnSyntax hlowerApplication.
  apply (rawDynamicTruthQuantifierLowerApplicationDirectTrace_of_native
    M hPA lowerLevel upperLevel lowerPredicate lowerApplication
    selector commutingOnSyntax).
  exact (proj1 (raw_dynamicTruthPiCoqLowerApplication_iff_sigma M
    lowerPredicate lowerApplication) hlowerApplication).
Qed.

Lemma rawDirectTemplateFormula_quantifier_embedPA : forall
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M)
    input,
  rawDirectTemplateFormula inputs (embedPAFormula input) =
  rawQuotedFormulaCode M input.
Proof.
  intros M inputs input.
  unfold rawDirectTemplateFormula.
  apply rawStructuralTemplateFormulaWith_embedPA.
Qed.

Theorem rawDirect_dynamicTruthSigmaExPiExConditionalCellTemplate_identified :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      lowerApplication
      (trace : RawDynamicTruthQuantifierLowerApplicationDirectTrace
        M lowerApplication),
  rawDirectTemplateFormula
    (rawDynamicTruthQuantifierLowerApplication_inputs trace)
    coqDynamicTruthSigmaExPiExConditionalCellTemplate =
  rawDynamicTruthSigmaExPiExConditionalCellCode M lowerApplication.
Proof.
  intros M hPA lowerApplication trace.
  unfold coqDynamicTruthSigmaExPiExConditionalCellTemplate,
    coqDynamicTruthSigmaEx8BranchTemplate,
    coqDynamicTruthPiExistentialEx8BranchTemplate,
    coqDynamicTruthPiExistentialCounterexampleTemplate,
    coqDynamicTruthSigmaExLeafTemplate,
    coqDynamicTruthPiExistentialPrefixTemplate,
    coqDynamicTruthPiBinderPrependTemplate,
    rawDynamicTruthSigmaExPiExConditionalCellCode,
    rawDynamicTruthSigmaExPiExCrossLevelPremiseCode,
    rawDynamicTruthSigmaEx8BranchCode,
    rawDynamicTruthPiExistentialEx8BranchCode,
    rawCoqDynamicTruthPiExistentialLeafTemplateCode,
    rawDynamicTruthPiExistentialCounterexampleCode,
    rawDynamicTruthQuantifierAll8Code.
  cbn [templateRepeatedExists templateRepeatedForall
    rawDirectTemplateFormula rawStructuralTemplateFormulaWith].
  repeat rewrite rawDirectTemplateFormula_quantifier_embedPA.
  rewrite rawDynamicTruthQuantifierLowerApplication_sigma_designated.
  try rewrite !rawFixedFormulaNumeralCode_eq_quoted by exact hPA.
  try rewrite !rawDynamicTruthPiFixedFormulaNumeralCode_eq_quoted
    by exact hPA.
  reflexivity.
Qed.

Theorem rawDirect_dynamicTruthSigmaAllPiAllConditionalCellTemplate_identified :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      lowerApplication
      (trace : RawDynamicTruthQuantifierLowerApplicationDirectTrace
        M lowerApplication),
  rawDirectTemplateFormula
    (rawDynamicTruthQuantifierLowerApplication_inputs trace)
    coqDynamicTruthSigmaAllPiAllConditionalCellTemplate =
  rawDynamicTruthSigmaAllPiAllConditionalCellCode M lowerApplication.
Proof.
  intros M hPA lowerApplication trace.
  unfold coqDynamicTruthSigmaAllPiAllConditionalCellTemplate,
    coqDynamicTruthSigmaUniversalEx8BranchTemplate,
    coqDynamicTruthPiAllEx8BranchTemplate,
    coqDynamicTruthSigmaUniversalCounterexampleTemplate,
    coqDynamicTruthSigmaUniversalPrefixTemplate,
    coqDynamicTruthSigmaBinderPrependTemplate,
    coqDynamicTruthPiAllLeafTemplate,
    rawDynamicTruthSigmaAllPiAllConditionalCellCode,
    rawDynamicTruthSigmaAllPiAllCrossLevelPremiseCode,
    rawDynamicTruthSigmaUniversalEx8BranchCode,
    rawCoqDynamicTruthSigmaUniversalLeafTemplateCode,
    rawDynamicTruthPiAllEx8BranchCode,
    rawDynamicTruthSigmaUniversalCounterexampleCode,
    rawDynamicTruthQuantifierAll8Code.
  cbn [templateRepeatedExists templateRepeatedForall
    rawDirectTemplateFormula rawStructuralTemplateFormulaWith].
  repeat rewrite rawDirectTemplateFormula_quantifier_embedPA.
  rewrite rawDynamicTruthQuantifierLowerApplication_designated.
  try rewrite !rawFixedFormulaNumeralCode_eq_quoted by exact hPA.
  try rewrite !rawDynamicTruthPiFixedFormulaNumeralCode_eq_quoted
    by exact hPA.
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Exact represented certificates under the direct-trace premise. *)

Definition rawDynamicTruthQuantifierDirectTranslation
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (lowerApplication : M)
    (trace : RawDynamicTruthQuantifierLowerApplicationDirectTrace
      M lowerApplication) : RawCodedTemplateTranslation M :=
  rawDirectStructuralTemplateTranslation M hPA
    (rawDynamicTruthQuantifierLowerApplication_inputs trace).

Arguments rawDynamicTruthQuantifierDirectTranslation
  M hPA lowerApplication trace : clear implicits.

Definition rawDynamicTruthSigmaExPiExConditionalCellCertificate
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (lowerApplication : M)
    (trace : RawDynamicTruthQuantifierLowerApplicationDirectTrace
      M lowerApplication) : M :=
  rawClosedTemplateProofCertificate M
    (rawDynamicTruthQuantifierDirectTranslation
      M hPA lowerApplication trace)
    coqDynamicTruthSigmaExPiExConditionalCellTemplateProof.

Definition rawDynamicTruthSigmaAllPiAllConditionalCellCertificate
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (lowerApplication : M)
    (trace : RawDynamicTruthQuantifierLowerApplicationDirectTrace
      M lowerApplication) : M :=
  rawClosedTemplateProofCertificate M
    (rawDynamicTruthQuantifierDirectTranslation
      M hPA lowerApplication trace)
    coqDynamicTruthSigmaAllPiAllConditionalCellTemplateProof.

Arguments rawDynamicTruthSigmaExPiExConditionalCellCertificate
  M hPA lowerApplication trace : clear implicits.
Arguments rawDynamicTruthSigmaAllPiAllConditionalCellCertificate
  M hPA lowerApplication trace : clear implicits.

Theorem raw_codedPAProofOf_dynamicTruthSigmaExPiExConditionalCell_direct :
    forall (M : RawPAModel) (hPA : RawPASatisfies M)
      lowerApplication
      (trace : RawDynamicTruthQuantifierLowerApplicationDirectTrace
        M lowerApplication),
  RawCodedPAProofOf M
    (rawDynamicTruthSigmaExPiExConditionalCellCode M lowerApplication)
    (rawDynamicTruthSigmaExPiExConditionalCellCertificate
      M hPA lowerApplication trace).
Proof.
  intros M hPA lowerApplication trace.
  rewrite <-
    (rawDirect_dynamicTruthSigmaExPiExConditionalCellTemplate_identified
      M hPA lowerApplication trace).
  unfold rawDynamicTruthSigmaExPiExConditionalCellCertificate,
    rawDynamicTruthQuantifierDirectTranslation.
  apply (raw_codedPAProofOf_closedTemplate M hPA).
  exact coqDynamicTruthSigmaExPiExConditionalCellTemplateProof_derives.
Qed.

Theorem raw_codedPAProofOf_dynamicTruthSigmaAllPiAllConditionalCell_direct :
    forall (M : RawPAModel) (hPA : RawPASatisfies M)
      lowerApplication
      (trace : RawDynamicTruthQuantifierLowerApplicationDirectTrace
        M lowerApplication),
  RawCodedPAProofOf M
    (rawDynamicTruthSigmaAllPiAllConditionalCellCode M lowerApplication)
    (rawDynamicTruthSigmaAllPiAllConditionalCellCertificate
      M hPA lowerApplication trace).
Proof.
  intros M hPA lowerApplication trace.
  rewrite <-
    (rawDirect_dynamicTruthSigmaAllPiAllConditionalCellTemplate_identified
      M hPA lowerApplication trace).
  unfold rawDynamicTruthSigmaAllPiAllConditionalCellCertificate,
    rawDynamicTruthQuantifierDirectTranslation.
  apply (raw_codedPAProofOf_closedTemplate M hPA).
  exact coqDynamicTruthSigmaAllPiAllConditionalCellTemplateProof_derives.
Qed.

(** Hence the original arbitrary-carrier compiler interface follows from
    trace totality on adequate applications.  This theorem isolates the one
    implication not currently supplied by atomic adequacy alone. *)
Theorem
    rawDynamicTruthQuantifierConditionalCellCompilerTotal_of_directTraceTotal
    : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthQuantifierLowerApplicationDirectTraceTotal M ->
  RawDynamicTruthQuantifierConditionalCellCompilerTotal M.
Proof.
  intros M hPA htrace lowerSigmaApplication lowerPiApplication
    hsigmaAdequate hpiAdequate.
  destruct (htrace lowerSigmaApplication hsigmaAdequate)
    as [sigmaTrace].
  destruct (htrace lowerPiApplication hpiAdequate)
    as [piTrace].
  split.
  - exists (rawDynamicTruthSigmaExPiExConditionalCellCertificate
      M hPA lowerSigmaApplication sigmaTrace).
    exact
      (raw_codedPAProofOf_dynamicTruthSigmaExPiExConditionalCell_direct
        M hPA lowerSigmaApplication sigmaTrace).
  - exists (rawDynamicTruthSigmaAllPiAllConditionalCellCertificate
      M hPA lowerPiApplication piTrace).
    exact
      (raw_codedPAProofOf_dynamicTruthSigmaAllPiAllConditionalCell_direct
        M hPA lowerPiApplication piTrace).
Qed.

(** ------------------------------------------------------------------
    Direct compilation in an existing self-shifting common context. *)

Definition rawDynamicTruthSigmaExPiExConditionalCellLocalRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (baseContext lowerApplication : M)
    (trace : RawDynamicTruthQuantifierLowerApplicationDirectTrace
      M lowerApplication) : M :=
  rawTemplateProofCodeOnTail
    (rawDynamicTruthQuantifierDirectTranslation
      M hPA lowerApplication trace)
    baseContext coqDynamicTruthSigmaExPiExConditionalCellTemplateProof.

Definition rawDynamicTruthSigmaAllPiAllConditionalCellLocalRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (baseContext lowerApplication : M)
    (trace : RawDynamicTruthQuantifierLowerApplicationDirectTrace
      M lowerApplication) : M :=
  rawTemplateProofCodeOnTail
    (rawDynamicTruthQuantifierDirectTranslation
      M hPA lowerApplication trace)
    baseContext coqDynamicTruthSigmaAllPiAllConditionalCellTemplateProof.

Arguments rawDynamicTruthSigmaExPiExConditionalCellLocalRoot
  M hPA baseContext lowerApplication trace : clear implicits.
Arguments rawDynamicTruthSigmaAllPiAllConditionalCellLocalRoot
  M hPA baseContext lowerApplication trace : clear implicits.

Theorem
    raw_codedPALocalProofOf_dynamicTruthSigmaExPiExConditionalCell_direct
    : forall (M : RawPAModel) (hPA : RawPASatisfies M)
      baseContext lowerApplication
      (trace : RawDynamicTruthQuantifierLowerApplicationDirectTrace
        M lowerApplication),
  RawContextListRealizable M baseContext ->
  RawContextShift M baseContext baseContext ->
  RawCodedPALocalProofOf M baseContext
    (rawDynamicTruthSigmaExPiExConditionalCellCode M lowerApplication)
    (rawDynamicTruthSigmaExPiExConditionalCellLocalRoot
      M hPA baseContext lowerApplication trace).
Proof.
  intros M hPA baseContext lowerApplication trace
    hcontext hselfShift.
  rewrite <-
    (rawDirect_dynamicTruthSigmaExPiExConditionalCellTemplate_identified
      M hPA lowerApplication trace).
  unfold rawDynamicTruthSigmaExPiExConditionalCellLocalRoot,
    rawDynamicTruthQuantifierDirectTranslation.
  pose proof (raw_templateProofOnTail_localProof M hPA
    (rawDirectStructuralTemplateTranslation M hPA
      (rawDynamicTruthQuantifierLowerApplication_inputs trace))
    baseContext coqDynamicTruthSigmaExPiExConditionalCellTemplateProof
    hcontext hselfShift
    (proj1 coqDynamicTruthSigmaExPiExConditionalCellTemplateProof_derives))
    as hlocal.
  cbn [rawTemplateContextCodeOnTail] in hlocal.
  exact hlocal.
Qed.

Theorem
    raw_codedPALocalProofOf_dynamicTruthSigmaAllPiAllConditionalCell_direct
    : forall (M : RawPAModel) (hPA : RawPASatisfies M)
      baseContext lowerApplication
      (trace : RawDynamicTruthQuantifierLowerApplicationDirectTrace
        M lowerApplication),
  RawContextListRealizable M baseContext ->
  RawContextShift M baseContext baseContext ->
  RawCodedPALocalProofOf M baseContext
    (rawDynamicTruthSigmaAllPiAllConditionalCellCode M lowerApplication)
    (rawDynamicTruthSigmaAllPiAllConditionalCellLocalRoot
      M hPA baseContext lowerApplication trace).
Proof.
  intros M hPA baseContext lowerApplication trace
    hcontext hselfShift.
  rewrite <-
    (rawDirect_dynamicTruthSigmaAllPiAllConditionalCellTemplate_identified
      M hPA lowerApplication trace).
  unfold rawDynamicTruthSigmaAllPiAllConditionalCellLocalRoot,
    rawDynamicTruthQuantifierDirectTranslation.
  pose proof (raw_templateProofOnTail_localProof M hPA
    (rawDirectStructuralTemplateTranslation M hPA
      (rawDynamicTruthQuantifierLowerApplication_inputs trace))
    baseContext coqDynamicTruthSigmaAllPiAllConditionalCellTemplateProof
    hcontext hselfShift
    (proj1 coqDynamicTruthSigmaAllPiAllConditionalCellTemplateProof_derives))
    as hlocal.
  cbn [rawTemplateContextCodeOnTail] in hlocal.
  exact hlocal.
Qed.

End PABoundedRawCodedDynamicTruthQuantifierConditionalCellCompilation.
