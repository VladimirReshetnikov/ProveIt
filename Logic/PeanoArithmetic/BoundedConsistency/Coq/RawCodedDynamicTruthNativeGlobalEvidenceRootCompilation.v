(**
  Trace-linked proof boundaries for the native local decision field.

  The first witnessed-tail leaf compiler exposed two proof-producing
  interfaces.  Its global-evidence interface quantified four row parameters
  independently of the successor trace.  That type is stronger than the
  intended eliminator: an application could request proofs of row formulae
  unrelated to the local rows hidden in the global successor witness.

  This file records the smallest type-correct replacement.  A transparent
  relation ties the requested row domains and lower-predicate applications to
  the *same* paired successor, global wrapper, and ternary applications that
  occur in the native trace.  Every native trace has such parameters, purely
  by destructing its relational witnesses.  The corrected proof interface
  then existentially returns roots only for those linked rows.

  A dependent matrix-resource callback is indexed by those same selected
  parameters.  This supplies a corrected assembly route into the completed
  7-by-6 collision matrix while leaving the independent local-decision root
  interface explicit.

  No semantic validity, completeness principle, context erasure, proof
  irrelevance, or choice principle is used below.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedPALocalProofExistential
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthPairedSuccessorRowGraph
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthNativeLocalProofCompilation
  RawCodedDynamicTruthNativeLocalLeafRootCompiler.

Module PABoundedRawCodedDynamicTruthNativeGlobalEvidenceRootCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeLocalProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalLeafRootCompiler.

(** ------------------------------------------------------------------
    The exact row parameters selected by a native trace. *)

(** This relation deliberately repeats the wrapper and application edges.
    They identify the local rows with the two evidence formulae actually
    present in the exclusive context; row-code equalities alone would not
    provide that evidence linkage. *)
Definition RawDynamicTruthNativeTraceRowParametersAt
    (M : RawPAModel)
    (predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication : M) : Prop :=
  exists inputLevel evidenceGlobalSigma evidenceGlobalPi
      localSigmaRow localPiRow : M,
    inputLevel = raw_succ M predecessorLevel /\
    RawDynamicTruthPairedSuccessorRowAt M
      inputGlobalSigma inputGlobalPi inputLevel
      localSigmaRow localPiRow /\
    RawDynamicTruthPairedGlobalWrapperAt M
      localSigmaRow localPiRow evidenceGlobalSigma evidenceGlobalPi /\
    RawDynamicTruthLocalTernaryApplication M
      evidenceGlobalSigma sigmaEvidence /\
    RawDynamicTruthLocalTernaryApplication M
      evidenceGlobalPi piEvidence /\
    localSigmaRow = rawDynamicTruthSigmaSuccessorRowCode M
      sigmaRowDomain lowerPiApplication /\
    localPiRow = rawDynamicTruthPiSuccessorRowCode M
      piRowDomain lowerSigmaApplication.

Arguments RawDynamicTruthNativeTraceRowParametersAt
  M predecessorLevel inputGlobalSigma inputGlobalPi
  sigmaEvidence piEvidence sigmaRowDomain piRowDomain
  lowerPiApplication lowerSigmaApplication : clear implicits.

(** Relational successor totality already contains all four row parameters.
    This theorem merely exposes them without selecting new or unrelated
    carrier values. *)
Theorem raw_dynamicTruthNativeLocalProofTraceAt_exposes_linked_rows :
    forall (M : RawPAModel) (tail : nat -> M) predecessorLevel
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence,
  RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence ->
  exists sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication : M,
    RawDynamicTruthNativeTraceRowParametersAt M predecessorLevel
      inputGlobalSigma inputGlobalPi sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication.
Proof.
  intros M tail predecessorLevel inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence
    (_ & inputLevel & evidenceGlobalSigma & evidenceGlobalPi &
      inputLevelNumeral & hlevel & hsuccessor & _ & _ & _ &
      hsigmaApplication & hpiApplication).
  destruct hsuccessor as
    (localSigmaRow & localPiRow & [hsigmaRow hpiRow] & hwrapper).
  assert (hpairedRows : RawDynamicTruthPairedSuccessorRowAt M
      inputGlobalSigma inputGlobalPi inputLevel
      localSigmaRow localPiRow).
  { split; assumption. }
  destruct hsigmaRow as
    (sigmaUpperNumeral & sigmaRowDomain & lowerPiApplication &
      _ & _ & _ & hsigmaRowCode).
  destruct hpiRow as
    (piUpperNumeral & piRowDomain & lowerSigmaApplication &
      _ & _ & _ & hpiRowCode).
  exists sigmaRowDomain, piRowDomain,
    lowerPiApplication, lowerSigmaApplication.
  exists inputLevel, evidenceGlobalSigma, evidenceGlobalPi,
    localSigmaRow, localPiRow.
  split; [exact hlevel |].
  split; [exact hpairedRows |].
  split; [exact hwrapper |].
  split; [exact hsigmaApplication |].
  split; [exact hpiApplication |].
  split; [exact hsigmaRowCode | exact hpiRowCode].
Qed.

(** The corrected evidence eliminator existentially chooses the row
    parameters that it proves.  The link conjunct prevents those witnesses
    from drifting away from the successor and ternary-application witnesses
    in the supplied trace. *)
Definition RawDynamicTruthNativeGlobalEvidenceLinkedRowRootInterface
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence baseContext,
    RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence ->
    exists sigmaRowDomain piRowDomain
        lowerPiApplication lowerSigmaApplication
        sigmaRowRoot piRowRoot : M,
      RawDynamicTruthNativeTraceRowParametersAt M predecessorLevel
        inputGlobalSigma inputGlobalPi sigmaEvidence piEvidence
        sigmaRowDomain piRowDomain
        lowerPiApplication lowerSigmaApplication /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
          sigmaDomain piDomain sigmaEvidence piEvidence)
        (rawDynamicTruthSigmaSuccessorRowCode M
          sigmaRowDomain lowerPiApplication) sigmaRowRoot /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
          sigmaDomain piDomain sigmaEvidence piEvidence)
        (rawDynamicTruthPiSuccessorRowCode M
          piRowDomain lowerSigmaApplication) piRowRoot.

Arguments RawDynamicTruthNativeGlobalEvidenceLinkedRowRootInterface M
  : clear implicits.

(** Pointwise form of the remaining global-evidence compiler.  Unlike the
    original interface, its row parameters are guarded by an explicit link.
    Separating this form from existential selection makes the outstanding
    proof obligation usable by compilers that operate on already exposed
    successor witnesses. *)
Definition RawDynamicTruthNativeGlobalEvidenceLinkedRowRootCompiler
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence baseContext
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication,
    RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence ->
    RawDynamicTruthNativeTraceRowParametersAt M predecessorLevel
      inputGlobalSigma inputGlobalPi sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication ->
    exists sigmaRowRoot piRowRoot : M,
      RawCodedPALocalProofOf M
        (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
          sigmaDomain piDomain sigmaEvidence piEvidence)
        (rawDynamicTruthSigmaSuccessorRowCode M
          sigmaRowDomain lowerPiApplication) sigmaRowRoot /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
          sigmaDomain piDomain sigmaEvidence piEvidence)
        (rawDynamicTruthPiSuccessorRowCode M
          piRowDomain lowerSigmaApplication) piRowRoot.

Arguments RawDynamicTruthNativeGlobalEvidenceLinkedRowRootCompiler M
  : clear implicits.

Theorem
    raw_dynamicTruthNativeGlobalEvidenceLinkedRowRootInterface_of_compiler :
    forall (M : RawPAModel),
  RawDynamicTruthNativeGlobalEvidenceLinkedRowRootCompiler M ->
  RawDynamicTruthNativeGlobalEvidenceLinkedRowRootInterface M.
Proof.
  intros M hcompiler tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence baseContext htrace.
  destruct
    (raw_dynamicTruthNativeLocalProofTraceAt_exposes_linked_rows
      M tail predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence htrace) as
    (sigmaRowDomain & piRowDomain &
      lowerPiApplication & lowerSigmaApplication & hlinked).
  destruct (hcompiler tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence baseContext
    sigmaRowDomain piRowDomain
    lowerPiApplication lowerSigmaApplication
    htrace hlinked) as
    (sigmaRowRoot & piRowRoot & hsigmaRoot & hpiRoot).
  exists sigmaRowDomain, piRowDomain,
    lowerPiApplication, lowerSigmaApplication,
    sigmaRowRoot, piRowRoot.
  split; [exact hlinked |].
  split; [exact hsigmaRoot | exact hpiRoot].
Qed.

(** The older unconstrained interface can of course satisfy the corrected
    one: first expose the canonical parameters, then instantiate the old
    universal request at exactly those values.  The converse is intentionally
    absent, since it would recreate the invalid arbitrary-row strengthening. *)
Theorem
    raw_dynamicTruthNativeGlobalEvidenceLinkedRowRoots_of_unlinked_interface :
    forall (M : RawPAModel),
  RawDynamicTruthNativeGlobalEvidenceRowRootInterface M ->
  RawDynamicTruthNativeGlobalEvidenceLinkedRowRootInterface M.
Proof.
  intros M hunlinked tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence baseContext htrace.
  destruct
    (raw_dynamicTruthNativeLocalProofTraceAt_exposes_linked_rows
      M tail predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence htrace) as
    (sigmaRowDomain & piRowDomain &
      lowerPiApplication & lowerSigmaApplication & hlinked).
  destruct (hunlinked tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence baseContext
    sigmaRowDomain piRowDomain
    lowerPiApplication lowerSigmaApplication htrace) as
    (sigmaRowRoot & piRowRoot & hsigmaRoot & hpiRoot).
  exists sigmaRowDomain, piRowDomain,
    lowerPiApplication, lowerSigmaApplication,
    sigmaRowRoot, piRowRoot.
  split; [exact hlinked |].
  split; [exact hsigmaRoot | exact hpiRoot].
Qed.

(** ------------------------------------------------------------------
    A corrected, dependent leaf-assembly seam. *)

(** Matrix resources necessarily depend on the row parameters selected by
    global evidence elimination.  Quantifying the resource compiler after
    the linkage witness preserves that dependency and prevents a caller from
    supplying a matrix for different rows. *)
Definition RawDynamicTruthNativeLocalLinkedMatrixResourceCompiler
    (M : RawPAModel) : Type :=
  forall (tail : nat -> M) predecessorLevel
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence baseContext
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication,
    RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence ->
    RawDynamicTruthNativeTraceRowParametersAt M predecessorLevel
      inputGlobalSigma inputGlobalPi sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication ->
    RawDynamicTruthNativeLocalExclusiveMatrixResourcesAt M
      (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
        sigmaDomain piDomain sigmaEvidence piEvidence)
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication.

Arguments RawDynamicTruthNativeLocalLinkedMatrixResourceCompiler M
  : clear implicits.

(** The linked row roots and the dependent resource callback meet at exactly
    the same four parameters.  This is the corrected direct adapter into the
    already compiled row-projection/collision matrix endpoint. *)
Theorem
    raw_dynamicTruthNativeLocalExclusiveRootOn_of_linked_interfaces :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeGlobalEvidenceLinkedRowRootInterface M ->
  RawDynamicTruthNativeLocalLinkedMatrixResourceCompiler M ->
  forall (tail : nat -> M) predecessorLevel
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence baseContext,
    RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence ->
    RawDynamicTruthNativeLocalExclusiveRootOn M baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence.
Proof.
  intros M hPA hrows hresources
    tail predecessorLevel inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence baseContext htrace.
  destruct (hrows tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence baseContext htrace) as
    (sigmaRowDomain & piRowDomain &
     lowerPiApplication & lowerSigmaApplication &
     sigmaRowRoot & piRowRoot & hlinked &
     hsigmaRowRoot & hpiRowRoot).
  apply (raw_dynamicTruthNativeLocalExclusiveRootOn_of_rows_and_matrix
    M hPA baseContext sigmaDomain piDomain sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain
    lowerPiApplication lowerSigmaApplication).
  - exact (hresources tail predecessorLevel
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence baseContext
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication htrace hlinked).
  - exists sigmaRowRoot, piRowRoot. split; assumption.
Qed.

(** This is the type-correct replacement for assembling the two witnessed-
    tail leaves.  It obtains linked row roots and resources at the same
    parameters and invokes the already complete 7-by-6 exclusivity matrix.
    Decision-root production remains an independent premise. *)
Theorem raw_dynamicTruthNativeLocalLeafRootsOn_of_linked_interfaces :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeLocalDecisionEvidenceRootInterface M ->
  RawDynamicTruthNativeGlobalEvidenceLinkedRowRootInterface M ->
  RawDynamicTruthNativeLocalLinkedMatrixResourceCompiler M ->
  forall (tail : nat -> M) predecessorLevel
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence baseContext,
    RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence ->
    RawDynamicTruthNativeLocalLeafRootsOn M baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence.
Proof.
  intros M hPA hdecision hrows hresources
    tail predecessorLevel inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence baseContext
    htrace.
  split.
  - exact (hdecision tail predecessorLevel
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence baseContext htrace).
  - exact
      (raw_dynamicTruthNativeLocalExclusiveRootOn_of_linked_interfaces
        M hPA hrows hresources
        tail predecessorLevel inputGlobalSigma inputGlobalPi
        sigmaDomain piDomain sigmaEvidence piEvidence baseContext htrace).
Qed.

(** ------------------------------------------------------------------
    Exact empty-base specialization used by the native compiler. *)

(** The final native leaf compiler needs roots only over the literal empty
    base.  Keeping this specialization separate avoids asking a compiler for
    uniform weakening into every carrier-coded context. *)
Definition
    RawDynamicTruthNativeGlobalEvidenceLinkedRowRootInterfaceAtEmptyBase
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence ->
    exists sigmaRowDomain piRowDomain
        lowerPiApplication lowerSigmaApplication
        sigmaRowRoot piRowRoot : M,
      RawDynamicTruthNativeTraceRowParametersAt M predecessorLevel
        inputGlobalSigma inputGlobalPi sigmaEvidence piEvidence
        sigmaRowDomain piRowDomain
        lowerPiApplication lowerSigmaApplication /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthNativeLocalExclusivePiContextOn M (raw_zero M)
          sigmaDomain piDomain sigmaEvidence piEvidence)
        (rawDynamicTruthSigmaSuccessorRowCode M
          sigmaRowDomain lowerPiApplication) sigmaRowRoot /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthNativeLocalExclusivePiContextOn M (raw_zero M)
          sigmaDomain piDomain sigmaEvidence piEvidence)
        (rawDynamicTruthPiSuccessorRowCode M
          piRowDomain lowerSigmaApplication) piRowRoot.

Arguments
  RawDynamicTruthNativeGlobalEvidenceLinkedRowRootInterfaceAtEmptyBase M
  : clear implicits.

Theorem
    raw_dynamicTruthNativeGlobalEvidenceLinkedRowRoots_at_empty_base :
    forall (M : RawPAModel),
  RawDynamicTruthNativeGlobalEvidenceLinkedRowRootInterface M ->
  RawDynamicTruthNativeGlobalEvidenceLinkedRowRootInterfaceAtEmptyBase M.
Proof.
  intros M hrows tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence htrace.
  exact (hrows tail predecessorLevel inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence (raw_zero M) htrace).
Qed.

Definition
    RawDynamicTruthNativeLocalLinkedEmptyBaseMatrixResourceCompiler
    (M : RawPAModel) : Type :=
  forall (tail : nat -> M) predecessorLevel
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication,
    RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence ->
    RawDynamicTruthNativeTraceRowParametersAt M predecessorLevel
      inputGlobalSigma inputGlobalPi sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication ->
    RawDynamicTruthNativeLocalExclusiveMatrixResourcesAt M
      (rawDynamicTruthNativeLocalExclusivePiContextOn M (raw_zero M)
        sigmaDomain piDomain sigmaEvidence piEvidence)
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication.

Arguments
  RawDynamicTruthNativeLocalLinkedEmptyBaseMatrixResourceCompiler M
  : clear implicits.

Theorem raw_dynamicTruthNativeLocalLinkedMatrixResources_at_empty_base :
    forall (M : RawPAModel),
  RawDynamicTruthNativeLocalLinkedMatrixResourceCompiler M ->
  RawDynamicTruthNativeLocalLinkedEmptyBaseMatrixResourceCompiler M.
Proof.
  intros M hresources tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence sigmaRowDomain piRowDomain
    lowerPiApplication lowerSigmaApplication htrace hlinked.
  exact (hresources tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence (raw_zero M)
    sigmaRowDomain piRowDomain
    lowerPiApplication lowerSigmaApplication htrace hlinked).
Qed.

(** Exact direct adapter into the residual native leaf compiler.  All row
    witnesses and matrix resources live over [raw_zero M]; the final bridge
    is only the definitional empty-tail lemma from the witnessed-tail module. *)
Theorem
    raw_dynamicTruthNativeLocalLeafRootCompiler_of_linked_empty_base_interfaces :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeLocalDecisionEvidenceRootInterface M ->
  RawDynamicTruthNativeGlobalEvidenceLinkedRowRootInterfaceAtEmptyBase M ->
  RawDynamicTruthNativeLocalLinkedEmptyBaseMatrixResourceCompiler M ->
  RawDynamicTruthNativeLocalLeafRootCompiler M.
Proof.
  intros M hPA hdecision hrows hresources
    tail predecessorLevel inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence htrace.
  apply (raw_dynamicTruthNativeLocalLeafRootsAt_of_empty_tail M
    sigmaDomain piDomain sigmaEvidence piEvidence).
  split.
  - exact (hdecision tail predecessorLevel
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence (raw_zero M) htrace).
  - destruct (hrows tail predecessorLevel
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence htrace) as
      (sigmaRowDomain & piRowDomain &
       lowerPiApplication & lowerSigmaApplication &
       sigmaRowRoot & piRowRoot & hlinked &
       hsigmaRowRoot & hpiRowRoot).
    apply (raw_dynamicTruthNativeLocalExclusiveRootOn_of_rows_and_matrix
      M hPA (raw_zero M) sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication).
    + exact (hresources tail predecessorLevel
        inputGlobalSigma inputGlobalPi sigmaDomain piDomain
        sigmaEvidence piEvidence sigmaRowDomain piRowDomain
        lowerPiApplication lowerSigmaApplication htrace hlinked).
    + exists sigmaRowRoot, piRowRoot. split; assumption.
Qed.

Corollary raw_dynamicTruthNativeLocalLeafRootCompiler_of_linked_interfaces :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeLocalDecisionEvidenceRootInterface M ->
  RawDynamicTruthNativeGlobalEvidenceLinkedRowRootInterface M ->
  RawDynamicTruthNativeLocalLinkedMatrixResourceCompiler M ->
  RawDynamicTruthNativeLocalLeafRootCompiler M.
Proof.
  intros M hPA hdecision hrows hresources.
  exact
    (raw_dynamicTruthNativeLocalLeafRootCompiler_of_linked_empty_base_interfaces
      M hPA hdecision
      (raw_dynamicTruthNativeGlobalEvidenceLinkedRowRoots_at_empty_base
        M hrows)
      (raw_dynamicTruthNativeLocalLinkedMatrixResources_at_empty_base
        M hresources)).
Qed.

End PABoundedRawCodedDynamicTruthNativeGlobalEvidenceRootCompilation.
