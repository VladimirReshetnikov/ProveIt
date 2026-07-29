(**
  Restricted-proof descent at an arbitrary carrier hierarchy level.

  The standard API indexes restricted proofs by a metatheoretic [nat].  For
  the uniform direct theorem the level is instead the value of a bound PA
  variable and may be nonstandard.  The proof of recursive-child descent does
  not inspect that level: it reuses every node predicate verbatim while
  shrinking only the arithmetic traversal bound.

  This module records that observation over the compact restricted-target
  interpreter.  A tail-indexed carrier restriction exposes the two support
  tables and the traversal rows without assigning any external natural number
  to the hierarchy hole.  The Or-I-left reroot theorem then copies the parent
  rows to the child's successor prefix and reuses the same support tables.
*)

From Stdlib Require Import List Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedAssignment
  PolynomialPairInjectivity
  RawCodedSyntaxConstructors
  RawCodedProofConstructors
  RawCodedProofDescent
  RawCodedProofTraversal
  RawCodedProofEndpoints
  RawCodedProofOrIConstructors
  RawCodedContextLists
  RawCodedFormulaRankTraversal
  RawCodedContextBounds
  RawCodedRestrictedProofTraversal
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedRestrictedTargetTemplateSemantics.

Import ListNotations.

Module PABoundedRawCodedCarrierRestrictedProofReroot.

Import PA.
Import PAListCode.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedAssignment.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofTraversal.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofOrIConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedFormulaRankTraversal.
Import PABoundedRawCodedContextBounds.
Import PABoundedRawCodedRestrictedProofTraversal.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedRestrictedTargetTemplateSemantics.

(** Carrier-valued counterparts of the standard-level hierarchy predicates.
    Unlike [RawFormulaQuantifierBounded], these definitions compare the coded
    ranks with an arbitrary model element instead of a numeral.  They expose
    all dependence on [level] while eliminating dependence on the de Bruijn
    tail used to evaluate the compact target context. *)
Definition RawCarrierFormulaQuantifierBounded (M : RawPAModel)
    (level code : M) : Prop :=
  (exists sigma pi : M,
    RawCodedFormulaRank M code sigma pi /\ rawLe M sigma level) \/
  (exists sigma pi : M,
    RawCodedFormulaRank M code sigma pi /\ rawLe M pi level).

Definition RawCarrierContextAllBoundedWithTables (M : RawPAModel)
    (level bound headCode headStep : M) : Prop :=
  forall index,
    rawLt M index bound ->
    forall code,
      RawCodedAssignmentLookup M headCode headStep index code ->
      RawCarrierFormulaQuantifierBounded M level code.

Definition RawCarrierContextAllBounded (M : RawPAModel)
    (level root : M) : Prop :=
  exists bound tailCode tailStep headCode headStep : M,
    RawContextListTraversal M
      root bound tailCode tailStep headCode headStep /\
    RawCarrierContextAllBoundedWithTables M
      level bound headCode headStep.

Definition RawCarrierProofOccurrenceCaseBounded (M : RawPAModel)
    (level code context : M) (entry : M * list M) : Prop :=
  code = fst entry ->
  RawCarrierContextAllBounded M level context /\
  Forall (RawCarrierFormulaQuantifierBounded M level) (snd entry).

Definition RawCarrierProofConstructorOccurrencesBounded (M : RawPAModel)
    (level code : M) : Prop :=
  forall context a b c t child1 child2 child3 : M,
    Forall
      (RawCarrierProofOccurrenceCaseBounded M level code context)
      (rawProofOccurrenceCases M
        context a b c t child1 child2 child3).

Definition RawCarrierProofEndpointOccurrencesBounded (M : RawPAModel)
    (level code : M) : Prop :=
  forall context conclusion : M,
    RawProofEndpoint M code context conclusion ->
    RawCarrierContextAllBounded M level context /\
    RawCarrierFormulaQuantifierBounded M level conclusion.

Definition RawCarrierRestrictedProofNode (M : RawPAModel)
    (level code supportCode supportStep : M) : Prop :=
  RawProofSyntaxStep M code supportCode supportStep /\
  RawProofRuleEndpointExists M code /\
  RawCarrierProofConstructorOccurrencesBounded M level code /\
  RawCarrierProofEndpointOccurrencesBounded M level code.

Arguments RawCarrierFormulaQuantifierBounded M level code : clear implicits.
Arguments RawCarrierContextAllBoundedWithTables
  M level bound headCode headStep : clear implicits.
Arguments RawCarrierContextAllBounded M level root : clear implicits.
Arguments RawCarrierProofOccurrenceCaseBounded
  M level code context entry : clear implicits.
Arguments RawCarrierProofConstructorOccurrencesBounded
  M level code : clear implicits.
Arguments RawCarrierProofEndpointOccurrencesBounded
  M level code : clear implicits.
Arguments RawCarrierRestrictedProofNode
  M level code supportCode supportStep : clear implicits.

Lemma raw_restrictedTargetLeContextSat_iff : forall
    (M : RawPAModel) variables level lhs,
  rawRestrictedTargetFormulaContextSat M variables level
    (restrictedTargetLeContext lhs) <->
  rawLe M (raw_term_eval M variables lhs) level.
Proof.
  intros M variables level lhs.
  unfold restrictedTargetLeContext, rawLe.
  cbn [rawRestrictedTargetFormulaContextSat
    rawRestrictedTargetTermContextEval].
  cbn [raw_term_eval].
  setoid_rewrite raw_term_eval_rename.
  reflexivity.
Qed.

Lemma raw_restrictedTargetFormulaQuantifierBoundedContextSat_iff : forall
    (M : RawPAModel) variables level code,
  rawRestrictedTargetFormulaContextSat M variables level
    (restrictedTargetFormulaQuantifierBoundedContext code) <->
  RawCarrierFormulaQuantifierBounded M level
    (raw_term_eval M variables code).
Proof.
  intros M variables level code.
  unfold restrictedTargetFormulaQuantifierBoundedContext,
    restrictedTargetSigmaDomainContext,
    restrictedTargetPiDomainContext,
    restrictedTargetExN,
    RawCarrierFormulaQuantifierBounded.
  cbn [rawRestrictedTargetFormulaContextSat].
  setoid_rewrite raw_sat_codedFormulaRankTermAt_iff.
  repeat setoid_rewrite raw_restrictedTargetLeContextSat_iff.
  repeat setoid_rewrite raw_restrictedProof_eval_liftTerm_two.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_restrictedTargetContextAllBoundedWithTablesContextSat_iff : forall
    (M : RawPAModel) variables level bound headCode headStep,
  rawRestrictedTargetFormulaContextSat M variables level
    (restrictedTargetContextAllBoundedWithTablesContext
      bound headCode headStep) <->
  RawCarrierContextAllBoundedWithTables M level
    (raw_term_eval M variables bound)
    (raw_term_eval M variables headCode)
    (raw_term_eval M variables headStep).
Proof.
  intros M variables level bound headCode headStep.
  unfold restrictedTargetContextAllBoundedWithTablesContext,
    RawCarrierContextAllBoundedWithTables.
  cbn [rawRestrictedTargetFormulaContextSat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedAssignmentLookupTermAt_iff.
  setoid_rewrite raw_restrictedTargetFormulaQuantifierBoundedContextSat_iff.
  repeat setoid_rewrite raw_contextList_eval_liftTerm_one.
  repeat setoid_rewrite raw_contextBound_eval_liftTerm_two.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_restrictedTargetContextAllBoundedContextSat_iff : forall
    (M : RawPAModel) variables level root,
  rawRestrictedTargetFormulaContextSat M variables level
    (restrictedTargetContextAllBoundedContext root) <->
  RawCarrierContextAllBounded M level
    (raw_term_eval M variables root).
Proof.
  intros M variables level root.
  unfold restrictedTargetContextAllBoundedContext,
    restrictedTargetExN, RawCarrierContextAllBounded.
  cbn [rawRestrictedTargetFormulaContextSat].
  setoid_rewrite raw_sat_contextListTraversalTermAt_iff.
  setoid_rewrite
    raw_restrictedTargetContextAllBoundedWithTablesContextSat_iff.
  repeat setoid_rewrite raw_contextList_eval_liftTerm_five.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_restrictedTargetProofFormulaFieldsBoundedContextSat_iff : forall
    (M : RawPAModel) variables level fields,
  rawRestrictedTargetFormulaContextSat M variables level
    (restrictedTargetProofFormulaFieldsBoundedContext fields) <->
  Forall
    (fun field => RawCarrierFormulaQuantifierBounded M level
      (raw_term_eval M variables field))
    fields.
Proof.
  intros M variables level fields. induction fields as [|field tail ih].
  - cbn [restrictedTargetProofFormulaFieldsBoundedContext
      rawRestrictedTargetFormulaContextSat].
    split; intro; [constructor | reflexivity].
  - cbn [restrictedTargetProofFormulaFieldsBoundedContext
      rawRestrictedTargetFormulaContextSat].
    rewrite raw_restrictedTargetFormulaQuantifierBoundedContextSat_iff, ih.
    split.
    + intros [hfield htail]. constructor; assumption.
    + intros hall. inversion hall; subst. split; assumption.
Qed.

Lemma raw_restrictedTargetProofOccurrenceCasesBoundedContextSat_iff : forall
    (M : RawPAModel) variables level code context cases,
  rawRestrictedTargetFormulaContextSat M variables level
    (restrictedTargetProofOccurrenceCasesBoundedContext
      code context cases) <->
  Forall
    (RawCarrierProofOccurrenceCaseBounded M level
      (raw_term_eval M variables code)
      (raw_term_eval M variables context))
    (map
      (fun entry =>
        (raw_term_eval M variables (fst entry),
         map (raw_term_eval M variables) (snd entry)))
      cases).
Proof.
  intros M variables level code context cases.
  induction cases as [|[constructorCode formulaFields] tail ih].
  - cbn [restrictedTargetProofOccurrenceCasesBoundedContext
      rawRestrictedTargetFormulaContextSat].
    split; intro; [constructor | reflexivity].
  - cbn [restrictedTargetProofOccurrenceCasesBoundedContext
      rawRestrictedTargetFormulaContextSat map].
    rewrite raw_restrictedTargetContextAllBoundedContextSat_iff,
      raw_restrictedTargetProofFormulaFieldsBoundedContextSat_iff, ih.
    split.
    + intros [hhead htail]. constructor.
      * unfold RawCarrierProofOccurrenceCaseBounded. cbn [fst snd].
        intros heq. destruct (hhead heq) as [hcontext hfields].
        split; [exact hcontext |].
        rewrite Forall_map. exact hfields.
      * exact htail.
    + intros hall. inversion hall; subst. split.
      * intros heq.
        unfold RawCarrierProofOccurrenceCaseBounded in H1.
        cbn [fst snd] in H1.
        destruct (H1 heq) as [hcontext hfields].
        split; [exact hcontext |].
        rewrite Forall_map in hfields. exact hfields.
      * assumption.
Qed.

Lemma raw_restrictedTargetProofConstructorOccurrencesBoundedContextSat_iff :
    forall (M : RawPAModel) variables level code,
  rawRestrictedTargetFormulaContextSat M variables level
    (restrictedTargetProofConstructorOccurrencesBoundedContext code) <->
  RawCarrierProofConstructorOccurrencesBounded M level
    (raw_term_eval M variables code).
Proof.
  intros M variables level code.
  unfold restrictedTargetProofConstructorOccurrencesBoundedContext,
    restrictedTargetAllN,
    RawCarrierProofConstructorOccurrencesBounded.
  cbn [rawRestrictedTargetFormulaContextSat].
  setoid_rewrite
    raw_restrictedTargetProofOccurrenceCasesBoundedContextSat_iff.
  repeat setoid_rewrite raw_restrictedProof_eval_liftTerm_eight.
  repeat setoid_rewrite raw_eval_proofOccurrenceCasesTerms.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_restrictedTargetProofEndpointOccurrencesBoundedContextSat_iff :
    forall (M : RawPAModel) variables level code,
  rawRestrictedTargetFormulaContextSat M variables level
    (restrictedTargetProofEndpointOccurrencesBoundedContext code) <->
  RawCarrierProofEndpointOccurrencesBounded M level
    (raw_term_eval M variables code).
Proof.
  intros M variables level code.
  unfold restrictedTargetProofEndpointOccurrencesBoundedContext,
    restrictedTargetAllN,
    RawCarrierProofEndpointOccurrencesBounded.
  cbn [rawRestrictedTargetFormulaContextSat].
  setoid_rewrite raw_sat_proofEndpointTermAt_iff.
  setoid_rewrite raw_restrictedTargetContextAllBoundedContextSat_iff.
  setoid_rewrite
    raw_restrictedTargetFormulaQuantifierBoundedContextSat_iff.
  repeat setoid_rewrite raw_restrictedProof_eval_liftTerm_two.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_restrictedTargetProofNodeContextSat_iff : forall
    (M : RawPAModel) variables level code supportCode supportStep,
  rawRestrictedTargetFormulaContextSat M variables level
    (restrictedTargetProofNodeContext code supportCode supportStep) <->
  RawCarrierRestrictedProofNode M level
    (raw_term_eval M variables code)
    (raw_term_eval M variables supportCode)
    (raw_term_eval M variables supportStep).
Proof.
  intros M variables level code supportCode supportStep.
  unfold restrictedTargetProofNodeContext,
    RawCarrierRestrictedProofNode.
  cbn [rawRestrictedTargetFormulaContextSat].
  rewrite raw_sat_proofSyntaxStepTermAt_iff,
    raw_sat_proofRuleEndpointExistsTermAt_iff,
    raw_restrictedTargetProofConstructorOccurrencesBoundedContextSat_iff,
    raw_restrictedTargetProofEndpointOccurrencesBoundedContextSat_iff.
  reflexivity.
Qed.

(** The node context is kept syntactically intact.  This is what makes the
    relation carrier-parametric: every occurrence of the hierarchy hole has
    already been interpreted as [level], and descent merely reuses the same
    proposition for a smaller proof-code prefix. *)
Definition RawCarrierRestrictedProofNodeAt
    (M : RawPAModel) (tail : nat -> M) (level code supportCode supportStep : M)
    : Prop :=
  rawRestrictedTargetFormulaContextSat M
    (scons M code (scons M supportStep (scons M supportCode tail)))
    level
    (restrictedTargetProofNodeContext
      (tVar 0) (liftTerm 1 (tVar 1)) (liftTerm 1 (tVar 0))).

Definition RawCarrierRestrictedProofTraversalAt
    (M : RawPAModel) (tail : nat -> M)
    (level bound supportCode supportStep : M) : Prop :=
  RawCodedAssignmentDefinedThrough M supportCode supportStep bound /\
  forall code : M,
    rawLt M code bound ->
    rawProofCodeSupported M supportCode supportStep code ->
    RawCarrierRestrictedProofNodeAt M tail
      level code supportCode supportStep.

Definition RawCarrierRestrictedProofCertificateAt
    (M : RawPAModel) (tail : nat -> M)
    (level root supportCode supportStep : M) : Prop :=
  RawCarrierRestrictedProofTraversalAt M tail level
    (raw_succ M root) supportCode supportStep /\
  rawProofCodeSupported M supportCode supportStep root.

Definition RawCarrierRestrictedProofAt
    (M : RawPAModel) (tail : nat -> M) (level root : M) : Prop :=
  exists supportCode supportStep : M,
    RawCarrierRestrictedProofCertificateAt M tail
      level root supportCode supportStep.

Arguments RawCarrierRestrictedProofNodeAt
  M tail level code supportCode supportStep : clear implicits.
Arguments RawCarrierRestrictedProofTraversalAt
  M tail level bound supportCode supportStep : clear implicits.
Arguments RawCarrierRestrictedProofCertificateAt
  M tail level root supportCode supportStep : clear implicits.
Arguments RawCarrierRestrictedProofAt M tail level root : clear implicits.

(** The expanded node context has the same compact, tail-free semantics as
    [RawCarrierRestrictedProofNode].  This theorem is the key replacement for
    normalizing the enormous syntactic free-variable bound. *)
Lemma raw_carrierRestrictedProofNodeAt_iff : forall
    (M : RawPAModel) tail level code supportCode supportStep,
  RawCarrierRestrictedProofNodeAt M tail
    level code supportCode supportStep <->
  RawCarrierRestrictedProofNode M
    level code supportCode supportStep.
Proof.
  intros M tail level code supportCode supportStep.
  unfold RawCarrierRestrictedProofNodeAt.
  rewrite raw_restrictedTargetProofNodeContextSat_iff.
  repeat rewrite raw_restrictedProof_eval_liftTerm_one.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_carrierRestrictedProofNodeAt_tail_ext : forall
    (M : RawPAModel) firstTail secondTail
    level code supportCode supportStep,
  RawCarrierRestrictedProofNodeAt M firstTail
    level code supportCode supportStep <->
  RawCarrierRestrictedProofNodeAt M secondTail
    level code supportCode supportStep.
Proof.
  intros. rewrite !raw_carrierRestrictedProofNodeAt_iff. reflexivity.
Qed.

Lemma raw_carrierRestrictedProofTraversalAt_tail_ext : forall
    (M : RawPAModel) firstTail secondTail
    level bound supportCode supportStep,
  RawCarrierRestrictedProofTraversalAt M firstTail
    level bound supportCode supportStep <->
  RawCarrierRestrictedProofTraversalAt M secondTail
    level bound supportCode supportStep.
Proof.
  intros M firstTail secondTail level bound supportCode supportStep.
  unfold RawCarrierRestrictedProofTraversalAt.
  split; intros [hdefined hnodes]; split; [exact hdefined | |exact hdefined |].
  - intros code hcode hsupported.
    apply (proj1 (raw_carrierRestrictedProofNodeAt_tail_ext M
      firstTail secondTail level code supportCode supportStep)).
    exact (hnodes code hcode hsupported).
  - intros code hcode hsupported.
    apply (proj2 (raw_carrierRestrictedProofNodeAt_tail_ext M
      firstTail secondTail level code supportCode supportStep)).
    exact (hnodes code hcode hsupported).
Qed.

Lemma raw_carrierRestrictedProofCertificateAt_tail_ext : forall
    (M : RawPAModel) firstTail secondTail
    level root supportCode supportStep,
  RawCarrierRestrictedProofCertificateAt M firstTail
    level root supportCode supportStep <->
  RawCarrierRestrictedProofCertificateAt M secondTail
    level root supportCode supportStep.
Proof.
  intros M firstTail secondTail level root supportCode supportStep.
  unfold RawCarrierRestrictedProofCertificateAt.
  rewrite raw_carrierRestrictedProofTraversalAt_tail_ext. reflexivity.
Qed.

Lemma raw_carrierRestrictedProofAt_tail_ext : forall
    (M : RawPAModel) firstTail secondTail level root,
  RawCarrierRestrictedProofAt M firstTail level root <->
  RawCarrierRestrictedProofAt M secondTail level root.
Proof.
  intros M firstTail secondTail level root.
  unfold RawCarrierRestrictedProofAt.
  split; intros (supportCode & supportStep & hcertificate);
    exists supportCode, supportStep.
  - apply (proj1 (raw_carrierRestrictedProofCertificateAt_tail_ext M
      firstTail secondTail level root supportCode supportStep)).
    exact hcertificate.
  - apply (proj2 (raw_carrierRestrictedProofCertificateAt_tail_ext M
      firstTail secondTail level root supportCode supportStep)).
    exact hcertificate.
Qed.

(** The fixed syntax conjunct is the first field of every restricted node and
    is independent of the carrier hierarchy level. *)
Lemma raw_carrierRestrictedProofNodeAt_syntax : forall
    (M : RawPAModel) tail level code supportCode supportStep,
  RawCarrierRestrictedProofNodeAt M tail
    level code supportCode supportStep ->
  RawProofSyntaxStep M code supportCode supportStep.
Proof.
  intros M tail level code supportCode supportStep hnode.
  unfold RawCarrierRestrictedProofNodeAt,
    restrictedTargetProofNodeContext in hnode.
  cbn [rawRestrictedTargetFormulaContextSat] in hnode.
  destruct hnode as [hsyntax _].
  apply (proj1 (raw_sat_proofSyntaxStepTermAt_iff M
    (scons M code (scons M supportStep (scons M supportCode tail)))
    (tVar 0) (tVar 2) (tVar 1))) in hsyntax.
  cbn [raw_term_eval scons] in hsyntax.
  exact hsyntax.
Qed.

(** Structural view of the compact target context. *)
Theorem raw_carrierRestrictedProofContextSat_iff : forall
    (M : RawPAModel) (tail : nat -> M) level root,
  rawRestrictedTargetFormulaContextSat M tail level
    (restrictedTargetProofContext root) <->
  RawCarrierRestrictedProofAt M tail level
    (raw_term_eval M tail root).
Proof.
  intros M tail level root.
  unfold restrictedTargetProofContext, restrictedTargetExN,
    restrictedTargetProofCertificateWithSupportContext,
    restrictedTargetProofTraversalContext,
    RawCarrierRestrictedProofAt,
    RawCarrierRestrictedProofCertificateAt,
    RawCarrierRestrictedProofTraversalAt,
    RawCarrierRestrictedProofNodeAt.
  cbn [rawRestrictedTargetFormulaContextSat].
  setoid_rewrite raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_proofCodeSupportedTermAt_iff.
  repeat setoid_rewrite raw_restrictedProof_eval_liftTerm_one.
  cbn [raw_term_eval scons].
  split; intros
      (supportCode & supportStep & htraversal & hroot);
    exists supportCode, supportStep; split.
  - rewrite raw_restrictedProof_eval_liftTerm_two in htraversal.
    exact htraversal.
  - rewrite raw_restrictedProof_eval_liftTerm_two in hroot.
    exact hroot.
  - rewrite raw_restrictedProof_eval_liftTerm_two.
    exact htraversal.
  - rewrite raw_restrictedProof_eval_liftTerm_two.
    exact hroot.
Qed.

(** Shrinking the prefix does not touch any level-dependent node formula. *)
Theorem raw_carrierRestrictedProofTraversalAt_weaken : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    tail level large small supportCode supportStep,
  RawCarrierRestrictedProofTraversalAt M tail
    level large supportCode supportStep ->
  rawLe M small large ->
  RawCarrierRestrictedProofTraversalAt M tail
    level small supportCode supportStep.
Proof.
  intros M hPA tail level large small supportCode supportStep
    [hdefined hrows] hsmall. split.
  - intros index hindex. apply hdefined.
    exact (raw_lt_le_trans_pair M hPA index small large hindex hsmall).
  - intros code hcode hsupported. apply hrows; [|exact hsupported].
    exact (raw_lt_le_trans_pair M hPA code small large hcode hsmall).
Qed.

(** Carrier-parametric Or-I-left descent.  The constructor equation is the
    sole branch-specific premise; no hierarchy reasoning occurs. *)
Theorem raw_carrierRestrictedProofAt_orI_left_child : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    tail level root context leftFormula rightFormula child,
  RawCarrierRestrictedProofAt M tail level root ->
  root = rawProofOrIRoot M RawOrLeft
    context leftFormula rightFormula child ->
  RawCarrierRestrictedProofAt M tail level child.
Proof.
  intros M hPA tail level root context leftFormula rightFormula child
    (supportCode & supportStep & htraversal & hroot) hcode.
  assert (hrootBelow : rawLt M root (raw_succ M root)).
  { apply raw_assignment_lt_self_succ. exact hPA. }
  pose proof (proj2 htraversal root hrootBelow hroot) as hrootNode.
  pose proof (raw_carrierRestrictedProofNodeAt_syntax M tail level
    root supportCode supportStep hrootNode) as hsyntax.
  assert (hconstructor : RawProofConstructorCode M
      root context leftFormula rightFormula
      (raw_zero M) (raw_zero M) child (raw_zero M) (raw_zero M)).
  {
    rewrite hcode.
    apply raw_proofOrIRoot_constructor.
  }
  pose proof (raw_proofSyntaxStep_closes_constructor M
    root supportCode supportStep hsyntax
    context leftFormula rightFormula
    (raw_zero M) (raw_zero M) child (raw_zero M) (raw_zero M)
    hconstructor) as hclosed.
  assert (hentry : In
      ([rawNumeralValue M 8; context; leftFormula; rightFormula; child],
       [child])
      (rawProofRecursiveCases M
        context leftFormula rightFormula
        (raw_zero M) (raw_zero M)
        child (raw_zero M) (raw_zero M))).
  { unfold rawProofRecursiveCases. cbn. tauto. }
  assert (hfields : root = rawListCode M
      [rawNumeralValue M 8; context; leftFormula; rightFormula; child]).
  { exact hcode. }
  destruct (raw_proofConstructorClosed_recursive_child M
    root supportCode supportStep
    context leftFormula rightFormula
    (raw_zero M) (raw_zero M) child (raw_zero M) (raw_zero M)
    hclosed
    [rawNumeralValue M 8; context; leftFormula; rightFormula; child]
    [child] hentry hfields child (or_introl eq_refl))
    as [hchildSupported hchildBelow].
  exists supportCode, supportStep. split.
  - apply (raw_carrierRestrictedProofTraversalAt_weaken M hPA tail level
      (raw_succ M root) (raw_succ M child)
      supportCode supportStep htraversal).
    eapply raw_le_trans; [exact hPA | |].
    + exact (raw_succ_le_of_lt_pair M hPA child root hchildBelow).
    + exact (raw_lt_to_le M root (raw_succ M root) hrootBelow).
  - exact hchildSupported.
Qed.

(** Assignment transport is orthogonal to recursive-child descent.  Once a
    node has been characterized by its carrier relations, the parent and
    child restrictions may be evaluated under unrelated surrounding tails. *)
Theorem raw_carrierRestrictedProofAt_orI_left_child_between : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    firstTail secondTail level root context leftFormula rightFormula child,
  RawCarrierRestrictedProofAt M firstTail level root ->
  root = rawProofOrIRoot M RawOrLeft
    context leftFormula rightFormula child ->
  RawCarrierRestrictedProofAt M secondTail level child.
Proof.
  intros M hPA firstTail secondTail level root context leftFormula
    rightFormula child hroot hcode.
  apply (proj1 (raw_carrierRestrictedProofAt_tail_ext M
    firstTail secondTail level child)).
  eapply raw_carrierRestrictedProofAt_orI_left_child; eauto.
Qed.

(** Direct compact-context form used by the fixed PA source. *)
Corollary raw_restrictedTargetProofContextSat_orI_left_child : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    tail level rootTerm childTerm contextTerm leftTerm rightTerm,
  rawRestrictedTargetFormulaContextSat M tail level
    (restrictedTargetProofContext rootTerm) ->
  raw_term_eval M tail rootTerm =
    rawProofOrIRoot M RawOrLeft
      (raw_term_eval M tail contextTerm)
      (raw_term_eval M tail leftTerm)
      (raw_term_eval M tail rightTerm)
      (raw_term_eval M tail childTerm) ->
  rawRestrictedTargetFormulaContextSat M tail level
    (restrictedTargetProofContext childTerm).
Proof.
  intros M hPA tail level rootTerm childTerm contextTerm
    leftTerm rightTerm hroot hcode.
  apply (proj2 (raw_carrierRestrictedProofContextSat_iff
    M tail level childTerm)).
  eapply raw_carrierRestrictedProofAt_orI_left_child; [exact hPA | |].
  - apply (proj1 (raw_carrierRestrictedProofContextSat_iff
      M tail level rootTerm)). exact hroot.
  - exact hcode.
Qed.

Corollary raw_restrictedTargetProofContextSat_orI_left_child_between : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    firstTail secondTail level
    rootTerm childTerm contextTerm leftTerm rightTerm,
  rawRestrictedTargetFormulaContextSat M firstTail level
    (restrictedTargetProofContext rootTerm) ->
  raw_term_eval M firstTail rootTerm =
    rawProofOrIRoot M RawOrLeft
      (raw_term_eval M firstTail contextTerm)
      (raw_term_eval M firstTail leftTerm)
      (raw_term_eval M firstTail rightTerm)
      (raw_term_eval M secondTail childTerm) ->
  rawRestrictedTargetFormulaContextSat M secondTail level
    (restrictedTargetProofContext childTerm).
Proof.
  intros M hPA firstTail secondTail level rootTerm childTerm contextTerm
    leftTerm rightTerm hroot hcode.
  apply (proj2 (raw_carrierRestrictedProofContextSat_iff
    M secondTail level childTerm)).
  eapply raw_carrierRestrictedProofAt_orI_left_child_between;
    [exact hPA | |exact hcode].
  apply (proj1 (raw_carrierRestrictedProofContextSat_iff
    M firstTail level rootTerm)).
  exact hroot.
Qed.

End PABoundedRawCodedCarrierRestrictedProofReroot.
