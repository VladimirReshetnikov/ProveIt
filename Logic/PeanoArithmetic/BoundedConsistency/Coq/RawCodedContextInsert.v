(**
  Insertion of one formula at a model-internal depth in a coded context.

  [RawContextShift] compares two context traversals of the *same* length row
  by row.  The transplant recursion needs a relation between contexts of
  lengths [n] and [n + 1]: the target is the source with one new formula
  placed at position [depth], everything strictly above [depth] left alone,
  and everything from [depth] on pushed up by one index.

  The depth is a carrier element, not a metatheoretic natural number, because
  a nonstandard proof code may have nonstandard nesting depth.  So the
  relation is stated pointwise against the two head tables, exactly as
  [RawContextShiftRows] is, and never decodes a carrier value or performs a
  Rocq recursion.

  Position zero is the ordinary cons already available from
  [RawCodedContextStructure], and the successor case pushes an insertion
  underneath one more assumption.  Those two constructions are what a descent
  through the proof tree consumes: the root inserts at depth zero, and each
  [RP_impI] or [RP_exE] node it enters increments the depth.
*)

From Stdlib Require Import List Arith Lia Classical_Prop.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedAdditionLaws
  PolynomialPairInjectivity
  RawCodedSyntaxConstructors RawCodedAssignment
  RawCodedContextLists RawCodedContextStructure
  RawCodedContextFunctionality.

Import ListNotations.

Module PABoundedRawCodedContextInsert.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedAdditionLaws.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedContextFunctionality.

(** ------------------------------------------------------------------
    Pointwise description of the inserted table. *)

(** Rows strictly below the insertion point are copied. *)
Definition RawContextInsertLowRows (M : RawPAModel)
    (depth sourceHeadCode sourceHeadStep targetHeadCode targetHeadStep : M)
    : Prop :=
  forall index,
    rawLt M index depth ->
    forall sourceFormula,
      RawCodedAssignmentLookup M
        sourceHeadCode sourceHeadStep index sourceFormula ->
      forall targetFormula,
        RawCodedAssignmentLookup M
          targetHeadCode targetHeadStep index targetFormula ->
        targetFormula = sourceFormula.

(** The insertion point itself carries the new formula. *)
Definition RawContextInsertHeadRow (M : RawPAModel)
    (depth head targetHeadCode targetHeadStep : M) : Prop :=
  forall targetFormula,
    RawCodedAssignmentLookup M
      targetHeadCode targetHeadStep depth targetFormula ->
    targetFormula = head.

(** Rows at or above the insertion point are copied one index up. *)
Definition RawContextInsertHighRows (M : RawPAModel)
    (depth bound
      sourceHeadCode sourceHeadStep targetHeadCode targetHeadStep : M)
    : Prop :=
  forall index,
    rawLt M index bound ->
    forall sourceFormula,
      RawCodedAssignmentLookup M
        sourceHeadCode sourceHeadStep index sourceFormula ->
      forall targetFormula,
        RawCodedAssignmentLookup M targetHeadCode targetHeadStep
          (raw_succ M index) targetFormula ->
        rawLt M index depth \/ targetFormula = sourceFormula.

Arguments RawContextInsertLowRows
  M depth sourceHeadCode sourceHeadStep targetHeadCode targetHeadStep
  : clear implicits.
Arguments RawContextInsertHeadRow
  M depth head targetHeadCode targetHeadStep : clear implicits.
Arguments RawContextInsertHighRows
  M depth bound
    sourceHeadCode sourceHeadStep targetHeadCode targetHeadStep
  : clear implicits.

Definition contextInsertLowRowsTermAt
    (depth sourceHeadCode sourceHeadStep targetHeadCode targetHeadStep : term)
    : formula :=
  pAll
    (pImp
      (Formula.ltTermAt (tVar 0) (liftTerm 1 depth))
      (pAll
        (pImp
          (codedAssignmentLookupTermAt
            (liftTerm 2 sourceHeadCode) (liftTerm 2 sourceHeadStep)
            (tVar 1) (tVar 0))
          (pAll
            (pImp
              (codedAssignmentLookupTermAt
                (liftTerm 3 targetHeadCode) (liftTerm 3 targetHeadStep)
                (tVar 2) (tVar 0))
              (pEq (tVar 0) (tVar 1))))))).

Definition contextInsertHeadRowTermAt
    (depth head targetHeadCode targetHeadStep : term) : formula :=
  pAll
    (pImp
      (codedAssignmentLookupTermAt
        (liftTerm 1 targetHeadCode) (liftTerm 1 targetHeadStep)
        (liftTerm 1 depth) (tVar 0))
      (pEq (tVar 0) (liftTerm 1 head))).

Definition contextInsertHighRowsTermAt
    (depth bound
      sourceHeadCode sourceHeadStep targetHeadCode targetHeadStep : term)
    : formula :=
  pAll
    (pImp
      (Formula.ltTermAt (tVar 0) (liftTerm 1 bound))
      (pAll
        (pImp
          (codedAssignmentLookupTermAt
            (liftTerm 2 sourceHeadCode) (liftTerm 2 sourceHeadStep)
            (tVar 1) (tVar 0))
          (pAll
            (pImp
              (codedAssignmentLookupTermAt
                (liftTerm 3 targetHeadCode) (liftTerm 3 targetHeadStep)
                (tSucc (tVar 2)) (tVar 0))
              (pOr
                (Formula.ltTermAt (tVar 2) (liftTerm 3 depth))
                (pEq (tVar 0) (tVar 1)))))))).

Lemma raw_contextInsert_eval_liftTerm_two : forall
    (M : RawPAModel) a b (e : nat -> M) t,
  raw_term_eval M (scons M a (scons M b e)) (liftTerm 2 t) =
  raw_term_eval M e t.
Proof.
  intros M a b e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro i.
  replace (i + 2) with (S (S i)) by lia. reflexivity.
Qed.

Lemma raw_sat_contextInsertLowRowsTermAt_iff : forall
    (M : RawPAModel) e
    depth sourceHeadCode sourceHeadStep targetHeadCode targetHeadStep,
  raw_formula_sat M e
    (contextInsertLowRowsTermAt
      depth sourceHeadCode sourceHeadStep
      targetHeadCode targetHeadStep) <->
  RawContextInsertLowRows M
    (raw_term_eval M e depth)
    (raw_term_eval M e sourceHeadCode)
    (raw_term_eval M e sourceHeadStep)
    (raw_term_eval M e targetHeadCode)
    (raw_term_eval M e targetHeadStep).
Proof.
  intros M e depth sourceHeadCode sourceHeadStep
    targetHeadCode targetHeadStep.
  unfold contextInsertLowRowsTermAt, RawContextInsertLowRows.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedAssignmentLookupTermAt_iff.
  repeat setoid_rewrite raw_contextList_eval_liftTerm_one.
  repeat setoid_rewrite raw_contextInsert_eval_liftTerm_two.
  repeat setoid_rewrite raw_contextList_eval_liftTerm_three.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_sat_contextInsertHeadRowTermAt_iff : forall
    (M : RawPAModel) e depth head targetHeadCode targetHeadStep,
  raw_formula_sat M e
    (contextInsertHeadRowTermAt
      depth head targetHeadCode targetHeadStep) <->
  RawContextInsertHeadRow M
    (raw_term_eval M e depth) (raw_term_eval M e head)
    (raw_term_eval M e targetHeadCode)
    (raw_term_eval M e targetHeadStep).
Proof.
  intros M e depth head targetHeadCode targetHeadStep.
  unfold contextInsertHeadRowTermAt, RawContextInsertHeadRow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedAssignmentLookupTermAt_iff.
  repeat setoid_rewrite raw_contextList_eval_liftTerm_one.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_sat_contextInsertHighRowsTermAt_iff : forall
    (M : RawPAModel) e
    depth bound sourceHeadCode sourceHeadStep
    targetHeadCode targetHeadStep,
  raw_formula_sat M e
    (contextInsertHighRowsTermAt
      depth bound sourceHeadCode sourceHeadStep
      targetHeadCode targetHeadStep) <->
  RawContextInsertHighRows M
    (raw_term_eval M e depth) (raw_term_eval M e bound)
    (raw_term_eval M e sourceHeadCode)
    (raw_term_eval M e sourceHeadStep)
    (raw_term_eval M e targetHeadCode)
    (raw_term_eval M e targetHeadStep).
Proof.
  intros M e depth bound sourceHeadCode sourceHeadStep
    targetHeadCode targetHeadStep.
  unfold contextInsertHighRowsTermAt, RawContextInsertHighRows.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedAssignmentLookupTermAt_iff.
  repeat setoid_rewrite raw_contextList_eval_liftTerm_one.
  repeat setoid_rewrite raw_contextInsert_eval_liftTerm_two.
  repeat setoid_rewrite raw_contextList_eval_liftTerm_three.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** The insertion position must lie inside the extended context. *)
Definition RawContextInsertDepthBound (M : RawPAModel)
    (depth bound : M) : Prop :=
  rawLt M depth (raw_succ M bound).

Arguments RawContextInsertDepthBound M depth bound : clear implicits.

Definition contextInsertDepthBoundTermAt (depth bound : term) : formula :=
  Formula.ltTermAt depth (tSucc bound).

Lemma raw_sat_contextInsertDepthBoundTermAt_iff : forall
    (M : RawPAModel) e depth bound,
  raw_formula_sat M e (contextInsertDepthBoundTermAt depth bound) <->
  RawContextInsertDepthBound M
    (raw_term_eval M e depth) (raw_term_eval M e bound).
Proof.
  intros M e depth bound.
  unfold contextInsertDepthBoundTermAt, RawContextInsertDepthBound.
  rewrite (raw_sat_ltTermAt_iff M depth (tSucc bound) e).
  cbn [raw_term_eval]. reflexivity.
Qed.

(** ------------------------------------------------------------------
    The public insertion relation. *)

Definition RawContextInsertWithTables (M : RawPAModel)
    (head depth sourceRoot targetRoot bound
      sourceTailCode sourceTailStep sourceHeadCode sourceHeadStep
      targetTailCode targetTailStep targetHeadCode targetHeadStep : M)
    : Prop :=
  RawContextListTraversal M sourceRoot bound
    sourceTailCode sourceTailStep sourceHeadCode sourceHeadStep /\
  RawContextListTraversal M targetRoot (raw_succ M bound)
    targetTailCode targetTailStep targetHeadCode targetHeadStep /\
  RawContextInsertDepthBound M depth bound /\
  RawContextInsertLowRows M depth
    sourceHeadCode sourceHeadStep targetHeadCode targetHeadStep /\
  RawContextInsertHeadRow M depth head
    targetHeadCode targetHeadStep /\
  RawContextInsertHighRows M depth bound
    sourceHeadCode sourceHeadStep targetHeadCode targetHeadStep.

Arguments RawContextInsertWithTables
  M head depth sourceRoot targetRoot bound
    sourceTailCode sourceTailStep sourceHeadCode sourceHeadStep
    targetTailCode targetTailStep targetHeadCode targetHeadStep
  : clear implicits.

Definition contextInsertWithTablesTermAt
    (head depth sourceRoot targetRoot bound
      sourceTailCode sourceTailStep sourceHeadCode sourceHeadStep
      targetTailCode targetTailStep targetHeadCode targetHeadStep : term)
    : formula :=
  pAnd
    (contextListTraversalTermAt
      sourceRoot bound sourceTailCode sourceTailStep
      sourceHeadCode sourceHeadStep)
    (pAnd
      (contextListTraversalTermAt
        targetRoot (tSucc bound) targetTailCode targetTailStep
        targetHeadCode targetHeadStep)
      (pAnd
        (contextInsertDepthBoundTermAt depth bound)
      (pAnd
        (contextInsertLowRowsTermAt depth
          sourceHeadCode sourceHeadStep targetHeadCode targetHeadStep)
        (pAnd
          (contextInsertHeadRowTermAt depth head
            targetHeadCode targetHeadStep)
          (contextInsertHighRowsTermAt depth bound
            sourceHeadCode sourceHeadStep
            targetHeadCode targetHeadStep))))).

Lemma raw_sat_contextInsertWithTablesTermAt_iff : forall
    (M : RawPAModel) e
    head depth sourceRoot targetRoot bound
    sourceTailCode sourceTailStep sourceHeadCode sourceHeadStep
    targetTailCode targetTailStep targetHeadCode targetHeadStep,
  raw_formula_sat M e
    (contextInsertWithTablesTermAt
      head depth sourceRoot targetRoot bound
      sourceTailCode sourceTailStep sourceHeadCode sourceHeadStep
      targetTailCode targetTailStep targetHeadCode targetHeadStep) <->
  RawContextInsertWithTables M
    (raw_term_eval M e head) (raw_term_eval M e depth)
    (raw_term_eval M e sourceRoot) (raw_term_eval M e targetRoot)
    (raw_term_eval M e bound)
    (raw_term_eval M e sourceTailCode)
    (raw_term_eval M e sourceTailStep)
    (raw_term_eval M e sourceHeadCode)
    (raw_term_eval M e sourceHeadStep)
    (raw_term_eval M e targetTailCode)
    (raw_term_eval M e targetTailStep)
    (raw_term_eval M e targetHeadCode)
    (raw_term_eval M e targetHeadStep).
Proof.
  intros. unfold contextInsertWithTablesTermAt,
    RawContextInsertWithTables.
  cbn [raw_formula_sat].
  rewrite !raw_sat_contextListTraversalTermAt_iff.
  rewrite raw_sat_contextInsertLowRowsTermAt_iff.
  rewrite raw_sat_contextInsertHeadRowTermAt_iff.
  rewrite raw_sat_contextInsertHighRowsTermAt_iff.
  rewrite raw_sat_contextInsertDepthBoundTermAt_iff.
  cbn [raw_term_eval]. reflexivity.
Qed.

Definition contextInsertEx9 (body : formula) : formula :=
  pEx (pEx (pEx (pEx (pEx (pEx (pEx (pEx (pEx body)))))))).

Definition contextInsertAtTermAt
    (head depth sourceRoot targetRoot : term) : formula :=
  contextInsertEx9
    (contextInsertWithTablesTermAt
      (liftTerm 9 head) (liftTerm 9 depth)
      (liftTerm 9 sourceRoot) (liftTerm 9 targetRoot)
      (tVar 8)
      (tVar 7) (tVar 6) (tVar 5) (tVar 4)
      (tVar 3) (tVar 2) (tVar 1) (tVar 0)).

Definition RawContextInsertAt (M : RawPAModel)
    (head depth sourceRoot targetRoot : M) : Prop :=
  exists bound
    sourceTailCode sourceTailStep sourceHeadCode sourceHeadStep
    targetTailCode targetTailStep targetHeadCode targetHeadStep : M,
  RawContextInsertWithTables M head depth sourceRoot targetRoot bound
    sourceTailCode sourceTailStep sourceHeadCode sourceHeadStep
    targetTailCode targetTailStep targetHeadCode targetHeadStep.

Arguments RawContextInsertAt M head depth sourceRoot targetRoot
  : clear implicits.

Lemma raw_contextInsert_eval_liftTerm_nine : forall
    (M : RawPAModel) a b c d f g h i j (e : nat -> M) t,
  raw_term_eval M
    (scons M a (scons M b (scons M c (scons M d
      (scons M f (scons M g (scons M h (scons M i (scons M j e)))))))))
    (liftTerm 9 t) = raw_term_eval M e t.
Proof.
  intros M a b c d f g h i j e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro k.
  replace (k + 9) with
    (S (S (S (S (S (S (S (S (S k))))))))) by lia.
  reflexivity.
Qed.

Lemma raw_sat_contextInsertAtTermAt_iff : forall
    (M : RawPAModel) e head depth sourceRoot targetRoot,
  raw_formula_sat M e
    (contextInsertAtTermAt head depth sourceRoot targetRoot) <->
  RawContextInsertAt M
    (raw_term_eval M e head) (raw_term_eval M e depth)
    (raw_term_eval M e sourceRoot) (raw_term_eval M e targetRoot).
Proof.
  intros M e head depth sourceRoot targetRoot.
  unfold contextInsertAtTermAt, contextInsertEx9, RawContextInsertAt.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_contextInsertWithTablesTermAt_iff.
  repeat setoid_rewrite raw_contextInsert_eval_liftTerm_nine.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** ------------------------------------------------------------------
    Realizability, in both directions.

    Both contexts of an insertion carry a complete model-internal traversal,
    so the side condition required by [raw_codedPALocalProofOf_assumption]
    and by [RawCodedPALocalProofConsTransplant] is available on either side
    without further hypotheses.  This is what lets the transplant obligation
    iterate without accumulating proof burden. *)
Lemma raw_contextInsertAt_source_realizable : forall
    (M : RawPAModel) head depth sourceRoot targetRoot,
  RawContextInsertAt M head depth sourceRoot targetRoot ->
  RawContextListRealizable M sourceRoot.
Proof.
  intros M head depth sourceRoot targetRoot
    (bound & sourceTailCode & sourceTailStep & sourceHeadCode &
      sourceHeadStep & targetTailCode & targetTailStep &
      targetHeadCode & targetHeadStep & [hsource _]).
  exists bound, sourceTailCode, sourceTailStep,
    sourceHeadCode, sourceHeadStep. exact hsource.
Qed.

Lemma raw_contextInsertAt_target_realizable : forall
    (M : RawPAModel) head depth sourceRoot targetRoot,
  RawContextInsertAt M head depth sourceRoot targetRoot ->
  RawContextListRealizable M targetRoot.
Proof.
  intros M head depth sourceRoot targetRoot
    (bound & sourceTailCode & sourceTailStep & sourceHeadCode &
      sourceHeadStep & targetTailCode & targetTailStep &
      targetHeadCode & targetHeadStep & [_ [htarget _]]).
  exists (raw_succ M bound), targetTailCode, targetTailStep,
    targetHeadCode, targetHeadStep. exact htarget.
Qed.

(** Realizability at a named length. *)
Definition RawContextListTraversalBoundedBy (M : RawPAModel)
    (root bound : M) : Prop :=
  exists tailCode tailStep headCode headStep : M,
    RawContextListTraversal M root bound
      tailCode tailStep headCode headStep.

Arguments RawContextListTraversalBoundedBy M root bound : clear implicits.

(** The target is exactly one longer than the source.  Recorded separately
    because it is the fact a length-indexed descent consumes, and because it
    is what distinguishes insertion from [RawContextShift], whose two
    traversals share a single bound. *)
Lemma raw_contextInsertAt_target_bound : forall
    (M : RawPAModel) head depth sourceRoot targetRoot,
  RawContextInsertAt M head depth sourceRoot targetRoot ->
  exists bound : M,
    RawContextListTraversalBoundedBy M sourceRoot bound /\
    RawContextListTraversalBoundedBy M targetRoot (raw_succ M bound).
Proof.
  intros M head depth sourceRoot targetRoot
    (bound & sourceTailCode & sourceTailStep & sourceHeadCode &
      sourceHeadStep & targetTailCode & targetTailStep &
      targetHeadCode & targetHeadStep & [hsource [htarget _]]).
  exists bound. split.
  - exists sourceTailCode, sourceTailStep,
      sourceHeadCode, sourceHeadStep. exact hsource.
  - exists targetTailCode, targetTailStep,
      targetHeadCode, targetHeadStep. exact htarget.
Qed.

(** ------------------------------------------------------------------
    Position zero is the ordinary cons. *)

Theorem raw_contextInsertAt_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall source head,
  RawContextListRealizable M source ->
  RawContextInsertAt M head (raw_zero M) source
    (rawListNode M head source).
Proof.
  intros M hPA source head
    (bound & tailCode & tailStep & headCode & headStep & htraversal).
  destruct (raw_contextListConsExtension_exists M hPA
    source head bound tailCode tailStep headCode headStep htraversal)
    as (newTailCode & newTailStep & newHeadCode & newHeadStep &
      _ & hheadPrepend & hnewTraversal).
  exists bound, tailCode, tailStep, headCode, headStep,
    newTailCode, newTailStep, newHeadCode, newHeadStep.
  split; [exact htraversal |].
  split; [exact hnewTraversal |].
  split; [exact (raw_lt_zero_succ M hPA bound) |].
  split.
  - intros index hindex.
    exfalso. exact (raw_not_lt_zero M hPA index hindex).
  - split.
    + intros targetFormula hlookup.
      exact (proj1 (raw_codedAssignmentPrepend_lookup_zero_iff M hPA
        headCode headStep head bound newHeadCode newHeadStep
        targetFormula hheadPrepend) hlookup).
    + intros index hindex sourceFormula hsource targetFormula htarget.
      right.
      assert (holdTarget : RawCodedAssignmentLookup M
          headCode headStep index targetFormula).
      {
        exact (proj1 (raw_codedAssignmentPrepend_lookup_succ_iff M hPA
          headCode headStep head bound newHeadCode newHeadStep
          (proj1 (proj2 (proj2 htraversal))) hheadPrepend
          index hindex targetFormula) htarget).
      }
      exact (raw_codedAssignmentLookup_functional M hPA
        headCode headStep index targetFormula sourceFormula
        holdTarget hsource).
Qed.

(** ------------------------------------------------------------------
    Descending under one more assumption increments the depth.

    This is the clause a proof-tree descent uses when it enters an [RP_impI]
    or [RP_exE] node: the node's child context is the parent's with one local
    assumption consed on, and the insertion point moves down by one. *)

Theorem raw_contextInsertAt_cons : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall head depth source target extra,
  RawContextInsertAt M head depth source target ->
  RawContextInsertAt M head (raw_succ M depth)
    (rawListNode M extra source) (rawListNode M extra target).
Proof.
  intros M hPA head depth source target extra
    (bound & sourceTailCode & sourceTailStep & sourceHeadCode &
      sourceHeadStep & targetTailCode & targetTailStep &
      targetHeadCode & targetHeadStep &
      [hsource [htarget [hdepth [hlow [hheadRow hhigh]]]]]).
  destruct (raw_contextListConsExtension_exists M hPA
    source extra bound sourceTailCode sourceTailStep
    sourceHeadCode sourceHeadStep hsource)
    as (newSourceTailCode & newSourceTailStep & newSourceHeadCode &
      newSourceHeadStep & _ & hsourcePrepend & hnewSource).
  destruct (raw_contextListConsExtension_exists M hPA
    target extra (raw_succ M bound) targetTailCode targetTailStep
    targetHeadCode targetHeadStep htarget)
    as (newTargetTailCode & newTargetTailStep & newTargetHeadCode &
      newTargetHeadStep & _ & htargetPrepend & hnewTarget).
  assert (hsourceDefined : RawCodedAssignmentDefinedThrough M
      sourceHeadCode sourceHeadStep bound).
  { exact (proj1 (proj2 (proj2 hsource))). }
  assert (htargetDefined : RawCodedAssignmentDefinedThrough M
      targetHeadCode targetHeadStep (raw_succ M bound)).
  { exact (proj1 (proj2 (proj2 htarget))). }
  exists (raw_succ M bound),
    newSourceTailCode, newSourceTailStep,
    newSourceHeadCode, newSourceHeadStep,
    newTargetTailCode, newTargetTailStep,
    newTargetHeadCode, newTargetHeadStep.
  split; [exact hnewSource |].
  split; [exact hnewTarget |].
  split.
  - apply raw_lt_succ_of_le; [exact hPA |].
    exact (raw_succ_le_of_lt_pair M hPA depth (raw_succ M bound) hdepth).
  - split.
    + intros index hindex sourceFormula hsrc targetFormula htgt.
      destruct (raw_assignment_zero_or_successor M hPA index)
        as [-> | [predecessor ->]].
      * rewrite (proj1 (raw_codedAssignmentPrepend_lookup_zero_iff M hPA
          sourceHeadCode sourceHeadStep extra bound
          newSourceHeadCode newSourceHeadStep sourceFormula
          hsourcePrepend) hsrc).
        exact (proj1 (raw_codedAssignmentPrepend_lookup_zero_iff M hPA
          targetHeadCode targetHeadStep extra (raw_succ M bound)
          newTargetHeadCode newTargetHeadStep targetFormula
          htargetPrepend) htgt).
      * assert (hpredDepth : rawLt M predecessor depth).
        { exact (raw_lt_succ_succ_inv M hPA predecessor depth hindex). }
        assert (hpredBound : rawLt M predecessor bound).
        {
          exact (raw_lt_of_lt_of_lt_succ M hPA predecessor depth bound
            hpredDepth hdepth).
        }
        assert (hpredTargetBound :
            rawLt M predecessor (raw_succ M bound)).
        {
          exact (raw_assignment_lt_trans M hPA predecessor bound
            (raw_succ M bound) hpredBound
            (raw_assignment_lt_self_succ M hPA bound)).
        }
        assert (holdSource : RawCodedAssignmentLookup M
            sourceHeadCode sourceHeadStep predecessor sourceFormula).
        {
          exact (proj1 (raw_codedAssignmentPrepend_lookup_succ_iff M hPA
            sourceHeadCode sourceHeadStep extra bound
            newSourceHeadCode newSourceHeadStep hsourceDefined
            hsourcePrepend predecessor hpredBound sourceFormula) hsrc).
        }
        assert (holdTarget : RawCodedAssignmentLookup M
            targetHeadCode targetHeadStep predecessor targetFormula).
        {
          exact (proj1 (raw_codedAssignmentPrepend_lookup_succ_iff M hPA
            targetHeadCode targetHeadStep extra (raw_succ M bound)
            newTargetHeadCode newTargetHeadStep htargetDefined
            htargetPrepend predecessor hpredTargetBound targetFormula)
            htgt).
        }
        exact (hlow predecessor hpredDepth sourceFormula holdSource
          targetFormula holdTarget).
    + split.
      * intros targetFormula htgt.
        assert (holdTarget : RawCodedAssignmentLookup M
            targetHeadCode targetHeadStep depth targetFormula).
        {
          exact (proj1 (raw_codedAssignmentPrepend_lookup_succ_iff M hPA
            targetHeadCode targetHeadStep extra (raw_succ M bound)
            newTargetHeadCode newTargetHeadStep htargetDefined
            htargetPrepend depth hdepth targetFormula) htgt).
        }
        exact (hheadRow targetFormula holdTarget).
      * intros index hindex sourceFormula hsrc targetFormula htgt.
        destruct (raw_assignment_zero_or_successor M hPA index)
          as [-> | [predecessor ->]].
        -- left. exact (raw_lt_zero_succ M hPA depth).
        -- destruct (classic (rawLt M predecessor depth))
             as [hlt | hnlt].
           ++ left.
              apply raw_lt_succ_of_le; [exact hPA |].
              exact (raw_succ_le_of_lt_pair M hPA predecessor depth hlt).
           ++ right.
              assert (hpredBound : rawLt M predecessor bound).
              {
                exact (raw_lt_succ_succ_inv M hPA predecessor bound
                  hindex).
              }
              assert (holdSource : RawCodedAssignmentLookup M
                  sourceHeadCode sourceHeadStep predecessor sourceFormula).
              {
                exact (proj1
                  (raw_codedAssignmentPrepend_lookup_succ_iff M hPA
                    sourceHeadCode sourceHeadStep extra bound
                    newSourceHeadCode newSourceHeadStep hsourceDefined
                    hsourcePrepend predecessor hpredBound sourceFormula)
                  hsrc).
              }
              assert (holdTarget : RawCodedAssignmentLookup M
                  targetHeadCode targetHeadStep (raw_succ M predecessor)
                  targetFormula).
              {
                exact (proj1
                  (raw_codedAssignmentPrepend_lookup_succ_iff M hPA
                    targetHeadCode targetHeadStep extra (raw_succ M bound)
                    newTargetHeadCode newTargetHeadStep htargetDefined
                    htargetPrepend (raw_succ M predecessor) hindex
                    targetFormula) htgt).
              }
              destruct (hhigh predecessor hpredBound sourceFormula
                holdSource targetFormula holdTarget)
                as [hcontradiction | heq].
              ** exfalso. exact (hnlt hcontradiction).
              ** exact heq.
Qed.

(** ------------------------------------------------------------------
    Membership transport.

    These are the facts the assumption-leaf constructor row consumes once the
    transplant obligation is restated at a depth. *)

Theorem raw_contextInsertAt_head_member : forall
    (M : RawPAModel), RawPASatisfies M -> forall head depth source target,
  RawContextInsertAt M head depth source target ->
  RawContextListMember M target head.
Proof.
  intros M hPA head depth source target
    (bound & sourceTailCode & sourceTailStep & sourceHeadCode &
      sourceHeadStep & targetTailCode & targetTailStep &
      targetHeadCode & targetHeadStep &
      [hsource [htarget [hdepth [_ [hheadRow _]]]]]).
  pose proof htarget as htargetFacts.
  destruct htargetFacts as [_ [_ [htargetDefined _]]].
  destruct (htargetDefined depth hdepth) as [value hlookup].
  apply (proj2 (raw_contextListMember_iff_with_traversal M hPA
    target head (raw_succ M bound) targetTailCode targetTailStep
    targetHeadCode targetHeadStep htarget)).
  exists depth. split; [exact hdepth |].
  rewrite <- (hheadRow value hlookup). exact hlookup.
Qed.

Theorem raw_contextInsertAt_source_member : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall head depth source target member,
  RawContextInsertAt M head depth source target ->
  RawContextListMember M source member ->
  RawContextListMember M target member.
Proof.
  intros M hPA head depth source target member
    (bound & sourceTailCode & sourceTailStep & sourceHeadCode &
      sourceHeadStep & targetTailCode & targetTailStep &
      targetHeadCode & targetHeadStep &
      [hsource [htarget [_ [hlow [_ hhigh]]]]]) hmember.
  pose proof (proj1 (raw_contextListMember_iff_with_traversal M hPA
    source member bound sourceTailCode sourceTailStep
    sourceHeadCode sourceHeadStep hsource) hmember)
    as [index [hindex hsourceLookup]].
  pose proof htarget as htargetFacts.
  destruct htargetFacts as [_ [_ [htargetDefined _]]].
  apply (proj2 (raw_contextListMember_iff_with_traversal M hPA
    target member (raw_succ M bound) targetTailCode targetTailStep
    targetHeadCode targetHeadStep htarget)).
  destruct (classic (rawLt M index depth)) as [hlt | hnlt].
  - assert (hindexSucc : rawLt M index (raw_succ M bound)).
    {
      exact (raw_assignment_lt_trans M hPA index bound (raw_succ M bound)
        hindex (raw_assignment_lt_self_succ M hPA bound)).
    }
    destruct (htargetDefined index hindexSucc) as [value hlookup].
    exists index. split; [exact hindexSucc |].
    rewrite <- (hlow index hlt member hsourceLookup value hlookup).
    exact hlookup.
  - assert (hindexSucc : rawLt M (raw_succ M index) (raw_succ M bound)).
    {
      apply raw_lt_succ_of_le; [exact hPA |].
      exact (raw_succ_le_of_lt_pair M hPA index bound hindex).
    }
    destruct (htargetDefined (raw_succ M index) hindexSucc)
      as [value hlookup].
    exists (raw_succ M index). split; [exact hindexSucc |].
    destruct (hhigh index hindex member hsourceLookup value hlookup)
      as [hcontradiction | heq].
    + exfalso. exact (hnlt hcontradiction).
    + rewrite <- heq. exact hlookup.
Qed.

End PABoundedRawCodedContextInsert.
