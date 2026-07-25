(**
  Coverage-certified disjunction elimination for model-coded PA proofs.

  The tag-10 constructor has three recursive premises.  The first proves
  the displayed disjunction in the parent context.  The other two prove the
  common conclusion after, respectively, the left and right disjunct has
  been pushed onto that context.

  The children may carry unrelated nonstandard support tables.  To avoid a
  new arithmetized ternary-table construction, the coverage proof performs
  two exact binary unions.  The first table joins the first two trees and
  marks the final parent; the second joins that entire table with the third
  tree and marks the same parent.  Using the final parent as the intermediate
  bound is important: no child root needs to be largest, and hence no part
  of either earlier tree is accidentally truncated.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedAssignment RawCodedSyntaxConstructors
  RawCodedProofConstructors RawCodedProofDescent RawCodedProofTraversal
  RawCodedProofEndpoints RawCodedProofRules RawCodedProofRuleCoverage
  RawCodedListInjectivity RawCodedProofSupportExtension
  RawCodedProofBinarySupportUnion.

Import ListNotations.

Module PABoundedRawCodedProofOrEConstructor.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofTraversal.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedListInjectivity.
Import PABoundedRawCodedProofSupportExtension.
Import PABoundedRawCodedProofBinarySupportUnion.

Definition rawProofOrERoot (M : RawPAModel)
    (context left right conclusion
      disjunctionChild leftChild rightChild : M) : M :=
  rawListCode M
    [rawNumeralValue M 10; context; left; right; conclusion;
      disjunctionChild; leftChild; rightChild].

Arguments rawProofOrERoot
  M context left right conclusion disjunctionChild leftChild rightChild
  : clear implicits.

Lemma raw_proofOrERoot_disjunction_child_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context left right conclusion disjunctionChild leftChild rightChild,
  rawLt M disjunctionChild
    (rawProofOrERoot M context left right conclusion
      disjunctionChild leftChild rightChild).
Proof.
  intros M hPA context left right conclusion
    disjunctionChild leftChild rightChild.
  unfold rawProofOrERoot.
  apply rawProofListCode_member_lt; [exact hPA |].
  cbn. tauto.
Qed.

Lemma raw_proofOrERoot_left_child_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context left right conclusion disjunctionChild leftChild rightChild,
  rawLt M leftChild
    (rawProofOrERoot M context left right conclusion
      disjunctionChild leftChild rightChild).
Proof.
  intros M hPA context left right conclusion
    disjunctionChild leftChild rightChild.
  unfold rawProofOrERoot.
  apply rawProofListCode_member_lt; [exact hPA |].
  cbn. tauto.
Qed.

Lemma raw_proofOrERoot_right_child_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context left right conclusion disjunctionChild leftChild rightChild,
  rawLt M rightChild
    (rawProofOrERoot M context left right conclusion
      disjunctionChild leftChild rightChild).
Proof.
  intros M hPA context left right conclusion
    disjunctionChild leftChild rightChild.
  unfold rawProofOrERoot.
  apply rawProofListCode_member_lt; [exact hPA |].
  cbn. tauto.
Qed.

(** Constructor-tag injectivity is needed even though this parent was built
    externally: an arbitrary model may allow many existential constructor
    views, and the traversal closes all of them. *)
Lemma raw_proofOrERoot_list_view : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context left right conclusion disjunctionChild leftChild rightChild
      tag payload,
  rawProofOrERoot M context left right conclusion
      disjunctionChild leftChild rightChild =
    rawListCode M (rawNumeralValue M tag :: payload) ->
  tag = 10 /\
  payload =
    [context; left; right; conclusion;
      disjunctionChild; leftChild; rightChild].
Proof.
  intros M hPA context left right conclusion
    disjunctionChild leftChild rightChild tag payload hcode.
  unfold rawProofOrERoot in hcode.
  pose proof (rawListCode_injective M hPA
    [rawNumeralValue M 10; context; left; right; conclusion;
      disjunctionChild; leftChild; rightChild]
    (rawNumeralValue M tag :: payload) hcode) as hfields.
  assert (hhead : rawNumeralValue M 10 = rawNumeralValue M tag).
  { now inversion hfields. }
  assert (htail :
      [context; left; right; conclusion;
        disjunctionChild; leftChild; rightChild] = payload).
  { now inversion hfields. }
  split.
  - symmetry. exact (rawNumeralValue_injective M hPA _ _ hhead).
  - symmetry. exact htail.
Qed.

Lemma raw_proofOrERoot_recursive_children : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context left right conclusion disjunctionChild leftChild rightChild
      rowContext a b c t child1 child2 child3 fields children,
  In (fields, children)
    (rawProofRecursiveCases M
      rowContext a b c t child1 child2 child3) ->
  rawProofOrERoot M context left right conclusion
      disjunctionChild leftChild rightChild =
    rawListCode M fields ->
  children = [disjunctionChild; leftChild; rightChild].
Proof.
  intros M hPA context left right conclusion
    disjunctionChild leftChild rightChild
    rowContext a b c t child1 child2 child3 fields children
    hentry hcode.
  unfold rawProofRecursiveCases in hentry. cbn in hentry.
  repeat match type of hentry with
  | _ \/ _ => destruct hentry as [hentry | hentry]
  end; try contradiction.
  all: inversion hentry; subst fields children; clear hentry.
  all: unfold rawProofOrERoot in hcode.
  all: pose proof (rawListCode_injective M hPA _ _ hcode) as hfields.
  all: try discriminate hfields.
  all: inversion hfields; reflexivity.
Qed.

Lemma raw_proofOrERoot_constructor : forall
    (M : RawPAModel)
      context left right conclusion disjunctionChild leftChild rightChild,
  RawProofConstructorCode M
    (rawProofOrERoot M context left right conclusion
      disjunctionChild leftChild rightChild)
    context left right conclusion (raw_zero M)
    disjunctionChild leftChild rightChild.
Proof.
  intros M context left right conclusion
    disjunctionChild leftChild rightChild.
  unfold RawProofConstructorCode, rawProofOrERoot.
  do 10 right. left. reflexivity.
Qed.

Lemma raw_proofOrE_syntax_step : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context left right conclusion disjunctionChild leftChild rightChild
      supportCode supportStep,
  rawProofCodeSupported M supportCode supportStep disjunctionChild ->
  rawProofCodeSupported M supportCode supportStep leftChild ->
  rawProofCodeSupported M supportCode supportStep rightChild ->
  RawProofSyntaxStep M
    (rawProofOrERoot M context left right conclusion
      disjunctionChild leftChild rightChild)
    supportCode supportStep.
Proof.
  intros M hPA context left right conclusion
    disjunctionChild leftChild rightChild supportCode supportStep
    hdisjunctionSupported hleftSupported hrightSupported.
  split.
  - exists context, left, right, conclusion, (raw_zero M),
      disjunctionChild, leftChild, rightChild.
    apply raw_proofOrERoot_constructor.
  - intros rowContext a b c t child1 child2 child3 hconstructor.
    split.
    + exact (raw_proofConstructorCode_descent M hPA
        (rawProofOrERoot M context left right conclusion
          disjunctionChild leftChild rightChild)
        rowContext a b c t child1 child2 child3 hconstructor).
    + apply Forall_forall. intros [fields children] hentry.
      unfold RawProofChildrenClosedCase.
      intro hcode.
      pose proof (raw_proofOrERoot_recursive_children M hPA
        context left right conclusion disjunctionChild leftChild rightChild
        rowContext a b c t child1 child2 child3 fields children
        hentry hcode) as ->.
      constructor.
      * split; [exact hdisjunctionSupported |].
        exact (raw_proofOrERoot_disjunction_child_lt M hPA
          context left right conclusion
          disjunctionChild leftChild rightChild).
      * constructor.
        -- split; [exact hleftSupported |].
           exact (raw_proofOrERoot_left_child_lt M hPA
             context left right conclusion
             disjunctionChild leftChild rightChild).
        -- constructor.
           ++ split; [exact hrightSupported |].
              exact (raw_proofOrERoot_right_child_lt M hPA
                context left right conclusion
                disjunctionChild leftChild rightChild).
           ++ constructor.
Qed.

Lemma raw_proofOrE_endpoint_rule_complete : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context left right conclusion disjunctionChild leftChild rightChild,
  RawProofEndpoint M disjunctionChild context
    (rawFormulaOrCode M left right) ->
  RawProofEndpoint M leftChild
    (rawListNode M left context) conclusion ->
  RawProofEndpoint M rightChild
    (rawListNode M right context) conclusion ->
  RawProofEndpointRuleComplete M
    (rawProofOrERoot M context left right conclusion
      disjunctionChild leftChild rightChild).
Proof.
  intros M hPA context left right conclusion
    disjunctionChild leftChild rightChild
    hdisjunctionEndpoint hleftEndpoint hrightEndpoint
    endpointContext endpointConclusion hendpoint.
  destruct hendpoint as
    (rowContext & a & b & c & t & child1 & child2 & child3 &
      hcontext & hcases).
  subst rowContext.
  unfold RawProofEndpointCases in hcases.
  repeat match type of hcases with
  | _ \/ _ => destruct hcases as [hcases | hcases]
  end; try contradiction.
  all: destruct hcases as [hhead hrest].
  all: pose proof (raw_proofOrERoot_list_view M hPA
    context left right conclusion disjunctionChild leftChild rightChild
    _ _ hhead) as hview.
  all: destruct hview as [htag hpayload].
  all: try discriminate htag.
  inversion hpayload;
    subst endpointContext a b c child1 child2 child3.
  subst endpointConclusion.
  exists context, left, right, conclusion,
    (rawFormulaOrCode M left right),
    disjunctionChild, leftChild, rightChild.
  split; [reflexivity |].
  unfold RawProofRuleValidCases, rawProofOrERoot.
  do 10 right. left.
  repeat split; assumption || reflexivity.
Qed.

Corollary raw_proofOrE_endpoint : forall
    (M : RawPAModel)
      context left right conclusion disjunctionChild leftChild rightChild,
  RawProofEndpoint M
    (rawProofOrERoot M context left right conclusion
      disjunctionChild leftChild rightChild)
    context conclusion.
Proof.
  intros M context left right conclusion
    disjunctionChild leftChild rightChild.
  exists context, left, right, conclusion, (raw_zero M),
    disjunctionChild, leftChild, rightChild.
  split; [reflexivity |].
  unfold RawProofEndpointCases, rawProofOrERoot.
  do 10 right. left. split; reflexivity.
Qed.

(** Exact coverage union for three children and one fresh parent.

    The intermediate union is deliberately bounded by [parent], not by one
    of the child roots.  Although every descendant is below its own root,
    the three roots need not be ordered relative to one another. *)
Lemma raw_proofTernary_ruleCoverage : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      firstRoot secondRoot thirdRoot parent,
  RawProofRuleCoverage M firstRoot ->
  RawProofRuleCoverage M secondRoot ->
  RawProofRuleCoverage M thirdRoot ->
  rawLt M firstRoot parent ->
  rawLt M secondRoot parent ->
  rawLt M thirdRoot parent ->
  (forall supportCode supportStep,
    rawProofCodeSupported M supportCode supportStep firstRoot ->
    rawProofCodeSupported M supportCode supportStep secondRoot ->
    rawProofCodeSupported M supportCode supportStep thirdRoot ->
    RawProofSyntaxStep M parent supportCode supportStep) ->
  RawProofEndpointRuleComplete M parent ->
  RawProofRuleCoverage M parent.
Proof.
  intros M hPA firstRoot secondRoot thirdRoot parent
    (firstCode & firstStep & [[[hfirstDefined hfirstRows]
      hfirstOldSupported] hfirstEndpointRows])
    (secondCode & secondStep & [[[hsecondDefined hsecondRows]
      hsecondOldSupported] hsecondEndpointRows])
    (thirdCode & thirdStep & [[[hthirdDefined hthirdRows]
      hthirdOldSupported] hthirdEndpointRows])
    hfirstBelow hsecondBelow hthirdBelow hparentSyntax hparentEndpoints.

  (** First join the first two complete trees through the final parent.
      This table already has the full final bound and marks [parent]. *)
  destruct (raw_proofBinarySupport_to_parent M hPA
    firstRoot firstCode firstStep
    secondRoot secondCode secondStep parent)
    as (pairCode & pairStep & [hpairDefined hpairExact]).

  (** Treat that full table as the left input rooted at [parent], then add
      the third complete tree.  The repeated parent marker is harmless and
      makes both exact-union characterizations convenient to invert. *)
  destruct (raw_proofBinarySupport_to_parent M hPA
    parent pairCode pairStep
    thirdRoot thirdCode thirdStep parent)
    as (newCode & newStep & [hnewDefined hnewExact]).

  assert (hfirstPairSupported :
      rawProofCodeSupported M pairCode pairStep firstRoot).
  {
    apply (proj2 (hpairExact firstRoot
      (raw_assignment_lt_trans M hPA
        firstRoot parent (raw_succ M parent) hfirstBelow
        (raw_assignment_lt_self_succ M hPA parent)))).
    left. split.
    - exact (raw_assignment_lt_self_succ M hPA firstRoot).
    - exact hfirstOldSupported.
  }
  assert (hsecondPairSupported :
      rawProofCodeSupported M pairCode pairStep secondRoot).
  {
    apply (proj2 (hpairExact secondRoot
      (raw_assignment_lt_trans M hPA
        secondRoot parent (raw_succ M parent) hsecondBelow
        (raw_assignment_lt_self_succ M hPA parent)))).
    right. left. split.
    - exact (raw_assignment_lt_self_succ M hPA secondRoot).
    - exact hsecondOldSupported.
  }
  assert (hfirstNewSupported :
      rawProofCodeSupported M newCode newStep firstRoot).
  {
    apply (proj2 (hnewExact firstRoot
      (raw_assignment_lt_trans M hPA
        firstRoot parent (raw_succ M parent) hfirstBelow
        (raw_assignment_lt_self_succ M hPA parent)))).
    left. split.
    - exact (raw_assignment_lt_trans M hPA
        firstRoot parent (raw_succ M parent) hfirstBelow
        (raw_assignment_lt_self_succ M hPA parent)).
    - exact hfirstPairSupported.
  }
  assert (hsecondNewSupported :
      rawProofCodeSupported M newCode newStep secondRoot).
  {
    apply (proj2 (hnewExact secondRoot
      (raw_assignment_lt_trans M hPA
        secondRoot parent (raw_succ M parent) hsecondBelow
        (raw_assignment_lt_self_succ M hPA parent)))).
    left. split.
    - exact (raw_assignment_lt_trans M hPA
        secondRoot parent (raw_succ M parent) hsecondBelow
        (raw_assignment_lt_self_succ M hPA parent)).
    - exact hsecondPairSupported.
  }
  assert (hthirdNewSupported :
      rawProofCodeSupported M newCode newStep thirdRoot).
  {
    apply (proj2 (hnewExact thirdRoot
      (raw_assignment_lt_trans M hPA
        thirdRoot parent (raw_succ M parent) hthirdBelow
        (raw_assignment_lt_self_succ M hPA parent)))).
    right. left. split.
    - exact (raw_assignment_lt_self_succ M hPA thirdRoot).
    - exact hthirdOldSupported.
  }

  exists newCode, newStep. split.
  - split.
    + split; [exact hnewDefined |].
      intros code hbelow hsupported.
      pose proof (proj1 (hnewExact code hbelow) hsupported) as houter.
      destruct houter as
        [[hbelowPair hpairSupported] |
          [[hbelowThird hthirdSupported] | heqParent]].
      * pose proof (proj1 (hpairExact code hbelowPair)
          hpairSupported) as hinner.
        destruct hinner as
          [[hbelowFirst hfirstSupported] |
            [[hbelowSecond hsecondSupported] | ->]].
        -- apply (raw_proofSyntaxStep_change_support M
             code firstCode firstStep newCode newStep
             (hfirstRows code hbelowFirst hfirstSupported)).
           intros nested hnestedBelow hnestedSupported.
           apply (proj2 (hnewExact nested
             (raw_assignment_lt_trans M hPA
               nested code (raw_succ M parent)
               hnestedBelow hbelowPair))).
           left. split.
           ++ exact (raw_assignment_lt_trans M hPA
                nested code (raw_succ M parent)
                hnestedBelow hbelowPair).
           ++ apply (proj2 (hpairExact nested
                (raw_assignment_lt_trans M hPA
                  nested code (raw_succ M parent)
                  hnestedBelow hbelowPair))).
              left. split.
              (* [hbelowFirst] is [code < S firstRoot]; descendants of
                 [code] therefore remain inside the first old table. *)
              --- exact (raw_assignment_lt_trans M hPA
                    nested code (raw_succ M firstRoot)
                    hnestedBelow hbelowFirst).
              --- exact hnestedSupported.
        -- apply (raw_proofSyntaxStep_change_support M
             code secondCode secondStep newCode newStep
             (hsecondRows code hbelowSecond hsecondSupported)).
           intros nested hnestedBelow hnestedSupported.
           apply (proj2 (hnewExact nested
             (raw_assignment_lt_trans M hPA
               nested code (raw_succ M parent)
               hnestedBelow hbelowPair))).
           left. split.
           ++ exact (raw_assignment_lt_trans M hPA
                nested code (raw_succ M parent)
                hnestedBelow hbelowPair).
           ++ apply (proj2 (hpairExact nested
                (raw_assignment_lt_trans M hPA
                  nested code (raw_succ M parent)
                  hnestedBelow hbelowPair))).
              right. left. split.
              --- exact (raw_assignment_lt_trans M hPA
                    nested code (raw_succ M secondRoot)
                    hnestedBelow hbelowSecond).
              --- exact hnestedSupported.
        -- exact (hparentSyntax newCode newStep
             hfirstNewSupported hsecondNewSupported hthirdNewSupported).
      * apply (raw_proofSyntaxStep_change_support M
          code thirdCode thirdStep newCode newStep
          (hthirdRows code hbelowThird hthirdSupported)).
        intros nested hnestedBelow hnestedSupported.
        apply (proj2 (hnewExact nested
          (raw_assignment_lt_trans M hPA
            nested code (raw_succ M parent) hnestedBelow hbelow))).
        right. left. split.
        -- exact (raw_assignment_lt_trans M hPA
             nested code (raw_succ M thirdRoot)
             hnestedBelow hbelowThird).
        -- exact hnestedSupported.
      * subst code.
        exact (hparentSyntax newCode newStep
          hfirstNewSupported hsecondNewSupported hthirdNewSupported).
    + apply (proj2 (hnewExact parent
        (raw_assignment_lt_self_succ M hPA parent))).
      right. right. reflexivity.
  - intros code hbelow hsupported.
    pose proof (proj1 (hnewExact code hbelow) hsupported) as houter.
    destruct houter as
      [[hbelowPair hpairSupported] |
        [[hbelowThird hthirdSupported] | heqParent]].
    + pose proof (proj1 (hpairExact code hbelowPair)
        hpairSupported) as hinner.
      destruct hinner as
        [[hbelowFirst hfirstSupported] |
          [[hbelowSecond hsecondSupported] | ->]].
      * exact (hfirstEndpointRows code hbelowFirst hfirstSupported).
      * exact (hsecondEndpointRows code hbelowSecond hsecondSupported).
      * exact hparentEndpoints.
    + exact (hthirdEndpointRows code hbelowThird hthirdSupported).
    + subst code. exact hparentEndpoints.
Qed.

Theorem raw_proofOrE_ruleCoverage : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context left right conclusion disjunctionChild leftChild rightChild,
  RawProofRuleCoverage M disjunctionChild ->
  RawProofEndpoint M disjunctionChild context
    (rawFormulaOrCode M left right) ->
  RawProofRuleCoverage M leftChild ->
  RawProofEndpoint M leftChild
    (rawListNode M left context) conclusion ->
  RawProofRuleCoverage M rightChild ->
  RawProofEndpoint M rightChild
    (rawListNode M right context) conclusion ->
  RawProofRuleCoverage M
    (rawProofOrERoot M context left right conclusion
      disjunctionChild leftChild rightChild).
Proof.
  intros M hPA context left right conclusion
    disjunctionChild leftChild rightChild
    hdisjunctionCoverage hdisjunctionEndpoint
    hleftCoverage hleftEndpoint hrightCoverage hrightEndpoint.
  exact (raw_proofTernary_ruleCoverage M hPA
    disjunctionChild leftChild rightChild
    (rawProofOrERoot M context left right conclusion
      disjunctionChild leftChild rightChild)
    hdisjunctionCoverage hleftCoverage hrightCoverage
    (raw_proofOrERoot_disjunction_child_lt M hPA
      context left right conclusion disjunctionChild leftChild rightChild)
    (raw_proofOrERoot_left_child_lt M hPA
      context left right conclusion disjunctionChild leftChild rightChild)
    (raw_proofOrERoot_right_child_lt M hPA
      context left right conclusion disjunctionChild leftChild rightChild)
    (raw_proofOrE_syntax_step M hPA
      context left right conclusion disjunctionChild leftChild rightChild)
    (raw_proofOrE_endpoint_rule_complete M hPA
      context left right conclusion disjunctionChild leftChild rightChild
      hdisjunctionEndpoint hleftEndpoint hrightEndpoint)).
Qed.

End PABoundedRawCodedProofOrEConstructor.
