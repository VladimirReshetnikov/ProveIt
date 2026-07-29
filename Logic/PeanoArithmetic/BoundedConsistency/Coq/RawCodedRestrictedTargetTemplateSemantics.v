(**
  Compositional semantics for unsealed restricted-target contexts.

  The restricted-proof fragment used by recursive-child descent contains no
  [RTFCSeal] node.  Its hierarchy-level hole may therefore be interpreted
  directly as a fixed carrier value while quantifiers extend only the
  ordinary de Bruijn assignment.  This is exactly the behavior of a named
  template parameter.

  The main theorem connects that compact context interpreter to the generic
  template semantics.  Keeping the theorem structural avoids expanding the
  large proof-restriction formula and, importantly, never asks whether the
  carrier level is a standard numeral.
*)

From Stdlib Require Import List Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding FiniteSkolemHull.
From BoundedPAConsistency Require Import
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedRestrictedTargetTemplateContext
  RawCodedTemplateSyntax
  RawCodedTemplateSemantics.

Module PABoundedRawCodedRestrictedTargetTemplateSemantics.

Module StdNat := PeanoNat.Nat.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PAFiniteSkolemHull.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedRestrictedTargetTemplateContext.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateSemantics.

Fixpoint rawRestrictedTargetTermContextEval
    (M : RawPAModel) (variables : nat -> M) (replacement : M)
    (context : RestrictedTargetTermContext) : M :=
  match context with
  | RTTCFixed fixed => raw_term_eval M variables fixed
  | RTTCHole => replacement
  | RTTCSucc child =>
      raw_succ M
        (rawRestrictedTargetTermContextEval M variables replacement child)
  | RTTCAdd lhs rhs =>
      raw_add M
        (rawRestrictedTargetTermContextEval M variables replacement lhs)
        (rawRestrictedTargetTermContextEval M variables replacement rhs)
  | RTTCMul lhs rhs =>
      raw_mul M
        (rawRestrictedTargetTermContextEval M variables replacement lhs)
        (rawRestrictedTargetTermContextEval M variables replacement rhs)
  end.

(** The seal branch is deliberately outside this interpreter.  Sealing
    closes a formula according to a syntactic bound and is not used anywhere
    in [restrictedTargetProofContext].  [RestrictedTargetFormulaContextSealFree]
    records the exact admissible fragment and makes the impossible branch
    explicit in every correctness proof. *)
Fixpoint RestrictedTargetFormulaContextSealFree
    (context : RestrictedTargetFormulaContext) : Prop :=
  match context with
  | RTFCFixed _ | RTFCBot | RTFCEq _ _ => True
  | RTFCImp lhs rhs | RTFCAnd lhs rhs | RTFCOr lhs rhs =>
      RestrictedTargetFormulaContextSealFree lhs /\
      RestrictedTargetFormulaContextSealFree rhs
  | RTFCAll child | RTFCEx child =>
      RestrictedTargetFormulaContextSealFree child
  | RTFCSeal _ => False
  end.

Fixpoint rawRestrictedTargetFormulaContextSat
    (M : RawPAModel) (variables : nat -> M) (replacement : M)
    (context : RestrictedTargetFormulaContext) : Prop :=
  match context with
  | RTFCFixed fixed => raw_formula_sat M variables fixed
  | RTFCBot => False
  | RTFCEq lhs rhs =>
      rawRestrictedTargetTermContextEval M variables replacement lhs =
      rawRestrictedTargetTermContextEval M variables replacement rhs
  | RTFCImp lhs rhs =>
      rawRestrictedTargetFormulaContextSat M variables replacement lhs ->
      rawRestrictedTargetFormulaContextSat M variables replacement rhs
  | RTFCAnd lhs rhs =>
      rawRestrictedTargetFormulaContextSat M variables replacement lhs /\
      rawRestrictedTargetFormulaContextSat M variables replacement rhs
  | RTFCOr lhs rhs =>
      rawRestrictedTargetFormulaContextSat M variables replacement lhs \/
      rawRestrictedTargetFormulaContextSat M variables replacement rhs
  | RTFCAll child =>
      forall value : M,
        rawRestrictedTargetFormulaContextSat M
          (scons M value variables) replacement child
  | RTFCEx child =>
      exists value : M,
        rawRestrictedTargetFormulaContextSat M
          (scons M value variables) replacement child
  | RTFCSeal _ => False
  end.

Arguments rawRestrictedTargetTermContextEval M variables replacement context
  : clear implicits.
Arguments rawRestrictedTargetFormulaContextSat M variables replacement context
  : clear implicits.

(** A tight upper bound on genuinely free outer variables.  In contrast with
    the coding-oriented bound above, binary nodes use [max] and quantifiers
    remove their freshly bound variable. *)
Fixpoint rawRestrictedTargetTermContextFreeBound
    (context : RestrictedTargetTermContext) : nat :=
  match context with
  | RTTCFixed fixed => Term.bound fixed
  | RTTCHole => 0
  | RTTCSucc child => rawRestrictedTargetTermContextFreeBound child
  | RTTCAdd lhs rhs | RTTCMul lhs rhs =>
      Nat.max
        (rawRestrictedTargetTermContextFreeBound lhs)
        (rawRestrictedTargetTermContextFreeBound rhs)
  end.

Fixpoint rawRestrictedTargetFormulaContextFreeBound
    (context : RestrictedTargetFormulaContext) : nat :=
  match context with
  | RTFCFixed fixed => Formula.bound fixed
  | RTFCBot => 0
  | RTFCEq lhs rhs =>
      Nat.max
        (rawRestrictedTargetTermContextFreeBound lhs)
        (rawRestrictedTargetTermContextFreeBound rhs)
  | RTFCImp lhs rhs | RTFCAnd lhs rhs | RTFCOr lhs rhs =>
      Nat.max
        (rawRestrictedTargetFormulaContextFreeBound lhs)
        (rawRestrictedTargetFormulaContextFreeBound rhs)
  | RTFCAll child | RTFCEx child =>
      Nat.pred (rawRestrictedTargetFormulaContextFreeBound child)
  | RTFCSeal _ => 0
  end.

(** A context depends only on variables below its free-variable bound.
    Binary nodes take the maximum of their children's bounds, while a binder
    removes its freshly bound variable with [Nat.pred]. *)
Lemma rawRestrictedTargetTermContextEval_ext_below : forall
    (M : RawPAModel) first second replacement context,
  (forall index,
    index < rawRestrictedTargetTermContextFreeBound context ->
    first index = second index) ->
  rawRestrictedTargetTermContextEval M first replacement context =
  rawRestrictedTargetTermContextEval M second replacement context.
Proof.
  intros M first second replacement context. revert first second.
  induction context as [fixed | | child ih | lhs ihlhs rhs ihrhs |
      lhs ihlhs rhs ihrhs]; intros first second hext;
    cbn [rawRestrictedTargetTermContextEval
      rawRestrictedTargetTermContextFreeBound] in hext |- *.
  - apply raw_term_eval_ext_free. intros index hfree.
    apply hext. exact (Term.free_lt_bound fixed index hfree).
  - reflexivity.
  - now rewrite (ih first second hext).
  - rewrite (ihlhs first second), (ihrhs first second); [reflexivity | |].
    + intros index hindex. apply (hext index).
      eapply StdNat.lt_le_trans; [exact hindex |].
      eauto using StdNat.le_max_l, StdNat.le_max_r.
    + intros index hindex. apply (hext index).
      eapply StdNat.lt_le_trans; [exact hindex |].
      eauto using StdNat.le_max_l, StdNat.le_max_r.
  - rewrite (ihlhs first second), (ihrhs first second); [reflexivity | |].
    + intros index hindex. apply (hext index).
      eapply StdNat.lt_le_trans; [exact hindex |].
      eauto using StdNat.le_max_l, StdNat.le_max_r.
    + intros index hindex. apply (hext index).
      eapply StdNat.lt_le_trans; [exact hindex |].
      eauto using StdNat.le_max_l, StdNat.le_max_r.
Qed.

Lemma rawRestrictedTargetFormulaContextSat_ext_below : forall
    (M : RawPAModel) first second replacement context,
  (forall index,
    index < rawRestrictedTargetFormulaContextFreeBound context ->
    first index = second index) ->
  (rawRestrictedTargetFormulaContextSat M first replacement context <->
   rawRestrictedTargetFormulaContextSat M second replacement context).
Proof.
  intros M first second replacement context. revert first second.
  induction context as
      [fixed | | lhs rhs | lhs ihlhs rhs ihrhs |
       lhs ihlhs rhs ihrhs | lhs ihlhs rhs ihrhs |
       child ihchild | child ihchild | child ihchild];
    intros first second hext;
    cbn [rawRestrictedTargetFormulaContextSat
      rawRestrictedTargetFormulaContextFreeBound] in hext |- *.
  - apply raw_formula_sat_ext_free. intros index hfree.
    apply hext. exact (Formula.free_lt_bound fixed index hfree).
  - reflexivity.
  - rewrite
      (rawRestrictedTargetTermContextEval_ext_below M first second
        replacement lhs),
      (rawRestrictedTargetTermContextEval_ext_below M first second
        replacement rhs); [reflexivity | |].
    + intros index hindex. apply (hext index).
      eapply StdNat.lt_le_trans; [exact hindex |].
      eauto using StdNat.le_max_l, StdNat.le_max_r.
    + intros index hindex. apply (hext index).
      eapply StdNat.lt_le_trans; [exact hindex |].
      eauto using StdNat.le_max_l, StdNat.le_max_r.
  - rewrite (ihlhs first second), (ihrhs first second); [reflexivity | |].
    + intros index hindex. apply (hext index).
      eapply StdNat.lt_le_trans; [exact hindex |].
      eauto using StdNat.le_max_l, StdNat.le_max_r.
    + intros index hindex. apply (hext index).
      eapply StdNat.lt_le_trans; [exact hindex |].
      eauto using StdNat.le_max_l, StdNat.le_max_r.
  - rewrite (ihlhs first second), (ihrhs first second); [reflexivity | |].
    + intros index hindex. apply (hext index).
      eapply StdNat.lt_le_trans; [exact hindex |].
      eauto using StdNat.le_max_l, StdNat.le_max_r.
    + intros index hindex. apply (hext index).
      eapply StdNat.lt_le_trans; [exact hindex |].
      eauto using StdNat.le_max_l, StdNat.le_max_r.
  - rewrite (ihlhs first second), (ihrhs first second); [reflexivity | |].
    + intros index hindex. apply (hext index).
      eapply StdNat.lt_le_trans; [exact hindex |].
      eauto using StdNat.le_max_l, StdNat.le_max_r.
    + intros index hindex. apply (hext index).
      eapply StdNat.lt_le_trans; [exact hindex |].
      eauto using StdNat.le_max_l, StdNat.le_max_r.
  - split; intros hall value.
    + assert (hext' : forall index,
          index < rawRestrictedTargetFormulaContextFreeBound child ->
          scons M value first index = scons M value second index).
      { intros [|index] hindex; cbn [scons]; [reflexivity |].
        apply hext. lia. }
      exact (proj1 (ihchild (scons M value first)
        (scons M value second) hext') (hall value)).
    + assert (hext' : forall index,
          index < rawRestrictedTargetFormulaContextFreeBound child ->
          scons M value first index = scons M value second index).
      { intros [|index] hindex; cbn [scons]; [reflexivity |].
        apply hext. lia. }
      exact (proj2 (ihchild (scons M value first)
        (scons M value second) hext') (hall value)).
  - split; intros [value hvalue]; exists value.
    + assert (hext' : forall index,
          index < rawRestrictedTargetFormulaContextFreeBound child ->
          scons M value first index = scons M value second index).
      { intros [|index] hindex; cbn [scons]; [reflexivity |].
        apply hext. lia. }
      exact (proj1 (ihchild (scons M value first)
        (scons M value second) hext') hvalue).
    + assert (hext' : forall index,
          index < rawRestrictedTargetFormulaContextFreeBound child ->
          scons M value first index = scons M value second index).
      { intros [|index] hindex; cbn [scons]; [reflexivity |].
        apply hext. lia. }
      exact (proj2 (ihchild (scons M value first)
        (scons M value second) hext') hvalue).
  - reflexivity.
Qed.

Theorem rawTemplateTermEval_restrictedTarget_parameter : forall
    (M : RawPAModel) variables parameters name context,
  rawTemplateTermEval M variables parameters
    (restrictedTargetTemplateTermContext (ttParameter name) context) =
  rawRestrictedTargetTermContextEval M variables (parameters name) context.
Proof.
  intros M variables parameters name context.
  induction context; cbn
      [restrictedTargetTemplateTermContext rawTemplateTermEval
       rawRestrictedTargetTermContextEval].
  - apply rawTemplateTermEval_embedPA.
  - reflexivity.
  - now rewrite IHcontext.
  - now rewrite IHcontext1, IHcontext2.
  - now rewrite IHcontext1, IHcontext2.
Qed.

Theorem rawTemplateFormulaSat_restrictedTarget_parameter : forall
    (M : RawPAModel) variables parameters predicates name context,
  RestrictedTargetFormulaContextSealFree context ->
  (rawTemplateFormulaSat M variables parameters predicates
    (restrictedTargetTemplateFormulaContext (ttParameter name) context) <->
   rawRestrictedTargetFormulaContextSat M variables
    (parameters name) context).
Proof.
  intros M variables parameters predicates name context.
  revert variables.
  induction context as
      [fixed | | lhs rhs | lhs ihlhs rhs ihrhs |
       lhs ihlhs rhs ihrhs | lhs ihlhs rhs ihrhs |
       child ihchild | child ihchild | child ihchild];
    intros variables hfree; cbn
      [RestrictedTargetFormulaContextSealFree
       restrictedTargetTemplateFormulaContext rawTemplateFormulaSat
       rawRestrictedTargetFormulaContextSat] in *.
  - apply rawTemplateFormulaSat_embedPA.
  - reflexivity.
  - now rewrite !rawTemplateTermEval_restrictedTarget_parameter.
  - destruct hfree as [hleft hright].
    now rewrite (ihlhs variables hleft), (ihrhs variables hright).
  - destruct hfree as [hleft hright].
    now rewrite (ihlhs variables hleft), (ihrhs variables hright).
  - destruct hfree as [hleft hright].
    now rewrite (ihlhs variables hleft), (ihrhs variables hright).
  - split; intros hall value.
    + apply (proj1 (ihchild (scons M value variables) hfree)). apply hall.
    + apply (proj2 (ihchild (scons M value variables) hfree)). apply hall.
  - split; intros [value hvalue]; exists value.
    + apply (proj1 (ihchild (scons M value variables) hfree)). exact hvalue.
    + apply (proj2 (ihchild (scons M value variables) hfree)). exact hvalue.
  - contradiction.
Qed.

(** The recursive-proof restriction family is entirely seal-free.  These
    named facts let downstream semantic lemmas avoid repeated normalization
    of the large contexts. *)
Lemma restrictedTargetFormulaQuantifierBoundedContext_seal_free : forall code,
  RestrictedTargetFormulaContextSealFree
    (restrictedTargetFormulaQuantifierBoundedContext code).
Proof. intro code. cbn. repeat split; exact I. Qed.

Lemma restrictedTargetContextAllBoundedContext_seal_free : forall context,
  RestrictedTargetFormulaContextSealFree
    (restrictedTargetContextAllBoundedContext context).
Proof. intro context. cbn. repeat split; exact I. Qed.

Lemma restrictedTargetProofNodeContext_seal_free : forall
    code supportCode supportStep,
  RestrictedTargetFormulaContextSealFree
    (restrictedTargetProofNodeContext code supportCode supportStep).
Proof.
  intros. cbn [restrictedTargetProofNodeContext
    restrictedTargetProofConstructorOccurrencesBoundedContext
    restrictedTargetProofEndpointOccurrencesBoundedContext
    restrictedTargetAllN
    restrictedTargetProofOccurrenceCasesBoundedContext
    restrictedTargetProofFormulaFieldsBoundedContext
    restrictedTargetContextAllBoundedContext
    restrictedTargetFormulaQuantifierBoundedContext].
  repeat split; exact I.
Qed.

Lemma restrictedTargetProofTraversalContext_seal_free : forall
    bound supportCode supportStep,
  RestrictedTargetFormulaContextSealFree
    (restrictedTargetProofTraversalContext bound supportCode supportStep).
Proof.
  intros. cbn [restrictedTargetProofTraversalContext].
  repeat split; exact I.
Qed.

Lemma restrictedTargetProofCertificateWithSupportContext_seal_free : forall
    root supportCode supportStep,
  RestrictedTargetFormulaContextSealFree
    (restrictedTargetProofCertificateWithSupportContext
      root supportCode supportStep).
Proof.
  intros. cbn [restrictedTargetProofCertificateWithSupportContext].
  split; [apply restrictedTargetProofTraversalContext_seal_free | exact I].
Qed.

Lemma restrictedTargetProofContext_seal_free : forall root,
  RestrictedTargetFormulaContextSealFree
    (restrictedTargetProofContext root).
Proof.
  intro root. cbn [restrictedTargetProofContext restrictedTargetExN].
  apply restrictedTargetProofCertificateWithSupportContext_seal_free.
Qed.

End PABoundedRawCodedRestrictedTargetTemplateSemantics.
