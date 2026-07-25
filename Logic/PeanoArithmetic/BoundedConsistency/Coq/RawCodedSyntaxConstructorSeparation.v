(**
  Separation boundary for the polynomial syntax constructors.

  Exact constructor semantics alone is sufficient to *build* coded rows.
  Deterministic parsing additionally needs injectivity of the polynomial
  pairing function inside arbitrary PA models.  This file represents that
  statement by one explicit PA sentence, proves its exact raw semantics, and
  derives list-node/list-arity injectivity from it.  Thus the remaining
  arithmetic obligation is isolated as the concrete derivation
  [PolynomialPairInjectivityProof], not hidden behind an axiom.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax RawCodedSyntaxConstructors.

Import ListNotations.

Module PABoundedRawCodedSyntaxConstructorSeparation.

Import PA.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.

Definition RawPolynomialPairInjective (M : RawPAModel) : Prop :=
  forall a b c d : M,
    rawPolynomialPair M a b = rawPolynomialPair M c d ->
    a = c /\ b = d.

Definition polynomialPairInjectiveTermAt
    (a b c d : term) : formula :=
  pImp (pEq (pairTerm a b) (pairTerm c d))
    (pAnd (pEq a c) (pEq b d)).

(** Four universal binders reverse the variable order in the body: variable
    three is the first quantified coordinate and variable zero the last. *)
Definition polynomialPairInjectiveFormula : formula :=
  pAll (pAll (pAll (pAll
    (polynomialPairInjectiveTermAt
      (tVar 3) (tVar 2) (tVar 1) (tVar 0))))).

Lemma raw_sat_polynomialPairInjectiveTermAt_iff : forall
    (M : RawPAModel) e a b c d,
  raw_formula_sat M e (polynomialPairInjectiveTermAt a b c d) <->
  (rawPolynomialPair M (raw_term_eval M e a) (raw_term_eval M e b) =
   rawPolynomialPair M (raw_term_eval M e c) (raw_term_eval M e d) ->
   raw_term_eval M e a = raw_term_eval M e c /\
   raw_term_eval M e b = raw_term_eval M e d).
Proof.
  intros. unfold polynomialPairInjectiveTermAt.
  cbn [raw_formula_sat]. rewrite !raw_eval_pairTerm. reflexivity.
Qed.

Theorem raw_sat_polynomialPairInjectiveFormula_iff : forall
    (M : RawPAModel) e,
  raw_formula_sat M e polynomialPairInjectiveFormula <->
  RawPolynomialPairInjective M.
Proof.
  intros M e. unfold polynomialPairInjectiveFormula,
    RawPolynomialPairInjective.
  cbn [raw_formula_sat]. split.
  - intros hall a b c d heq.
    pose proof (hall a b c d) as h.
    pose proof (proj1 (raw_sat_polynomialPairInjectiveTermAt_iff M
      (scons M d (scons M c (scons M b (scons M a e))))
      (tVar 3) (tVar 2) (tVar 1) (tVar 0)) h) as himp.
    cbn [raw_term_eval scons] in himp. exact (himp heq).
  - intros hinjective a b c d.
    apply (proj2 (raw_sat_polynomialPairInjectiveTermAt_iff M
      (scons M d (scons M c (scons M b (scons M a e))))
      (tVar 3) (tVar 2) (tVar 1) (tVar 0))).
    cbn [raw_term_eval scons]. apply hinjective.
Qed.

(** This is the single explicit arithmetic proof obligation left by the
    constructor-separation layer. *)
Definition PolynomialPairInjectivityProof : Prop :=
  Formula.BProv Formula.Ax_s [] polynomialPairInjectiveFormula.

Lemma raw_succ_injective_syntax : forall (M : RawPAModel),
  RawPASatisfies M -> forall x y : M,
  raw_succ M x = raw_succ M y -> x = y.
Proof.
  intros M hPA x y heq.
  set (e := scons M x (scons M y (fun _ : nat => raw_zero M))).
  pose proof (raw_sat_of_BProv_axs M _ hPA
    (Formula.BProv_Ax_s_succInj_terms nil (tVar 0) (tVar 1)) e) as hinj.
  cbn [raw_formula_sat raw_term_eval scons] in hinj.
  exact (hinj heq).
Qed.

Lemma raw_zero_not_succ_syntax : forall (M : RawPAModel),
  RawPASatisfies M -> forall x : M, raw_zero M <> raw_succ M x.
Proof.
  intros M hPA x.
  set (e := scons M x (fun _ : nat => raw_zero M)).
  pose proof (raw_sat_of_BProv_axs M _ hPA
    (Formula.BProv_Ax_s_zeroNotSucc_term nil (tVar 0)) e) as hnot.
  cbn [raw_formula_sat raw_term_eval scons] in hnot.
  intro hzero. apply hnot. symmetry. exact hzero.
Qed.

Lemma raw_pair_injective_of_proof :
  PolynomialPairInjectivityProof ->
  forall (M : RawPAModel), RawPASatisfies M ->
  RawPolynomialPairInjective M.
Proof.
  intros hproof M hPA.
  pose proof (raw_sat_of_BProv_axs M polynomialPairInjectiveFormula
    hPA hproof (fun _ => raw_zero M)) as hsat.
  apply (proj1 (raw_sat_polynomialPairInjectiveFormula_iff M
    (fun _ => raw_zero M))). exact hsat.
Qed.

Definition RawListNodeInjective (M : RawPAModel) : Prop :=
  forall head tail head' tail' : M,
    rawListNode M head tail = rawListNode M head' tail' ->
    head = head' /\ tail = tail'.

Lemma raw_listNode_injective_of_pair_injective : forall (M : RawPAModel),
  RawPASatisfies M ->
  RawPolynomialPairInjective M ->
  RawListNodeInjective M.
Proof.
  intros M hPA hpair head tail head' tail' hnode.
  unfold rawListNode in hnode.
  apply (raw_succ_injective_syntax M hPA) in hnode.
  exact (hpair head tail head' tail' hnode).
Qed.

Lemma raw_codeList1_injective : forall (M : RawPAModel),
  RawListNodeInjective M -> forall x y,
  rawCodeList1 M x = rawCodeList1 M y -> x = y.
Proof.
  intros M hnode x y h.
  unfold rawCodeList1, rawListCode in h.
  exact (proj1 (hnode x (raw_zero M) y (raw_zero M) h)).
Qed.

Lemma raw_codeList2_injective : forall (M : RawPAModel),
  RawListNodeInjective M -> forall x y x' y',
  rawCodeList2 M x y = rawCodeList2 M x' y' ->
  x = x' /\ y = y'.
Proof.
  intros M hnode x y x' y' h.
  unfold rawCodeList2, rawListCode in h.
  destruct (hnode x (rawListNode M y (raw_zero M))
    x' (rawListNode M y' (raw_zero M)) h) as [hx htail].
  split; [exact hx |].
  exact (proj1 (hnode y (raw_zero M) y' (raw_zero M) htail)).
Qed.

Lemma raw_codeList3_injective : forall (M : RawPAModel),
  RawListNodeInjective M -> forall x y z x' y' z',
  rawCodeList3 M x y z = rawCodeList3 M x' y' z' ->
  x = x' /\ y = y' /\ z = z'.
Proof.
  intros M hnode x y z x' y' z' h.
  unfold rawCodeList3, rawListCode in h.
  destruct (hnode x
    (rawListNode M y (rawListNode M z (raw_zero M))) x'
    (rawListNode M y' (rawListNode M z' (raw_zero M))) h)
    as [hx htail].
  destruct (hnode y (rawListNode M z (raw_zero M)) y'
    (rawListNode M z' (raw_zero M)) htail) as [hy hlast].
  destruct (hnode z (raw_zero M) z' (raw_zero M) hlast) as [hz _].
  repeat split; assumption.
Qed.

Lemma raw_codeList1_neq_codeList2 : forall (M : RawPAModel),
  RawPASatisfies M -> RawListNodeInjective M -> forall x y z,
  rawCodeList1 M x <> rawCodeList2 M y z.
Proof.
  intros M hPA hnode x y z heq.
  unfold rawCodeList1, rawCodeList2, rawListCode in heq.
  pose proof (proj2 (hnode x (raw_zero M) y
    (rawListNode M z (raw_zero M)) heq)) as hzero.
  exact (raw_zero_not_succ_syntax M hPA
    (rawPolynomialPair M z (raw_zero M)) hzero).
Qed.

Lemma raw_codeList2_neq_codeList3 : forall (M : RawPAModel),
  RawPASatisfies M -> RawListNodeInjective M -> forall x y x' y' z',
  rawCodeList2 M x y <> rawCodeList3 M x' y' z'.
Proof.
  intros M hPA hnode x y x' y' z' heq.
  unfold rawCodeList2, rawCodeList3, rawListCode in heq.
  pose proof (proj2 (hnode x (rawListNode M y (raw_zero M)) x'
    (rawListNode M y' (rawListNode M z' (raw_zero M))) heq)) as htail.
  pose proof (proj2 (hnode y (raw_zero M) y'
    (rawListNode M z' (raw_zero M)) htail)) as hzero.
  exact (raw_zero_not_succ_syntax M hPA
    (rawPolynomialPair M z' (raw_zero M)) hzero).
Qed.

(** Standard syntax quotations are injective unconditionally from PA, even
    before the stronger nonstandard constructor separation obligation above
    is discharged. *)
Theorem rawQuotedTermCode_injective : forall (M : RawPAModel),
  RawPASatisfies M -> forall a b,
  rawQuotedTermCode M a = rawQuotedTermCode M b -> a = b.
Proof.
  intros M hPA a b h.
  rewrite !rawQuotedTermCode_standard in h by exact hPA.
  apply termCode_injective.
  exact (rawNumeralValue_injective M hPA _ _ h).
Qed.

Theorem rawQuotedFormulaCode_injective : forall (M : RawPAModel),
  RawPASatisfies M -> forall a b,
  rawQuotedFormulaCode M a = rawQuotedFormulaCode M b -> a = b.
Proof.
  intros M hPA a b h.
  rewrite !rawQuotedFormulaCode_standard in h by exact hPA.
  apply formulaCode_injective.
  exact (rawNumeralValue_injective M hPA _ _ h).
Qed.

End PABoundedRawCodedSyntaxConstructorSeparation.
