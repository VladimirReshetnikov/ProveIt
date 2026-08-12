From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From mathcomp.multinomials Require Import mpoly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The first multivariate-polynomial layer for Lazard's invariant-module
    theorem.

    This file uses the official MathComp multinomials API.  It packages the
    elementary-symmetric substitution, the fundamental theorem and its
    homogeneous refinement, the correctly oriented left permutation action,
    and the finite Artin monomial family with Lazard's degree bound.

    The source is written against [coq-mathcomp-multinomials] 2.4.0.  In that
    release [msymMm] gives [msym (s1 * s2) p = msym s2 (msym s1 p)], so the
    inverse in [mpoly_left_action] is essential. *)
Module PolynomialFormulasLazardInvariantMultinomials.

Import GRing.Theory.

Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope mpoly_scope.

Section SymmetricCoordinates.

Variables (R : comRingType) (n : nat).

(** The tuple [(e1, ..., en)] of elementary symmetric polynomials. *)
Definition elementary_symmetric_tuple : n.-tuple {mpoly R[n]} :=
  [tuple mesym n R i.+1 | i < n].

(** Evaluation of a source polynomial in the elementary symmetric tuple. *)
Definition sym_eval (t : {mpoly R[n]}) : {mpoly R[n]} :=
  t \mPo elementary_symmetric_tuple.

Lemma sym_eval0 : sym_eval 0 = 0.
Proof. exact: comp_mpoly0. Qed.

Lemma sym_eval1 :
  sym_eval (1%R : {mpoly R[n]}) = (1%R : {mpoly R[n]}).
Proof. exact: comp_mpoly1. Qed.

Lemma sym_evalD : {morph sym_eval : x y / x + y}.
Proof. exact: comp_mpolyD. Qed.

Lemma sym_evalM : {morph sym_eval : x y / (x * y)%R}.
Proof. exact: rmorphM. Qed.

Fact sym_eval_is_additive : additive sym_eval.
Proof. exact: comp_mpolyB. Qed.

HB.instance Definition sym_eval_additive := GRing.isAdditive.Build
  {mpoly R[n]} {mpoly R[n]} sym_eval sym_eval_is_additive.

Fact sym_eval_is_multiplicative : multiplicative sym_eval.
Proof.
split.
- move=> p q; exact (sym_evalM p q).
- exact: sym_eval1.
Qed.

HB.instance Definition sym_eval_multiplicative := GRing.isMultiplicative.Build
  {mpoly R[n]} {mpoly R[n]} sym_eval sym_eval_is_multiplicative.

(** Elementary-symmetric substitution is injective.  This is the uniqueness
    half of the fundamental theorem, not an assumed normal-form property. *)
Lemma sym_eval_injective : injective sym_eval.
Proof.
move=> t1 t2; rewrite /sym_eval /elementary_symmetric_tuple.
exact: msym_fundamental_un.
Qed.

(** Every elementary-symmetric composition is fully symmetric. *)
Lemma sym_eval_symmetric t : sym_eval t \is symmetric.
Proof.
apply: mcomp_sym => i.
rewrite /elementary_symmetric_tuple -tnth_nth tnth_mktuple.
exact: mesym_sym.
Qed.

(** Exact image characterization of the full symmetric polynomials. *)
Lemma sym_eval_imageP p :
  reflect (exists t, sym_eval t = p) (p \is symmetric).
Proof.
apply: (iffP idP).
- move/sym_fundamental=> [t [ht _]].
  exists t; exact: ht.
- move=> [t <-].
  exact: sym_eval_symmetric.
Qed.

(** The quantitative existence theorem supplied by multinomials 2.4.0. *)
Lemma symmetric_coordinates p :
  p \is symmetric ->
  {t : {mpoly R[n]} |
    sym_eval t = p /\ (mweight t <= msize p)%N}.
Proof.
rewrite /sym_eval /elementary_symmetric_tuple.
exact: sym_fundamental.
Qed.

(** Weighted homogeneity of a source is equivalent to ordinary homogeneity
    after elementary-symmetric substitution. *)
Lemma sym_eval_homogeneousE t d :
  (t \is d.-homog for mnmwgt) = (sym_eval t \is d.-homog).
Proof.
rewrite /sym_eval /elementary_symmetric_tuple.
exact: mwmwgt_homogE.
Qed.

(** Homogeneous refinement of the fundamental theorem. *)
Lemma symmetric_homogeneous_coordinates p d :
  p \is symmetric -> p \is d.-homog ->
  {t : {mpoly R[n]} |
    sym_eval t = p /\ t \is d.-homog for mnmwgt}.
Proof.
rewrite /sym_eval /elementary_symmetric_tuple.
exact: sym_fundamental_homog.
Qed.

End SymmetricCoordinates.

Section PermutationAction.

Variables (R : comRingType) (n : nat).

(** The left action corresponding to multinomials' right-oriented [msym]. *)
Definition mpoly_left_action (s : 'S_n) (p : {mpoly R[n]}) :
    {mpoly R[n]} :=
  msym s^-1 p.

Lemma mpoly_left_action1 p : mpoly_left_action 1 p = p.
Proof. by rewrite /mpoly_left_action invg1 msym1m. Qed.

Lemma mpoly_left_actionM (s1 s2 : 'S_n) p :
  mpoly_left_action (s1 * s2) p =
    mpoly_left_action s1 (mpoly_left_action s2 p).
Proof. by rewrite /mpoly_left_action invMg msymMm. Qed.

Lemma mpoly_left_actionD s :
  {morph mpoly_left_action s : x y / x + y}.
Proof. exact: msymD. Qed.

Lemma mpoly_left_action0 s : mpoly_left_action s 0 = 0.
Proof. exact: msym0. Qed.

Lemma mpoly_left_actionN s :
  {morph mpoly_left_action s : x / - x}.
Proof. exact: msymN. Qed.

Lemma mpoly_left_actionB s :
  {morph mpoly_left_action s : x y / x - y}.
Proof. exact: msymB. Qed.

Lemma mpoly_left_action_mul s :
  {morph mpoly_left_action s : x y / (x * y)%R}.
Proof. exact: msymM. Qed.

Lemma mpoly_left_actionZ s c p :
  mpoly_left_action s ((c *: p)%R) =
    (c *: mpoly_left_action s p)%R.
Proof. exact: msymZ. Qed.

(** Permuting variables preserves ordinary total-degree homogeneity. *)
Lemma mpoly_left_action_homogeneous s p d :
  p \is d.-homog -> mpoly_left_action s p \is d.-homog.
Proof.
rewrite !homog_piE /mpoly_left_action.
move/eqP=> hp; apply/eqP.
by rewrite -msym_pihomog hp.
Qed.

(** Full symmetry is equivalently fixedness under this honest left action. *)
Lemma full_symmetricP p :
  reflect (forall s : 'S_n, mpoly_left_action s p = p)
    (p \is symmetric).
Proof.
apply: (iffP (issymP p)).
- move=> hp s; exact: hp s^-1.
- move=> hp s.
  have := hp s^-1.
  by rewrite /mpoly_left_action invgK.
Qed.

End PermutationAction.

Section ArtinFamily.

(** An Artin exponent has [0 <= a_i < n-i] at coordinate [i].  Dependent
    finite functions make finiteness part of the type, including at [n = 0]. *)
Definition artin_index (n : nat) :=
  {dffun forall i : 'I_n, 'I_(n - i) : finType}.

(** The exponent vector and its total degree. *)
Definition artin_exponent n (a : artin_index n) : 'X_{1..n} :=
  [multinom (a i : nat) | i < n].

Definition artin_degree n (a : artin_index n) : nat :=
  \sum_(i < n) (a i : nat).

Lemma artin_exponent_degree n (a : artin_index n) :
  mdeg (artin_exponent a) = artin_degree a.
Proof.
rewrite /artin_exponent /artin_degree mdegE.
apply: eq_bigr => i _.
by rewrite mnmE.
Qed.

Lemma artin_exponent_injective n : injective (@artin_exponent n).
Proof.
move=> a b hab; apply/ffunP=> i; apply/val_inj.
move: (congr1 (fun m : 'X_{1..n} => m i) hab).
by rewrite !mnmE.
Qed.

(** Lazard's uniform degree bound [n(n-1)/2]. *)
Definition lazard_degree_bound (n : nat) : nat := (n * n.-1)./2.

Lemma lazard_degree_bound_binomial n :
  lazard_degree_bound n = 'C(n, 2).
Proof. by rewrite /lazard_degree_bound bin2. Qed.

Lemma sum_rev_ord_lazard_degree_bound n :
  \sum_(i < n) (rev_ord i : nat) = lazard_degree_bound n.
Proof.
rewrite /lazard_degree_bound -bin2.
rewrite (reindex_inj rev_ord_inj) /=.
have hsum : \sum_(i < n) (i : nat) = 'C(n, 2) by
  rewrite -(@big_mkord nat 0 addn n xpredT (fun i => i)) bin2_sum.
transitivity (\sum_(j < n) (j : nat)).
- apply: eq_bigr => j _.
  rewrite (subnSK (ltn_ord j)).
  exact: subKn (ltnW (ltn_ord j)).
- exact: hsum.
Qed.

Lemma artin_degree_le n (a : artin_index n) :
  (artin_degree a <= lazard_degree_bound n)%N.
Proof.
rewrite /artin_degree -sum_rev_ord_lazard_degree_bound.
apply: leq_sum => i _.
change ((a i : nat) <= n - i.+1)%N.
move: (ltn_ord (a i)).
by rewrite ltn_subRL
  (@leq_subRL i.+1 (a i : nat) n (ltn_ord i)) addSn.
Qed.

(** The Artin monomial indexed by [a]. *)
Definition artin_monomial (R : ringType) n (a : artin_index n) :
    {mpoly R[n]} :=
  'X_[R, artin_exponent a].

Lemma artin_monomial_homogeneous (R : ringType) n (a : artin_index n) :
  artin_monomial R a \is (artin_degree a).-homog.
Proof.
rewrite /artin_monomial dhomogX.
change (mdeg (artin_exponent a) == artin_degree a).
by rewrite artin_exponent_degree eqxx.
Qed.

Lemma artin_monomial_degree_le (R : ringType) n (a : artin_index n) :
  (mdeg (artin_exponent a) <= lazard_degree_bound n)%N.
Proof. by rewrite artin_exponent_degree; exact: artin_degree_le. Qed.

(** The index family has the expected finite cardinality [n!]. *)
Lemma card_artin_index n : #|artin_index n| = n`!.
Proof.
rewrite /artin_index card_dep_ffun.
have hseq :
    [seq #|'I_(n - i)| | i : 'I_n] = [seq (n - i)%N | i : 'I_n].
  apply: eq_map => i.
  exact: card_ord.
rewrite hseq.
rewrite -ffactnn ffact_prod.
unfold image_mem, enum_mem.
rewrite filter_predT.
rewrite (@unlock _ _ bigop_unlock) /reducebig.
rewrite foldr_map.
cbv delta [index_enum locked_with index_enum_key applybig comp].
done.
Qed.

End ArtinFamily.

End PolynomialFormulasLazardInvariantMultinomials.
