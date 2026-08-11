(** PAUSED DRAFT CHECKPOINT (not registered in the committed Coq manifests).

    This file records unfinished Rocq work while development is focused on
    Lean.  The square-conjugacy table has passed the kernel, but the direct
    and cube conjugacy scripts below still need to be completed before this
    module is added to the build. *)
From Stdlib Require Import Lia.
From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field.
From PolynomialFormulas Require Import
  QuinticF20Data LazardQuinticF20Molien.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A coefficientwise Molien bridge for the permutation action of [F20] on
    five variables.

    Everything in this file is finite.  In degree [d], monomials are indexed
    by the five-tuples of exponents having total [d].  The group action is an
    explicit permutation matrix on that finite index type.  Its trace counts
    fixed exponent tuples.  The normalized sum of these matrices is an
    idempotent Reynolds matrix, so its trace is its rank, i.e. the dimension
    of the common fixed row space.

    The last part identifies the fixed exponent tuples in the four cycle
    types [1^5], [5], [1 2^2], and [1 4] with finite weighted-assignment
    counts.  A separate file proves that, for the positive weights used
    here, these counts are coefficients of the corresponding geometric
    products.  Connecting the finite row spaces themselves to an encoded
    polynomial invariant space is also a separate bridge. *)
Module PolynomialFormulasLazardInvariantMolienCoefficients.

Import GRing.Theory Num.Theory.
Import PolynomialFormulasQuinticF20Data.
Module MQ := PolynomialFormulasLazardQuinticF20Molien.

Local Open Scope ring_scope.
Local Open Scope group_scope.

(** * The finite homogeneous monomial basis *)

Definition bounded_quintic_exponent (d : nat) := 5.-tuple 'I_d.+1.

Definition exponent_total d (a : bounded_quintic_exponent d) : nat :=
  \sum_(i < 5) (tnth a i : nat).

Definition degree_exponent d :=
  {a : bounded_quintic_exponent d | exponent_total a == d}.

Definition act_bounded_exponent (s : S5) d
    (a : bounded_quintic_exponent d) : bounded_quintic_exponent d :=
  [tuple tnth a (s^-1 i) | i < 5].

Lemma exponent_total_act_bounded s d (a : bounded_quintic_exponent d) :
  exponent_total (act_bounded_exponent s a) = exponent_total a.
Proof.
rewrite /exponent_total /act_bounded_exponent.
under [LHS] eq_bigr => i _ do rewrite tnth_mktuple.
by rewrite [RHS](reindex_perm s^-1).
Qed.

Lemma act_degree_exponent_closed (s : S5) d (a : degree_exponent d) :
  exponent_total (act_bounded_exponent s (val a)) == d.
Proof.
by rewrite exponent_total_act_bounded; exact: valP a.
Qed.

Definition act_degree_exponent (s : S5) d (a : degree_exponent d) :
    degree_exponent d :=
  Sub (act_bounded_exponent s (val a))
    (act_degree_exponent_closed s a).

Lemma act_degree_exponent_one d (a : degree_exponent d) :
  act_degree_exponent 1 a = a.
Proof.
apply/val_inj/eq_from_tnth=> i.
by rewrite /act_degree_exponent /= /act_bounded_exponent
  tnth_mktuple invg1 perm1.
Qed.

Lemma act_degree_exponent_mul s t d (a : degree_exponent d) :
  act_degree_exponent (s * t) a =
    act_degree_exponent t (act_degree_exponent s a).
Proof.
apply/val_inj/eq_from_tnth=> i.
rewrite /act_degree_exponent /= /act_bounded_exponent
  !tnth_mktuple invMg permM.
by [].
Qed.

(** Enumerating the finite exponent type turns its action into an ordinal
    permutation, hence into a square permutation matrix. *)
Definition degree_exponent_index_action s d
    (i : 'I_#|{: degree_exponent d}|) : 'I_#|{: degree_exponent d}| :=
  enum_rank (act_degree_exponent s (enum_val i)).
Arguments degree_exponent_index_action s d i : clear implicits.

Lemma degree_exponent_index_action_injective s d :
  injective (degree_exponent_index_action s d).
Proof.
move=> i j /enum_rank_inj hij.
have hij' := congr1
  (fun x : degree_exponent d => act_degree_exponent s^-1 x) hij.
rewrite -!act_degree_exponent_mul mulgV
  !act_degree_exponent_one in hij'.
exact: enum_val_inj hij'.
Qed.
Arguments degree_exponent_index_action_injective s d : clear implicits.

Definition degree_exponent_perm s d : 'S_#|{: degree_exponent d}| :=
  perm (degree_exponent_index_action_injective s d).
Arguments degree_exponent_perm s d : clear implicits.

Lemma degree_exponent_permE s d i :
  degree_exponent_perm s d i =
    enum_rank (act_degree_exponent s (enum_val i)).
Proof. exact: permE _ _. Qed.

Lemma degree_exponent_perm_one d : degree_exponent_perm 1 d = 1%g.
Proof.
apply/permP=> i.
by rewrite degree_exponent_permE act_degree_exponent_one enum_valK perm1.
Qed.

Lemma degree_exponent_perm_mul s t d :
  degree_exponent_perm (s * t) d =
    (degree_exponent_perm s d * degree_exponent_perm t d)%g.
Proof.
apply/permP=> i.
rewrite permM !degree_exponent_permE enum_rankK.
by rewrite act_degree_exponent_mul.
Qed.

Definition fixed_degree_exponent s d :=
  {a : degree_exponent d | act_degree_exponent s a == a}.

Definition fixed_degree_index s d :=
  {i : 'I_#|{: degree_exponent d}| | degree_exponent_perm s d i == i}.

Definition fixed_exponent_count s d : nat := #|{: fixed_degree_exponent s d}|.

Definition fixed_exponent_to_index s d
    (a : fixed_degree_exponent s d) : fixed_degree_index s d.
Proof.
refine (Sub (enum_rank (val a)) _).
apply/eqP.
rewrite degree_exponent_permE enum_rankK.
by rewrite (eqP (valP a)).
Defined.

Definition fixed_index_to_exponent s d
    (i : fixed_degree_index s d) : fixed_degree_exponent s d.
Proof.
refine (Sub (enum_val (val i)) _).
apply/eqP.
apply/enum_rank_inj.
rewrite enum_valK.
move/eqP: (valP i).
by rewrite degree_exponent_permE.
Defined.

Arguments fixed_exponent_to_index s d a : clear implicits.
Arguments fixed_index_to_exponent s d i : clear implicits.

Lemma fixed_exponent_indexK s d :
  cancel (fixed_exponent_to_index s d) (fixed_index_to_exponent s d).
Proof. by move=> a; apply/val_inj; rewrite /= enum_rankK. Qed.

Lemma fixed_index_exponentK s d :
  cancel (fixed_index_to_exponent s d) (fixed_exponent_to_index s d).
Proof. by move=> i; apply/val_inj; rewrite /= enum_valK. Qed.

Lemma card_fixed_degree_index s d :
  #|{: fixed_degree_index s d}| = fixed_exponent_count s d.
Proof.
rewrite /fixed_exponent_count.
apply: (@bij_eq_card (fixed_degree_index s d) (fixed_degree_exponent s d)
  (fixed_index_to_exponent s d)).
exact: (@Bijective (fixed_degree_exponent s d) (fixed_degree_index s d)
  (fixed_index_to_exponent s d) (fixed_exponent_to_index s d)
  (@fixed_index_exponentK s d) (@fixed_exponent_indexK s d)).
Qed.

(** Trace of a permutation matrix is the number of fixed indices. *)
Lemma mxtrace_perm_mx_fixed (F : fieldType) n (p : 'S_n) :
  \tr (perm_mx p : 'M[F]_n) =
    (#|{: {i : 'I_n | p i == i}}|%:R : F).
Proof.
rewrite /mxtrace /perm_mx card_sub -sum1_card natr_sum [RHS]big_mkcond.
apply: eq_bigr=> i _.
rewrite /row_perm !mxE.
rewrite inE.
by case: (p i == i).
Qed.

Definition homogeneous_monomial_matrix (F : fieldType) (s : S5) d :
    'M[F]_#|{: degree_exponent d}| :=
  (perm_mx (degree_exponent_perm s d))^T.

(** Transposition makes these matrices an anti-homomorphism: the matrix of
    [s * t] is the product of the matrix of [t] followed by that of [s].
    Consequently, right multiplication of row vectors realizes a left
    action: applying [t] and then [s] multiplies by [M_t M_s = M_(s*t)].
    This is also the orientation of the coefficient action on polynomials;
    treating the same matrices as a right action would be incorrect. *)

Lemma homogeneous_monomial_matrix_one (F : fieldType) d :
  homogeneous_monomial_matrix F 1 d = 1%:M.
Proof.
by rewrite /homogeneous_monomial_matrix degree_exponent_perm_one
  perm_mx1 trmx1.
Qed.

Lemma homogeneous_monomial_matrix_mul (F : fieldType) s t d :
  homogeneous_monomial_matrix F (s * t) d =
    homogeneous_monomial_matrix F t d *m
      homogeneous_monomial_matrix F s d.
Proof.
by rewrite /homogeneous_monomial_matrix degree_exponent_perm_mul
  perm_mxM trmx_mul.
Qed.

Theorem homogeneous_monomial_trace_fixed_count
    (F : fieldType) s d :
  \tr (homogeneous_monomial_matrix F s d) =
    (fixed_exponent_count s d)%:R.
Proof.
rewrite /homogeneous_monomial_matrix mxtrace_tr
  mxtrace_perm_mx_fixed.
congr (_%:R : F).
exact: card_fixed_degree_index.
Qed.

(** * Reynolds averaging and fixed homogeneous dimension *)

Section HomogeneousReynolds.

Variables (F : fieldType) (H : {group S5}) (d : nat).
Hypothesis cardH_neq0 : (#|[subg H]|%:R : F) != 0.

Definition homogeneous_reynolds_matrix :
    'M[F]_#|{: degree_exponent d}| :=
  (#|[subg H]|%:R : F)^-1 *:
    \sum_(g : [subg H])
      homogeneous_monomial_matrix F (sgval g) d.

Lemma homogeneous_reynolds_mul (h : [subg H]) :
  homogeneous_reynolds_matrix *m
      homogeneous_monomial_matrix F (sgval h) d =
    homogeneous_reynolds_matrix.
Proof.
rewrite /homogeneous_reynolds_matrix -[LHS]scalemxAl.
apply: congr1.
have hmul (g : [subg H]) :
    homogeneous_monomial_matrix F (sgval g) d *m
        homogeneous_monomial_matrix F (sgval h) d =
      homogeneous_monomial_matrix F (sgval (h * g)) d.
  rewrite sgvalM.
  - exact: esym (@homogeneous_monomial_matrix_mul F
      (sgval h) (sgval g) d).
  - by rewrite inE.
  - by rewrite inE.
rewrite mulmx_suml.
under [LHS] eq_bigr => g _ do rewrite hmul.
(** The anti-homomorphism gives [h * g], so this is reindexing by left
    multiplication.  MathComp names its injectivity lemma [mulgI h]
    ([mulIg h] instead fixes the right factor). *)
symmetry.
apply: (reindex_inj
  (h := fun g : [subg H] => h * g)
  (P := predT)
  (F := fun g : [subg H] => homogeneous_monomial_matrix F (sgval g) d)).
exact: mulgI h.
Qed.

Lemma homogeneous_reynolds_fix_row
    (v : 'rV[F]_#|{: degree_exponent d}|) :
  (forall g : [subg H],
      v *m homogeneous_monomial_matrix F (sgval g) d = v) ->
  v *m homogeneous_reynolds_matrix = v.
Proof.
move=> hv.
rewrite /homogeneous_reynolds_matrix -scalemxAr mulmx_sumr.
under eq_bigr => g _ do rewrite hv.
rewrite sumr_const cardsT -scaler_nat scalerA.
have cardH_type_neq0 : (#|{: [subg H]}|%:R : F) != 0.
  by move: cardH_neq0; rewrite cardsT.
have hcard : #| (xpredT : pred [subg H]) | = #|{: [subg H]}|
  by reflexivity.
rewrite hcard.
rewrite (mulVf cardH_type_neq0).
exact: scale1r v.
Qed.

Lemma homogeneous_reynolds_idempotent :
  homogeneous_reynolds_matrix *m homogeneous_reynolds_matrix =
    homogeneous_reynolds_matrix.
Proof.
rewrite /homogeneous_reynolds_matrix -scalemxAr mulmx_sumr.
under eq_bigr => g _ do rewrite homogeneous_reynolds_mul.
rewrite sumr_const -scaler_nat scalerA.
have hcard : #| (xpredT : pred [subg H]) | = #|[set: [subg H]]|
  by rewrite cardsT.
rewrite hcard (mulVf cardH_neq0).
fold homogeneous_reynolds_matrix.
exact: scale1r homogeneous_reynolds_matrix.
Qed.

(** Membership in the row space of the Reynolds matrix is exactly the
    coordinate-vector formulation of invariance under every group element. *)
Lemma homogeneous_reynolds_row_spaceP
    (v : 'rV[F]_#|{: degree_exponent d}|) :
  reflect
    (forall g : [subg H],
      v *m homogeneous_monomial_matrix F (sgval g) d = v)
    (v <= homogeneous_reynolds_matrix)%MS.
Proof.
apply: (iffP submxP).
- move=> [u ->] g.
  by rewrite -mulmxA homogeneous_reynolds_mul.
- move=> hv.
  exists v.
  exact: esym (homogeneous_reynolds_fix_row hv).
Qed.

Definition homogeneous_fixed_dimension : nat :=
  \rank homogeneous_reynolds_matrix.

Lemma mxtrace_idempotent_rank n (A : 'M[F]_n) :
  A *m A = A -> \tr A = (\rank A)%:R.
Proof.
move=> hAA.
pose C := col_base A.
pose B := row_base A.
have hCB : C *m B = A by exact: mulmx_base A.
have hAC : A *m C = C.
  apply: (row_free_inj (row_base_free A)).
  by rewrite -mulmxA hCB hAA.
have hBC : B *m C = 1%:M.
  apply: (row_full_inj (col_base_full A)).
  by rewrite mulmxA hCB hAC mulmx1.
have htrace : \tr A = \tr (C *m B) by rewrite hCB.
by rewrite htrace mxtrace_mulC hBC mxtrace1.
Qed.

Lemma homogeneous_reynolds_trace_average :
  \tr homogeneous_reynolds_matrix =
    ((#|[subg H]|%:R : F)^-1 *
      \sum_(g : [subg H]) (fixed_exponent_count (sgval g) d)%:R)%R.
Proof.
rewrite /homogeneous_reynolds_matrix mxtraceZ raddf_sum.
apply: congr1.
apply: eq_bigr=> g _.
exact: homogeneous_monomial_trace_fixed_count.
Qed.

Theorem coefficientwise_molien_fixed_dimension :
  ((#|[subg H]|%:R : F)^-1 *
      \sum_(g : [subg H]) (fixed_exponent_count (sgval g) d)%:R)%R =
    (homogeneous_fixed_dimension)%:R.
Proof.
rewrite -homogeneous_reynolds_trace_average.
apply: mxtrace_idempotent_rank.
exact: homogeneous_reynolds_idempotent.
Qed.

End HomogeneousReynolds.

(** * Coefficients of the four geometric products *)

Definition weighted_total n d (w : n.-tuple nat)
    (q : n.-tuple 'I_d.+1) : nat :=
  \sum_(i < n) tnth w i * (tnth q i : nat).

Definition weighted_assignment n (w : n.-tuple nat) d :=
  {q : n.-tuple 'I_d.+1 | weighted_total w q == d}.

(** This is an entirely finite weighted-assignment count.  For the strictly
    positive concrete weights below it is the coefficient of
    [prod_i (1 - X^(w_i))^-1]: choosing [q_i] records how many copies of
    [X^(w_i)] are taken from the [i]-th geometric factor.  That geometric
    interpretation is not valid for an arbitrary tuple containing a zero
    weight. *)
Definition weighted_geometric_coefficient n (w : n.-tuple nat) d : rat :=
  (#|{: weighted_assignment w d}|%:R : rat).

Definition rational_series := nat -> rat.
Definition series_equiv (a b : rational_series) : Prop :=
  forall d, a d = b d.

Definition fixed_exponent_series s : rational_series :=
  fun d => (fixed_exponent_count s d)%:R.

Definition identity_weights : 5.-tuple nat := [tuple 1%N | _ < 5].
Definition five_cycle_weights : 1.-tuple nat := [tuple 5]%N.
Definition one_two_two_weights : 3.-tuple nat := [tuple 2; 2; 1]%N.
Definition one_four_weights : 2.-tuple nat := [tuple 4; 1]%N.

Lemma identity_weightE (i : 'I_5) : tnth identity_weights i = 1%N.
Proof. by rewrite /identity_weights tnth_mktuple. Qed.

Definition identity_geometric_series : rational_series :=
  weighted_geometric_coefficient identity_weights.
Definition five_cycle_geometric_series : rational_series :=
  weighted_geometric_coefficient five_cycle_weights.
Definition one_two_two_geometric_series : rational_series :=
  weighted_geometric_coefficient one_two_two_weights.
Definition one_four_geometric_series : rational_series :=
  weighted_geometric_coefficient one_four_weights.

Definition i1_0 : 'I_1 := @Ordinal 1 0 isT.
Definition i2_0 : 'I_2 := @Ordinal 2 0 isT.
Definition i2_1 : 'I_2 := @Ordinal 2 1 isT.
Definition i3_0 : 'I_3 := @Ordinal 3 0 isT.
Definition i3_1 : 'I_3 := @Ordinal 3 1 isT.
Definition i3_2 : 'I_3 := @Ordinal 3 2 isT.

Lemma one_two_two_weight0E : tnth one_two_two_weights i3_0 = 2%N.
Proof. by rewrite /one_two_two_weights /i3_0 /=. Qed.

Lemma one_two_two_weight1E : tnth one_two_two_weights i3_1 = 2%N.
Proof. by rewrite /one_two_two_weights /i3_1 /=. Qed.

Lemma one_two_two_weight2E : tnth one_two_two_weights i3_2 = 1%N.
Proof. by rewrite /one_two_two_weights /i3_2 /=. Qed.

Lemma one_four_weight0E : tnth one_four_weights i2_0 = 4%N.
Proof. by rewrite /one_four_weights /i2_0 /=. Qed.

Lemma one_four_weight1E : tnth one_four_weights i2_1 = 1%N.
Proof. by rewrite /one_four_weights /i2_1 /=. Qed.

(** Canonical indices produced by repeated [big_ord_recr].  Naming these
    equalities once keeps every explicit fixed-length sum proof independent
    of the proof fields stored in ordinal values. *)
Lemma ord5_widen0E :
    widen_ord (leqnSn 4)
      (widen_ord (leqnSn 3)
        (widen_ord (leqnSn 2)
          (widen_ord (leqnSn 1) ord_max))) = o0.
Proof. by apply/val_inj. Qed.

Lemma ord5_widen1E :
    widen_ord (leqnSn 4)
      (widen_ord (leqnSn 3) (widen_ord (leqnSn 2) ord_max)) = o1.
Proof. by apply/val_inj. Qed.

Lemma ord5_widen2E :
    widen_ord (leqnSn 4) (widen_ord (leqnSn 3) ord_max) = o2.
Proof. by apply/val_inj. Qed.

Lemma ord5_widen3E : widen_ord (leqnSn 4) ord_max = o3.
Proof. by apply/val_inj. Qed.

Lemma ord5_maxE : (ord_max : 'I_5) = o4.
Proof. by apply/val_inj. Qed.

Lemma ord3_widen0E :
    widen_ord (leqnSn 2) (widen_ord (leqnSn 1) ord_max) = i3_0.
Proof. by apply/val_inj. Qed.

Lemma ord3_widen1E : widen_ord (leqnSn 2) ord_max = i3_1.
Proof. by apply/val_inj. Qed.

Lemma ord3_maxE : (ord_max : 'I_3) = i3_2.
Proof. by apply/val_inj. Qed.

Lemma ord2_widen0E : widen_ord (leqnSn 1) ord_max = i2_0.
Proof. by apply/val_inj. Qed.

Lemma ord2_maxE : (ord_max : 'I_2) = i2_1.
Proof. by apply/val_inj. Qed.

Lemma ord1_maxE : (ord_max : 'I_1) = i1_0.
Proof. by apply/val_inj. Qed.

Lemma exponent_totalE d (a : bounded_quintic_exponent d) :
  exponent_total a =
    (tnth a o0 : nat) + (tnth a o1 : nat) + (tnth a o2 : nat) +
    (tnth a o3 : nat) + (tnth a o4 : nat).
Proof.
rewrite /exponent_total !big_ord_recr.
rewrite big_ord0 /=.
by rewrite ord5_widen0E ord5_widen1E ord5_widen2E ord5_widen3E
  ord5_maxE add0n.
Qed.

Lemma weighted_total_identityE d (q : 5.-tuple 'I_d.+1) :
  weighted_total identity_weights q = exponent_total q.
Proof.
rewrite /weighted_total /exponent_total.
apply: eq_bigr=> i _.
by rewrite identity_weightE mul1n.
Qed.

Lemma weighted_total_five_cycleE d (q : 1.-tuple 'I_d.+1) :
  weighted_total five_cycle_weights q =
    (5 * (tnth q i1_0 : nat))%N.
Proof.
by rewrite /weighted_total /five_cycle_weights
  !big_ord_recr big_ord0 /= ord1_maxE.
Qed.

Lemma weighted_total_one_two_twoE d (q : 3.-tuple 'I_d.+1) :
  weighted_total one_two_two_weights q =
    (2 * (tnth q i3_0 : nat) + 2 * (tnth q i3_1 : nat) +
      (tnth q i3_2 : nat))%N.
Proof.
rewrite /weighted_total
  !big_ord_recr big_ord0 /=.
rewrite ord3_widen0E ord3_widen1E ord3_maxE
  one_two_two_weight0E one_two_two_weight1E one_two_two_weight2E /=.
by rewrite add0n mul1n.
Qed.

Lemma weighted_total_one_fourE d (q : 2.-tuple 'I_d.+1) :
  weighted_total one_four_weights q =
    (4 * (tnth q i2_0 : nat) + (tnth q i2_1 : nat))%N.
Proof.
rewrite /weighted_total
  !big_ord_recr big_ord0 /=.
rewrite ord2_widen0E ord2_maxE one_four_weight0E one_four_weight1E /=.
by rewrite add0n mul1n.
Qed.

(** Concrete representatives of the remaining two nontrivial cycle types. *)
Definition one_two_two_representative : S5 :=
  (tperm o0 o1 * tperm o2 o3)%g.

Definition one_four_representative : S5 :=
  (tperm o0 o1 * tperm o1 o2 * tperm o2 o3)%g.

(** Explicit changes of labels from the convenient cycle representatives
    above to the affine [F20] representatives used in the class partition. *)
Definition one_two_two_conjugator : S5 := tperm o0 o4.

Definition one_four_conjugator : S5 :=
  (tperm o0 o4 * tperm o1 o2)%g.

Definition one_four_cube_conjugator : S5 :=
  (tperm o0 o4 * tperm o3 o4)%g.

(** Extensionality for permutations of the five explicitly named points.
    This keeps the concrete conjugacy certificates below both small and
    independent of reduction through MathComp's finite permutation record. *)
Lemma perm5_pointwise (s t : S5) :
    s o0 = t o0 -> s o1 = t o1 -> s o2 = t o2 ->
    s o3 = t o3 -> s o4 = t o4 -> s = t.
Proof.
move=> h0 h1 h2 h3 h4; apply/permP=> i.
case: i=> [[|[|[|[|[|i]]]]] hi].
- have -> : @Ordinal 5 0 hi = o0 by apply/val_inj.
  exact: h0.
- have -> : @Ordinal 5 1 hi = o1 by apply/val_inj.
  exact: h1.
- have -> : @Ordinal 5 2 hi = o2 by apply/val_inj.
  exact: h2.
- have -> : @Ordinal 5 3 hi = o3 by apply/val_inj.
  exact: h3.
- have -> : @Ordinal 5 4 hi = o4 by apply/val_inj.
  exact: h4.
- by move: hi.
Qed.

Lemma multiplier_two_sq_conjugate_one_two_two :
  multiplier_two ^+ 2 =
    one_two_two_representative ^ one_two_two_conjugator.
Proof.
apply: perm5_pointwise.
- by rewrite expgS expg1 permM multiplier_two_o0 multiplier_two_o0
    conjg_permE /one_two_two_conjugator tpermV tpermL
    /one_two_two_representative permM
    (tpermD (x := o0) (y := o1) (z := o4)) //
    (tpermD (x := o2) (y := o3) (z := o4)) // tpermR.
- by rewrite expgS expg1 permM multiplier_two_o1 multiplier_two_o2
    conjg_permE /one_two_two_conjugator tpermV
    (tpermD (x := o0) (y := o4) (z := o1)) //
    /one_two_two_representative permM tpermR
    (tpermD (x := o2) (y := o3) (z := o0)) // tpermL.
- by rewrite expgS expg1 permM multiplier_two_o2 multiplier_two_o4
    conjg_permE /one_two_two_conjugator tpermV
    (tpermD (x := o0) (y := o4) (z := o2)) //
    /one_two_two_representative permM
    (tpermD (x := o0) (y := o1) (z := o2)) // tpermL
    (tpermD (x := o0) (y := o4) (z := o3)).
- by rewrite expgS expg1 permM multiplier_two_o3 multiplier_two_o1
    conjg_permE /one_two_two_conjugator tpermV
    (tpermD (x := o0) (y := o4) (z := o3)) //
    /one_two_two_representative permM
    (tpermD (x := o0) (y := o1) (z := o3)) // tpermR
    (tpermD (x := o0) (y := o4) (z := o2)).
- by rewrite expgS expg1 permM multiplier_two_o4 multiplier_two_o3
    conjg_permE /one_two_two_conjugator tpermV tpermR
    /one_two_two_representative permM tpermL
    (tpermD (x := o2) (y := o3) (z := o1)) //
    (tpermD (x := o0) (y := o4) (z := o1)).
Qed.

Lemma multiplier_two_conjugate_one_four :
  multiplier_two = one_four_representative ^ one_four_conjugator.
Proof.
apply: perm5_pointwise.
all: rewrite ?multiplier_two_o0 ?multiplier_two_o1
  ?multiplier_two_o2 ?multiplier_two_o3 ?multiplier_two_o4.
all: rewrite conjg_permE /one_four_conjugator invgM !tpermV
  /one_four_representative !permM.
all: rewrite
  ?tpermL ?tpermR ?tpermD ?tpermL ?tpermR ?tpermD
  ?tpermL ?tpermR ?tpermD ?tpermL ?tpermR ?tpermD
  ?tpermL ?tpermR ?tpermD ?tpermL ?tpermR ?tpermD
  ?tpermL ?tpermR ?tpermD ?tpermL ?tpermR ?tpermD //.
all: exact: erefl.
Qed.

Lemma multiplier_two_cube_conjugate_one_four :
  multiplier_two ^+ 3 =
    one_four_representative ^ one_four_cube_conjugator.
Proof.
have h0 : (multiplier_two ^+ 3) o0 = o0.
  by rewrite expgS expgS expg1 !permM !multiplier_two_o0.
have h1 : (multiplier_two ^+ 3) o1 = o3.
  by rewrite expgS expgS expg1 !permM multiplier_two_o1
    multiplier_two_o2 multiplier_two_o4.
have h2 : (multiplier_two ^+ 3) o2 = o1.
  by rewrite expgS expgS expg1 !permM multiplier_two_o2
    multiplier_two_o4 multiplier_two_o3.
have h3 : (multiplier_two ^+ 3) o3 = o4.
  by rewrite expgS expgS expg1 !permM multiplier_two_o3
    multiplier_two_o1 multiplier_two_o2.
have h4 : (multiplier_two ^+ 3) o4 = o2.
  by rewrite expgS expgS expg1 !permM multiplier_two_o4
    multiplier_two_o3 multiplier_two_o1.
apply: perm5_pointwise.
all: rewrite ?h0 ?h1 ?h2 ?h3 ?h4.
all: rewrite conjg_permE /one_four_cube_conjugator invgM !tpermV
  /one_four_representative !permM.
all: by rewrite
  ?tpermL ?tpermR ?tpermD ?tpermL ?tpermR ?tpermD
  ?tpermL ?tpermR ?tpermD ?tpermL ?tpermR ?tpermD
  ?tpermL ?tpermR ?tpermD ?tpermL ?tpermR ?tpermD
  ?tpermL ?tpermR ?tpermD ?tpermL ?tpermR ?tpermD //.
Qed.

Lemma act_bounded_five_cycleE d (a : bounded_quintic_exponent d) :
  act_bounded_exponent five_cycle a =
    [tuple tnth a o1; tnth a o2; tnth a o3; tnth a o4; tnth a o0].
Proof.
apply: eq_from_tnth=> i.
case: i=> [[|[|[|[|[|i]]]]]] hi; last by move: hi.
all: rewrite /act_bounded_exponent !tnth_mktuple.
- by rewrite five_cycle_inv_o0.
- by rewrite five_cycle_inv_o1.
- by rewrite five_cycle_inv_o2.
- by rewrite five_cycle_inv_o3.
- by rewrite five_cycle_inv_o4.
Qed.

Lemma act_bounded_one_two_twoE d (a : bounded_quintic_exponent d) :
  act_bounded_exponent one_two_two_representative a =
    [tuple tnth a o1; tnth a o0; tnth a o3; tnth a o2; tnth a o4].
Proof.
apply: eq_from_tnth=> i.
case: i=> [[|[|[|[|[|i]]]]]] hi; last by move: hi.
all: rewrite /act_bounded_exponent /one_two_two_representative
  !tnth_mktuple invgM !tpermV permM.
all: by rewrite ?tpermL ?tpermR ?tpermD.
Qed.

Lemma act_bounded_one_fourE d (a : bounded_quintic_exponent d) :
  act_bounded_exponent one_four_representative a =
    [tuple tnth a o1; tnth a o2; tnth a o3; tnth a o0; tnth a o4].
Proof.
apply: eq_from_tnth=> i.
case: i=> [[|[|[|[|[|i]]]]]] hi; last by move: hi.
all: rewrite /act_bounded_exponent /one_four_representative
  !tnth_mktuple invgM !tpermV !permM.
all: by rewrite ?tpermL ?tpermR ?tpermD.
Qed.

Lemma fixed_degree_exponent_tupleE s d (a : fixed_degree_exponent s d) :
  act_bounded_exponent s (val (val a)) = val (val a).
Proof.
exact: congr1 val (eqP (valP a)).
Qed.

Lemma five_cycle_fixed_coordinates d
    (a : fixed_degree_exponent five_cycle d) :
  tnth (val (val a)) o1 = tnth (val (val a)) o0 /\
  tnth (val (val a)) o2 = tnth (val (val a)) o0 /\
  tnth (val (val a)) o3 = tnth (val (val a)) o0 /\
  tnth (val (val a)) o4 = tnth (val (val a)) o0.
Proof.
have h := fixed_degree_exponent_tupleE a.
rewrite act_bounded_five_cycleE in h.
have h0 := congr1 (fun q => tnth q o0) h.
have h1 := congr1 (fun q => tnth q o1) h.
have h2 := congr1 (fun q => tnth q o2) h.
have h3 := congr1 (fun q => tnth q o3) h.
have h4 := congr1 (fun q => tnth q o4) h.
move: h0 h1 h2 h3 h4; rewrite /= => h0 h1 h2 h3 h4.
repeat split.
- exact: h0.
- exact: (h1.trans h0).
- exact: (h2.trans (h1.trans h0)).
- exact: esym h4.
Qed.

Lemma one_two_two_fixed_coordinates d
    (a : fixed_degree_exponent one_two_two_representative d) :
  tnth (val (val a)) o1 = tnth (val (val a)) o0 /\
  tnth (val (val a)) o3 = tnth (val (val a)) o2.
Proof.
have h := fixed_degree_exponent_tupleE a.
rewrite act_bounded_one_two_twoE in h.
have h0 := congr1 (fun q => tnth q o0) h.
have h2 := congr1 (fun q => tnth q o2) h.
move: h0 h2; rewrite /= => h0 h2.
by split.
Qed.

Lemma one_four_fixed_coordinates d
    (a : fixed_degree_exponent one_four_representative d) :
  tnth (val (val a)) o1 = tnth (val (val a)) o0 /\
  tnth (val (val a)) o2 = tnth (val (val a)) o0 /\
  tnth (val (val a)) o3 = tnth (val (val a)) o0.
Proof.
have h := fixed_degree_exponent_tupleE a.
rewrite act_bounded_one_fourE in h.
have h0 := congr1 (fun q => tnth q o0) h.
have h1 := congr1 (fun q => tnth q o1) h.
have h2 := congr1 (fun q => tnth q o2) h.
move: h0 h1 h2; rewrite /= => h0 h1 h2.
repeat split.
- exact: h0.
- exact: (h1.trans h0).
- exact: (h2.trans (h1.trans h0)).
Qed.

(** The identity class. *)
Lemma identity_fixed_weighted_total d (a : fixed_degree_exponent 1 d) :
  weighted_total identity_weights (val (val a)) == d.
Proof.
by rewrite weighted_total_identityE; exact: valP (val a).
Qed.

Definition identity_fixed_to_weighted d
    (a : fixed_degree_exponent 1 d) :
    weighted_assignment identity_weights d :=
  Sub (val (val a))
    (identity_fixed_weighted_total a).

Definition identity_weighted_to_fixed d
    (q : weighted_assignment identity_weights d) :
    fixed_degree_exponent 1 d.
Proof.
refine (Sub (Sub (val q) _) _).
- by rewrite -weighted_total_identityE; exact: valP q.
- apply/eqP.
  exact: act_degree_exponent_one _.
Defined.

Lemma identity_fixed_weightedK d :
  cancel (identity_fixed_to_weighted d) (identity_weighted_to_fixed d).
Proof. by move=> a; apply/val_inj/val_inj. Qed.

Lemma identity_weighted_fixedK d :
  cancel (identity_weighted_to_fixed d) (identity_fixed_to_weighted d).
Proof. by move=> q; apply/val_inj. Qed.

Lemma card_fixed_identity_weighted d :
  fixed_exponent_count 1 d = #|{: weighted_assignment identity_weights d}|.
Proof.
apply: (@bij_eq_card (fixed_degree_exponent 1 d)
  (weighted_assignment identity_weights d) (identity_fixed_to_weighted d)).
exact: (@Bijective (weighted_assignment identity_weights d)
  (fixed_degree_exponent 1 d) (identity_fixed_to_weighted d)
  (identity_weighted_to_fixed d) (identity_fixed_weightedK d)
  (identity_weighted_fixedK d)).
Qed.

(** The five-cycle class. *)
Definition five_fixed_to_weighted d
    (a : fixed_degree_exponent five_cycle d) :
    weighted_assignment five_cycle_weights d.
Proof.
refine (Sub [tuple tnth (val (val a)) o0] _).
apply/eqP.
rewrite weighted_total_five_cycleE /=.
move/eqP: (valP (val a))=> htotal.
rewrite exponent_totalE in htotal.
have [h1 [h2 [h3 h4]]] := five_cycle_fixed_coordinates a.
move: htotal.
rewrite h1 h2 h3 h4.
lia.
Defined.

Definition five_weighted_to_fixed d
    (q : weighted_assignment five_cycle_weights d) :
    fixed_degree_exponent five_cycle d.
Proof.
pose a : bounded_quintic_exponent d :=
  [tuple tnth (val q) i1_0; tnth (val q) i1_0;
    tnth (val q) i1_0; tnth (val q) i1_0; tnth (val q) i1_0].
have ha : exponent_total a == d.
  apply/eqP.
  move/eqP: (valP q)=> hq.
  rewrite weighted_total_five_cycleE in hq.
  rewrite exponent_totalE /a /=.
  lia.
refine (Sub (Sub a ha) _).
apply/eqP/val_inj.
by rewrite /= act_bounded_five_cycleE /a.
Defined.

Lemma five_fixed_weightedK d :
  cancel (five_fixed_to_weighted d) (five_weighted_to_fixed d).
Proof.
move=> a.
apply/val_inj/val_inj/eq_from_tnth=> i.
have [h1 [h2 [h3 h4]]] := five_cycle_fixed_coordinates a.
case: i=> [[|[|[|[|[|i]]]]]] hi; last by move: hi.
- by rewrite /=.
- by rewrite /= h1.
- by rewrite /= h2.
- by rewrite /= h3.
- by rewrite /= h4.
Qed.

Lemma five_weighted_fixedK d :
  cancel (five_weighted_to_fixed d) (five_fixed_to_weighted d).
Proof.
move=> q; apply/val_inj/eq_from_tnth=> i.
case: i=> [[|i]] hi; last by move: hi.
by rewrite /=.
Qed.

Lemma card_fixed_five_cycle_weighted d :
  fixed_exponent_count five_cycle d =
    #|{: weighted_assignment five_cycle_weights d}|.
Proof.
apply: (@bij_eq_card (fixed_degree_exponent five_cycle d)
  (weighted_assignment five_cycle_weights d) (five_fixed_to_weighted d)).
exact: (@Bijective (weighted_assignment five_cycle_weights d)
  (fixed_degree_exponent five_cycle d) (five_fixed_to_weighted d)
  (five_weighted_to_fixed d) (five_fixed_weightedK d)
  (five_weighted_fixedK d)).
Qed.

(** The [1 2^2] class. *)
Definition one_two_two_fixed_to_weighted d
    (a : fixed_degree_exponent one_two_two_representative d) :
    weighted_assignment one_two_two_weights d.
Proof.
refine (Sub
  [tuple tnth (val (val a)) o0; tnth (val (val a)) o2;
    tnth (val (val a)) o4] _).
apply/eqP.
rewrite weighted_total_one_two_twoE /=.
move/eqP: (valP (val a))=> htotal.
rewrite exponent_totalE in htotal.
have [h1 h3] := one_two_two_fixed_coordinates a.
move: htotal.
rewrite h1 h3.
lia.
Defined.

Definition one_two_two_weighted_to_fixed d
    (q : weighted_assignment one_two_two_weights d) :
    fixed_degree_exponent one_two_two_representative d.
Proof.
pose a : bounded_quintic_exponent d :=
  [tuple tnth (val q) i3_0; tnth (val q) i3_0;
    tnth (val q) i3_1; tnth (val q) i3_1; tnth (val q) i3_2].
have ha : exponent_total a == d.
  apply/eqP.
  move/eqP: (valP q)=> hq.
  rewrite weighted_total_one_two_twoE in hq.
  rewrite exponent_totalE /a /=.
  lia.
refine (Sub (Sub a ha) _).
apply/eqP/val_inj.
by rewrite /= act_bounded_one_two_twoE /a.
Defined.

Lemma one_two_two_fixed_weightedK d :
  cancel (one_two_two_fixed_to_weighted d)
    (one_two_two_weighted_to_fixed d).
Proof.
move=> a.
apply/val_inj/val_inj/eq_from_tnth=> i.
have [h1 h3] := one_two_two_fixed_coordinates a.
case: i=> [[|[|[|[|[|i]]]]]] hi; last by move: hi.
- by rewrite /=.
- by rewrite /= h1.
- by rewrite /=.
- by rewrite /= h3.
- by rewrite /=.
Qed.

Lemma one_two_two_weighted_fixedK d :
  cancel (one_two_two_weighted_to_fixed d)
    (one_two_two_fixed_to_weighted d).
Proof.
move=> q; apply/val_inj/eq_from_tnth=> i.
case: i=> [[|[|[|i]]]] hi; last by move: hi.
all: by rewrite /=.
Qed.

Lemma card_fixed_one_two_two_weighted d :
  fixed_exponent_count one_two_two_representative d =
    #|{: weighted_assignment one_two_two_weights d}|.
Proof.
apply: (@bij_eq_card (fixed_degree_exponent one_two_two_representative d)
  (weighted_assignment one_two_two_weights d)
  (one_two_two_fixed_to_weighted d)).
exact: (@Bijective (weighted_assignment one_two_two_weights d)
  (fixed_degree_exponent one_two_two_representative d)
  (one_two_two_fixed_to_weighted d) (one_two_two_weighted_to_fixed d)
  (one_two_two_fixed_weightedK d) (one_two_two_weighted_fixedK d)).
Qed.

(** The [1 4] class. *)
Definition one_four_fixed_to_weighted d
    (a : fixed_degree_exponent one_four_representative d) :
    weighted_assignment one_four_weights d.
Proof.
refine (Sub
  [tuple tnth (val (val a)) o0; tnth (val (val a)) o4] _).
apply/eqP.
rewrite weighted_total_one_fourE /=.
move/eqP: (valP (val a))=> htotal.
rewrite exponent_totalE in htotal.
have [h1 [h2 h3]] := one_four_fixed_coordinates a.
move: htotal.
rewrite h1 h2 h3.
lia.
Defined.

Definition one_four_weighted_to_fixed d
    (q : weighted_assignment one_four_weights d) :
    fixed_degree_exponent one_four_representative d.
Proof.
pose a : bounded_quintic_exponent d :=
  [tuple tnth (val q) i2_0; tnth (val q) i2_0;
    tnth (val q) i2_0; tnth (val q) i2_0; tnth (val q) i2_1].
have ha : exponent_total a == d.
  apply/eqP.
  move/eqP: (valP q)=> hq.
  rewrite weighted_total_one_fourE in hq.
  rewrite exponent_totalE /a /=.
  lia.
refine (Sub (Sub a ha) _).
apply/eqP/val_inj.
by rewrite /= act_bounded_one_fourE /a.
Defined.

Lemma one_four_fixed_weightedK d :
  cancel (one_four_fixed_to_weighted d) (one_four_weighted_to_fixed d).
Proof.
move=> a.
apply/val_inj/val_inj/eq_from_tnth=> i.
have [h1 [h2 h3]] := one_four_fixed_coordinates a.
case: i=> [[|[|[|[|[|i]]]]]] hi; last by move: hi.
- by rewrite /=.
- by rewrite /= h1.
- by rewrite /= h2.
- by rewrite /= h3.
- by rewrite /=.
Qed.

Lemma one_four_weighted_fixedK d :
  cancel (one_four_weighted_to_fixed d) (one_four_fixed_to_weighted d).
Proof.
move=> q; apply/val_inj/eq_from_tnth=> i.
case: i=> [[|[|i]]] hi; last by move: hi.
all: by rewrite /=.
Qed.

Lemma card_fixed_one_four_weighted d :
  fixed_exponent_count one_four_representative d =
    #|{: weighted_assignment one_four_weights d}|.
Proof.
apply: (@bij_eq_card (fixed_degree_exponent one_four_representative d)
  (weighted_assignment one_four_weights d) (one_four_fixed_to_weighted d)).
exact: (@Bijective (weighted_assignment one_four_weights d)
  (fixed_degree_exponent one_four_representative d)
  (one_four_fixed_to_weighted d) (one_four_weighted_to_fixed d)
  (one_four_fixed_weightedK d) (one_four_weighted_fixedK d)).
Qed.

(** These are the four generating-series identities, deliberately stated
    coefficientwise so no functional-extensionality principle is needed. *)
Theorem identity_fixed_exponent_series :
  series_equiv (fixed_exponent_series 1) identity_geometric_series.
Proof.
move=> d.
by rewrite /fixed_exponent_series /identity_geometric_series
  /weighted_geometric_coefficient card_fixed_identity_weighted.
Qed.

Theorem five_cycle_fixed_exponent_series :
  series_equiv (fixed_exponent_series five_cycle)
    five_cycle_geometric_series.
Proof.
move=> d.
by rewrite /fixed_exponent_series /five_cycle_geometric_series
  /weighted_geometric_coefficient card_fixed_five_cycle_weighted.
Qed.

Theorem one_two_two_fixed_exponent_series :
  series_equiv (fixed_exponent_series one_two_two_representative)
    one_two_two_geometric_series.
Proof.
move=> d.
by rewrite /fixed_exponent_series /one_two_two_geometric_series
  /weighted_geometric_coefficient card_fixed_one_two_two_weighted.
Qed.

Theorem one_four_fixed_exponent_series :
  series_equiv (fixed_exponent_series one_four_representative)
    one_four_geometric_series.
Proof.
move=> d.
by rewrite /fixed_exponent_series /one_four_geometric_series
  /weighted_geometric_coefficient card_fixed_one_four_weighted.
Qed.

(** * The [F20] class sum *)

(** Trace, hence fixed-exponent count after casting to a field, is invariant
    under conjugation. *)
Lemma homogeneous_monomial_trace_conjugate
    (F : fieldType) s c d :
  \tr (homogeneous_monomial_matrix F (s ^ c) d) =
    \tr (homogeneous_monomial_matrix F s d).
Proof.
rewrite conjgE !homogeneous_monomial_matrix_mul mxtrace_mulC -mulmxA.
by rewrite -homogeneous_monomial_matrix_mul mulgV
  homogeneous_monomial_matrix_one mulmx1.
Qed.

Lemma fixed_exponent_count_conjugate s c d :
  (fixed_exponent_count (s ^ c) d)%:R =
    (fixed_exponent_count s d)%:R :> rat.
Proof.
rewrite -!homogeneous_monomial_trace_fixed_count.
exact: homogeneous_monomial_trace_conjugate.
Qed.

(** The structural [F20] class equalities, together with the explicit label
    changes above, identify each nonidentity class with the conjugacy class
    of the displayed representative. *)
Lemma f20_five_cycle_class_conjugateb :
  [forall s : S5,
    MQ.f20_class MQ.f20_five_cycle_classb s ==>
      [exists c : S5, s == five_cycle ^ c]].
Proof.
apply/forallP=> s; apply/implyP=> hs.
rewrite MQ.f20_five_cycle_classE in hs.
move/imsetP: hs=> [c hc ->].
apply/existsP; exists c.
by rewrite eqxx.
Qed.

Lemma f20_one_two_two_class_conjugateb :
  [forall s : S5,
    MQ.f20_class MQ.f20_one_two_two_classb s ==>
      [exists c : S5, s == one_two_two_representative ^ c]].
Proof.
apply/forallP=> s; apply/implyP=> hs.
rewrite MQ.f20_one_two_two_classE in hs.
move/imsetP: hs=> [c hc ->].
apply/existsP; exists (one_two_two_conjugator * c)%g.
apply/eqP.
by rewrite conjgM -multiplier_two_sq_conjugate_one_two_two.
Qed.

Lemma f20_one_four_class_conjugateb :
  [forall s : S5,
    MQ.f20_class MQ.f20_one_four_classb s ==>
      [exists c : S5, s == one_four_representative ^ c]].
Proof.
apply/forallP=> s; apply/implyP=> hs.
rewrite MQ.f20_one_four_classE in hs.
move/orP: hs=> [hs | hs].
- move/imsetP: hs=> [c hc ->].
  apply/existsP; exists (one_four_conjugator * c)%g.
  apply/eqP.
  by rewrite conjgM -multiplier_two_conjugate_one_four.
- move/imsetP: hs=> [c hc ->].
  apply/existsP; exists (one_four_cube_conjugator * c)%g.
  apply/eqP.
  by rewrite conjgM -multiplier_two_cube_conjugate_one_four.
Qed.

Definition f20_identity_set : {set S5} :=
  MQ.f20_class MQ.f20_identity_classb.
Definition f20_five_cycle_set : {set S5} :=
  MQ.f20_class MQ.f20_five_cycle_classb.
Definition f20_one_two_two_set : {set S5} :=
  MQ.f20_class MQ.f20_one_two_two_classb.
Definition f20_one_four_set : {set S5} :=
  MQ.f20_class MQ.f20_one_four_classb.

Definition f20_cycle_class_union : {set S5} :=
  (((f20_identity_set :|: f20_five_cycle_set) :|:
      f20_one_two_two_set) :|: f20_one_four_set).

(** Small projections from membership in each class.  Keeping these facts
    separate makes the partition and disjointness proofs purely logical;
    they no longer enumerate [S5]. *)
Lemma f20_identity_set_eq1 s :
  s \in f20_identity_set -> s = 1%g.
Proof.
by rewrite /f20_identity_set MQ.f20_identity_classE inE => /eqP.
Qed.

Lemma f20_five_cycle_set_fixed_count s :
  s \in f20_five_cycle_set -> MQ.f20_fixed_count s = 0%N.
Proof.
rewrite /f20_five_cycle_set MQ.f20_five_cycle_classE.
exact: MQ.five_cycle_C4_fixed_count.
Qed.

Lemma f20_one_two_two_set_data s :
  s \in f20_one_two_two_set ->
    MQ.f20_fixed_count s = 1%N /\ s ^+ 2 = 1%g.
Proof.
rewrite /f20_one_two_two_set MQ.f20_one_two_two_classE=> hs.
split.
- exact: MQ.multiplier_two_sq_C5_fixed_count hs.
- exact: MQ.multiplier_two_sq_C5_sq_eq1 hs.
Qed.

Lemma f20_one_four_set_data s :
  s \in f20_one_four_set ->
    MQ.f20_fixed_count s = 1%N /\ s ^+ 2 != 1%g.
Proof.
rewrite /f20_one_four_set MQ.f20_one_four_classE inE=> /orP[hs | hs].
- split.
  + exact: MQ.multiplier_two_C5_fixed_count hs.
  + exact: MQ.multiplier_two_C5_sq_neq1 hs.
- split.
  + exact: MQ.multiplier_two_cube_C5_fixed_count hs.
  + exact: MQ.multiplier_two_cube_C5_sq_neq1 hs.
Qed.

Lemma f20_cycle_class_partition :
  f20_cycle_class_union = [set s : S5 | normalizes_cycleb s].
Proof.
apply/setP=> s.
rewrite /f20_cycle_class_union /f20_identity_set
  /f20_five_cycle_set /f20_one_two_two_set /f20_one_four_set
  /MQ.f20_class !inE.
case hnorm: (normalizes_cycleb s)=> //=.
exact: implyP (forallP MQ.f20_cycle_classes_exhaustb s) hnorm.
Qed.

Lemma f20_identity_five_disjoint :
  [disjoint f20_identity_set & f20_five_cycle_set].
Proof.
rewrite disjoint_subset.
apply/subsetP=> s hs1.
rewrite inE.
apply/negP=> hs5.
have -> := f20_identity_set_eq1 hs1.
have hfix := f20_five_cycle_set_fixed_count hs5.
by move: hfix; rewrite MQ.f20_fixed_count_one.
Qed.

Lemma f20_identity_five_two_two_disjoint :
  [disjoint (f20_identity_set :|: f20_five_cycle_set) &
    f20_one_two_two_set].
Proof.
rewrite disjoint_subset.
apply/subsetP=> s hs.
rewrite inE.
apply/negP=> hs22.
have [hfix22 _] := f20_one_two_two_set_data hs22.
move/orP: hs=> [hs1 | hs5].
- have -> := f20_identity_set_eq1 hs1.
  move: hfix22; rewrite MQ.f20_fixed_count_one.
  by [].
- have hfix5 := f20_five_cycle_set_fixed_count hs5.
  lia.
Qed.

Lemma f20_previous_one_four_disjoint :
  [disjoint
    ((f20_identity_set :|: f20_five_cycle_set) :|:
      f20_one_two_two_set) & f20_one_four_set].
Proof.
rewrite disjoint_subset.
apply/subsetP=> s hs.
rewrite inE.
apply/negP=> hs4.
have [hfix4 hsq4] := f20_one_four_set_data hs4.
move/orP: hs=> [hs15 | hs22].
- move/orP: hs15=> [hs1 | hs5].
  + have -> := f20_identity_set_eq1 hs1.
    move: hfix4; rewrite MQ.f20_fixed_count_one.
    by [].
  + have hfix5 := f20_five_cycle_set_fixed_count hs5.
    lia.
- have [_ hsq22] := f20_one_two_two_set_data hs22.
  by move: hsq4; rewrite hsq22 eqxx.
Qed.

Lemma f20_identity_class_fixed_count s d :
  s \in f20_identity_set ->
  (fixed_exponent_count s d)%:R =
    (fixed_exponent_count 1 d)%:R :> rat.
Proof.
move=> hs.
have -> := f20_identity_set_eq1 hs.
reflexivity.
Qed.

Lemma f20_five_cycle_class_fixed_count s d :
  s \in f20_five_cycle_set ->
  (fixed_exponent_count s d)%:R =
    (fixed_exponent_count five_cycle d)%:R :> rat.
Proof.
move=> hs.
have hsMQ : MQ.f20_class MQ.f20_five_cycle_classb s := hs.
have hs' := implyP (forallP f20_five_cycle_class_conjugateb s) hsMQ.
move/existsP: hs'=> [c /eqP ->].
exact: fixed_exponent_count_conjugate.
Qed.

Lemma f20_one_two_two_class_fixed_count s d :
  s \in f20_one_two_two_set ->
  (fixed_exponent_count s d)%:R =
    (fixed_exponent_count one_two_two_representative d)%:R :> rat.
Proof.
move=> hs.
have hsMQ : MQ.f20_class MQ.f20_one_two_two_classb s := hs.
have hs' := implyP (forallP f20_one_two_two_class_conjugateb s) hsMQ.
move/existsP: hs'=> [c /eqP ->].
exact: fixed_exponent_count_conjugate.
Qed.

Lemma f20_one_four_class_fixed_count s d :
  s \in f20_one_four_set ->
  (fixed_exponent_count s d)%:R =
    (fixed_exponent_count one_four_representative d)%:R :> rat.
Proof.
move=> hs.
have hsMQ : MQ.f20_class MQ.f20_one_four_classb s := hs.
have hs' := implyP (forallP f20_one_four_class_conjugateb s) hsMQ.
move/existsP: hs'=> [c /eqP ->].
exact: fixed_exponent_count_conjugate.
Qed.

Lemma f20_identity_class_sum d :
  \sum_(s in f20_identity_set) (fixed_exponent_count s d)%:R =
    (fixed_exponent_count 1 d)%:R :> rat.
Proof.
under eq_bigr => s hs do rewrite (f20_identity_class_fixed_count hs).
rewrite sumr_const -mulr_natl.
have hcard : #|f20_identity_set| = 1%N.
  exact: MQ.card_f20_identity_class.
by rewrite hcard /= mul1r.
Qed.

Lemma f20_five_cycle_class_sum d :
  \sum_(s in f20_five_cycle_set) (fixed_exponent_count s d)%:R =
    4%:R * (fixed_exponent_count five_cycle d)%:R :> rat.
Proof.
under eq_bigr => s hs do rewrite (f20_five_cycle_class_fixed_count hs).
rewrite sumr_const -mulr_natl.
have hcard : #|f20_five_cycle_set| = 4%N.
  exact: MQ.card_f20_five_cycle_class.
by rewrite hcard.
Qed.

Lemma f20_one_two_two_class_sum d :
  \sum_(s in f20_one_two_two_set) (fixed_exponent_count s d)%:R =
    5%:R * (fixed_exponent_count one_two_two_representative d)%:R :> rat.
Proof.
under eq_bigr => s hs do
  rewrite (f20_one_two_two_class_fixed_count hs).
rewrite sumr_const -mulr_natl.
have hcard : #|f20_one_two_two_set| = 5%N.
  exact: MQ.card_f20_one_two_two_class.
by rewrite hcard.
Qed.

Lemma f20_one_four_class_sum d :
  \sum_(s in f20_one_four_set) (fixed_exponent_count s d)%:R =
    10%:R * (fixed_exponent_count one_four_representative d)%:R :> rat.
Proof.
under eq_bigr => s hs do rewrite (f20_one_four_class_fixed_count hs).
rewrite sumr_const -mulr_natl.
have hcard : #|f20_one_four_set| = 10%N.
  exact: MQ.card_f20_one_four_class.
by rewrite hcard.
Qed.

Theorem f20_fixed_exponent_class_sum d :
  \sum_(g : [subg standard_F20])
      (fixed_exponent_count (sgval g) d)%:R =
    (fixed_exponent_count 1 d)%:R +
    4%:R * (fixed_exponent_count five_cycle d)%:R +
    5%:R * (fixed_exponent_count one_two_two_representative d)%:R +
    10%:R * (fixed_exponent_count one_four_representative d)%:R :> rat.
Proof.
transitivity
  (\sum_(s in [set s : S5 | normalizes_cycleb s])
    (fixed_exponent_count s d)%:R : rat).
- rewrite -big_sub.
  apply: eq_bigl=> s.
  by rewrite normalizes_cyclebE.
- rewrite -f20_cycle_class_partition /f20_cycle_class_union.
  rewrite (bigU f20_previous_one_four_disjoint)
    (bigU f20_identity_five_two_two_disjoint)
    (bigU f20_identity_five_disjoint).
  by rewrite f20_identity_class_sum f20_five_cycle_class_sum
    f20_one_two_two_class_sum f20_one_four_class_sum.
Qed.

(** Legacy name for the rank sequence of the finite Reynolds matrices.
    The row-space fixed-vector predicate was characterized above; identifying
    it with an actual encoded polynomial invariant space is not done here. *)
Definition f20_invariant_hilbert_series : rational_series :=
  fun d =>
    (homogeneous_fixed_dimension rat standard_F20 d)%:R.

Definition f20_geometric_class_sum_series : rational_series :=
  fun d => (20%:R : rat)^-1 *
    (identity_geometric_series d +
     4%:R * five_cycle_geometric_series d +
     5%:R * one_two_two_geometric_series d +
     10%:R * one_four_geometric_series d).

Lemma f20_subgroup_card_rat_neq0 :
  (#|[subg standard_F20]|%:R : rat) != 0.
Proof. exact: natrG_neq0. Qed.

Theorem f20_class_sum_hilbert_series :
  series_equiv f20_invariant_hilbert_series
    f20_geometric_class_sum_series.
Proof.
move=> d.
have hmol := @coefficientwise_molien_fixed_dimension
  rat standard_F20 d f20_subgroup_card_rat_neq0.
rewrite /f20_invariant_hilbert_series
  /f20_geometric_class_sum_series.
symmetry.
move: hmol.
rewrite card_sub card_standard_F20 f20_fixed_exponent_class_sum
  card_fixed_identity_weighted card_fixed_five_cycle_weighted
  card_fixed_one_two_two_weighted card_fixed_one_four_weighted.
by rewrite /identity_geometric_series /five_cycle_geometric_series
  /one_two_two_geometric_series /one_four_geometric_series
  /weighted_geometric_coefficient.
Qed.

(** The first conjunct is the coefficientwise Reynolds fixed-dimension
    calculation against the four finitely defined weighted-geometric
    coefficient sequences.  Identifying those sequences with coefficients
    of the corresponding rational functions is a separate formal bridge.
    The second conjunct is the previously proved rational simplification to
    Lazard's numerator. *)
Theorem f20_hilbert_series_and_rational_numerator
    (F : fieldType) (t : F)
    (h1 : 1 - t != 0)
    (h2 : 1 - t ^+ 2 != 0)
    (h3 : 1 - t ^+ 3 != 0)
    (h4 : 1 - t ^+ 4 != 0)
    (h5 : 1 - t ^+ 5 != 0)
    (h20 : (20%:R : F) != 0) :
  series_equiv f20_invariant_hilbert_series
      f20_geometric_class_sum_series /\
  MQ.f20_molien_class_sum t =
    MQ.f20_molien_numerator t / MQ.f20_symmetric_denominator t.
Proof.
split.
- exact: f20_class_sum_hilbert_series.
- exact: MQ.f20_molien_class_sum_identity h1 h2 h3 h4 h5 h20.
Qed.

End PolynomialFormulasLazardInvariantMolienCoefficients.
