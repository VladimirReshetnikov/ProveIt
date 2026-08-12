From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The order-free, all-degrees change-of-generators core of Lazard's
    displayed family.

    This file deliberately works in an arbitrary commutative ring and does
    not mention a monomial order.  It separates three facts which are easy to
    conflate in a fixed quintic expansion:

    - the elementary/complete-homogeneous convolution;
    - equality of the literal printed alternating-[e] expression with the
      triangular Vieta combination;
    - equality of the two finitely generated ideals.

    [printed_cancellation] below is the precise interface needed from a
    concrete complete-homogeneous implementation.  MathComp multinomials
    currently expose [mesym] and Vieta, but not a complete-homogeneous
    multinomial or a formal-power-series inverse theorem.  Consequently this
    file proves the generic algebra after that single interface and, in the
    first section, proves the usual elementary/complete recurrence implies
    the corresponding cancellation.  For a prefix one must additionally
    split the full elementary product into prefix and suffix products and use
    that the suffix of length [k] has zero coefficient in degree [k+1].  It is
    exactly this [mesym]/prefix-[hsymm] product bridge, rather than any ideal
    algebra below, that remains to be supplied for MathComp multinomials. *)
Module PolynomialFormulasLazardDisplayedGroebnerGeneralIdeal.

Import GRing.Theory.
Local Open Scope ring_scope.

(** * The elementary/complete-homogeneous recurrence *)

Section ElementaryCompleteRecurrence.

Variable A : comRingType.

(** Coefficient [r] of the product of the signed elementary series and
    the complete-homogeneous series. *)
Definition elementary_complete_convolution
    (elementary complete : nat -> A) (r : nat) : A :=
  \sum_(j < r.+1)
    (((-1 : A) ^+ j) * elementary j) * complete ((r - j)%N).

(** The standard inverse-series recurrence

    [h_(r+1) = sum_(j=0)^r (-1)^j e_(j+1) h_(r-j)].

    This is a convenient standalone specification of complete homogeneous
    coefficients when a library has elementary coefficients but no [hsymm]. *)
Definition complete_homogeneous_recurrence
    (elementary complete : nat -> A) : Prop :=
  elementary 0 = 1 /\
  complete 0 = 1 /\
  forall r,
    complete r.+1 =
      \sum_(j < r.+1)
        (((-1 : A) ^+ j) * elementary j.+1) * complete ((r - j)%N).

(** The inverse-series recurrence honestly proves every positive-degree
    elementary/complete cancellation; there is no division and hence no
    characteristic assumption. *)
Theorem complete_homogeneous_recurrence_cancellation
    (elementary complete : nat -> A) :
  complete_homogeneous_recurrence elementary complete ->
  forall r,
    elementary_complete_convolution elementary complete r.+1 = 0.
Proof.
move=> [elementary0 [complete0 hrec]] r.
rewrite /elementary_complete_convolution big_ord_recl /=.
rewrite elementary0 expr0 mul1r subn0.
under eq_bigr do rewrite /bump /= subSS exprS.
rewrite hrec mul1r.
rewrite -big_split /=.
apply: big1 => j _.
by rewrite mulN1r !mulNr addrN.
Qed.

End ElementaryCompleteRecurrence.

(** * Literal displayed family and its Vieta-combination form *)

Section DisplayedFamily.

Variables (A : comRingType) (n : nat).

(** Expose MathComp's packed commutative ring to the standard reflective
    [ring] tactic used by the two small change-of-generators calculations. *)
Let general_ideal_ring_carrier := GRing.PzSemiRing.sort A.
Local Definition general_ideal_ring_zero : general_ideal_ring_carrier := 0.
Local Definition general_ideal_ring_one : general_ideal_ring_carrier := 1.
Local Definition general_ideal_ring_add :
    general_ideal_ring_carrier -> general_ideal_ring_carrier ->
      general_ideal_ring_carrier := @GRing.add A.
Local Definition general_ideal_ring_mul :
    general_ideal_ring_carrier -> general_ideal_ring_carrier ->
      general_ideal_ring_carrier := @GRing.mul A.
Local Definition general_ideal_ring_sub :
    general_ideal_ring_carrier -> general_ideal_ring_carrier ->
      general_ideal_ring_carrier := fun x y => x - y.
Local Definition general_ideal_ring_opp :
    general_ideal_ring_carrier -> general_ideal_ring_carrier := @GRing.opp A.
Local Definition general_ideal_ring_eq :
    general_ideal_ring_carrier -> general_ideal_ring_carrier -> Prop :=
  @eq general_ideal_ring_carrier.

Lemma general_ideal_ring_theory :
  @ring_theory general_ideal_ring_carrier
    general_ideal_ring_zero general_ideal_ring_one general_ideal_ring_add
    general_ideal_ring_mul general_ideal_ring_sub general_ideal_ring_opp
    general_ideal_ring_eq.
Proof.
constructor; unfold general_ideal_ring_zero, general_ideal_ring_one,
  general_ideal_ring_add, general_ideal_ring_mul, general_ideal_ring_sub,
  general_ideal_ring_opp, general_ideal_ring_eq; intros.
- exact: add0r.
- exact: addrC.
- exact: addrA.
- exact: mul1r.
- exact: mulrC.
- exact: mulrA.
- exact: mulrDl.
- reflexivity.
- exact: addrN.
Qed.

Add Ring lazard_displayed_general_ideal_ring : general_ideal_ring_theory.

Lemma general_ideal_ring_addE x y :
  x + y = general_ideal_ring_add x y.
Proof. reflexivity. Qed.
Lemma general_ideal_ring_mulE x y :
  x * y = general_ideal_ring_mul x y.
Proof. reflexivity. Qed.
Lemma general_ideal_ring_subE x y :
  x - y = general_ideal_ring_sub x y.
Proof. reflexivity. Qed.
Lemma general_ideal_ring_oppE x :
  - x = general_ideal_ring_opp x.
Proof. reflexivity. Qed.
Lemma general_ideal_ring_zeroE : (0 : A) = general_ideal_ring_zero.
Proof. reflexivity. Qed.
Lemma general_ideal_ring_oneE : (1 : A) = general_ideal_ring_one.
Proof. reflexivity. Qed.

Opaque general_ideal_ring_zero general_ideal_ring_one general_ideal_ring_add
  general_ideal_ring_mul general_ideal_ring_sub general_ideal_ring_opp
  general_ideal_ring_eq.

Ltac finish_general_ideal_ring :=
  repeat first
    [ rewrite general_ideal_ring_addE | rewrite general_ideal_ring_mulE
    | rewrite general_ideal_ring_subE | rewrite general_ideal_ring_oppE
    | rewrite general_ideal_ring_zeroE | rewrite general_ideal_ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (general_ideal_ring_eq lhs rhs)
  end;
  ring.

(** [sigma r] is the degree-[r] elementary symmetric coefficient in all
    roots; [formal_e r] is the independent formal coefficient with
    [formal_e 0 = 1]. *)
Variables (sigma formal_e : nat -> A).

(** [prefix_h k r] is the degree-[r] complete homogeneous coefficient in
    the first [n-k] roots. *)
Variable prefix_h : 'I_n -> nat -> A.

Hypothesis sigma0 : sigma 0 = 1.
Hypothesis formal_e0 : formal_e 0 = 1.
Hypothesis prefix_h0 : forall k, prefix_h k 0 = 1.

(** The precise elementary/complete statement supplied by a concrete
    prefix implementation: in degree [k+1], the complementary suffix has
    only [k] variables, so its coefficient is zero. *)
Hypothesis printed_cancellation : forall k : 'I_n,
  elementary_complete_convolution sigma (prefix_h k) k.+1 = 0.

(** Embed a relation number [j <= k] in the full family. *)
Definition degree_index (k : 'I_n) (j : 'I_k.+1) : 'I_n :=
  widen_ord (ltn_ord k) j.

Arguments degree_index k j : clear implicits.

Lemma degree_index_val (k : 'I_n) (j : 'I_k.+1) :
  (degree_index k j : nat) = (j : nat).
Proof. exact: erefl. Qed.

Lemma degree_index_last (k : 'I_n) :
  degree_index k ord_max = k.
Proof. by apply/val_inj. Qed.

Definition vieta_relation (i : 'I_n) : A :=
  sigma i.+1 - formal_e i.+1.

(** Uniform triangular Vieta-combination form.  The index [k] is the root
    degree minus one, matching the Lean file. *)
Definition displayed_J (k : 'I_n) : A :=
  \sum_(j < k.+1)
    (((-1 : A) ^+ j) * prefix_h k ((k - j)%N)) *
      vieta_relation (degree_index k j).

(** The literal formula printed in Lazard:

    [sum_(r=0)^(k+1) (-1)^r e_r h_(k+1-r)], including [e_0 = 1]. *)
Definition printed_displayed_J (k : 'I_n) : A :=
  \sum_(r < k.+2)
    (((-1 : A) ^+ r) * formal_e r) *
      prefix_h k ((k.+1 - r)%N).

Definition sigma_tail (k : 'I_n) (j : 'I_k.+1) : A :=
  (((-1 : A) ^+ j.+1) * sigma j.+1) * prefix_h k ((k - j)%N).

Arguments sigma_tail k j : clear implicits.

Definition formal_e_tail (k : 'I_n) (j : 'I_k.+1) : A :=
  (((-1 : A) ^+ j.+1) * formal_e j.+1) * prefix_h k ((k - j)%N).

Arguments formal_e_tail k j : clear implicits.

Definition relation_term (k : 'I_n) (j : 'I_k.+1) : A :=
  (((-1 : A) ^+ j) * prefix_h k ((k - j)%N)) *
    vieta_relation (degree_index k j).

Arguments relation_term k j : clear implicits.

Lemma printed_displayed_J_split (k : 'I_n) :
  printed_displayed_J k =
    prefix_h k k.+1 + \sum_(j < k.+1) formal_e_tail k j.
Proof.
rewrite /printed_displayed_J big_ord_recl /=.
rewrite formal_e0 expr0 !mul1r subn0.
congr (_ + _); apply: eq_bigr => j _.
Qed.

Lemma printed_cancellation_split (k : 'I_n) :
  prefix_h k k.+1 + \sum_(j < k.+1) sigma_tail k j = 0.
Proof.
move: (printed_cancellation k).
rewrite /elementary_complete_convolution big_ord_recl /=.
rewrite sigma0 expr0 !mul1r subn0.
congr (_ + _ = 0); apply: eq_bigr => j _.
Qed.

Lemma tails_change_of_generators (k : 'I_n) :
  \sum_(j < k.+1) formal_e_tail k j =
    \sum_(j < k.+1) sigma_tail k j +
      \sum_(j < k.+1) relation_term k j.
Proof.
rewrite -big_split /=.
apply: eq_bigr => j _.
rewrite /formal_e_tail /sigma_tail /relation_term
  /vieta_relation degree_index_val exprS.
finish_general_ideal_ring.
Qed.

(** The literal printed polynomial is exactly the Vieta-combination
    polynomial. *)
Theorem printed_displayed_J_eq_displayed_J (k : 'I_n) :
  printed_displayed_J k = displayed_J k.
Proof.
rewrite printed_displayed_J_split tails_change_of_generators.
rewrite addrA printed_cancellation_split add0r /displayed_J.
apply: eq_bigr => j _.
exact: erefl.
Qed.

(** * Generated ideals without a proper-ideal side condition *)

Definition generated_by (f : 'I_n -> A) (p : A) : Prop :=
  exists c : 'I_n -> A, p = \sum_i c i * f i.

Lemma generated_by0 f : generated_by f 0.
Proof.
exists (fun _ => 0).
by rewrite big1 // => i _; rewrite mul0r.
Qed.

Lemma generated_byD f p q :
  generated_by f p -> generated_by f q -> generated_by f (p + q).
Proof.
move=> [a ->] [b ->].
exists (fun i => a i + b i).
rewrite -big_split /=.
apply: eq_bigr => i _.
finish_general_ideal_ring.
Qed.

Lemma generated_byN f p : generated_by f p -> generated_by f (- p).
Proof.
move=> [a ->].
exists (fun i => - a i).
rewrite -sumrN.
apply: eq_bigr => i _.
by rewrite mulNr.
Qed.

Lemma generated_byB f p q :
  generated_by f p -> generated_by f q -> generated_by f (p - q).
Proof.
move=> hp hq.
exact: generated_byD hp (generated_byN hq).
Qed.

Lemma generated_by_mul_left f a p :
  generated_by f p -> generated_by f (a * p).
Proof.
move=> [c ->].
exists (fun i => a * c i).
rewrite mulr_sumr.
apply: eq_bigr => i _.
by rewrite mulrA.
Qed.

Lemma generated_by_generator f (i : 'I_n) : generated_by f (f i).
Proof.
exists (fun j => (j == i)%:R).
rewrite (bigD1 i) //= eqxx mul1r.
rewrite big1 ?addr0 // => j hji.
by rewrite (negbTE hji) mul0r.
Qed.

Lemma generated_by_sum f (T : finType) (p : T -> A) :
  (forall i, generated_by f (p i)) ->
  generated_by f (\sum_i p i).
Proof.
move=> hp.
elim/big_ind: _ => [|a b ha hb|i _].
- exact: generated_by0.
- exact: generated_byD ha hb.
- exact: hp i.
Qed.

Lemma generated_by_change (f g : 'I_n -> A)
    (hfg : forall i, generated_by g (f i)) p :
  generated_by f p -> generated_by g p.
Proof.
move=> [c ->].
apply: generated_by_sum => i.
exact: generated_by_mul_left (hfg i).
Qed.

Lemma displayed_J_generated_by_vieta (k : 'I_n) :
  generated_by vieta_relation (displayed_J k).
Proof.
rewrite /displayed_J.
apply: generated_by_sum => j.
exact: generated_by_mul_left
  (generated_by_generator vieta_relation (degree_index k j)).
Qed.

(** Split off the unit diagonal term of the triangular combination. *)
Lemma displayed_J_split_last (k : 'I_n) :
  displayed_J k =
    \sum_(j < k)
      relation_term k (widen_ord (leqnSn k) j) +
    ((-1 : A) ^+ k) * vieta_relation k.
Proof.
rewrite /displayed_J big_ord_recr /= /relation_term.
rewrite degree_index_last subnn prefix_h0 mulr1.
apply: congr2; last exact: erefl.
apply: eq_bigr => j _.
exact: erefl.
Qed.

Lemma sign_square (k : nat) :
  ((-1 : A) ^+ k) * ((-1 : A) ^+ k) = 1.
Proof. by rewrite -exprMn mulrNN mul1r expr1n. Qed.

(** One triangular inversion step, assuming all earlier Vieta relations are
    already generated by the displayed family. *)
Lemma vieta_relation_generated_step (k : 'I_n)
    (hprevious : forall j : 'I_k,
      generated_by displayed_J
        (vieta_relation
          (degree_index k (widen_ord (leqnSn k) j)))) :
  generated_by displayed_J (vieta_relation k).
Proof.
have hrest : generated_by displayed_J
    (\sum_(j < k) relation_term k (widen_ord (leqnSn k) j)).
  apply: generated_by_sum => j.
  exact: generated_by_mul_left (hprevious j).
have hJ := generated_by_generator displayed_J k.
rewrite displayed_J_split_last in hJ.
have hsigned := generated_byB hJ hrest.
have hsigned' : generated_by displayed_J
    (((-1 : A) ^+ k) * vieta_relation k).
  have hcancel :
      (\sum_(j < k)
          relation_term k (widen_ord (leqnSn k) j) +
        ((-1 : A) ^+ k) * vieta_relation k -
        \sum_(j < k)
          relation_term k (widen_ord (leqnSn k) j)) =
      ((-1 : A) ^+ k) * vieta_relation k.
    finish_general_ideal_ring.
  by rewrite -hcancel.
have hunsigned := generated_by_mul_left ((-1 : A) ^+ k) hsigned'.
move: hunsigned.
by rewrite mulrA sign_square mul1r.
Qed.

(** Triangular induction, valid for every finite [n]. *)
Theorem vieta_relation_generated_by_displayed (i : 'I_n) :
  generated_by displayed_J (vieta_relation i).
Proof.
case: i => k hk.
elim: k {-2} k (leqnn k) hk => [|b ih] k.
- rewrite leqn0 => /eqP -> hk.
  apply: vieta_relation_generated_step => j.
  by move: (ltn_ord j); rewrite ltn0.
- rewrite leq_eqVlt ltnS => /orP [/eqP ->|hkb] hk.
  + apply: vieta_relation_generated_step => j.
    have hjn : (j < n)%N := ltn_trans (ltn_ord j) hk.
    have hjb : (j <= b)%N by rewrite -ltnS; exact: ltn_ord j.
    pose ji : 'I_n := Ordinal hjn.
    have hprev := ih (j : nat) hjb hjn.
    have hindex :
        degree_index (Ordinal hk)
          (widen_ord (leqnSn b.+1) j) = ji by
      apply/val_inj.
    by rewrite hindex; exact: hprev.
  + exact: ih k hkb hk.
Qed.

(** Equality of the generated ideals, expressed extensionally as equality
    of membership predicates. *)
Theorem displayed_generated_ideal_eq_vieta p :
  generated_by displayed_J p <-> generated_by vieta_relation p.
Proof.
split.
- exact: (@generated_by_change displayed_J vieta_relation
    displayed_J_generated_by_vieta p).
- exact: (@generated_by_change vieta_relation displayed_J
    vieta_relation_generated_by_displayed p).
Qed.

(** The same theorem for the literal printed family. *)
Theorem printed_displayed_generated_ideal_eq_vieta p :
  generated_by printed_displayed_J p <-> generated_by vieta_relation p.
Proof.
split.
- apply: generated_by_change => i.
  rewrite printed_displayed_J_eq_displayed_J.
  exact: displayed_J_generated_by_vieta.
- apply: generated_by_change => i.
  have hi := vieta_relation_generated_by_displayed i.
  move: hi.
  apply: generated_by_change => j.
  rewrite -printed_displayed_J_eq_displayed_J.
  exact: generated_by_generator.
Qed.

End DisplayedFamily.

End PolynomialFormulasLazardDisplayedGroebnerGeneralIdeal.
