From Coq Require Import Lia Morphisms.

From SyntheticComputability Require Import partial reductions.
From SyntheticComputability.TuringReducibility Require Import OracleComputability.
From TuringDegrees Require Import Core.

(** The Wikipedia convention codes the disjoint union by even and odd natural
    numbers.  The upstream oracle library uses the actual sum type.  The
    following explicit bijection connects the two presentations. *)

Fixpoint nat_sum_decode (n : nat) : nat + nat :=
  match n with
  | 0 => inl 0
  | 1 => inr 0
  | S (S k) =>
      match nat_sum_decode k with
      | inl i => inl (S i)
      | inr i => inr (S i)
      end
  end.

Definition nat_sum_encode (s : nat + nat) : nat :=
  match s with
  | inl i => i * 2
  | inr i => i * 2 + 1
  end.

Lemma nat_sum_decode_even_right n : nat_sum_decode (n * 2) = inl n.
Proof.
  induction n as [|n IH]; cbn; now rewrite ?IH.
Qed.

Lemma nat_sum_decode_odd_right n : nat_sum_decode (n * 2 + 1) = inr n.
Proof.
  induction n as [|n IH]; cbn; now rewrite ?IH.
Qed.

Lemma nat_sum_decode_even n : nat_sum_decode (2 * n) = inl n.
Proof. replace (2 * n) with (n * 2) by lia. apply nat_sum_decode_even_right. Qed.

Lemma nat_sum_decode_odd n : nat_sum_decode (2 * n + 1) = inr n.
Proof.
  replace (2 * n + 1) with (n * 2 + 1) by lia.
  apply nat_sum_decode_odd_right.
Qed.

Lemma nat_sum_decode_encode s : nat_sum_decode (nat_sum_encode s) = s.
Proof.
  destruct s as [n|n]; cbn [nat_sum_encode].
  - apply nat_sum_decode_even_right.
  - apply nat_sum_decode_odd_right.
Qed.

Lemma nat_sum_encode_decode n : nat_sum_encode (nat_sum_decode n) = n.
Proof.
  revert n. fix IH 1. intros [|[|n]]; cbn [nat_sum_encode].
  - reflexivity.
  - reflexivity.
  - cbn [nat_sum_decode].
    destruct (nat_sum_decode n) eqn:E; cbn [nat_sum_encode].
    + pose proof (IH n) as H. rewrite E in H.
      cbn [nat_sum_encode] in H. lia.
    + pose proof (IH n) as H. rewrite E in H.
      cbn [nat_sum_encode] in H. lia.
Qed.

Section TuringJoin.
  Context {Part : partiality}.

  Definition turing_join (A B : nat_set) : nat_set :=
    fun n => join A B (nat_sum_decode n).

  Lemma turing_join_even (A B : nat_set) n :
    turing_join A B (2 * n) <-> A n.
  Proof.
    unfold turing_join. now rewrite nat_sum_decode_even.
  Qed.

  Lemma turing_join_odd (A B : nat_set) n :
    turing_join A B (2 * n + 1) <-> B n.
  Proof.
    unfold turing_join. now rewrite nat_sum_decode_odd.
  Qed.

  (** Exact even/odd membership formula from the Turing-degree page. *)
  Theorem turing_join_spec (A B : nat_set) k :
    turing_join A B k <->
      (exists n, k = 2 * n /\ A n) \/
      (exists n, k = 2 * n + 1 /\ B n).
  Proof.
    unfold turing_join.
    destruct (nat_sum_decode k) as [n|n] eqn:E; cbn.
    - split.
      + intro HA. left. exists n. split; [|assumption].
        pose proof (nat_sum_encode_decode k) as H.
        rewrite E in H. cbn [nat_sum_encode] in H. lia.
      + intros [[m [Hk Hm]] | [m [Hk Hm]]].
        * pose proof (nat_sum_encode_decode k) as Hencode.
          rewrite E in Hencode. cbn [nat_sum_encode] in Hencode.
          assert (m = n) by lia. subst. exact Hm.
        * pose proof (nat_sum_encode_decode k) as Hencode.
          rewrite E in Hencode. cbn [nat_sum_encode] in Hencode. lia.
    - split.
      + intro HB. right. exists n. split; [|assumption].
        pose proof (nat_sum_encode_decode k) as H.
        rewrite E in H. cbn [nat_sum_encode] in H. lia.
      + intros [[m [Hk Hm]] | [m [Hk Hm]]].
        * pose proof (nat_sum_encode_decode k) as Hencode.
          rewrite E in Hencode. cbn [nat_sum_encode] in Hencode. lia.
        * pose proof (nat_sum_encode_decode k) as Hencode.
          rewrite E in Hencode. cbn [nat_sum_encode] in Hencode.
          assert (m = n) by lia. subst. exact Hm.
  Qed.

  Lemma turing_join_red_sum_join (A B : nat_set) :
    turing_join A B ⪯ₘ join A B.
  Proof.
    exists nat_sum_decode. intros n. reflexivity.
  Qed.

  Lemma sum_join_red_turing_join (A B : nat_set) :
    join A B ⪯ₘ turing_join A B.
  Proof.
    exists nat_sum_encode. intros [n|n]; cbn [nat_sum_encode].
    - replace (n * 2) with (2 * n) by lia.
      change (A n <-> turing_join A B (2 * n)).
      symmetry. apply turing_join_even.
    - replace (n * 2 + 1) with (2 * n + 1) by lia.
      change (B n <-> turing_join A B (2 * n + 1)).
      symmetry. apply turing_join_odd.
  Qed.

  Lemma turing_join_equiv_sum_join (A B : nat_set) :
    (turing_join A B ⪯ᴛ join A B) /\
    (join A B ⪯ᴛ turing_join A B).
  Proof.
    split; apply red_m_impl_red_T.
    - apply turing_join_red_sum_join.
    - apply sum_join_red_turing_join.
  Qed.

  Lemma turing_join_left (A B : nat_set) :
    turing_reducible A (turing_join A B).
  Proof.
    destruct (Turing_upper_semi_lattice A B (turing_join A B))
      as [HA [_ _]].
    eapply Turing_transitive; [exact HA|].
    apply red_m_impl_red_T, sum_join_red_turing_join.
  Qed.

  Lemma turing_join_right (A B : nat_set) :
    turing_reducible B (turing_join A B).
  Proof.
    destruct (Turing_upper_semi_lattice A B (turing_join A B))
      as [_ [HB _]].
    eapply Turing_transitive; [exact HB|].
    apply red_m_impl_red_T, sum_join_red_turing_join.
  Qed.

  Lemma turing_join_least (A B U : nat_set) :
    turing_reducible A U ->
    turing_reducible B U ->
    turing_reducible (turing_join A B) U.
  Proof.
    intros HA HB.
    eapply Turing_transitive.
    - apply red_m_impl_red_T, turing_join_red_sum_join.
    - destruct (Turing_upper_semi_lattice A B U) as [_ [_ Hlub]].
      now apply Hlub.
  Qed.

  Theorem turing_join_is_lub (A B : nat_set) :
    is_least_upper_bound A B (turing_join A B).
  Proof.
    split.
    - split; [apply turing_join_left|apply turing_join_right].
    - intros U [HA HB]. now apply turing_join_least.
  Qed.

  Global Instance turing_join_Proper :
    Proper (turing_equiv ==> turing_equiv ==> turing_equiv) turing_join.
  Proof.
    intros A A' [HAA' HA'A] B B' [HBB' HB'B]. split;
      apply turing_join_least.
    - transitivity A'; [exact HAA'|apply turing_join_left].
    - transitivity B'; [exact HBB'|apply turing_join_right].
    - transitivity A; [exact HA'A|apply turing_join_left].
    - transitivity B; [exact HB'B|apply turing_join_right].
  Qed.

  Theorem turing_join_commutative (A B : nat_set) :
    turing_equiv (turing_join A B) (turing_join B A).
  Proof.
    split; apply turing_join_least.
    - apply turing_join_right.
    - apply turing_join_left.
    - apply turing_join_right.
    - apply turing_join_left.
  Qed.

  Theorem turing_join_idempotent (A : nat_set) :
    turing_equiv (turing_join A A) A.
  Proof.
    split.
    - apply turing_join_least; reflexivity.
    - apply turing_join_left.
  Qed.

  Theorem turing_join_zero (A : nat_set) :
    turing_equiv (turing_join A empty_set) A.
  Proof.
    split.
    - apply turing_join_least; [reflexivity|apply empty_set_least].
    - apply turing_join_left.
  Qed.

  Theorem turing_join_associative (A B C : nat_set) :
    turing_equiv (turing_join (turing_join A B) C)
                  (turing_join A (turing_join B C)).
  Proof.
    split.
    - apply turing_join_least.
      + apply turing_join_least.
        * apply turing_join_left.
        * transitivity (turing_join B C);
            [apply turing_join_left|apply turing_join_right].
      + transitivity (turing_join B C);
          [apply turing_join_right|apply turing_join_right].
    - apply turing_join_least.
      + transitivity (turing_join A B);
          [apply turing_join_left|apply turing_join_left].
      + apply turing_join_least.
        * transitivity (turing_join A B);
            [apply turing_join_right|apply turing_join_left].
        * apply turing_join_right.
  Qed.
End TuringJoin.
