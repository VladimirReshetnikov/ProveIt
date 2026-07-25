From Coq Require Import Morphisms RelationClasses Setoid.

From SyntheticComputability Require Import Dec DecidabilityFacts partial principles.
From SyntheticComputability.TuringReducibility Require Import OracleComputability.

(** A constructive, quotient-free presentation of the Turing degrees.

    Predicates are representatives.  [turing_equiv] is the setoid equality and
    [turing_reducible] is its well-defined order.  This avoids postulating a
    quotient of predicates by an undecidable equivalence relation. *)

Definition nat_set := nat -> Prop.

Section TuringDegrees.
  Context {Part : partiality}.

  Definition turing_reducible (A B : nat_set) : Prop := A ⪯ᴛ B.

  Definition turing_equiv (A B : nat_set) : Prop :=
    turing_reducible A B /\ turing_reducible B A.

  Definition turing_strict (A B : nat_set) : Prop :=
    turing_reducible A B /\ ~ turing_reducible B A.

  Definition turing_incomparable (A B : nat_set) : Prop :=
    ~ turing_reducible A B /\ ~ turing_reducible B A.

  Definition is_upper_bound (A B U : nat_set) : Prop :=
    turing_reducible A U /\ turing_reducible B U.

  Definition is_least_upper_bound (A B U : nat_set) : Prop :=
    is_upper_bound A B U /\
    forall V, is_upper_bound A B V -> turing_reducible U V.

  Definition is_least_degree (Z : nat_set) : Prop :=
    forall A, turing_reducible Z A.

  Global Instance turing_reducible_PreOrder : PreOrder turing_reducible.
  Proof.
    split.
    - intros A. apply Turing_refl.
    - intros A B C HAB HBC.
      eapply Turing_transitive; eauto.
  Qed.

  Global Instance turing_equiv_Equivalence : Equivalence turing_equiv.
  Proof.
    split.
    - intros A. split; reflexivity.
    - intros A B [HAB HBA]. now split.
    - intros A B C [HAB HBA] [HBC HCB].
      split; etransitivity; eauto.
  Qed.

  Global Instance turing_degree_PartialOrder :
    PartialOrder turing_equiv turing_reducible.
  Proof.
    red. intros A B. split; intro H; exact H.
  Qed.

  Global Instance turing_reducible_Proper :
    Proper (turing_equiv ==> turing_equiv ==> iff) turing_reducible.
  Proof.
    intros A A' [HAA' HA'A] B B' [HBB' HB'B]. split; intro H.
    - transitivity A; [exact HA'A|]. transitivity B; assumption.
    - transitivity A'; [exact HAA'|]. transitivity B'; assumption.
  Qed.

  Global Instance turing_strict_Proper :
    Proper (turing_equiv ==> turing_equiv ==> iff) turing_strict.
  Proof.
    intros A A' HA B B' HB.
    unfold turing_strict.
    now setoid_rewrite HA; setoid_rewrite HB.
  Qed.

  Global Instance turing_incomparable_Proper :
    Proper (turing_equiv ==> turing_equiv ==> iff) turing_incomparable.
  Proof.
    intros A A' HA B B' HB.
    unfold turing_incomparable.
    now setoid_rewrite HA; setoid_rewrite HB.
  Qed.

  Lemma extensionally_equal_turing_reducible (A B : nat_set) :
    (forall x, A x <-> B x) -> turing_reducible A B.
  Proof.
    intros Hext.
    exists (fun R => R). split.
    - apply computable_id.
    - intros x []; cbn [char_rel].
      + apply Hext.
      + specialize (Hext x). tauto.
  Qed.

  Lemma extensionally_equal_turing_equiv (A B : nat_set) :
    (forall x, A x <-> B x) -> turing_equiv A B.
  Proof.
    intros Hext. split; apply extensionally_equal_turing_reducible;
      firstorder.
  Qed.

  Definition empty_set : nat_set := fun _ => False.

  Lemma empty_set_least : is_least_degree empty_set.
  Proof.
    intros A.
    exists (fun (_ : Rel nat bool) (_ : nat) b => false = b). split.
    - apply computable_function.
    - intros x []; cbn [char_rel empty_set].
      + split; intro H; [contradiction|discriminate H].
      + split; [intros _; reflexivity|tauto].
  Qed.

  Lemma decidable_empty_set : decidable empty_set.
  Proof.
    exists (fun _ => false). intros x. cbn [reflects empty_set].
    split; intro H; [contradiction|discriminate H].
  Qed.

  Lemma decidable_turing_reducible_empty (A : nat_set) :
    decidable A -> turing_reducible A empty_set.
  Proof.
    intros [d Hd].
    exists (fun (_ : Rel nat bool) x b => d x = b). split.
    - apply computable_function.
    - intros x b. specialize (Hd x).
      unfold reflects in Hd. destruct b, (d x); cbn [char_rel] in *;
        firstorder congruence.
  Qed.

  Lemma decidable_turing_equiv_empty (A : nat_set) :
    decidable A -> turing_equiv A empty_set.
  Proof.
    intro HA. split.
    - now apply decidable_turing_reducible_empty.
    - apply empty_set_least.
  Qed.

  Lemma all_decidable_sets_same_degree (A B : nat_set) :
    decidable A -> decidable B -> turing_equiv A B.
  Proof.
    intros HA HB. split.
    - transitivity empty_set.
      + now apply decidable_turing_reducible_empty.
      + apply empty_set_least.
    - transitivity empty_set.
      + now apply decidable_turing_reducible_empty.
      + apply empty_set_least.
  Qed.

  (** The converse uses exactly Markov's principle, matching the constructive
      boundary identified by the oracle-computability library. *)
  Lemma zero_degree_decidable (mp : MP) (A : nat_set) :
    turing_equiv A empty_set -> decidable A.
  Proof.
    intros [HA _].
    eapply transport_decidable; eauto using decidable_empty_set.
  Qed.

  Theorem zero_degree_iff_decidable (mp : MP) (A : nat_set) :
    turing_equiv A empty_set <-> decidable A.
  Proof.
    split.
    - apply zero_degree_decidable; assumption.
    - apply decidable_turing_equiv_empty.
  Qed.
End TuringDegrees.
