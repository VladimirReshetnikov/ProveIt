(** Computability obstructions and independent arithmetic instances.

    Foundation obtains first incompleteness from a recursively enumerable,
    nonrecursive predicate and ultimately instantiates it with the halting
    problem.  The reusable proof only needs a representation of the positive
    predicate, semidecidability of proofs of the negative instances, and the
    fact that the predicate's complement is not semidecidable.  We expose
    exactly that weaker core here.

    The final unconditional halting specialization remains outside this
    module: it requires arithmetic certificates for proof recognition,
    numeral substitution, and negation, plus a certified bridge to a concrete
    undecidable machine model.  None of those services is postulated. *)

From Stdlib Require Import Logic.Classical_Prop Vectors.Fin.
From FoundationModal Require Import GenericEntailment.
From Foundation.Vorspiel Require Import Computability.
From Foundation.Syntax.Predicate Require Import Language.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Calculus.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Hierarchy Misc.
From Foundation.FirstOrder.Arithmetic.Definability Require Import Absoluteness.
From Foundation.FirstOrder.Arithmetic.R0 Require Import
  Basic Semidecidability Representation RepresentationCompleteness.
From Foundation.FirstOrder.Incompleteness Require Import RosserProvability.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** Semidecidability is invariant under pointwise logical equivalence. *)
Lemma semidecidable_iff_transport : forall A (p q : A -> Prop),
  semidecidable p ->
  (forall a, p a <-> q a) ->
  semidecidable q.
Proof.
  intros A p q [recognize Hrecognize] Hequiv.
  exists recognize. intro a.
  transitivity (p a); [symmetry; apply Hequiv | apply Hrecognize].
Qed.

(** Decode an arbitrary natural code, rejecting codes outside the image. *)
Definition decoded_predicate {A}
    (E : encoding A) (P : A -> Prop) (code : nat) : Prop :=
  match decode E code with
  | Some a => P a
  | None => False
  end.

Lemma decoded_predicate_encode_iff : forall A (E : encoding A)
    (P : A -> Prop) a,
  decoded_predicate E P (encode E a) <-> P a.
Proof.
  intros A E P a. unfold decoded_predicate.
  rewrite (decode_encode E a). reflexivity.
Qed.

(** Source theorem [REPred.iff_decoded_pred], generalized from primitive
    recursive encodings to the exact retraction data used by this port. *)
Theorem semidecidable_decoded_predicate_iff : forall A
    (E : encoding A) (P : A -> Prop),
  semidecidable P <->
  semidecidable (decoded_predicate E P).
Proof.
  intros A E P. split.
  - intros [recognize Hrecognize].
    exists (fun code fuel =>
      match decode E code with
      | Some a => recognize a fuel
      | None => false
      end).
    intro code. unfold decoded_predicate.
    destruct (decode E code) as [a|] eqn:Hdecode; simpl.
    + apply Hrecognize.
    + split; [contradiction | intros [fuel Hfuel]; discriminate].
  - intro Hdecoded.
    apply (@semidecidable_iff_transport A
      (fun a => decoded_predicate E P (encode E a)) P).
    + apply (@semidecidable_comp A nat (encode E)
        (decoded_predicate E P)).
      exact Hdecoded.
    + apply decoded_predicate_encode_iff.
Qed.

(** Forward half of [ComputablePred.iff_decoded_pred].  This is a genuine
    executable decision procedure because [decode] is data. *)
Lemma decidable_predicate_decoded : forall A (E : encoding A)
    (P : A -> Prop),
  decidable_predicate P ->
  decidable_predicate (decoded_predicate E P).
Proof.
  intros A E P Hdec code. unfold decoded_predicate.
  destruct (decode E code) as [a|] eqn:Hdecode.
  - exact (Hdec a).
  - right. tauto.
Qed.

(** Reverse half, by restricting the decoded predicate to canonical codes. *)
Lemma decidable_predicate_of_decoded : forall A (E : encoding A)
    (P : A -> Prop),
  decidable_predicate (decoded_predicate E P) ->
  decidable_predicate P.
Proof.
  intros A E P Hdec a.
  specialize (Hdec (encode E a)).
  unfold decoded_predicate in Hdec.
  rewrite (decode_encode E a) in Hdec. exact Hdec.
Qed.

(** The representation-independent core of Foundation's halting argument.
    It is generalized from first-order syntax to any entailment and negation
    operation.  Classical logic is used only to extract one failed instance
    from the negation of uniform completeness. *)
Theorem independent_instance_of_not_cosemidecidable : forall
    (S F : Type) (E : generic_entailment S F) (neg : F -> F) (s : S)
    (P : nat -> Prop) (phi : nat -> F),
  (forall n, P n <-> generic_provable E s (phi n)) ->
  (forall n,
    generic_provable E s (phi n) ->
    generic_provable E s (neg (phi n)) -> False) ->
  semidecidable
    (fun n => generic_provable E s (neg (phi n))) ->
  ~ semidecidable (fun n => ~ P n) ->
  exists n, generic_independent E neg s (phi n).
Proof.
  intros S F E neg s P phi Hrep Hnot_both Hnegative Hnot_co.
  apply NNPP. intro Hno_independent.
  apply Hnot_co.
  apply (@semidecidable_iff_transport nat
    (fun n => generic_provable E s (neg (phi n)))
    (fun n => ~ P n)); [exact Hnegative |].
  intro n. split.
  - intros Hneg Hpos.
    exact (Hnot_both n (proj1 (Hrep n) Hpos) Hneg).
  - intro Hnot_P.
    assert (Hnot_pos : ~ generic_provable E s (phi n)).
    { intro Hpos. apply Hnot_P. exact (proj2 (Hrep n) Hpos). }
    apply NNPP. intro Hnot_neg.
    apply Hno_independent. exists n. split; assumption.
Qed.

Corollary incomplete_of_not_cosemidecidable : forall
    (S F : Type) (E : generic_entailment S F) (neg : F -> F) (s : S)
    (P : nat -> Prop) (phi : nat -> F),
  (forall n, P n <-> generic_provable E s (phi n)) ->
  (forall n,
    generic_provable E s (phi n) ->
    generic_provable E s (neg (phi n)) -> False) ->
  semidecidable
    (fun n => generic_provable E s (neg (phi n))) ->
  ~ semidecidable (fun n => ~ P n) ->
  generic_incomplete E neg s.
Proof.
  intros S F E neg s P phi Hrep Hnot_both Hnegative Hnot_co.
  constructor.
  destruct (@independent_instance_of_not_cosemidecidable
    S F E neg s P phi Hrep Hnot_both Hnegative Hnot_co)
    as [n Hn].
  now exists (phi n).
Qed.

(** The one-entry environment used to instantiate unary arithmetic formulas. *)
Definition halting_unary_vector (a : nat) : Fin.t 1 -> nat :=
  fun _ => a.

Lemma halting_unary_vector_f1 : forall a,
  halting_unary_vector a Fin.F1 = a.
Proof. reflexivity. Qed.

Definition halting_arithmetic_instance
    (p : arithmetic_semisentence 1) (a : nat) : sentence oring_language :=
  arithmetic_numeral_instance p (halting_unary_vector a).

(** The one concrete service still needed after R0 representation: proofs of
    negated numeral instances must themselves be semidecidable.  Foundation
    obtains this from its internal Delta-one proof predicate. *)
Definition arithmetic_negative_instance_semidecidable
    (T : theory oring_language) : Prop :=
  forall p : arithmetic_semisentence 1,
    semidecidable (fun a =>
      first_order_theory_provable T
        (semiformula_neg (halting_arithmetic_instance p a))).

(** Arithmetic specialization of the source primed theorem.  The base theory
    is weakened from ISigma1 to R0, the exact strength consumed by the
    representation theorem. *)
Theorem r0_independent_instance_of_not_cosemidecidable : forall
    (T : theory oring_language),
  generic_weaker_than
    (first_order_theory_entailment oring_language)
    (first_order_theory_entailment oring_language) r0_axiom T ->
  arithmetic_theory_sound_on_hierarchy T arithmetic_sigma 1 ->
  forall P : nat -> Prop,
  arithmetically_semidecidable
    (fun v : Fin.t 1 -> nat => P (v Fin.F1)) ->
  ~ semidecidable (fun a => ~ P a) ->
  arithmetic_negative_instance_semidecidable T ->
  exists p : arithmetic_semisentence 1,
    arithmetic_hierarchy Empty_set arithmetic_sigma 1 1 p /\
    exists a,
      generic_independent
        (first_order_theory_entailment oring_language)
        semiformula_neg T (halting_arithmetic_instance p a).
Proof.
  intros T Hweak Hsound P Hsemi Hnot_co Hnegative.
  destruct (@r0_arithmetically_semidecidable_provability_representation
    T Hweak Hsound 1 (fun v : Fin.t 1 -> nat => P (v Fin.F1)) Hsemi)
    as [p [Hp Hrep]].
  exists p. split; [exact Hp |].
  assert (Hrep_unary : forall a,
      P a <->
      first_order_theory_provable T (halting_arithmetic_instance p a)).
  { intro a. exact (Hrep (halting_unary_vector a)). }
  apply (@independent_instance_of_not_cosemidecidable
    (theory oring_language) (sentence oring_language)
    (first_order_theory_entailment oring_language)
    semiformula_neg T P (halting_arithmetic_instance p)).
  - exact Hrep_unary.
  - intros a Hpos Hneg.
    exact (@first_order_consistent_not_both oring_language T
      (halting_arithmetic_instance p a)
      (@arithmetic_theory_consistent_of_sigma_one_sound T Hsound)
      Hpos Hneg).
  - exact (Hnegative p).
  - exact Hnot_co.
Qed.

Corollary r0_incomplete_of_not_cosemidecidable : forall
    (T : theory oring_language),
  generic_weaker_than
    (first_order_theory_entailment oring_language)
    (first_order_theory_entailment oring_language) r0_axiom T ->
  arithmetic_theory_sound_on_hierarchy T arithmetic_sigma 1 ->
  forall P : nat -> Prop,
  arithmetically_semidecidable
    (fun v : Fin.t 1 -> nat => P (v Fin.F1)) ->
  ~ semidecidable (fun a => ~ P a) ->
  arithmetic_negative_instance_semidecidable T ->
  generic_incomplete
    (first_order_theory_entailment oring_language)
    semiformula_neg T.
Proof.
  intros T Hweak Hsound P Hsemi Hnot_co Hnegative.
  constructor.
  destruct (@r0_independent_instance_of_not_cosemidecidable
    T Hweak Hsound P Hsemi Hnot_co Hnegative)
    as [p [_ [a Hindependent]]].
  now exists (halting_arithmetic_instance p a).
Qed.
