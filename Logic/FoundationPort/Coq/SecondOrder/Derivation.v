(** One-sided classical derivations for monadic second-order logic. *)

From Stdlib Require Import Lists.List Vectors.Fin.
From Foundation.Syntax.Predicate Require Import Language Term.
From Foundation.SecondOrder.Syntax Require Import Formula Rew.

Import ListNotations.
Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition second_order_sequent (L : language) : Type :=
  list (second_order_proposition L).

Definition second_order_sequent_shift_individual {L}
    (Gamma : second_order_sequent L) : second_order_sequent L :=
  map second_order_semiproposition_shift_individual Gamma.

Lemma second_order_sequent_shift_individual_nil : forall L,
  second_order_sequent_shift_individual ([] : second_order_sequent L) = [].
Proof. reflexivity. Qed.

Lemma second_order_sequent_shift_individual_cons : forall L
    (p : second_order_proposition L) Gamma,
  second_order_sequent_shift_individual (p :: Gamma) =
  second_order_semiproposition_shift_individual p ::
    second_order_sequent_shift_individual Gamma.
Proof. reflexivity. Qed.

Definition second_order_sequent_shift_predicate {L}
    (Gamma : second_order_sequent L) : second_order_sequent L :=
  map second_order_semiproposition_shift_predicate Gamma.

Lemma second_order_sequent_shift_predicate_nil : forall L,
  second_order_sequent_shift_predicate ([] : second_order_sequent L) = [].
Proof. reflexivity. Qed.

Lemma second_order_sequent_shift_predicate_cons : forall L
    (p : second_order_proposition L) Gamma,
  second_order_sequent_shift_predicate (p :: Gamma) =
  second_order_semiproposition_shift_predicate p ::
    second_order_sequent_shift_predicate Gamma.
Proof. reflexivity. Qed.

Definition second_order_sequent_neg {L}
    (Gamma : second_order_sequent L) : second_order_sequent L :=
  map second_order_neg Gamma.

Lemma second_order_sequent_neg_nil : forall L,
  second_order_sequent_neg ([] : second_order_sequent L) = [].
Proof. reflexivity. Qed.

Lemma second_order_sequent_neg_cons : forall L
    (p : second_order_proposition L) Gamma,
  second_order_sequent_neg (p :: Gamma) =
  second_order_neg p :: second_order_sequent_neg Gamma.
Proof. reflexivity. Qed.

(** The quantifier rules deliberately reuse the general rewrite operations:
    individual existential introduction is unary instantiation, and predicate
    existential introduction is formula-valued predicate substitution. *)
Inductive second_order_lk_derivation {L} :
    second_order_sequent L -> Type :=
| SO_LK_identity : forall p,
    second_order_lk_derivation [p; second_order_neg p]
| SO_LK_cut : forall p Gamma,
    second_order_lk_derivation (p :: Gamma) ->
    second_order_lk_derivation (second_order_neg p :: Gamma) ->
    second_order_lk_derivation Gamma
| SO_LK_weakening : forall Gamma Delta,
    second_order_lk_derivation Gamma ->
    incl Gamma Delta -> second_order_lk_derivation Delta
| SO_LK_verum : second_order_lk_derivation [SOFormula_verum]
| SO_LK_and : forall p q Gamma,
    second_order_lk_derivation (p :: Gamma) ->
    second_order_lk_derivation (q :: Gamma) ->
    second_order_lk_derivation (SOFormula_and p q :: Gamma)
| SO_LK_or : forall p q Gamma,
    second_order_lk_derivation (p :: q :: Gamma) ->
    second_order_lk_derivation (SOFormula_or p q :: Gamma)
| SO_LK_all_individual : forall
    (p : second_order_semiproposition L 0 1) Gamma,
    second_order_lk_derivation
      (@second_order_semiproposition_free_individual L 0 0 p ::
        second_order_sequent_shift_individual Gamma) ->
    second_order_lk_derivation (SOFormula_all0 p :: Gamma)
| SO_LK_exists_individual : forall
    (p : second_order_semiproposition L 0 1)
    (t : semiterm L nat 0) Gamma,
    second_order_lk_derivation (second_order_instantiate p t :: Gamma) ->
    second_order_lk_derivation (SOFormula_exs0 p :: Gamma)
| SO_LK_all_predicate : forall
    (p : second_order_semiproposition L 1 0) Gamma,
    second_order_lk_derivation
      (@second_order_semiproposition_free_predicate L 0 0 p ::
        second_order_sequent_shift_predicate Gamma) ->
    second_order_lk_derivation (SOFormula_all1 p :: Gamma)
| SO_LK_exists_predicate : forall
    (p : second_order_semiproposition L 1 0)
    (q : second_order_semiproposition L 0 1) Gamma,
    second_order_lk_derivation
      (second_order_semiproposition_substitute_predicates
        (fun _ : Fin.t 1 => q) p :: Gamma) ->
    second_order_lk_derivation (SOFormula_exs1 p :: Gamma).

Definition second_order_lk_derivation_cast {L Gamma Delta}
    (d : @second_order_lk_derivation L Gamma) (h : Gamma = Delta) :
    @second_order_lk_derivation L Delta :=
  match h with eq_refl => d end.

Definition second_order_sentence_as_proposition {L}
    (p : second_order_sentence L) : second_order_proposition L :=
  second_order_semisentence_embed p.

Definition second_order_lk_proof {L} (p : second_order_sentence L) : Type :=
  second_order_lk_derivation [second_order_sentence_as_proposition p].

(** A schema is a predicate on open propositions. *)
Definition second_order_schema (L : language) : Type :=
  second_order_proposition L -> Prop.

Record second_order_schema_derivation {L}
    (S : second_order_schema L) (p : second_order_proposition L) : Type := {
  second_order_schema_axioms : second_order_sequent L;
  second_order_schema_lk_derivation : second_order_lk_derivation
    (p :: second_order_sequent_neg second_order_schema_axioms);
  second_order_schema_instances : forall q,
    In q second_order_schema_axioms -> S q
}.

(** Proposition-valued provability is the truncation of the data-carrying
    schema derivation, which is the appropriate Coq counterpart of using the
    source structure as an entailment witness. *)
Definition second_order_schema_provable {L}
    (S : second_order_schema L) (p : second_order_proposition L) : Prop :=
  exists d : second_order_schema_derivation S p, True.

Definition second_order_theory (L : language) : Type :=
  second_order_sentence L -> Prop.

Definition second_order_theory_provable {L}
    (T : second_order_theory L) (p : second_order_sentence L) : Prop := T p.

Lemma second_order_theory_provable_iff : forall L
    (T : second_order_theory L) (p : second_order_sentence L),
  second_order_theory_provable T p <-> T p.
Proof. reflexivity. Qed.

Definition second_order_schema_theory {L}
    (S : second_order_schema L) : second_order_theory L :=
  fun p => second_order_schema_provable S
    (second_order_sentence_as_proposition p).

Lemma second_order_schema_theory_provable_iff : forall L
    (S : second_order_schema L) (p : second_order_sentence L),
  second_order_theory_provable (second_order_schema_theory S) p <->
  second_order_schema_provable S (second_order_sentence_as_proposition p).
Proof. reflexivity. Qed.
