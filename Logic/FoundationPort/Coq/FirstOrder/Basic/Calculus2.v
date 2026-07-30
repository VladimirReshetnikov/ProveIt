(**
  Alternative finite-context presentation of first-order LK.

  This ports the first half of
  [Foundation/FirstOrder/Basic/Calculus2.lean].  Foundation uses finsets and
  consequently assumes decidable formula equality.  Coq instead reuses the
  duplicate-insensitive list membership relation from the generic calculus:
  contexts have the same set-like rules, but neither the syntax nor the
  translations require an equality decision.
*)

From Stdlib Require Import Lists.List Vectors.Fin.
From FoundationModal Require Import GenericAdjunctiveSet GenericCalculus.
From Foundation.Syntax.Predicate Require Import Language Rew Term.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Calculus.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** Set-style rules over duplicate-tolerant finite list contexts. *)
Inductive first_order_derivation2 (L : language) (T : theory L) :
    first_order_sequent L -> Type :=
| FOD2Closed : forall Gamma (p : proposition L),
    generic_list_member p Gamma ->
    generic_list_member (semiformula_neg p) Gamma ->
    @first_order_derivation2 L T Gamma
| FOD2Axiom : forall Gamma (sigma : sentence L),
    T sigma ->
    generic_list_member (first_order_sentence_embed sigma) Gamma ->
    @first_order_derivation2 L T Gamma
| FOD2Verum : forall Gamma,
    generic_list_member (Semiformula_verum 0) Gamma ->
    @first_order_derivation2 L T Gamma
| FOD2And : forall Gamma (p q : proposition L),
    generic_list_member (Semiformula_and p q) Gamma ->
    @first_order_derivation2 L T (p :: Gamma) ->
    @first_order_derivation2 L T (q :: Gamma) ->
    @first_order_derivation2 L T Gamma
| FOD2Or : forall Gamma (p q : proposition L),
    generic_list_member (Semiformula_or p q) Gamma ->
    @first_order_derivation2 L T (p :: q :: Gamma) ->
    @first_order_derivation2 L T Gamma
| FOD2All : forall Gamma (p : semiproposition L 1),
    generic_list_member (Semiformula_all p) Gamma ->
    @first_order_derivation2 L T
      (@semiformula_free L 0 p :: first_order_sequent_shift Gamma) ->
    @first_order_derivation2 L T Gamma
| FOD2Exists : forall Gamma (p : semiproposition L 1),
    generic_list_member (Semiformula_exists p) Gamma ->
    forall t : syntactic_term L,
    @first_order_derivation2 L T
      (semiformula_substitute (fun _ : Fin.t 1 => t) p :: Gamma) ->
    @first_order_derivation2 L T Gamma
| FOD2Weakening : forall Delta Gamma,
    @first_order_derivation2 L T Delta ->
    generic_list_subset Delta Gamma ->
    @first_order_derivation2 L T Gamma
| FOD2Shift : forall Gamma,
    @first_order_derivation2 L T Gamma ->
    @first_order_derivation2 L T (first_order_sequent_shift Gamma)
| FOD2Cut : forall Gamma (p : proposition L),
    @first_order_derivation2 L T (p :: Gamma) ->
    @first_order_derivation2 L T (semiformula_neg p :: Gamma) ->
    @first_order_derivation2 L T Gamma.

Arguments first_order_derivation2 L T Gamma : clear implicits.
Arguments FOD2Closed {L T Gamma} p _ _.
Arguments FOD2Axiom {L T Gamma} sigma _ _.
Arguments FOD2Verum {L T Gamma} _.
Arguments FOD2And {L T Gamma p q} _ _ _.
Arguments FOD2Or {L T Gamma p q} _ _.
Arguments FOD2All {L T Gamma p} _ _.
Arguments FOD2Exists {L T Gamma p} _ t _.
Arguments FOD2Weakening {L T Delta Gamma} _ _.
Arguments FOD2Shift {L T Gamma} _.
Arguments FOD2Cut {L T Gamma p} _ _.

Definition first_order_derivable2 {L}
    (T : theory L) (Gamma : first_order_sequent L) : Prop :=
  inhabited (first_order_derivation2 L T Gamma).

Definition first_order_derivation2_cast {L T Gamma Delta}
    (d : first_order_derivation2 L T Gamma) (e : Gamma = Delta) :
    first_order_derivation2 L T Delta :=
  match e with
  | eq_refl => d
  end.

(** Every ordinary LK derivation is an alternative derivation over any
    ambient theory.  No formula equality or theory membership is used. *)
Fixpoint first_order_derivation_to_derivation2 {L T Gamma}
    (d : first_order_derivation L Gamma) {struct d} :
    first_order_derivation2 L T Gamma.
Proof.
  destruct d as [k r v | p Gamma Delta dp dn | Gamma Delta d Hsub |
    | p q Gamma d | p q Gamma dp dq | p Gamma d | p t Gamma d].
  - apply (FOD2Closed (Semiformula_rel r v));
      [now left | now right; left].
  - apply (FOD2Cut (p := p)).
    + apply (FOD2Weakening
        (@first_order_derivation_to_derivation2 L T _ dp)).
      exact (@generic_list_subset_cons_append_right
        (proposition L) p Gamma Delta).
    + apply (FOD2Weakening
        (@first_order_derivation_to_derivation2 L T _ dn)).
      exact (@generic_list_subset_cons_append_left
        (proposition L) (semiformula_neg p) Gamma Delta).
  - exact (FOD2Weakening
      (@first_order_derivation_to_derivation2 L T _ d) Hsub).
  - apply FOD2Verum. now left.
  - apply (FOD2Or (p := p) (q := q)); [now left |].
    apply (FOD2Weakening
      (@first_order_derivation_to_derivation2 L T _ d)).
    intros x [Hx | [Hx | Hx]].
    + now left.
    + right. now left.
    + right. right. now right.
  - apply (FOD2And (p := p) (q := q)); [now left | |].
    + apply (FOD2Weakening
        (@first_order_derivation_to_derivation2 L T _ dp)).
      intros x [Hx | Hx]; [now left | right; now right].
    + apply (FOD2Weakening
        (@first_order_derivation_to_derivation2 L T _ dq)).
      intros x [Hx | Hx]; [now left | right; now right].
  - apply (FOD2All (p := p)); [now left |].
    apply (FOD2Weakening
      (@first_order_derivation_to_derivation2 L T _ d)).
    intros x [Hx | Hx]; [now left |].
    right. simpl. now right.
  - refine (@FOD2Exists L T (Semiformula_exists p :: Gamma) p
      (or_introl eq_refl) t _).
    apply (FOD2Weakening
      (@first_order_derivation_to_derivation2 L T _ d)).
    intros x [Hx | Hx]; [now left | right; now right].
Defined.

(** The reverse translation records the finite theory support accumulated by
    an alternative derivation. *)
Record first_order_derivation2_proof_data {L}
    (T : theory L) (Gamma : first_order_sequent L) : Type := {
  first_order_derivation2_axioms : list (sentence L);
  first_order_derivation2_axioms_member :
    forall sigma,
      generic_list_member sigma first_order_derivation2_axioms -> T sigma;
  first_order_derivation2_lk :
    first_order_derivation L
      (Gamma ++ map semiformula_neg
        (map first_order_sentence_embed first_order_derivation2_axioms))
}.
