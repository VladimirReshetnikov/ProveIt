(**
  Generic disjunctive entailments.

  This module ports all four active declarations from the pinned Foundation
  module [Logic/Disjunctive.lean].  Negation and disjunction are explicit
  operations, so the development is independent of modal syntax and of every
  unused connective.

  Foundation states the completeness/disjunctiveness equivalence under a
  full classical-entailment dictionary and decidable formula equality.  Its
  proof uses only two consequences: excluded middle and resolution of a
  disjunction against the negation of its left disjunct.  Exposing those exact
  rules removes decidable equality and keeps the equivalence constructive.
*)

From FoundationModal Require Import GenericEntailment.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** Source declaration 1/4: [Entailment.Disjunctive]. *)
Record generic_disjunctive {S F : Type}
    (E : generic_entailment S F)
    (disj : F -> F -> F) (s : S) : Prop := {
  generic_disjunctive_cases :
    forall p q : F,
      generic_provable E s (disj p q) ->
      generic_provable E s p \/ generic_provable E s q
}.

Arguments generic_disjunctive_cases
  {S F E disj s} _ _ _ _.

(** Source declaration 2/4: alias [disjunctive]. *)
Definition generic_disjunctive_raw := @generic_disjunctive_cases.

(** Source declaration 3/4: [iff_disjunctive]. *)
Lemma generic_disjunctive_iff :
  forall (S F : Type)
         (E : generic_entailment S F)
         (disj : F -> F -> F) (s : S),
    generic_disjunctive E disj s <->
    forall p q : F,
      generic_provable E s (disj p q) ->
      generic_provable E s p \/ generic_provable E s q.
Proof.
  intros S F E disj s; split.
  - intros H p q. exact (generic_disjunctive_cases H p q).
  - intro H. constructor. exact H.
Qed.

(** The two exact classical rules used by source declaration 4. *)
Definition generic_excluded_middle {S F : Type}
    (E : generic_entailment S F)
    (neg : F -> F) (disj : F -> F -> F) (s : S) : Prop :=
  forall p : F, generic_provable E s (disj p (neg p)).

Definition generic_disjunctive_left_resolution {S F : Type}
    (E : generic_entailment S F)
    (neg : F -> F) (disj : F -> F -> F) (s : S) : Prop :=
  forall p q : F,
    generic_provable E s (neg p) ->
    generic_provable E s (disj p q) ->
    generic_provable E s q.

(** Completeness implies disjunctiveness using resolution alone. *)
Lemma generic_disjunctive_of_complete :
  forall (S F : Type)
         (E : generic_entailment S F)
         (neg : F -> F) (disj : F -> F -> F) (s : S),
    generic_disjunctive_left_resolution E neg disj s ->
    generic_syntactically_complete E neg s ->
    generic_disjunctive E disj s.
Proof.
  intros S F E neg disj s Hresolve Hcomplete.
  constructor. intros p q Hor.
  destruct (generic_syntactically_complete_cases Hcomplete p)
    as [Hp | Hneg].
  - now left.
  - right. exact (Hresolve p q Hneg Hor).
Qed.

(** Disjunctiveness implies completeness using excluded middle alone. *)
Lemma generic_complete_of_disjunctive :
  forall (S F : Type)
         (E : generic_entailment S F)
         (neg : F -> F) (disj : F -> F -> F) (s : S),
    generic_excluded_middle E neg disj s ->
    generic_disjunctive E disj s ->
    generic_syntactically_complete E neg s.
Proof.
  intros S F E neg disj s Hlem Hdisjunctive.
  constructor. intro p.
  exact (generic_disjunctive_cases Hdisjunctive p (neg p) (Hlem p)).
Qed.

(** Source declaration 4/4: [iff_complete_disjunctive], strengthened from
    full classical entailment and decidable formula equality to the two rules
    above. *)
Lemma generic_complete_iff_disjunctive :
  forall (S F : Type)
         (E : generic_entailment S F)
         (neg : F -> F) (disj : F -> F -> F) (s : S),
    generic_excluded_middle E neg disj s ->
    generic_disjunctive_left_resolution E neg disj s ->
    generic_syntactically_complete E neg s <->
    generic_disjunctive E disj s.
Proof.
  intros S F E neg disj s Hlem Hresolve; split.
  - exact (generic_disjunctive_of_complete Hresolve).
  - exact (generic_complete_of_disjunctive Hlem).
Qed.
