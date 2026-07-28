(**
  Generic intuitionistic and weak/classical forcing relations.

  This module ports all 20 active declaration-producing commands in the
  pinned [Foundation/Logic/ForcingRelation.lean].  Ordinary and weak forcing
  both reuse the models-only [generic_semantics] dictionary.  Existence at a
  world remains a distinct dictionary because downstream first-order models
  use it for domain membership rather than formula truth.

  Relational implication, negation, and persistence are factored into shared
  capabilities.  No order law is imposed on the accessibility relation, and
  every result is constructive: the source's one use of choice for an
  inhabited world is replaced by elimination of [inhabited] into [Prop].
*)

From FoundationModal Require Import GenericSemantics GenericAdjunctiveSet.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** Source declaration 1/20: [LO.ForcingRelation].  Its sole field is exactly
    the relation in Foundation's models-only semantics. *)
Definition generic_forcing_relation (W F : Type) : Type :=
  generic_semantics W F.

Definition generic_forces {W F : Type}
    (K : generic_forcing_relation W F) (w : W) (p : F) : Prop :=
  generic_models K w p.

(** Source declaration 2/20: [LO.ForcingExists]. *)
Record generic_forcing_exists (W A : Type) : Type := {
  generic_exists_forces : W -> A -> Prop
}.

(** Source declaration 3/20: [ForcingRelation.NotForces]. *)
Definition generic_forcing_not_forces {W F : Type}
    (K : generic_forcing_relation W F) (w : W) (p : F) : Prop :=
  ~ generic_forces K w p.

(** Source declaration 4/20: [ForcingRelation.BasicSemantics].  Existing
    connective-specific semantic records retain the reusable component
    boundaries instead of repeating their fields. *)
Record generic_forcing_basic_semantics {W F : Type}
    (C : generic_connectives F)
    (K : generic_forcing_relation W F) : Prop := {
  generic_forcing_basic_top : generic_semantics_top C K;
  generic_forcing_basic_and : generic_semantics_and C K;
  generic_forcing_basic_or : generic_semantics_or C K
}.

(** Source declaration 5/20: [ForcingRelation.Monotone]. *)
Record generic_forcing_monotone {W F : Type}
    (K : generic_forcing_relation W F)
    (R : W -> W -> Prop) : Prop := {
  generic_forcing_persistent :
    forall (w : W) (p : F),
      generic_forces K w p ->
      forall v : W, R w v -> generic_forces K v p
}.

(** Shared future-world implication and negation clauses.  They are not the
    point-local Tarski clauses [generic_semantics_imp] and
    [generic_semantics_neg]. *)
Record generic_forcing_imp {W F : Type}
    (C : generic_connectives F)
    (K : generic_forcing_relation W F)
    (R : W -> W -> Prop) : Prop := {
  generic_forcing_imp_clause :
    forall (w : W) (p q : F),
      generic_forces K w (generic_imp C p q) <->
      forall v : W, R w v ->
        generic_forces K v p -> generic_forces K v q
}.

Record generic_forcing_neg {W F : Type}
    (C : generic_connectives F)
    (K : generic_forcing_relation W F)
    (R : W -> W -> Prop) : Prop := {
  generic_forcing_neg_clause :
    forall (w : W) (p : F),
      generic_forces K w (generic_neg C p) <->
      forall v : W, R w v -> ~ generic_forces K v p
}.

(** Source declaration 6/20: [ForcingRelation.IntKripke]. *)
Record generic_int_kripke {W F : Type}
    (C : generic_connectives F)
    (K : generic_forcing_relation W F)
    (R : W -> W -> Prop) : Prop := {
  generic_int_kripke_basic : generic_forcing_basic_semantics C K;
  generic_int_kripke_monotone : generic_forcing_monotone K R;
  generic_int_kripke_imp : generic_forcing_imp C K R;
  generic_int_kripke_bottom : generic_semantics_bottom C K;
  generic_int_kripke_neg : generic_forcing_neg C K R
}.

(** Source declaration 7/20: [ForcingRelation.iff].  The source assumes a
    full intuitionistic Kripke structure; only conjunction and relational
    implication are actually needed. *)
Lemma generic_forcing_models_iff :
  forall (W F : Type) (C : generic_connectives F)
         (K : generic_forcing_relation W F)
         (R : W -> W -> Prop),
    generic_semantics_and C K ->
    generic_forcing_imp C K R ->
    forall (w : W) (p q : F),
      generic_forces K w
        (generic_and C (generic_imp C p q) (generic_imp C q p)) <->
      forall v : W, R w v ->
        (generic_forces K v p <-> generic_forces K v q).
Proof.
  intros W F C K R [HAnd] [HImp] w p q.
  rewrite (HAnd w (generic_imp C p q) (generic_imp C q p)).
  rewrite (HImp w p q), (HImp w q p).
  split.
  - intros [Hpq Hqp] v Hwv; split.
    + apply (Hpq v Hwv).
    + apply (Hqp v Hwv).
  - intro Hall; split.
    + intros v Hwv. exact (proj1 (Hall v Hwv)).
    + intros v Hwv. exact (proj2 (Hall v Hwv)).
Qed.

(** Source declaration 8/20: [ForcingRelation.AllForces]. *)
Definition generic_all_forces {W F : Type}
    (K : generic_forcing_relation W F) (p : F) : Prop :=
  generic_valid K p.

(** Source declaration 9/20: [ForcingRelation.AllForcesSet]. *)
Definition generic_all_forces_context {W F S : Type}
    (K : generic_forcing_relation W F)
    (A : generic_adjunctive_set F S) (s : S) : Prop :=
  forall p : F,
    generic_adjunctive_member A p s -> generic_all_forces K p.

(** A context is globally forced exactly when every world models its carrier.
    This connects the source-facing context API to [generic_models_set]. *)
Lemma generic_all_forces_context_iff_models_set :
  forall (W F S : Type) (K : generic_forcing_relation W F)
         (A : generic_adjunctive_set F S) (s : S),
    generic_all_forces_context K A s <->
    forall w : W,
      generic_models_set K w (generic_adjunctive_carrier A s).
Proof.
  intros W F S K A s; split.
  - intros Hall w. constructor. intros p Hp.
    exact (Hall p Hp w).
  - intros Hall p Hp w.
    destruct (Hall w) as [Hw]. exact (Hw p Hp).
Qed.

(** Source declaration 10/20: [ForcingRelation.AllForces.verum].  Only the
    top clause is required, rather than the aggregate basic semantics. *)
Lemma generic_all_forces_top :
  forall (W F : Type) (C : generic_connectives F)
         (K : generic_forcing_relation W F),
    generic_semantics_top C K ->
    generic_all_forces K (generic_top C).
Proof.
  intros W F C K [HTop] w. apply HTop.
Qed.

(** Source declaration 11/20: [ForcingRelation.AllForces.and]. *)
Lemma generic_all_forces_and :
  forall (W F : Type) (C : generic_connectives F)
         (K : generic_forcing_relation W F),
    generic_semantics_and C K ->
    forall p q : F,
      generic_all_forces K (generic_and C p q) <->
      generic_all_forces K p /\ generic_all_forces K q.
Proof.
  intros W F C K [HAnd] p q; split.
  - intro Hall; split; intro w.
    + exact (proj1 (proj1 (HAnd w p q) (Hall w))).
    + exact (proj2 (proj1 (HAnd w p q) (Hall w))).
  - intros [Hp Hq] w. apply (proj2 (HAnd w p q)).
    split; [apply Hp | apply Hq].
Qed.

(** Source declaration 12/20: [LO.WeakForcingRelation]. *)
Definition generic_weak_forcing_relation (P F : Type) : Type :=
  generic_semantics P F.

Definition generic_weakly_forces {P F : Type}
    (K : generic_weak_forcing_relation P F) (p : P) (f : F) : Prop :=
  generic_models K p f.

(** Source declaration 13/20: [WeakForcingRelation.NotForces]. *)
Definition generic_weak_forcing_not_forces {P F : Type}
    (K : generic_weak_forcing_relation P F) (p : P) (f : F) : Prop :=
  ~ generic_weakly_forces K p f.

(** Source declaration 14/20: [WeakForcingRelation.BasicSemantics]. *)
Record generic_weak_forcing_basic_semantics {P F : Type}
    (C : generic_connectives F)
    (K : generic_weak_forcing_relation P F) : Prop := {
  generic_weak_forcing_basic_top : generic_semantics_top C K;
  generic_weak_forcing_basic_bottom : generic_semantics_bottom C K;
  generic_weak_forcing_basic_and : generic_semantics_and C K
}.

(** Source declaration 15/20: [WeakForcingRelation.ClassicalKripke].
    "Classical" names the semantic construction; this record itself invokes
    no classical axiom. *)
Record generic_classical_kripke {P F : Type}
    (C : generic_connectives F)
    (K : generic_weak_forcing_relation P F)
    (R : P -> P -> Prop) : Prop := {
  generic_classical_kripke_basic :
    generic_weak_forcing_basic_semantics C K;
  generic_classical_kripke_or :
    forall (p : P) (f g : F),
      generic_weakly_forces K p (generic_or C f g) <->
      forall q : P, R p q ->
        exists x : P, R q x /\
          (generic_weakly_forces K x f \/ generic_weakly_forces K x g);
  generic_classical_kripke_neg : generic_forcing_neg C K R;
  generic_classical_kripke_imp : generic_forcing_imp C K R;
  generic_classical_kripke_monotone : generic_forcing_monotone K R;
  generic_classical_kripke_generic :
    forall (p : P) (f : F),
      (forall q : P, R p q ->
        exists r : P, R q r /\ generic_weakly_forces K r f) ->
      generic_weakly_forces K p f
}.

(** Source declaration 16/20: [WeakForcingRelation.AllForces]. *)
Definition generic_weak_all_forces {P F : Type}
    (K : generic_weak_forcing_relation P F) (f : F) : Prop :=
  generic_all_forces K f.

(** Source declaration 17/20: [WeakForcingRelation.AllForcesSet]. *)
Definition generic_weak_all_forces_context {P F S : Type}
    (K : generic_weak_forcing_relation P F)
    (A : generic_adjunctive_set F S) (s : S) : Prop :=
  generic_all_forces_context K A s.

(** Source declaration 18/20: [WeakForcingRelation.AllForces.verum]. *)
Lemma generic_weak_all_forces_top :
  forall (P F : Type) (C : generic_connectives F)
         (K : generic_weak_forcing_relation P F),
    generic_semantics_top C K ->
    generic_weak_all_forces K (generic_top C).
Proof. exact generic_all_forces_top. Qed.

(** Shared constructive form of global bottom failure on a nonempty model
    type. *)
Lemma generic_all_forces_bottom_of_inhabited :
  forall (W F : Type) (C : generic_connectives F)
         (K : generic_forcing_relation W F),
    generic_semantics_bottom C K ->
    inhabited W ->
    ~ generic_all_forces K (generic_bottom C).
Proof.
  intros W F C K [HBottom] [w] Hall.
  exact (HBottom w (Hall w)).
Qed.

(** Source declaration 19/20: [WeakForcingRelation.AllForces.falsum].  The
    source selects a world with classical choice; elimination of [inhabited]
    suffices constructively because the conclusion is a proposition. *)
Lemma generic_weak_all_forces_bottom :
  forall (P F : Type) (C : generic_connectives F)
         (K : generic_weak_forcing_relation P F),
    generic_semantics_bottom C K ->
    inhabited P ->
    ~ generic_weak_all_forces K (generic_bottom C).
Proof. exact generic_all_forces_bottom_of_inhabited. Qed.

(** Source declaration 20/20: [WeakForcingRelation.AllForces.and]. *)
Lemma generic_weak_all_forces_and :
  forall (P F : Type) (C : generic_connectives F)
         (K : generic_weak_forcing_relation P F),
    generic_semantics_and C K ->
    forall f g : F,
      generic_weak_all_forces K (generic_and C f g) <->
      generic_weak_all_forces K f /\ generic_weak_all_forces K g.
Proof. exact generic_all_forces_and. Qed.

Arguments generic_forces {W F} K w p.
Arguments generic_exists_forces {W A} _ _ _.
Arguments generic_forcing_not_forces {W F} K w p.
Arguments generic_forcing_basic_top {W F} C K _.
Arguments generic_forcing_basic_and {W F} C K _.
Arguments generic_forcing_basic_or {W F} C K _.
Arguments generic_forcing_persistent {W F} K R _ w p _ v _.
Arguments generic_forcing_imp_clause {W F} C K R _ w p q.
Arguments generic_forcing_neg_clause {W F} C K R _ w p.
Arguments generic_int_kripke_basic {W F} C K R _.
Arguments generic_int_kripke_monotone {W F} C K R _.
Arguments generic_int_kripke_imp {W F} C K R _.
Arguments generic_int_kripke_bottom {W F} C K R _.
Arguments generic_int_kripke_neg {W F} C K R _.
Arguments generic_forcing_models_iff {W F} C K R _ _ w p q.
Arguments generic_all_forces_context_iff_models_set {W F S} K A s.
Arguments generic_all_forces_top {W F} C K _.
Arguments generic_all_forces_and {W F} C K _ p q.
Arguments generic_all_forces_bottom_of_inhabited {W F} C K _ _.
Arguments generic_weakly_forces {P F} K p f.
Arguments generic_weak_forcing_not_forces {P F} K p f.
Arguments generic_weak_forcing_basic_top {P F} C K _.
Arguments generic_weak_forcing_basic_bottom {P F} C K _.
Arguments generic_weak_forcing_basic_and {P F} C K _.
Arguments generic_classical_kripke_basic {P F} C K R _.
Arguments generic_classical_kripke_or {P F} C K R _ p f g.
Arguments generic_classical_kripke_neg {P F} C K R _.
Arguments generic_classical_kripke_imp {P F} C K R _.
Arguments generic_classical_kripke_monotone {P F} C K R _.
Arguments generic_classical_kripke_generic {P F} C K R _ p f _.
Arguments generic_weak_all_forces_top {P F} C K _.
Arguments generic_weak_all_forces_bottom {P F} C K _ _.
Arguments generic_weak_all_forces_and {P F} C K _ f g.
