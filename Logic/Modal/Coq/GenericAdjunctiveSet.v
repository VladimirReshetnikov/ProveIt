(**
  Generic contexts with empty and single-formula extension.

  This is the explicit-dictionary counterpart of the pinned Foundation module
  [Vorspiel/AdjunctiveSet.lean].  Membership is primitive, while inclusion is
  deliberately pointwise.  Consequently the API needs neither predicate
  extensionality nor a redundant primitive subset relation.

  Context finiteness is witnessed by a list whose membership predicate agrees
  pointwise with context membership.  Lists may contain duplicates, and all
  equality reasoning remains in [Prop], so no decidable equality is required.
*)

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Primitive adjunctive contexts *)

Record generic_adjunctive_set (F S : Type) : Type := {
  generic_adjunctive_member : F -> S -> Prop;
  generic_adjunctive_empty : S;
  generic_adjunctive_adjoin : F -> S -> S;
  generic_adjunctive_not_mem_empty :
    forall p : F,
      ~ generic_adjunctive_member p generic_adjunctive_empty;
  generic_adjunctive_mem_adjoin_iff :
    forall (p q : F) (s : S),
      generic_adjunctive_member p (generic_adjunctive_adjoin q s) <->
      p = q \/ generic_adjunctive_member p s
}.

Arguments generic_adjunctive_member {F S} _ _ _.
Arguments generic_adjunctive_empty {F S} _.
Arguments generic_adjunctive_adjoin {F S} _ _ _.
Arguments generic_adjunctive_not_mem_empty {F S} _ _ _.
Arguments generic_adjunctive_mem_adjoin_iff {F S} _ _ _ _.

(** The predicate of formulas represented by a context. *)
Definition generic_adjunctive_carrier {F S : Type}
    (A : generic_adjunctive_set F S) (s : S) : F -> Prop :=
  fun p => generic_adjunctive_member A p s.

(** Inclusion is the operational, pointwise relation from Foundation's
    [subset_iff] law. *)
Definition generic_adjunctive_subset {F S : Type}
    (A : generic_adjunctive_set F S) (s t : S) : Prop :=
  forall p, generic_adjunctive_member A p s ->
            generic_adjunctive_member A p t.

Lemma generic_adjunctive_subset_refl :
  forall (F S : Type) (A : generic_adjunctive_set F S) (s : S),
    generic_adjunctive_subset A s s.
Proof.
  intros F S A s p Hp. exact Hp.
Qed.

Lemma generic_adjunctive_subset_trans :
  forall (F S : Type) (A : generic_adjunctive_set F S) (s t u : S),
    generic_adjunctive_subset A s t ->
    generic_adjunctive_subset A t u ->
    generic_adjunctive_subset A s u.
Proof.
  intros F S A s t u Hst Htu p Hp.
  exact (Htu p (Hst p Hp)).
Qed.

(** Mutual inclusion yields the pointwise equality interface used throughout
    the generic port, without asserting equality of context values. *)
Lemma generic_adjunctive_subset_antisymm_pointwise :
  forall (F S : Type) (A : generic_adjunctive_set F S) (s t : S),
    generic_adjunctive_subset A s t ->
    generic_adjunctive_subset A t s ->
    forall p, generic_adjunctive_carrier A s p <->
              generic_adjunctive_carrier A t p.
Proof.
  intros F S A s t Hst Hts p; split.
  - apply Hst.
  - apply Hts.
Qed.

Lemma generic_adjunctive_empty_subset :
  forall (F S : Type) (A : generic_adjunctive_set F S) (s : S),
    generic_adjunctive_subset A (generic_adjunctive_empty A) s.
Proof.
  intros F S A s p Hp. exfalso.
  exact (generic_adjunctive_not_mem_empty A p Hp).
Qed.

(** Foundation's derived [mem_cons]. *)
Lemma generic_adjunctive_mem_adjoin_self :
  forall (F S : Type) (A : generic_adjunctive_set F S)
         (s : S) (p : F),
    generic_adjunctive_member A p (generic_adjunctive_adjoin A p s).
Proof.
  intros F S A s p.
  apply (proj2 (generic_adjunctive_mem_adjoin_iff A p p s)).
  now left.
Qed.

(** Existing members survive an adjoin. *)
Lemma generic_adjunctive_mem_adjoin_old :
  forall (F S : Type) (A : generic_adjunctive_set F S)
         (s : S) (p q : F),
    generic_adjunctive_member A p s ->
    generic_adjunctive_member A p (generic_adjunctive_adjoin A q s).
Proof.
  intros F S A s p q Hp.
  apply (proj2 (generic_adjunctive_mem_adjoin_iff A p q s)).
  now right.
Qed.

(** Foundation's derived [subset_cons]. *)
Lemma generic_adjunctive_subset_adjoin :
  forall (F S : Type) (A : generic_adjunctive_set F S)
         (s : S) (p : F),
    generic_adjunctive_subset A s (generic_adjunctive_adjoin A p s).
Proof.
  intros F S A s p q Hq.
  exact (@generic_adjunctive_mem_adjoin_old F S A s q p Hq).
Qed.

Lemma generic_adjunctive_adjoin_monotone :
  forall (F S : Type) (A : generic_adjunctive_set F S)
         (s t : S) (p : F),
    generic_adjunctive_subset A s t ->
    generic_adjunctive_subset A
      (generic_adjunctive_adjoin A p s)
      (generic_adjunctive_adjoin A p t).
Proof.
  intros F S A s t p Hst q Hq.
  apply (proj2 (generic_adjunctive_mem_adjoin_iff A q p t)).
  destruct (proj1 (generic_adjunctive_mem_adjoin_iff A q p s) Hq)
    as [Heq | Hmem].
  - now left.
  - right. exact (Hst q Hmem).
Qed.

(** Keep the public dictionary/context arguments explicit.  Coq would
    otherwise infer some of them from the reducible pointwise subset body,
    making ordinary API calls unnecessarily fragile. *)
Arguments generic_adjunctive_subset_refl {F S} A s.
Arguments generic_adjunctive_subset_trans {F S} A s t u _ _.
Arguments generic_adjunctive_subset_antisymm_pointwise
  {F S} A s t _ _ p.
Arguments generic_adjunctive_empty_subset {F S} A s.
Arguments generic_adjunctive_mem_adjoin_self {F S} A s p.
Arguments generic_adjunctive_mem_adjoin_old {F S} A s p q _.
Arguments generic_adjunctive_subset_adjoin {F S} A s p.
Arguments generic_adjunctive_adjoin_monotone {F S} A s t p _.

(** * List-backed finiteness *)

(** Stdlib's [List.In] is fixed at the universe of its defining module in the
    Rocq release used by this project.  This structurally identical local
    predicate keeps the generic formula universe genuinely polymorphic. *)
Fixpoint generic_list_member {F : Type} (p : F) (xs : list F) : Prop :=
  match xs with
  | nil => False
  | cons q qs => p = q \/ generic_list_member p qs
  end.

Definition generic_adjunctive_finite {F S : Type}
    (A : generic_adjunctive_set F S) (s : S) : Prop :=
  exists xs : list F,
    forall p, generic_adjunctive_member A p s <->
              generic_list_member p xs.

(** The generic conversion corresponding to Foundation's
    [List.toAdjunctiveSet]. *)
Fixpoint generic_adjunctive_from_list {F S : Type}
    (A : generic_adjunctive_set F S) (xs : list F) : S :=
  match xs with
  | nil => generic_adjunctive_empty A
  | cons p ps =>
      generic_adjunctive_adjoin A p (generic_adjunctive_from_list A ps)
  end.

Lemma generic_adjunctive_member_from_list_iff :
  forall (F S : Type) (A : generic_adjunctive_set F S)
         (xs : list F) (p : F),
    generic_adjunctive_member A p (generic_adjunctive_from_list A xs) <->
    generic_list_member p xs.
Proof.
  intros F S A xs; induction xs as [|q qs IH]; intro p; simpl.
  - split.
    + intro Hmem. exfalso.
      exact (generic_adjunctive_not_mem_empty A p Hmem).
    + intro Hin. contradiction.
  - split.
    + intro Hmem.
      destruct (proj1 (generic_adjunctive_mem_adjoin_iff
        A p q (generic_adjunctive_from_list A qs)) Hmem)
        as [Heq | Htail].
      * now left.
      * right. exact (proj1 (IH p) Htail).
    + intros [Heq | Htail].
      * apply (proj2 (generic_adjunctive_mem_adjoin_iff
          A p q (generic_adjunctive_from_list A qs))).
        now left.
      * apply (proj2 (generic_adjunctive_mem_adjoin_iff
          A p q (generic_adjunctive_from_list A qs))).
        right. exact (proj2 (IH p) Htail).
Qed.

Lemma generic_adjunctive_empty_finite :
  forall (F S : Type) (A : generic_adjunctive_set F S),
    generic_adjunctive_finite A (generic_adjunctive_empty A).
Proof.
  intros F S A. exists nil. intro p; split.
  - intro Hmem. exfalso.
    exact (generic_adjunctive_not_mem_empty A p Hmem).
  - intro Hin. contradiction.
Qed.

Lemma generic_adjunctive_adjoin_finite :
  forall (F S : Type) (A : generic_adjunctive_set F S)
         (s : S) (q : F),
    generic_adjunctive_finite A s ->
    generic_adjunctive_finite A (generic_adjunctive_adjoin A q s).
Proof.
  intros F S A s q [xs Hxs]. exists (cons q xs). intro p.
  split.
  - intro Hmem.
    destruct (proj1 (generic_adjunctive_mem_adjoin_iff A p q s) Hmem)
      as [Heq | Hold].
    + now left.
    + right. exact (proj1 (Hxs p) Hold).
  - intros [Heq | Hold].
    + apply (proj2 (generic_adjunctive_mem_adjoin_iff A p q s)).
      now left.
    + apply (proj2 (generic_adjunctive_mem_adjoin_iff A p q s)).
      right. exact (proj2 (Hxs p) Hold).
Qed.

Lemma generic_adjunctive_from_list_finite :
  forall (F S : Type) (A : generic_adjunctive_set F S) (xs : list F),
    generic_adjunctive_finite A (generic_adjunctive_from_list A xs).
Proof.
  intros F S A xs. exists xs.
  exact (generic_adjunctive_member_from_list_iff A xs).
Qed.

(** * Canonical models *)

(** Predicates provide Foundation's set instance without any appeal to
    predicate extensionality. *)
Definition generic_predicate_adjunctive_set (F : Type) :
    generic_adjunctive_set F (F -> Prop).
Proof.
  refine {| generic_adjunctive_member := fun p s => s p;
            generic_adjunctive_empty := fun _ => False;
            generic_adjunctive_adjoin :=
              fun q s p => p = q \/ s p |}.
  - intros p H. exact H.
  - intros p q s; split; intro H; exact H.
Defined.

(** Lists provide Foundation's list instance without decidable equality. *)
Definition generic_list_adjunctive_set (F : Type) :
    generic_adjunctive_set F (list F).
Proof.
  refine {| generic_adjunctive_member := generic_list_member;
            generic_adjunctive_empty := nil;
            generic_adjunctive_adjoin := cons |}.
  - intros p H. inversion H.
  - intros p q s; split; intro H; exact H.
Defined.

Lemma generic_list_adjunctive_finite :
  forall (F : Type) (xs : list F),
    generic_adjunctive_finite (generic_list_adjunctive_set F) xs.
Proof.
  intros F xs. exists xs. intro p; split; intro H; exact H.
Qed.
