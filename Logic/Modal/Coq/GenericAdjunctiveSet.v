(**
  Generic contexts with empty and single-formula extension.

  This is the explicit-dictionary counterpart of the pinned Foundation module
  [Vorspiel/AdjunctiveSet.lean].  Membership is primitive, while inclusion is
  deliberately pointwise.  Consequently the API needs neither predicate
  extensionality nor a redundant primitive subset relation.

  Context finiteness is witnessed by a finite list covering every member.
  Lists may contain duplicates and need not be filtered against an arbitrary
  membership predicate.  This subfinite presentation is closed under subsets,
  and all equality reasoning remains in [Prop], so no decidable equality is
  required.

  The source's Multiset and Finset instances add no theorem-level behavior:
  both are converted through a finite list, and every result depends only on
  membership.  The duplicate-tolerant list realization below therefore
  represents those seven representation-specific declarations as well as the
  source List instance, without adding an equality decision or a bespoke
  finite-container hierarchy to the Coq boundary.
*)

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Primitive adjunctive contexts *)

(** Source declaration 1/35: [Adjoin].  Source declaration 6/35:
    [AdjunctiveSet].  One explicit dictionary is more idiomatic here than a
    weak adjoin dictionary immediately extended by a second type class. *)
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

(** Source declaration 11/35: [AdjunctiveSet.set]. *)
Definition generic_adjunctive_carrier {F S : Type}
    (A : generic_adjunctive_set F S) (s : S) : F -> Prop :=
  fun p => generic_adjunctive_member A p s.

(** Source declaration 12/35: [AdjunctiveSet.mem_set_iff]. *)
Lemma generic_adjunctive_member_carrier_iff :
  forall (F S : Type) (A : generic_adjunctive_set F S)
         (s : S) (p : F),
    generic_adjunctive_carrier A s p <->
    generic_adjunctive_member A p s.
Proof. intros; split; intro H; exact H. Qed.

(** Inclusion is the operational, pointwise relation from Foundation's
    [subset_iff] law. *)
Definition generic_adjunctive_subset {F S : Type}
    (A : generic_adjunctive_set F S) (s t : S) : Prop :=
  forall p, generic_adjunctive_member A p s ->
            generic_adjunctive_member A p t.

(** Source declaration 13/35: [AdjunctiveSet.subset_iff_set_subset_set]. *)
Lemma generic_adjunctive_subset_iff_carrier_subset :
  forall (F S : Type) (A : generic_adjunctive_set F S) (s t : S),
    generic_adjunctive_subset A s t <->
    forall p, generic_adjunctive_carrier A s p ->
              generic_adjunctive_carrier A t p.
Proof. intros; split; intro H; exact H. Qed.

(** Source declaration 14/35: [AdjunctiveSet.subset_refl]. *)
Lemma generic_adjunctive_subset_refl :
  forall (F S : Type) (A : generic_adjunctive_set F S) (s : S),
    generic_adjunctive_subset A s s.
Proof.
  intros F S A s p Hp. exact Hp.
Qed.

(** Source declaration 15/35: [AdjunctiveSet.subset_trans]. *)
Lemma generic_adjunctive_subset_trans :
  forall (F S : Type) (A : generic_adjunctive_set F S) (s t u : S),
    generic_adjunctive_subset A s t ->
    generic_adjunctive_subset A t u ->
    generic_adjunctive_subset A s u.
Proof.
  intros F S A s t u Hst Htu p Hp.
  exact (Htu p (Hst p Hp)).
Qed.

(** Source declaration 16/35: [AdjunctiveSet.subset_antisymm].
    Mutual inclusion yields the pointwise equality interface used throughout
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

(** Source declaration 17/35: [AdjunctiveSet.empty_subset]. *)
Lemma generic_adjunctive_empty_subset :
  forall (F S : Type) (A : generic_adjunctive_set F S) (s : S),
    generic_adjunctive_subset A (generic_adjunctive_empty A) s.
Proof.
  intros F S A s p Hp. exfalso.
  exact (generic_adjunctive_not_mem_empty A p Hp).
Qed.

(** Source declaration 20/35: [AdjunctiveSet.set_empty], stated pointwise so
    that neither propositional nor functional extensionality is needed. *)
Lemma generic_adjunctive_carrier_empty_iff :
  forall (F S : Type) (A : generic_adjunctive_set F S) (p : F),
    generic_adjunctive_carrier A (generic_adjunctive_empty A) p <-> False.
Proof.
  intros F S A p; split.
  - apply (generic_adjunctive_not_mem_empty A p).
  - contradiction.
Qed.

(** Source declaration 18/35: [AdjunctiveSet.mem_cons]. *)
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

(** Source declaration 19/35: [AdjunctiveSet.subset_cons]. *)
Lemma generic_adjunctive_subset_adjoin :
  forall (F S : Type) (A : generic_adjunctive_set F S)
         (s : S) (p : F),
    generic_adjunctive_subset A s (generic_adjunctive_adjoin A p s).
Proof.
  intros F S A s p q Hq.
  exact (@generic_adjunctive_mem_adjoin_old F S A s q p Hq).
Qed.

(** Source declaration 21/35: [AdjunctiveSet.set_cons], generalized to an
    axiom-free pointwise form. *)
Lemma generic_adjunctive_carrier_adjoin_iff :
  forall (F S : Type) (A : generic_adjunctive_set F S)
         (s : S) (p q : F),
    generic_adjunctive_carrier A (generic_adjunctive_adjoin A q s) p <->
    p = q \/ generic_adjunctive_carrier A s p.
Proof.
  intros F S A s p q.
  exact (generic_adjunctive_mem_adjoin_iff A p q s).
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

(** Source declaration 22/35: [AdjunctiveSet.Finite].  A finite cover is the
    constructive, subset-closed form of the source's classically finite
    carrier. *)
Definition generic_adjunctive_finite {F S : Type}
    (A : generic_adjunctive_set F S) (s : S) : Prop :=
  exists xs : list F,
    forall p, generic_adjunctive_member A p s ->
              generic_list_member p xs.

(** Source declaration 26/35: [AdjunctiveSet.addList], separated from
    conversion of a list into
    a context so it can extend an arbitrary base context. *)
Fixpoint generic_adjunctive_add_list {F S : Type}
    (A : generic_adjunctive_set F S) (s : S) (xs : list F) : S :=
  match xs with
  | nil => s
  | cons p ps =>
      generic_adjunctive_adjoin A p (generic_adjunctive_add_list A s ps)
  end.

Lemma generic_adjunctive_member_add_list_iff :
  forall (F S : Type) (A : generic_adjunctive_set F S)
         (s : S) (xs : list F) (p : F),
    generic_adjunctive_member A p (generic_adjunctive_add_list A s xs) <->
    generic_list_member p xs \/ generic_adjunctive_member A p s.
Proof.
  intros F S A s xs; induction xs as [|q qs IH]; intro p; simpl.
  - split.
    + now right.
    + intros [Hfalse | Hmem]; [contradiction | exact Hmem].
  - split.
    + intro Hmem.
      destruct (proj1 (generic_adjunctive_mem_adjoin_iff
        A p q (generic_adjunctive_add_list A s qs)) Hmem)
        as [Heq | Htail].
      * left. now left.
      * destruct (proj1 (IH p) Htail) as [Hin | Hbase].
        -- left. now right.
        -- now right.
    + intros [[Heq | Hin] | Hbase].
      * apply (proj2 (generic_adjunctive_mem_adjoin_iff
          A p q (generic_adjunctive_add_list A s qs))).
        now left.
      * apply (proj2 (generic_adjunctive_mem_adjoin_iff
          A p q (generic_adjunctive_add_list A s qs))).
        right. apply (proj2 (IH p)). now left.
      * apply (proj2 (generic_adjunctive_mem_adjoin_iff
          A p q (generic_adjunctive_add_list A s qs))).
        right. apply (proj2 (IH p)). now right.
Qed.

(** Source declaration 27/35: [List.toAdjunctiveSet].
    Source declaration 28/35: [Finset.toAdjunctiveSet].
    A finite collection crosses the generic Coq
    boundary through its enumeration, so the one conversion covers both. *)
Fixpoint generic_adjunctive_from_list {F S : Type}
    (A : generic_adjunctive_set F S) (xs : list F) : S :=
  match xs with
  | nil => generic_adjunctive_empty A
  | cons p ps =>
      generic_adjunctive_adjoin A p (generic_adjunctive_from_list A ps)
  end.

Lemma generic_adjunctive_from_list_as_add_list :
  forall (F S : Type) (A : generic_adjunctive_set F S) (xs : list F),
    generic_adjunctive_from_list A xs =
    generic_adjunctive_add_list A (generic_adjunctive_empty A) xs.
Proof.
  intros F S A xs. induction xs as [|p ps IH]; simpl.
  - reflexivity.
  - now rewrite IH.
Qed.

(** Source declaration 29/35:
    [AdjunctiveSet.mem_list_toAdjunctiveSet] and Source declaration 30/35:
    [AdjunctiveSet.mem_finset_toAdjunctiveSet].  Duplicates are immaterial. *)
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

(** Source declaration 23/35: [AdjunctiveSet.empty_finite]. *)
Lemma generic_adjunctive_empty_finite :
  forall (F S : Type) (A : generic_adjunctive_set F S),
    generic_adjunctive_finite A (generic_adjunctive_empty A).
Proof.
  intros F S A. exists nil. intros p Hmem. exfalso.
  exact (generic_adjunctive_not_mem_empty A p Hmem).
Qed.

(** Source declaration 24/35: [AdjunctiveSet.Finite.of_subset].  The same
    finite cover works for every
    subcontext, constructively and without deciding membership. *)
Lemma generic_adjunctive_finite_of_subset :
  forall (F S : Type) (A : generic_adjunctive_set F S) (s t : S),
    generic_adjunctive_finite A s ->
    generic_adjunctive_subset A t s ->
    generic_adjunctive_finite A t.
Proof.
  intros F S A s t [xs Hcover] Hsub. exists xs.
  intros p Hp. exact (Hcover p (Hsub p Hp)).
Qed.

Lemma generic_adjunctive_adjoin_finite :
  forall (F S : Type) (A : generic_adjunctive_set F S)
         (s : S) (q : F),
    generic_adjunctive_finite A s ->
    generic_adjunctive_finite A (generic_adjunctive_adjoin A q s).
Proof.
  intros F S A s q [xs Hcover]. exists (cons q xs).
  intros p Hmem.
  destruct (proj1 (generic_adjunctive_mem_adjoin_iff A p q s) Hmem)
    as [Heq | Hold].
  - now left.
  - right. exact (Hcover p Hold).
Qed.

(** Source declaration 25/35: [AdjunctiveSet.cons_finite_iff]. *)
Lemma generic_adjunctive_adjoin_finite_iff :
  forall (F S : Type) (A : generic_adjunctive_set F S)
         (s : S) (q : F),
    generic_adjunctive_finite A (generic_adjunctive_adjoin A q s) <->
    generic_adjunctive_finite A s.
Proof.
  intros F S A s q; split.
  - intro Hfinite.
    exact (@generic_adjunctive_finite_of_subset F S A
      (generic_adjunctive_adjoin A q s) s Hfinite
      (@generic_adjunctive_subset_adjoin F S A s q)).
  - apply generic_adjunctive_adjoin_finite.
Qed.

Lemma generic_adjunctive_add_list_finite :
  forall (F S : Type) (A : generic_adjunctive_set F S)
         (s : S) (xs : list F),
    generic_adjunctive_finite A s ->
    generic_adjunctive_finite A (generic_adjunctive_add_list A s xs).
Proof.
  intros F S A s xs; induction xs as [|p ps IH]; intro Hfinite; simpl.
  - exact Hfinite.
  - apply generic_adjunctive_adjoin_finite. now apply IH.
Qed.

(** Source declaration 31/35:
    [AdjunctiveSet.list_toAdjunctiveSet_finite] and Source declaration 32/35:
    [AdjunctiveSet.finset_toAdjunctiveSet_finite]. *)
Lemma generic_adjunctive_from_list_finite :
  forall (F S : Type) (A : generic_adjunctive_set F S) (xs : list F),
    generic_adjunctive_finite A (generic_adjunctive_from_list A xs).
Proof.
  intros F S A xs. exists xs.
  intros p Hmem.
  exact (proj1 (generic_adjunctive_member_from_list_iff A xs p) Hmem).
Qed.

(** * Canonical models *)

(** Source declaration 2/35 and Source declaration 7/35: the Set [Adjoin]
    and [AdjunctiveSet]
    instances.  Predicates provide the corresponding realization without any
    appeal to predicate extensionality. *)
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

(** Source declaration 33/35: [Set.cons_eq]. *)
Lemma generic_predicate_adjunctive_adjoin_eq :
  forall (F : Type) (q : F) (s : F -> Prop),
    generic_adjunctive_adjoin (generic_predicate_adjunctive_set F) q s =
    (fun p => p = q \/ s p).
Proof. reflexivity. Qed.

(** Source declaration 34/35: [Set.adjunctiveSet_set]. *)
Lemma generic_predicate_adjunctive_carrier_eq :
  forall (F : Type) (s : F -> Prop),
    generic_adjunctive_carrier (generic_predicate_adjunctive_set F) s = s.
Proof. reflexivity. Qed.

(** Source declaration 35/35: [Set.adjunctiveSet_finite_iff].  The right side
    is the constructive finite-cover presentation of predicate finiteness. *)
Lemma generic_predicate_adjunctive_finite_iff :
  forall (F : Type) (s : F -> Prop),
    generic_adjunctive_finite (generic_predicate_adjunctive_set F) s <->
    exists xs : list F,
      forall p, s p -> generic_list_member p xs.
Proof. intros; split; intro H; exact H. Qed.

(** Source declaration 3/35, Source declaration 4/35, and
    Source declaration 5/35: the List, Multiset, and Finset [Adjoin]
    instances.  Source declaration 8/35, Source declaration 9/35, and
    Source declaration 10/35: their [AdjunctiveSet] instances.
    Lists provide the common finite
    enumeration model; allowing duplicates subsumes multisets, while ignoring
    duplicates subsumes finite sets, all without decidable equality. *)
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
  intros F xs. exists xs. intros p Hmem. exact Hmem.
Qed.

(** Keep the generalized conversion and finiteness interfaces pleasant to
    call even when their reducible definitions would permit Coq to infer
    additional arguments. *)
Arguments generic_adjunctive_member_carrier_iff {F S} A s p.
Arguments generic_adjunctive_subset_iff_carrier_subset {F S} A s t.
Arguments generic_adjunctive_carrier_empty_iff {F S} A p.
Arguments generic_adjunctive_carrier_adjoin_iff {F S} A s p q.
Arguments generic_adjunctive_member_add_list_iff {F S} A s xs p.
Arguments generic_adjunctive_from_list_as_add_list {F S} A xs.
Arguments generic_adjunctive_member_from_list_iff {F S} A xs p.
Arguments generic_adjunctive_finite_of_subset {F S} A s t _ _.
Arguments generic_adjunctive_adjoin_finite {F S} A s q _.
Arguments generic_adjunctive_adjoin_finite_iff {F S} A s q.
Arguments generic_adjunctive_add_list_finite {F S} A s xs _.
Arguments generic_adjunctive_from_list_finite {F S} A xs.
