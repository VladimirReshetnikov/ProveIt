(**
  Generic one-sided classical sequent calculi.

  This first tranche ports declarations 1--15 of the forty-three active
  declarations in the pinned Foundation module [Logic/Calculus.lean].  The
  calculus is Type-valued, so derivations retain their computational content.

  Foundation assumes De Morgan and involutive-negation type classes at the
  namespace boundary.  None of the first fifteen declarations uses those
  laws: identity and cut merely mention the raw negation operation.  Their
  Coq counterparts therefore require only [generic_connectives], a strictly
  weaker and more reusable interface.

  List inclusion is duplicate-insensitive, exactly as Lean's [List.Subset].
  The local universe-polymorphic membership predicate is inherited from
  [GenericAdjunctiveSet].  A small library of membership lemmas centralizes
  every exchange, weakening, and contraction side condition.

  The source proves its folded-disjunction rule with cut.  Here contraction
  first rotates the head behind the tail, recursion folds the tail, exchange
  restores the head, and the primitive disjunction rule finishes.  Thus the
  result is strengthened to every cut-free one-sided calculus.
*)

From Stdlib Require Import Lists.List.
From FoundationModal Require Import GenericSemantics GenericAdjunctiveSet.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** Pointwise, duplicate-insensitive list inclusion. *)
Definition generic_list_subset {A : Type} (xs ys : list A) : Prop :=
  forall x, generic_list_member x xs -> generic_list_member x ys.

Lemma generic_list_member_app_iff :
  forall (A : Type) (x : A) (xs ys : list A),
    generic_list_member x (xs ++ ys) <->
    generic_list_member x xs \/ generic_list_member x ys.
Proof.
  intros A x xs; induction xs as [|y xs IH]; intro ys; simpl.
  - split; [now right | intros [H | H]; [contradiction | exact H]].
  - rewrite IH. tauto.
Qed.

Lemma generic_list_subset_refl :
  forall (A : Type) (xs : list A), generic_list_subset xs xs.
Proof. intros A xs x Hx; exact Hx. Qed.

Lemma generic_list_subset_trans :
  forall (A : Type) (xs ys zs : list A),
    generic_list_subset xs ys ->
    generic_list_subset ys zs ->
    generic_list_subset xs zs.
Proof. intros A xs ys zs Hxy Hyz x Hx; exact (Hyz x (Hxy x Hx)). Qed.

Lemma generic_list_subset_cons_append_right :
  forall (A : Type) (x : A) (xs ys : list A),
    generic_list_subset (x :: xs) (x :: xs ++ ys).
Proof.
  intros A x xs ys z [Hz | Hz].
  - now left.
  - right. apply (proj2 (@generic_list_member_app_iff A z xs ys)).
    now left.
Qed.

Lemma generic_list_subset_cons_append_left :
  forall (A : Type) (x : A) (xs ys : list A),
    generic_list_subset (x :: ys) (x :: xs ++ ys).
Proof.
  intros A x xs ys z [Hz | Hz].
  - now left.
  - right. apply (proj2 (@generic_list_member_app_iff A z xs ys)).
    now right.
Qed.

Lemma generic_list_subset_rotate :
  forall (A : Type) (x : A) (xs : list A),
    generic_list_subset (x :: xs) (xs ++ [x]).
Proof.
  intros A x xs z [Hz | Hz].
  - apply (proj2 (@generic_list_member_app_iff A z xs [x])).
    right. now left.
  - apply (proj2 (@generic_list_member_app_iff A z xs [x])).
    now left.
Qed.

Lemma generic_list_subset_swap_two :
  forall (A : Type) (x y : A) (xs : list A),
    generic_list_subset (y :: x :: xs) (x :: y :: xs).
Proof.
  intros A x y xs z [Hz | [Hz | Hz]].
  - right. now left.
  - now left.
  - right. now right.
Qed.

Lemma generic_list_subset_move_third :
  forall (A : Type) (x y z : A) (xs : list A),
    generic_list_subset (z :: x :: y :: xs) (x :: y :: z :: xs).
Proof.
  intros A x y z xs a [Ha | [Ha | [Ha | Ha]]].
  - right. right. now left.
  - now left.
  - right. now left.
  - right. right. now right.
Qed.

Lemma generic_list_subset_move_fourth :
  forall (A : Type) (w x y z : A) (xs : list A),
    generic_list_subset (w :: x :: y :: z :: xs)
                        (x :: y :: z :: w :: xs).
Proof.
  intros A w x y z xs a [Ha | [Ha | [Ha | [Ha | Ha]]]].
  - right. right. right. now left.
  - now left.
  - right. now left.
  - right. right. now left.
  - right. right. right. now right.
Qed.

Lemma generic_list_subset_rotate_across :
  forall (A : Type) (x : A) (xs ys : list A),
    generic_list_subset ((x :: xs) ++ ys) (xs ++ x :: ys).
Proof.
  intros A x xs ys a Ha.
  apply (proj1 (@generic_list_member_app_iff A a (x :: xs) ys)) in Ha.
  apply (proj2 (@generic_list_member_app_iff A a xs (x :: ys))).
  destruct Ha as [[Ha | Ha] | Ha].
  - right. now left.
  - now left.
  - right. now right.
Qed.

(** Source declaration 1/43: [OneSidedLK].  The record stores primitive
    derivation constructors and no equations between connectives. *)
Record generic_one_sided_lk {F : Type}
    (C : generic_connectives F) (D : list F -> Type) : Type := {
  generic_lk_identity :
    forall p, D [p; generic_neg C p];
  generic_lk_contraction :
    forall delta gamma,
      D delta -> generic_list_subset delta gamma -> D gamma;
  generic_lk_verum :
    D [generic_top C];
  generic_lk_and :
    forall p q gamma,
      D (p :: gamma) -> D (q :: gamma) ->
      D (generic_and C p q :: gamma);
  generic_lk_or :
    forall p q gamma,
      D (p :: q :: gamma) ->
      D (generic_or C p q :: gamma)
}.

Arguments generic_lk_identity {F C D} _ _.
Arguments generic_lk_contraction {F C D} _ _ _ _ _.
Arguments generic_lk_verum {F C D} _.
Arguments generic_lk_and {F C D} _ _ _ _ _ _.
Arguments generic_lk_or {F C D} _ _ _ _ _.

(** Source declaration 2/43: [OneSidedLK.Cut]. *)
Record generic_one_sided_lk_cut {F : Type}
    (C : generic_connectives F) (D : list F -> Type) : Type := {
  generic_lk_cut_base : generic_one_sided_lk C D;
  generic_lk_cut_raw :
    forall p gamma delta,
      D (p :: gamma) ->
      D (generic_neg C p :: delta) ->
      D (gamma ++ delta)
}.

Arguments generic_lk_cut_base {F C D} _.
Arguments generic_lk_cut_raw {F C D} _ _ _ _ _ _.

(** Source declaration 3/43: [OneSidedLK.cast]. *)
Definition generic_lk_cast {F : Type} (D : list F -> Type)
    {gamma delta : list F} (b : D gamma) (e : gamma = delta) : D delta :=
  match e with
  | eq_refl => b
  end.

(** Source declaration 4/43: [OneSidedLK.contra]. *)
Definition generic_lk_contra {F : Type} {C : generic_connectives F}
    {D : list F -> Type} (H : generic_one_sided_lk C D)
    {gamma delta : list F} (d : D gamma)
    (h : generic_list_subset gamma delta) : D delta :=
  generic_lk_contraction H gamma delta d h.

(** Source declaration 5/43: [OneSidedLK.rotate]. *)
Definition generic_lk_rotate {F : Type} {C : generic_connectives F}
    {D : list F -> Type} (H : generic_one_sided_lk C D)
    {p : F} {gamma : list F} (d : D (p :: gamma)) :
    D (gamma ++ [p]) :=
  generic_lk_contra H d (@generic_list_subset_rotate F p gamma).

(** Source declaration 6/43: [OneSidedLK.close]. *)
Definition generic_lk_close {F : Type} {C : generic_connectives F}
    {D : list F -> Type} (H : generic_one_sided_lk C D)
    (p : F) {gamma : list F}
    (hp : generic_list_member p gamma)
    (hn : generic_list_member (generic_neg C p) gamma) : D gamma.
Proof.
  apply (generic_lk_contra H (generic_lk_identity H p)).
  intros q [hq | [hq | hq]].
  - now subst q.
  - now subst q.
  - contradiction.
Defined.

(** Source declaration 7/43: [OneSidedLK.top]. *)
Definition generic_lk_top {F : Type} {C : generic_connectives F}
    {D : list F -> Type} (H : generic_one_sided_lk C D)
    {gamma : list F}
    (htop : generic_list_member (generic_top C) gamma) : D gamma.
Proof.
  apply (generic_lk_contra H (generic_lk_verum H)).
  intros q [hq | hq].
  - now subst q.
  - contradiction.
Defined.

(** Source declaration 8/43: [OneSidedLK.tensor]. *)
Definition generic_lk_tensor {F : Type} {C : generic_connectives F}
    {D : list F -> Type} (H : generic_one_sided_lk C D)
    {p q : F} {gamma delta : list F}
    (dp : D (p :: gamma)) (dq : D (q :: delta)) :
    D (generic_and C p q :: gamma ++ delta) :=
  generic_lk_and H p q (gamma ++ delta)
    (generic_lk_contra H dp
      (@generic_list_subset_cons_append_right F p gamma delta))
    (generic_lk_contra H dq
      (@generic_list_subset_cons_append_left F q gamma delta)).

(** Source declaration 9/43: [OneSidedLK.swap₁]. *)
Definition generic_lk_swap1 {F : Type} {C : generic_connectives F}
    {D : list F -> Type} (H : generic_one_sided_lk C D)
    {p1 p2 : F} {gamma : list F} (d : D (p2 :: p1 :: gamma)) :
    D (p1 :: p2 :: gamma) :=
  generic_lk_contra H d (@generic_list_subset_swap_two F p1 p2 gamma).

(** Source declaration 10/43: [OneSidedLK.swap₂]. *)
Definition generic_lk_swap2 {F : Type} {C : generic_connectives F}
    {D : list F -> Type} (H : generic_one_sided_lk C D)
    {p1 p2 p3 : F} {gamma : list F}
    (d : D (p3 :: p1 :: p2 :: gamma)) :
    D (p1 :: p2 :: p3 :: gamma) :=
  generic_lk_contra H d
    (@generic_list_subset_move_third F p1 p2 p3 gamma).

(** Source declaration 11/43: [OneSidedLK.swap₃]. *)
Definition generic_lk_swap3 {F : Type} {C : generic_connectives F}
    {D : list F -> Type} (H : generic_one_sided_lk C D)
    {p1 p2 p3 p4 : F} {gamma : list F}
    (d : D (p4 :: p1 :: p2 :: p3 :: gamma)) :
    D (p1 :: p2 :: p3 :: p4 :: gamma) :=
  generic_lk_contra H d
    (@generic_list_subset_move_fourth F p4 p1 p2 p3 gamma).

(** Source declaration 12/43: alias [OneSidedLK.cut]. *)
Definition generic_lk_cut := @generic_lk_cut_raw.

(** Source declaration 13/43: [OneSidedLK.eCut]. *)
Definition generic_lk_extended_cut {F : Type}
    {C : generic_connectives F} {D : list F -> Type}
    (H : generic_one_sided_lk_cut C D)
    {p q : F} {gamma delta : list F}
    (dp : D (p :: gamma)) (dq : D (q :: delta))
    (e : generic_neg C p = q) : D (gamma ++ delta) :=
  match e as e0 in (_ = q0)
        return D (q0 :: delta) -> D (gamma ++ delta) with
  | eq_refl => fun dn => generic_lk_cut_raw H p gamma delta dp dn
  end dq.

(** Source declaration 14/43: [OneSidedLK.disj₂].  This strengthened form
    does not require cut. *)
Fixpoint generic_lk_disj2 {F : Type} {C : generic_connectives F}
    {D : list F -> Type} (H : generic_one_sided_lk C D)
    (gamma : list F) {struct gamma} :
    forall delta, D (gamma ++ delta) ->
      D (generic_list_disj2 C gamma :: delta) :=
  match gamma as gamma0 return
      forall delta,
        D (gamma0 ++ delta) ->
        D (generic_list_disj2 C gamma0 :: delta)
  with
  | [] => fun delta d =>
      @generic_lk_contra F C D H delta
        (generic_bottom C :: delta) d
        (fun p hp => or_intror hp)
  | p :: tail => fun delta d =>
      let dtail :=
        @generic_lk_disj2 F C D H tail (p :: delta)
          (generic_lk_contra H d
            (@generic_list_subset_rotate_across F p tail delta)) in
      match tail as tail0 return
          D ((p :: tail0) ++ delta) ->
          D (generic_list_disj2 C tail0 :: p :: delta) ->
          D (generic_list_disj2 C (p :: tail0) :: delta)
      with
      | [] => fun d0 _ => d0
      | q :: rest => fun _ dtail0 =>
          generic_lk_or H p (generic_list_disj2 C (q :: rest)) delta
            (generic_lk_swap1 H dtail0)
      end d dtail
  end.

(** Source declaration 15/43: [OneSidedLK.conj₂]. *)
Fixpoint generic_lk_conj2 {F : Type} {C : generic_connectives F}
    {D : list F -> Type} (H : generic_one_sided_lk C D)
    (gamma : list F) {struct gamma} :
    forall delta,
      (forall p, generic_list_member p gamma -> D (p :: delta)) ->
      D (generic_list_conj2 C gamma :: delta) :=
  match gamma as gamma0 return
      forall delta,
        (forall p, generic_list_member p gamma0 -> D (p :: delta)) ->
        D (generic_list_conj2 C gamma0 :: delta)
  with
  | [] => fun delta _ =>
      @generic_lk_contra F C D H [generic_top C]
        (generic_top C :: delta) (generic_lk_verum H)
        (fun p hp =>
          match hp with
          | or_introl e => or_introl e
          | or_intror hfalse => False_rect _ hfalse
          end)
  | p :: tail => fun delta d =>
      let dtail :=
        @generic_lk_conj2 F C D H tail delta
          (fun r hr => d r (or_intror hr)) in
      match tail as tail0 return
          (forall r, generic_list_member r (p :: tail0) ->
                     D (r :: delta)) ->
          D (generic_list_conj2 C tail0 :: delta) ->
          D (generic_list_conj2 C (p :: tail0) :: delta)
      with
      | [] => fun d0 _ => d0 p (or_introl eq_refl)
      | q :: rest => fun d0 dtail0 =>
          generic_lk_and H p (generic_list_conj2 C (q :: rest)) delta
            (d0 p (or_introl eq_refl)) dtail0
      end d dtail
  end.

Arguments generic_lk_cast {F} D {gamma delta} _ _.
Arguments generic_lk_contra {F C D} H {gamma delta} _ _.
Arguments generic_lk_rotate {F C D} H {p gamma} _.
Arguments generic_lk_close {F C D} H p {gamma} _ _.
Arguments generic_lk_top {F C D} H {gamma} _.
Arguments generic_lk_tensor {F C D} H {p q gamma delta} _ _.
Arguments generic_lk_swap1 {F C D} H {p1 p2 gamma} _.
Arguments generic_lk_swap2 {F C D} H {p1 p2 p3 gamma} _.
Arguments generic_lk_swap3 {F C D} H {p1 p2 p3 p4 gamma} _.
Arguments generic_lk_extended_cut {F C D} H
  {p q gamma delta} _ _ _.
Arguments generic_lk_disj2 {F C D} H gamma delta _.
Arguments generic_lk_conj2 {F C D} H gamma delta _.
