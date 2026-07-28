(**
  Generic one-sided classical sequent calculi.

  This module currently ports declarations 1--42 of the forty-three active
  declarations in the pinned Foundation module [Logic/Calculus.lean].  The
  calculus and its principal entailments are Type-valued, so derivations
  retain their computational content.

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

  Contextual entailment is represented by a dependent finite witness: its
  formulas carry pointwise evidence that they belong to the ambient
  adjunctive set, while the corresponding one-sided derivation remains in
  [Type].  The representation and structural transport require only an
  arbitrary negation operation; the axiom adapter adds precisely the base LK
  dictionary needed to derive identity.
*)

From Stdlib Require Import Lists.List.
From FoundationModal Require Import
  GenericSemantics GenericAdjunctiveSet GenericEntailment.

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

(** * Entailment adapters *)

(** A universe-polymorphic equivalence of raw proof types.  The laws are
    retained because Foundation's [Equiv] is stronger than merely having a
    map in each direction. *)
Record generic_type_equiv (A B : Type) : Type := {
  generic_equiv_to : A -> B;
  generic_equiv_from : B -> A;
  generic_equiv_to_from :
    forall y, generic_equiv_to (generic_equiv_from y) = y;
  generic_equiv_from_to :
    forall x, generic_equiv_from (generic_equiv_to x) = x
}.

Arguments generic_equiv_to {A B} _ _.
Arguments generic_equiv_from {A B} _ _.
Arguments generic_equiv_to_from {A B} _ _.
Arguments generic_equiv_from_to {A B} _ _.

(** Each connective equation is exposed independently so downstream rules
    can state exactly the normalization laws they use. *)
Definition generic_neg_involutive_law {F : Type}
    (C : generic_connectives F) : Prop :=
  forall p, generic_neg C (generic_neg C p) = p.

Definition generic_neg_top_law {F : Type}
    (C : generic_connectives F) : Prop :=
  generic_neg C (generic_top C) = generic_bottom C.

Definition generic_neg_bottom_law {F : Type}
    (C : generic_connectives F) : Prop :=
  generic_neg C (generic_bottom C) = generic_top C.

Definition generic_imp_as_or_law {F : Type}
    (C : generic_connectives F) : Prop :=
  forall p q,
    generic_imp C p q = generic_or C (generic_neg C p) q.

Definition generic_neg_and_law {F : Type}
    (C : generic_connectives F) : Prop :=
  forall p q,
    generic_neg C (generic_and C p q) =
    generic_or C (generic_neg C p) (generic_neg C q).

Definition generic_neg_or_law {F : Type}
    (C : generic_connectives F) : Prop :=
  forall p q,
    generic_neg C (generic_or C p q) =
    generic_and C (generic_neg C p) (generic_neg C q).

(** Infrastructure corresponding to Foundation's imported raw modus-ponens
    capability. *)
Record generic_modus_ponens {S F : Type}
    (E : generic_entailment S F)
    (C : generic_connectives F) (s : S) : Type := {
  generic_modus_ponens_raw :
    forall p q,
      generic_proof E s (generic_imp C p q) ->
      generic_proof E s p ->
      generic_proof E s q
}.

Arguments generic_modus_ponens_raw {S F E C s} _ _ _ _ _.

(** Source declaration 16/43: [OneSidedLK.PrincipalEntailment]. *)
Record generic_principal_entailment {P F : Type}
    (E : generic_entailment P F)
    (D : list F -> Type) (theory : P) : Type := {
  generic_principal_equiv :
    forall p, generic_type_equiv (generic_proof E theory p) (D [p])
}.

Arguments generic_principal_equiv {P F E D theory} _ _.

(** Source declaration 17/43: [PrincipalEntailment.provable_iff].  As in the
    source, this result is independent of every connective operation. *)
Lemma generic_principal_provable_iff :
  forall (P F : Type) (E : generic_entailment P F)
         (D : list F -> Type) (theory : P),
    generic_principal_entailment E D theory ->
    forall p,
      generic_provable E theory p <-> inhabited (D [p]).
Proof.
  intros P F E D theory Hprincipal p; split.
  - intros [b]. constructor.
    exact (generic_equiv_to (generic_principal_equiv Hprincipal p) b).
  - intros [d]. constructor.
    exact (generic_equiv_from (generic_principal_equiv Hprincipal p) d).
Qed.

(** Source declaration 18/43: the principal [Entailment.ModusPonens]
    instance.  Only implication-as-disjunction, negated-disjunction De Morgan,
    and involutive negation are required. *)
Definition generic_principal_modus_ponens {P F : Type}
    {E : generic_entailment P F} (C : generic_connectives F)
    {D : list F -> Type} {theory : P}
    (Hprincipal : generic_principal_entailment E D theory)
    (Hinv : generic_neg_involutive_law C)
    (Himp : generic_imp_as_or_law C)
    (Hneg_or : generic_neg_or_law C)
    (K : generic_one_sided_lk_cut C D) :
    generic_modus_ponens E C theory.
Proof.
  constructor. intros p q bpq bp.
  apply (generic_equiv_from (generic_principal_equiv Hprincipal q)).
  pose proof (generic_lk_tensor (generic_lk_cut_base K)
    (generic_lk_identity (generic_lk_cut_base K) p)
    (generic_lk_identity (generic_lk_cut_base K) (generic_neg C q)))
    as dcontra.
  assert (econtra :
    generic_and C p (generic_neg C q) ::
      [generic_neg C p; generic_neg C (generic_neg C q)] =
    [generic_neg C (generic_imp C p q); generic_neg C p; q]).
  { simpl. rewrite (Hinv q), (Himp p q), (Hneg_or (generic_neg C p) q).
    rewrite (Hinv p). reflexivity. }
  pose proof (@generic_lk_cast F D _ _ dcontra econtra) as dcontra'.
  pose proof (generic_equiv_to
    (generic_principal_equiv Hprincipal (generic_imp C p q)) bpq) as dpq.
  pose proof (generic_equiv_to
    (generic_principal_equiv Hprincipal p) bp) as dp.
  pose proof (generic_lk_cut_raw K (generic_imp C p q) []
    [generic_neg C p; q] dpq dcontra') as d1.
  pose proof (generic_lk_cut_raw K p [] [q] dp d1) as d2.
  exact d2.
Defined.

(** Formula shapes from Foundation's imported classical-entailment
    interface.  Keeping them explicit makes declaration 19 usable for an
    arbitrary formula representation. *)
Definition generic_formula_iff {F : Type}
    (C : generic_connectives F) (p q : F) : F :=
  generic_and C (generic_imp C p q) (generic_imp C q p).

Definition generic_axiom_neg_equiv {F : Type}
    (C : generic_connectives F) (p : F) : F :=
  generic_formula_iff C (generic_neg C p)
    (generic_imp C p (generic_bottom C)).

Definition generic_axiom_K {F : Type}
    (C : generic_connectives F) (p q : F) : F :=
  generic_imp C p (generic_imp C q p).

Definition generic_axiom_S {F : Type}
    (C : generic_connectives F) (p q r : F) : F :=
  generic_imp C (generic_imp C p (generic_imp C q r))
    (generic_imp C (generic_imp C p q) (generic_imp C p r)).

Definition generic_axiom_and1 {F : Type}
    (C : generic_connectives F) (p q : F) : F :=
  generic_imp C (generic_and C p q) p.

Definition generic_axiom_and2 {F : Type}
    (C : generic_connectives F) (p q : F) : F :=
  generic_imp C (generic_and C p q) q.

Definition generic_axiom_and3 {F : Type}
    (C : generic_connectives F) (p q : F) : F :=
  generic_imp C p (generic_imp C q (generic_and C p q)).

Definition generic_axiom_or1 {F : Type}
    (C : generic_connectives F) (p q : F) : F :=
  generic_imp C p (generic_or C p q).

Definition generic_axiom_or2 {F : Type}
    (C : generic_connectives F) (p q : F) : F :=
  generic_imp C q (generic_or C p q).

Definition generic_axiom_or3 {F : Type}
    (C : generic_connectives F) (p q r : F) : F :=
  generic_imp C (generic_imp C p r)
    (generic_imp C (generic_imp C q r)
      (generic_imp C (generic_or C p q) r)).

Definition generic_axiom_dne {F : Type}
    (C : generic_connectives F) (p : F) : F :=
  generic_imp C (generic_neg C (generic_neg C p)) p.

Record generic_classical_entailment {S F : Type}
    (E : generic_entailment S F)
    (C : generic_connectives F) (s : S) : Type := {
  generic_classical_mdp : generic_modus_ponens E C s;
  generic_classical_neg_equiv :
    forall p, generic_proof E s (generic_axiom_neg_equiv C p);
  generic_classical_verum :
    generic_proof E s (generic_top C);
  generic_classical_K :
    forall p q, generic_proof E s (generic_axiom_K C p q);
  generic_classical_S :
    forall p q r, generic_proof E s (generic_axiom_S C p q r);
  generic_classical_and1 :
    forall p q, generic_proof E s (generic_axiom_and1 C p q);
  generic_classical_and2 :
    forall p q, generic_proof E s (generic_axiom_and2 C p q);
  generic_classical_and3 :
    forall p q, generic_proof E s (generic_axiom_and3 C p q);
  generic_classical_or1 :
    forall p q, generic_proof E s (generic_axiom_or1 C p q);
  generic_classical_or2 :
    forall p q, generic_proof E s (generic_axiom_or2 C p q);
  generic_classical_or3 :
    forall p q r, generic_proof E s (generic_axiom_or3 C p q r);
  generic_classical_dne :
    forall p, generic_proof E s (generic_axiom_dne C p)
}.

(** These eleven sequents are shared by declarations 19 and 39.  Factoring
    them keeps both entailment adapters as transparent transports rather than
    duplicating the nontrivial LK derivations. *)
Record generic_lk_classical_derivations {F : Type}
    (C : generic_connectives F) (D : list F -> Type) : Type := {
  generic_lk_classical_neg_equiv :
    forall p, D [generic_axiom_neg_equiv C p];
  generic_lk_classical_verum : D [generic_top C];
  generic_lk_classical_K : forall p q, D [generic_axiom_K C p q];
  generic_lk_classical_S : forall p q r, D [generic_axiom_S C p q r];
  generic_lk_classical_and1 : forall p q, D [generic_axiom_and1 C p q];
  generic_lk_classical_and2 : forall p q, D [generic_axiom_and2 C p q];
  generic_lk_classical_and3 : forall p q, D [generic_axiom_and3 C p q];
  generic_lk_classical_or1 : forall p q, D [generic_axiom_or1 C p q];
  generic_lk_classical_or2 : forall p q, D [generic_axiom_or2 C p q];
  generic_lk_classical_or3 : forall p q r, D [generic_axiom_or3 C p q r];
  generic_lk_classical_dne : forall p, D [generic_axiom_dne C p]
}.

(** Construct all source classical axioms once at the sequent level.  This
    is object-logic classicality proved constructively; it assumes no
    meta-level excluded middle. *)
Definition generic_lk_classical {F : Type}
    (C : generic_connectives F) (D : list F -> Type)
    (Hinv : generic_neg_involutive_law C)
    (Hneg_bottom : generic_neg_bottom_law C)
    (Himp : generic_imp_as_or_law C)
    (Hneg_and : generic_neg_and_law C)
    (Hneg_or : generic_neg_or_law C)
    (K : generic_one_sided_lk C D) :
    generic_lk_classical_derivations C D.
Proof.
  constructor.
  - intro p.
    assert (dleft : D [generic_or C p
      (generic_or C (generic_neg C p) (generic_bottom C))]).
    { apply (generic_lk_or K p
        (generic_or C (generic_neg C p) (generic_bottom C)) []).
      apply (generic_lk_swap1 K).
      apply (generic_lk_or K (generic_neg C p) (generic_bottom C) [p]).
      apply (generic_lk_close K p).
      + now right; right; left.
      + now left. }
    assert (dright : D [generic_or C
      (generic_and C p (generic_top C)) (generic_neg C p)]).
    { apply (generic_lk_or K
        (generic_and C p (generic_top C)) (generic_neg C p) []).
      apply (generic_lk_and K p (generic_top C) [generic_neg C p]).
      + exact (generic_lk_identity K p).
      + apply (generic_lk_top K). now left. }
    pose proof (generic_lk_and K
      (generic_or C p (generic_or C (generic_neg C p) (generic_bottom C)))
      (generic_or C (generic_and C p (generic_top C)) (generic_neg C p))
      [] dleft dright) as d.
    apply (@generic_lk_cast F D _ _ d).
    unfold generic_axiom_neg_equiv, generic_formula_iff.
    rewrite !Himp, (Hinv p), Hneg_or, (Hinv p), Hneg_bottom.
    reflexivity.
  - exact (generic_lk_verum K).
  - intros p q.
    pose proof (generic_lk_close K p
      (gamma := [generic_neg C q; p; generic_neg C p])
      (or_intror (or_introl eq_refl))
      (or_intror (or_intror (or_introl eq_refl)))) as d.
    pose proof (generic_lk_or K (generic_neg C q) p
      [generic_neg C p] d) as d1.
    pose proof (generic_lk_swap1 K d1) as d2.
    pose proof (generic_lk_or K (generic_neg C p)
      (generic_or C (generic_neg C q) p) [] d2) as d3.
    apply (@generic_lk_cast F D _ _ d3).
    unfold generic_axiom_K. rewrite !Himp. reflexivity.
  - intros p q r.
    set (A := generic_and C p (generic_and C q (generic_neg C r))).
    set (B := generic_and C p (generic_neg C q)).
    set (N := generic_neg C p).
    assert (dB : D [B; q; N; r]).
    { unfold B, N.
      apply (generic_lk_and K p (generic_neg C q) [q; generic_neg C p; r]).
      + apply (generic_lk_close K p); [now left | now right; right; left].
      + apply (generic_lk_close K q); [now right; left | now left]. }
    pose proof (generic_lk_swap3 K dB) as dq.
    assert (dnr : D [generic_neg C r; N; r; B]).
    { apply (generic_lk_close K r); [now right; right; left | now left]. }
    assert (dright : D [generic_and C q (generic_neg C r); N; r; B]).
    { exact (generic_lk_and K q (generic_neg C r) [N; r; B] dq dnr). }
    assert (dp : D [p; N; r; B]).
    { apply (generic_lk_close K p); [now left | now right; left]. }
    assert (dA : D [A; N; r; B]).
    { unfold A. exact (generic_lk_and K p
        (generic_and C q (generic_neg C r)) [N; r; B] dp dright). }
    pose proof (generic_lk_swap3 K dA) as d0.
    pose proof (generic_lk_or K N r [B; A] d0) as d1.
    pose proof (generic_lk_swap1 K d1) as d2.
    pose proof (generic_lk_or K B (generic_or C N r) [A] d2) as d3.
    pose proof (generic_lk_swap1 K d3) as d4.
    pose proof (generic_lk_or K A
      (generic_or C B (generic_or C N r)) [] d4) as d5.
    apply (@generic_lk_cast F D _ _ d5).
    unfold generic_axiom_S, A, B, N.
    rewrite !Himp, !Hneg_or, !Hinv. reflexivity.
  - intros p q.
    pose proof (generic_lk_close K p
      (gamma := [generic_neg C p; generic_neg C q; p])
      (or_intror (or_intror (or_introl eq_refl)))
      (or_introl eq_refl)) as d.
    pose proof (generic_lk_or K (generic_neg C p) (generic_neg C q) [p] d)
      as d1.
    pose proof (generic_lk_or K
      (generic_or C (generic_neg C p) (generic_neg C q)) p [] d1)
      as d2.
    apply (@generic_lk_cast F D _ _ d2).
    unfold generic_axiom_and1. rewrite Himp, Hneg_and. reflexivity.
  - intros p q.
    pose proof (generic_lk_close K q
      (gamma := [generic_neg C p; generic_neg C q; q])
      (or_intror (or_intror (or_introl eq_refl)))
      (or_intror (or_introl eq_refl))) as d.
    pose proof (generic_lk_or K (generic_neg C p) (generic_neg C q) [q] d)
      as d1.
    pose proof (generic_lk_or K
      (generic_or C (generic_neg C p) (generic_neg C q)) q [] d1)
      as d2.
    apply (@generic_lk_cast F D _ _ d2).
    unfold generic_axiom_and2. rewrite Himp, Hneg_and. reflexivity.
  - intros p q.
    assert (dand : D [generic_and C p q; generic_neg C q; generic_neg C p]).
    { apply (generic_lk_and K p q [generic_neg C q; generic_neg C p]).
      + apply (generic_lk_close K p); [now left | now right; right; left].
      + apply (generic_lk_close K q); [now left | now right; left]. }
    pose proof (generic_lk_swap1 K dand) as d1.
    pose proof (generic_lk_or K (generic_neg C q) (generic_and C p q)
      [generic_neg C p] d1) as d2.
    pose proof (generic_lk_swap1 K d2) as d3.
    pose proof (generic_lk_or K (generic_neg C p)
      (generic_or C (generic_neg C q) (generic_and C p q)) [] d3)
      as d4.
    apply (@generic_lk_cast F D _ _ d4).
    unfold generic_axiom_and3. rewrite !Himp. reflexivity.
  - intros p q.
    apply (@generic_lk_cast F D _ _
      (generic_lk_or K (generic_neg C p) (generic_or C p q) []
        (generic_lk_swap1 K
          (generic_lk_or K p q [generic_neg C p]
            (generic_lk_close K p
              (gamma := [p; q; generic_neg C p])
              (or_introl eq_refl)
              (or_intror (or_intror (or_introl eq_refl)))))))).
    unfold generic_axiom_or1. rewrite Himp. reflexivity.
  - intros p q.
    apply (@generic_lk_cast F D _ _
      (generic_lk_or K (generic_neg C q) (generic_or C p q) []
        (generic_lk_swap1 K
          (generic_lk_or K p q [generic_neg C q]
            (generic_lk_close K q
              (gamma := [p; q; generic_neg C q])
              (or_intror (or_introl eq_refl))
              (or_intror (or_intror (or_introl eq_refl)))))))).
    unfold generic_axiom_or2. rewrite Himp. reflexivity.
  - intros p q r.
    set (A := generic_and C p (generic_neg C r)).
    set (B := generic_and C q (generic_neg C r)).
    set (N := generic_and C (generic_neg C p) (generic_neg C q)).
    assert (dA : D [A; generic_neg C p; r; B]).
    { unfold A.
      apply (generic_lk_and K p (generic_neg C r)
        [generic_neg C p; r; B]).
      + apply (generic_lk_close K p); [now left | now right; left].
      + apply (generic_lk_close K r); [now right; right; left | now left]. }
    pose proof (generic_lk_swap3 K dA) as dnp.
    assert (dB : D [B; generic_neg C q; r; A]).
    { unfold B.
      apply (generic_lk_and K q (generic_neg C r)
        [generic_neg C q; r; A]).
      + apply (generic_lk_close K q); [now left | now right; left].
      + apply (generic_lk_close K r); [now right; right; left | now left]. }
    pose proof (generic_lk_swap2 K dB) as dnq.
    pose proof (generic_lk_and K (generic_neg C p) (generic_neg C q)
      [r; B; A] dnp dnq) as dN.
    pose proof (generic_lk_or K N r [B; A] dN) as d1.
    pose proof (generic_lk_swap1 K d1) as d2.
    pose proof (generic_lk_or K B (generic_or C N r) [A] d2) as d3.
    pose proof (generic_lk_swap1 K d3) as d4.
    pose proof (generic_lk_or K A
      (generic_or C B (generic_or C N r)) [] d4) as d5.
    apply (@generic_lk_cast F D _ _ d5).
    unfold generic_axiom_or3, A, B, N.
    rewrite !Himp, !Hneg_or, !Hinv. reflexivity.
  - intro p.
    pose proof (generic_lk_or K (generic_neg C p) p []
      (generic_lk_swap1 K (generic_lk_identity K p))) as d.
    apply (@generic_lk_cast F D _ _ d).
    unfold generic_axiom_dne. rewrite Himp, (Hinv (generic_neg C p)).
    reflexivity.
Defined.

(** Source declaration 19/43: the principal [Entailment.Cl] instance.  The
    eleven Hilbert sequents are constructive; Cut is used only by the bundled
    modus-ponens rule. *)
Definition generic_principal_classical {P F : Type}
    {E : generic_entailment P F} (C : generic_connectives F)
    {D : list F -> Type} {theory : P}
    (Hprincipal : generic_principal_entailment E D theory)
    (Hinv : generic_neg_involutive_law C)
    (Hneg_bottom : generic_neg_bottom_law C)
    (Himp : generic_imp_as_or_law C)
    (Hneg_and : generic_neg_and_law C)
    (Hneg_or : generic_neg_or_law C)
    (K : generic_one_sided_lk_cut C D) :
    generic_classical_entailment E C theory.
Proof.
  pose proof (@generic_lk_classical F C D Hinv Hneg_bottom Himp
    Hneg_and Hneg_or (generic_lk_cut_base K)) as Hclassical.
  constructor.
  - exact (@generic_principal_modus_ponens P F E C D theory Hprincipal
      Hinv Himp Hneg_or K).
  - intro p. apply (generic_equiv_from
      (generic_principal_equiv Hprincipal (generic_axiom_neg_equiv C p))).
    exact (generic_lk_classical_neg_equiv Hclassical p).
  - apply (generic_equiv_from
      (generic_principal_equiv Hprincipal (generic_top C))).
    exact (generic_lk_classical_verum Hclassical).
  - intros p q. apply (generic_equiv_from
      (generic_principal_equiv Hprincipal (generic_axiom_K C p q))).
    exact (generic_lk_classical_K Hclassical p q).
  - intros p q r. apply (generic_equiv_from
      (generic_principal_equiv Hprincipal (generic_axiom_S C p q r))).
    exact (generic_lk_classical_S Hclassical p q r).
  - intros p q. apply (generic_equiv_from
      (generic_principal_equiv Hprincipal (generic_axiom_and1 C p q))).
    exact (generic_lk_classical_and1 Hclassical p q).
  - intros p q. apply (generic_equiv_from
      (generic_principal_equiv Hprincipal (generic_axiom_and2 C p q))).
    exact (generic_lk_classical_and2 Hclassical p q).
  - intros p q. apply (generic_equiv_from
      (generic_principal_equiv Hprincipal (generic_axiom_and3 C p q))).
    exact (generic_lk_classical_and3 Hclassical p q).
  - intros p q. apply (generic_equiv_from
      (generic_principal_equiv Hprincipal (generic_axiom_or1 C p q))).
    exact (generic_lk_classical_or1 Hclassical p q).
  - intros p q. apply (generic_equiv_from
      (generic_principal_equiv Hprincipal (generic_axiom_or2 C p q))).
    exact (generic_lk_classical_or2 Hclassical p q).
  - intros p q r. apply (generic_equiv_from
      (generic_principal_equiv Hprincipal (generic_axiom_or3 C p q r))).
    exact (generic_lk_classical_or3 Hclassical p q r).
  - intro p. apply (generic_equiv_from
      (generic_principal_equiv Hprincipal (generic_axiom_dne C p))).
    exact (generic_lk_classical_dne Hclassical p).
Defined.

(** Membership in a mapped list has a source witness propositionally; no
    injectivity or decidable equality is needed. *)
Lemma generic_list_member_map_elim :
  forall (A B : Type) (f : A -> B) (y : B) (xs : list A),
    generic_list_member y (map f xs) ->
    exists x,
      generic_list_member x xs /\ f x = y.
Proof.
  intros A B f y xs; induction xs as [|x xs IH]; simpl.
  - contradiction.
  - intros [Hy | Hy].
    + exists x. split; [now left | now symmetry].
    + destruct (IH Hy) as [z [Hz Heq]].
      exists z. split; [now right | exact Heq].
Qed.

(** A mapped-negation membership can be reflected after one more negation.
    Unlike existential preimage extraction, this proof can be consumed while
    constructing a Type-valued derivation without eliminating Prop into Type. *)
Lemma generic_list_member_map_neg_back :
  forall (F : Type) (C : generic_connectives F),
    generic_neg_involutive_law C ->
    forall (r : F) (xs : list F),
      generic_list_member r (map (generic_neg C) xs) ->
      generic_list_member (generic_neg C r) xs.
Proof.
  intros F C Hinv r xs; induction xs as [|q qs IH]; simpl.
  - contradiction.
  - intros [Hr | Hr].
    + left. rewrite <- (Hinv q). now rewrite Hr.
    + right. exact (IH Hr).
Qed.

(** Singleton-normalized finite De Morgan for disjunction. *)
Lemma generic_neg_list_disj2 :
  forall (F : Type) (C : generic_connectives F),
    generic_neg_bottom_law C ->
    generic_neg_or_law C ->
    forall xs : list F,
      generic_neg C (generic_list_disj2 C xs) =
      generic_list_conj2 C (map (generic_neg C) xs).
Proof.
  intros F C Hneg_bottom Hneg_or xs.
  induction xs as [|p ps IH].
  - simpl. exact Hneg_bottom.
  - destruct ps as [|q qs].
    + reflexivity.
    + simpl in IH |- *. rewrite Hneg_or, IH. reflexivity.
Qed.

(** Source declaration 20/43:
    [PrincipalEntailment.derivable_iff_provable_disj]. *)
Lemma generic_principal_derivable_iff_provable_disj :
  forall (P F : Type) (E : generic_entailment P F)
         (C : generic_connectives F) (D : list F -> Type)
         (theory : P),
    generic_principal_entailment E D theory ->
    generic_neg_involutive_law C ->
    generic_neg_bottom_law C ->
    generic_neg_or_law C ->
    generic_one_sided_lk_cut C D ->
    forall gamma : list F,
      inhabited (D gamma) <->
      generic_provable E theory (generic_list_disj2 C gamma).
Proof.
  intros P F E C D theory Hprincipal Hinv Hneg_bottom Hneg_or K gamma.
  split.
  - intros [d]. constructor.
    apply (generic_equiv_from
      (generic_principal_equiv Hprincipal (generic_list_disj2 C gamma))).
    apply (generic_lk_disj2 (generic_lk_cut_base K) gamma []).
    exact (generic_lk_cast D d (eq_sym (app_nil_r gamma))).
  - intros [b].
    pose proof (generic_equiv_to
      (generic_principal_equiv Hprincipal (generic_list_disj2 C gamma)) b)
      as ddisj.
    assert (dneg :
      D (generic_list_conj2 C (map (generic_neg C) gamma) :: gamma)).
    { apply (generic_lk_conj2 (generic_lk_cut_base K)
        (map (generic_neg C) gamma) gamma).
      intros r Hr.
      apply (generic_lk_close (generic_lk_cut_base K) r
        (gamma := r :: gamma)).
      + now left.
      + right. exact (@generic_list_member_map_neg_back
          F C Hinv r gamma Hr). }
    constructor.
    exact (generic_lk_extended_cut K ddisj dneg
      (@generic_neg_list_disj2 F C Hneg_bottom Hneg_or gamma)).
Qed.

(** * Pullback along a formula translation *)

(** The one-sided kernel uses exactly these four preservation laws.  In
    particular its pullback does not depend on implication or bottom. *)
Record generic_lk_connective_hom {F G : Type}
    (CF : generic_connectives F) (CG : generic_connectives G)
    (f : G -> F) : Prop := {
  generic_lk_hom_top :
    f (generic_top CG) = generic_top CF;
  generic_lk_hom_neg :
    forall p, f (generic_neg CG p) = generic_neg CF (f p);
  generic_lk_hom_and :
    forall p q,
      f (generic_and CG p q) = generic_and CF (f p) (f q);
  generic_lk_hom_or :
    forall p q,
      f (generic_or CG p q) = generic_or CF (f p) (f q)
}.

Arguments generic_lk_hom_top {F G CF CG f} _.
Arguments generic_lk_hom_neg {F G CF CG f} _ _.
Arguments generic_lk_hom_and {F G CF CG f} _ _ _.
Arguments generic_lk_hom_or {F G CF CG f} _ _ _.

Lemma generic_list_member_map_intro :
  forall (A B : Type) (f : A -> B) (x : A) (xs : list A),
    generic_list_member x xs ->
    generic_list_member (f x) (map f xs).
Proof.
  intros A B f x xs; induction xs as [|y ys IH]; simpl.
  - contradiction.
  - intros [Hx | Hx].
    + left. now rewrite Hx.
    + right. now apply IH.
Qed.

Lemma generic_list_map_subset :
  forall (A B : Type) (f : A -> B) (xs ys : list A),
    generic_list_subset xs ys ->
    generic_list_subset (map f xs) (map f ys).
Proof.
  intros A B f xs ys Hsubset y Hy.
  destruct (@generic_list_member_map_elim A B f y xs Hy)
    as [x [Hx <-]].
  apply (@generic_list_member_map_intro A B f x ys).
  exact (Hsubset x Hx).
Qed.

(** Source declaration 21/43: [OneSidedLK.Pullback]. *)
Definition generic_lk_pullback {F G : Type}
    (D : list F -> Type) (f : G -> F) : list G -> Type :=
  fun gamma => D (map f gamma).

(** Source declaration 22/43: [Pullback.cast]. *)
Definition generic_lk_pullback_cast {F G : Type}
    (D : list F -> Type) (f : G -> F)
    {delta : list F} {gamma : list G}
    (d : D delta) (e : delta = map f gamma) :
    generic_lk_pullback D f gamma :=
  eq_rect delta D d (map f gamma) e.

(** Source declaration 23/43: [Pullback.uncast]. *)
Definition generic_lk_pullback_uncast {F G : Type}
    (D : list F -> Type) (f : G -> F)
    {delta : list F} {gamma : list G}
    (d : generic_lk_pullback D f gamma)
    (e : delta = map f gamma) : D delta :=
  eq_rect (map f gamma) D d delta (eq_sym e).

(** Source declaration 24/43: pullback [OneSidedLK] instance. *)
Definition generic_lk_pullback_one_sided {F G : Type}
    {CF : generic_connectives F} {CG : generic_connectives G}
    {D : list F -> Type} {f : G -> F}
    (Hhom : generic_lk_connective_hom CF CG f)
    (Hlk : generic_one_sided_lk CF D) :
    generic_one_sided_lk CG (generic_lk_pullback D f).
Proof.
  constructor.
  - intro p. unfold generic_lk_pullback. simpl.
    refine (generic_lk_cast D (generic_lk_identity Hlk (f p)) _).
    exact (f_equal (fun x => [f p; x])
      (eq_sym (generic_lk_hom_neg Hhom p))).
  - intros delta gamma d Hsubset.
    exact (generic_lk_contraction Hlk (map f delta) (map f gamma) d
      (@generic_list_map_subset G F f delta gamma Hsubset)).
  - unfold generic_lk_pullback. simpl.
    refine (generic_lk_cast D (generic_lk_verum Hlk) _).
    exact (f_equal (fun x => [x])
      (eq_sym (generic_lk_hom_top Hhom))).
  - intros p q gamma dp dq. unfold generic_lk_pullback in *; simpl in *.
    refine (generic_lk_cast D
      (generic_lk_and Hlk (f p) (f q) (map f gamma) dp dq) _).
    exact (f_equal (fun x => x :: map f gamma)
      (eq_sym (generic_lk_hom_and Hhom p q))).
  - intros p q gamma d. unfold generic_lk_pullback in *; simpl in *.
    refine (generic_lk_cast D
      (generic_lk_or Hlk (f p) (f q) (map f gamma) d) _).
    exact (f_equal (fun x => x :: map f gamma)
      (eq_sym (generic_lk_hom_or Hhom p q))).
Defined.

(** Source declaration 25/43: pullback [Cut] instance. *)
Definition generic_lk_pullback_cut {F G : Type}
    {CF : generic_connectives F} {CG : generic_connectives G}
    {D : list F -> Type} {f : G -> F}
    (Hhom : generic_lk_connective_hom CF CG f)
    (Hcut : generic_one_sided_lk_cut CF D) :
    generic_one_sided_lk_cut CG (generic_lk_pullback D f).
Proof.
  refine {| generic_lk_cut_base :=
      generic_lk_pullback_one_sided Hhom (generic_lk_cut_base Hcut) |}.
  intros p gamma delta dp dn.
  unfold generic_lk_pullback in *; simpl in *.
  pose (dn' := generic_lk_cast D dn
    (f_equal (fun x => x :: map f delta)
      (generic_lk_hom_neg Hhom p))).
  refine (generic_lk_cast D
    (generic_lk_cut_raw Hcut (f p) (map f gamma) (map f delta) dp dn') _).
  symmetry. apply map_app.
Defined.

(** Source declaration 26/43: pullback [PrincipalEntailment] instance.
    No connective-preservation law is needed because singleton mapping is
    definitional. *)
Definition generic_lk_pullback_principal {P F G : Type}
    {E : generic_entailment P F} {D : list F -> Type}
    {theory : P} (f : G -> F)
    (Hprincipal : generic_principal_entailment E D theory) :
    generic_principal_entailment
      (generic_pullback_entailment E f)
      (generic_lk_pullback D f)
      (generic_pullback_of theory f).
Proof.
  constructor. intro p.
  exact (generic_principal_equiv Hprincipal (f p)).
Defined.

(** Source declaration 27/43: [Pullback.nonempty_iff]. *)
Lemma generic_lk_pullback_inhabited_iff :
  forall (F G : Type) (D : list F -> Type) (f : G -> F)
         (gamma : list G),
    inhabited (generic_lk_pullback D f gamma) <->
    inhabited (D (map f gamma)).
Proof. reflexivity. Qed.

(** Source declaration 28/43: [Pullback.isEmpty_iff]. *)
Lemma generic_lk_pullback_empty_iff :
  forall (F G : Type) (D : list F -> Type) (f : G -> F)
         (gamma : list G),
    generic_empty_type (generic_lk_pullback D f gamma) <->
    generic_empty_type (D (map f gamma)).
Proof. reflexivity. Qed.

Arguments generic_lk_pullback_cast {F G} D f {delta gamma} _ _.
Arguments generic_lk_pullback_uncast {F G} D f {delta gamma} _ _.
Arguments generic_lk_pullback_one_sided {F G CF CG D f} _ _.
Arguments generic_lk_pullback_cut {F G CF CG D f} _ _.
Arguments generic_lk_pullback_principal {P F G E D theory} f _.

(** * Contextual entailment *)

(** A finite context witness carries precisely the pointwise membership
    evidence needed by contextual derivability. *)
Definition generic_context_witness {F S : Type}
    (A : generic_adjunctive_set F S) (s : S) : Type :=
  { gamma : list F |
      forall p, generic_list_member p gamma ->
                generic_adjunctive_member A p s }.

Definition generic_context_witness_formulas {F S : Type}
    {A : generic_adjunctive_set F S} {s : S}
    (w : generic_context_witness A s) : list F :=
  proj1_sig w.

Definition generic_context_witness_covers {F S : Type}
    {A : generic_adjunctive_set F S} {s : S}
    (w : generic_context_witness A s) :
    forall p,
      generic_list_member p (generic_context_witness_formulas w) ->
      generic_adjunctive_member A p s :=
  proj2_sig w.

(** Source declaration 29/43: [ContextualEntailment].  Only the raw
    negation operation is used by the contextual representation. *)
Record generic_contextual_entailment {S F : Type}
    (E : generic_entailment S F)
    (A : generic_adjunctive_set F S)
    (neg : F -> F) (D : list F -> Type) : Type := {
  generic_contextual_equiv :
    forall (s : S) (p : F),
      generic_type_equiv
        (generic_proof E s p)
        { w : generic_context_witness A s &
          D (p :: map neg (generic_context_witness_formulas w)) }
}.

Arguments generic_contextual_equiv {S F E A neg D} _ _ _.

(** Source declaration 30/43: [ContextualEntailment.provable_iff]. *)
Lemma generic_contextual_provable_iff :
  forall (S F : Type) (E : generic_entailment S F)
         (A : generic_adjunctive_set F S)
         (neg : F -> F) (D : list F -> Type),
    generic_contextual_entailment E A neg D ->
    forall (s : S) (p : F),
      generic_provable E s p <->
      exists gamma : list F,
        (forall q,
          generic_list_member q gamma -> generic_adjunctive_member A q s) /\
        inhabited (D (p :: map neg gamma)).
Proof.
  intros S F E A neg D Hcontext s p; split.
  - intros [b].
    destruct (generic_equiv_to
      (generic_contextual_equiv Hcontext s p) b) as [w d].
    exists (generic_context_witness_formulas w). split.
    + exact (@generic_context_witness_covers F S A s w).
    + now constructor.
  - intros [gamma [Hgamma [d]]]. constructor.
    apply (generic_equiv_from (generic_contextual_equiv Hcontext s p)).
    exact (existT _ (exist _ gamma Hgamma) d).
Qed.

(** Source declaration 31/43: [ContextualEntailment.toProof]. *)
Definition generic_contextual_to_proof {S F : Type}
    {E : generic_entailment S F}
    {A : generic_adjunctive_set F S}
    {neg : F -> F} {D : list F -> Type}
    (Hcontext : generic_contextual_entailment E A neg D)
    (s : S) (p : F) (d : D [p]) : generic_proof E s p.
Proof.
  apply (generic_equiv_from (generic_contextual_equiv Hcontext s p)).
  refine (existT _ (exist _ [] _) d).
  intros q Hq. contradiction.
Defined.

(** Source declaration 32/43: [ContextualEntailment.ofAxiom]. *)
Definition generic_contextual_of_axiom {S F : Type}
    {E : generic_entailment S F}
    {A : generic_adjunctive_set F S}
    {C : generic_connectives F} {D : list F -> Type}
    (Hcontext : generic_contextual_entailment E A (generic_neg C) D)
    (Hlk : generic_one_sided_lk C D)
    (s : S) (p : F) (Hp : generic_adjunctive_member A p s) :
    generic_proof E s p.
Proof.
  apply (generic_equiv_from (generic_contextual_equiv Hcontext s p)).
  refine (existT _ (exist _ [p] _) (generic_lk_identity Hlk p)).
  intros q [Hq | Hq].
  - now subst q.
  - contradiction.
Defined.

(** Source declaration 33/43: [ContextualEntailment.ofAxiomSubset]. *)
Definition generic_contextual_of_axiom_subset {S F : Type}
    {E : generic_entailment S F}
    {A : generic_adjunctive_set F S}
    {neg : F -> F} {D : list F -> Type}
    (Hcontext : generic_contextual_entailment E A neg D)
    (s t : S) (p : F)
    (b : generic_proof E s p)
    (Hsubset : generic_adjunctive_subset A s t) :
    generic_proof E t p.
Proof.
  destruct (generic_equiv_to
    (generic_contextual_equiv Hcontext s p) b) as [w d].
  apply (generic_equiv_from (generic_contextual_equiv Hcontext t p)).
  refine (existT _
    (exist _ (generic_context_witness_formulas w) _) d).
  intros q Hq.
  exact (Hsubset q (@generic_context_witness_covers F S A s w q Hq)).
Defined.

(** Source declaration 34/43: the contextual [Entailment.Axiomatized]
    instance. *)
Definition generic_contextual_axiomatized {S F : Type}
    {E : generic_entailment S F}
    {A : generic_adjunctive_set F S}
    {C : generic_connectives F} {D : list F -> Type}
    (Hcontext : generic_contextual_entailment E A (generic_neg C) D)
    (Hlk : generic_one_sided_lk C D) :
    generic_axiomatized E A.
Proof.
  constructor.
  - intros s p Hp.
    exact (@generic_contextual_of_axiom S F E A C D
      Hcontext Hlk s p Hp).
  - intros s t Hsubset p b.
    exact (@generic_contextual_of_axiom_subset S F E A (generic_neg C) D
      Hcontext s t p b Hsubset).
Defined.

Arguments generic_context_witness_formulas {F S A s} _.
Arguments generic_context_witness_covers {F S A s} _ _ _.
Arguments generic_contextual_to_proof {S F E A neg D} _ _ _ _.
Arguments generic_contextual_of_axiom {S F E A C D} _ _ _ _ _.
Arguments generic_contextual_of_axiom_subset {S F E A neg D}
  _ _ _ _ _ _.
Arguments generic_contextual_axiomatized {S F E A C D} _ _.

(** Source declaration 35/43: the contextual [Entailment.ModusPonens]
    instance.  The proof uses only involutive negation, implication as
    disjunction, and De Morgan for a negated disjunction. *)
Definition generic_contextual_modus_ponens {S F : Type}
    {E : generic_entailment S F}
    {A : generic_adjunctive_set F S}
    (C : generic_connectives F) {D : list F -> Type}
    (Hcontext :
      generic_contextual_entailment E A (generic_neg C) D)
    (Hinv : generic_neg_involutive_law C)
    (Himp : generic_imp_as_or_law C)
    (Hneg_or : generic_neg_or_law C)
    (K : generic_one_sided_lk_cut C D)
    (s : S) : generic_modus_ponens E C s.
Proof.
  constructor. intros p q bpq bp.
  destruct (generic_equiv_to
    (generic_contextual_equiv Hcontext s (generic_imp C p q)) bpq)
    as [wimp dimp].
  destruct (generic_equiv_to
    (generic_contextual_equiv Hcontext s p) bp)
    as [wp dp].
  apply (generic_equiv_from (generic_contextual_equiv Hcontext s q)).
  assert (Hcovers : forall r,
    generic_list_member r
      (generic_context_witness_formulas wimp ++
       generic_context_witness_formulas wp) ->
    generic_adjunctive_member A r s).
  { intros r Hr.
    apply (proj1 (@generic_list_member_app_iff F r
      (generic_context_witness_formulas wimp)
      (generic_context_witness_formulas wp))) in Hr.
    destruct Hr as [Hr | Hr].
    + exact (generic_context_witness_covers wimp r Hr).
    + exact (generic_context_witness_covers wp r Hr). }
  refine (existT _
    (exist _
      (generic_context_witness_formulas wimp ++
       generic_context_witness_formulas wp) Hcovers)
    _).
  pose proof (generic_lk_tensor (generic_lk_cut_base K)
      (generic_lk_identity (generic_lk_cut_base K) p)
      (generic_lk_identity (generic_lk_cut_base K) (generic_neg C q)))
      as dcontra.
  assert (econtra :
    generic_and C p (generic_neg C q) ::
      [generic_neg C p; generic_neg C (generic_neg C q)] =
    [generic_neg C (generic_imp C p q); generic_neg C p; q]).
  { simpl. rewrite (Hinv q), (Himp p q),
      (Hneg_or (generic_neg C p) q), (Hinv p).
    reflexivity. }
  pose proof (@generic_lk_cast F D _ _ dcontra econtra) as dcontra'.
  pose proof (generic_lk_cut_raw K (generic_imp C p q)
    (map (generic_neg C) (generic_context_witness_formulas wimp))
    [generic_neg C p; q] dimp dcontra') as d1.
  assert (Hreorder1 : generic_list_subset
    (map (generic_neg C) (generic_context_witness_formulas wimp) ++
     [generic_neg C p; q])
    (generic_neg C p :: q ::
     map (generic_neg C) (generic_context_witness_formulas wimp))).
  { intros r Hr.
    apply (proj1 (@generic_list_member_app_iff F r
      (map (generic_neg C) (generic_context_witness_formulas wimp))
      [generic_neg C p; q])) in Hr.
    destruct Hr as [Hr | [Hr | [Hr | Hfalse]]].
    - now right; right.
    - now left.
    - now right; left.
    - contradiction. }
  pose proof (generic_lk_contra (generic_lk_cut_base K) d1 Hreorder1)
    as d1'.
  pose proof (generic_lk_cut_raw K p
    (map (generic_neg C) (generic_context_witness_formulas wp))
    (q :: map (generic_neg C)
      (generic_context_witness_formulas wimp))
    dp d1') as d2.
  refine (@generic_lk_contra F C D (generic_lk_cut_base K)
    (map (generic_neg C) (generic_context_witness_formulas wp) ++
     q :: map (generic_neg C) (generic_context_witness_formulas wimp))
    (q :: map (generic_neg C)
      (generic_context_witness_formulas wimp ++
       generic_context_witness_formulas wp)) d2 _).
  rewrite map_app.
  intros r Hr.
  apply (proj1 (@generic_list_member_app_iff F r
    (map (generic_neg C) (generic_context_witness_formulas wp))
    (q :: map (generic_neg C)
      (generic_context_witness_formulas wimp)))) in Hr.
  destruct Hr as [Hr | [Hr | Hr]].
  - right. apply (proj2 (@generic_list_member_app_iff F r
      (map (generic_neg C) (generic_context_witness_formulas wimp))
      (map (generic_neg C) (generic_context_witness_formulas wp)))).
    now right.
  - now left.
  - right. apply (proj2 (@generic_list_member_app_iff F r
      (map (generic_neg C) (generic_context_witness_formulas wimp))
      (map (generic_neg C) (generic_context_witness_formulas wp)))).
    now left.
Defined.

(** The recursion underlying source declaration 36 is more general than the
    exported adapter: it needs only one-sided disjunction, implication's
    normalization equation, and an already available modus-ponens rule. *)
Fixpoint generic_contextual_cut_list
    {S F : Type} {E : generic_entailment S F}
    {A : generic_adjunctive_set F S}
    (C : generic_connectives F) {D : list F -> Type}
    (Hcontext :
      generic_contextual_entailment E A (generic_neg C) D)
    (Himp : generic_imp_as_or_law C)
    (Hlk : generic_one_sided_lk C D)
    (source : S)
    (Hmp : generic_modus_ponens E C source)
    (gamma : list F) {struct gamma} :
    forall target : S,
      (forall r, generic_list_member r gamma ->
                 generic_adjunctive_member A r target) ->
      generic_proof_set E source (generic_adjunctive_carrier A target) ->
      forall chi : F,
        D (chi :: map (generic_neg C) gamma) ->
        generic_proof E source chi :=
  match gamma as gamma0 return
    forall target : S,
      (forall r, generic_list_member r gamma0 ->
                 generic_adjunctive_member A r target) ->
      generic_proof_set E source (generic_adjunctive_carrier A target) ->
      forall chi : F,
        D (chi :: map (generic_neg C) gamma0) ->
        generic_proof E source chi
  with
  | [] => fun _ _ _ chi d =>
      generic_contextual_to_proof Hcontext source chi d
  | psi :: tail => fun target Hmembers bs chi d =>
      let dor := generic_lk_or Hlk (generic_neg C psi) chi
        (map (generic_neg C) tail) (generic_lk_swap1 Hlk d) in
      let bor := @generic_contextual_cut_list S F E A C D Hcontext
        Himp Hlk source Hmp tail target
        (fun r Hr => Hmembers r (or_intror Hr)) bs
        (generic_or C (generic_neg C psi) chi) dor in
      let bimp := @generic_proof_cast S F E source
        (generic_or C (generic_neg C psi) chi)
        (generic_imp C psi chi) bor (eq_sym (Himp psi chi)) in
      let bpsi := bs psi (Hmembers psi (or_introl eq_refl)) in
      generic_modus_ponens_raw Hmp psi chi bimp bpsi
  end.

(** Source declaration 36/43: the contextual [Entailment.StrongCut]
    instance.  No bottom, top, or negated-conjunction law is used. *)
Definition generic_contextual_strong_cut {S F : Type}
    {E : generic_entailment S F}
    {A : generic_adjunctive_set F S}
    (C : generic_connectives F) {D : list F -> Type}
    (Hcontext :
      generic_contextual_entailment E A (generic_neg C) D)
    (Hinv : generic_neg_involutive_law C)
    (Himp : generic_imp_as_or_law C)
    (Hneg_or : generic_neg_or_law C)
    (K : generic_one_sided_lk_cut C D) :
    generic_strong_cut E E A.
Proof.
  constructor. intros source target p bs b.
  destruct (generic_equiv_to
    (generic_contextual_equiv Hcontext target p) b) as [w d].
  exact (@generic_contextual_cut_list S F E A C D Hcontext
    Himp (generic_lk_cut_base K) source
    (@generic_contextual_modus_ponens
      S F E A C D Hcontext Hinv Himp Hneg_or K source)
    (generic_context_witness_formulas w) target
    (generic_context_witness_covers w) bs p d).
Defined.

(** Source declaration 37/43: the contextual
    [Entailment.DeductiveExplosion] instance.  Bottom elimination requires
    only [neg bottom = top] in addition to cut. *)
Definition generic_contextual_deductive_explosion {S F : Type}
    {E : generic_entailment S F}
    {A : generic_adjunctive_set F S}
    (C : generic_connectives F) {D : list F -> Type}
    (Hcontext :
      generic_contextual_entailment E A (generic_neg C) D)
    (Hneg_bottom : generic_neg_bottom_law C)
    (K : generic_one_sided_lk_cut C D) :
    generic_deductive_explosion E (generic_bottom C).
Proof.
  constructor. intros s b p.
  destruct (generic_equiv_to
    (generic_contextual_equiv Hcontext s (generic_bottom C)) b)
    as [w d].
  assert (dnot_bottom : D [generic_neg C (generic_bottom C)]).
  { apply (@generic_lk_cast F D _ _
      (generic_lk_verum (generic_lk_cut_base K))).
    now rewrite Hneg_bottom. }
  pose proof (generic_lk_cut_raw K (generic_bottom C)
    (map (generic_neg C) (generic_context_witness_formulas w)) []
    d dnot_bottom) as dcut0.
  pose proof (@generic_lk_cast F D _ _ dcut0
    (app_nil_r (map (generic_neg C)
      (generic_context_witness_formulas w)))) as dcut.
  apply (generic_equiv_from (generic_contextual_equiv Hcontext s p)).
  refine (existT _ w _).
  apply (generic_lk_contra (generic_lk_cut_base K) dcut).
  intros r Hr. now right.
Defined.

(** Source declaration 38/43: [ContextualEntailment.inconsistent_iff].
    This characterization is constructive and inherits only the single
    bottom-negation equation used by contextual explosion. *)
Lemma generic_contextual_inconsistent_iff :
  forall (S F : Type) (E : generic_entailment S F)
         (A : generic_adjunctive_set F S)
         (C : generic_connectives F) (D : list F -> Type),
    generic_contextual_entailment E A (generic_neg C) D ->
    generic_neg_bottom_law C ->
    generic_one_sided_lk_cut C D ->
    forall s : S,
      generic_inconsistent E s <->
      exists gamma : list F,
        (forall r, generic_list_member r gamma ->
                   generic_adjunctive_member A r s) /\
        inhabited (D (map (generic_neg C) gamma)).
Proof.
  intros S F E A C D Hcontext Hneg_bottom K s; split.
  - intro Hinc.
    destruct (proj1 (generic_contextual_provable_iff Hcontext s
      (generic_bottom C)) (Hinc (generic_bottom C)))
      as [gamma [Hgamma [d]]].
    assert (dnot_bottom : D [generic_neg C (generic_bottom C)]).
    { apply (@generic_lk_cast F D _ _
        (generic_lk_verum (generic_lk_cut_base K))).
      now rewrite Hneg_bottom. }
    pose proof (generic_lk_cut_raw K (generic_bottom C)
      (map (generic_neg C) gamma) [] d dnot_bottom) as dcut0.
    pose proof (@generic_lk_cast F D _ _ dcut0
      (app_nil_r (map (generic_neg C) gamma))) as dcut.
    exists gamma. split; [exact Hgamma | now constructor].
  - intros [gamma [Hgamma [d]]].
    assert (Hbottom : generic_provable E s (generic_bottom C)).
    { apply (proj2 (generic_contextual_provable_iff Hcontext s
        (generic_bottom C))).
      exists gamma. split; [exact Hgamma |]. constructor.
      apply (generic_lk_contra (generic_lk_cut_base K) d).
      intros r Hr. now right. }
    exact (@generic_inconsistent_of_provable_bottom S F E
      (generic_bottom C)
      (@generic_contextual_deductive_explosion
        S F E A C D Hcontext Hneg_bottom K) s Hbottom).
Qed.

Arguments generic_contextual_modus_ponens
  {S F E A} C {D} _ _ _ _ _ _.
Arguments generic_contextual_cut_list
  {S F E A} C {D} _ _ _ _ _ _ _ _ _ _ _.
Arguments generic_contextual_strong_cut
  {S F E A} C {D} _ _ _ _ _.
Arguments generic_contextual_deductive_explosion
  {S F E A} C {D} _ _ _.

(** Source declaration 39/43: the contextual [Entailment.Cl] instance.
    All nontrivial axiom sequents are shared with declaration 19 through
    [generic_lk_classical]; only transport through the contextual
    equivalence is new here. *)
Definition generic_contextual_classical {S F : Type}
    {E : generic_entailment S F}
    {A : generic_adjunctive_set F S}
    (C : generic_connectives F) {D : list F -> Type}
    (Hcontext :
      generic_contextual_entailment E A (generic_neg C) D)
    (Hinv : generic_neg_involutive_law C)
    (Hneg_bottom : generic_neg_bottom_law C)
    (Himp : generic_imp_as_or_law C)
    (Hneg_and : generic_neg_and_law C)
    (Hneg_or : generic_neg_or_law C)
    (K : generic_one_sided_lk_cut C D)
    (s : S) : generic_classical_entailment E C s.
Proof.
  pose proof (@generic_lk_classical F C D Hinv Hneg_bottom Himp
    Hneg_and Hneg_or (generic_lk_cut_base K)) as Hclassical.
  constructor.
  - exact (@generic_contextual_modus_ponens S F E A C D Hcontext
      Hinv Himp Hneg_or K s).
  - intro p. exact (@generic_contextual_to_proof S F E A
      (generic_neg C) D Hcontext s (generic_axiom_neg_equiv C p)
      (generic_lk_classical_neg_equiv Hclassical p)).
  - exact (@generic_contextual_to_proof S F E A
      (generic_neg C) D Hcontext s (generic_top C)
      (generic_lk_classical_verum Hclassical)).
  - intros p q. exact (@generic_contextual_to_proof S F E A
      (generic_neg C) D Hcontext s (generic_axiom_K C p q)
      (generic_lk_classical_K Hclassical p q)).
  - intros p q r. exact (@generic_contextual_to_proof S F E A
      (generic_neg C) D Hcontext s (generic_axiom_S C p q r)
      (generic_lk_classical_S Hclassical p q r)).
  - intros p q. exact (@generic_contextual_to_proof S F E A
      (generic_neg C) D Hcontext s (generic_axiom_and1 C p q)
      (generic_lk_classical_and1 Hclassical p q)).
  - intros p q. exact (@generic_contextual_to_proof S F E A
      (generic_neg C) D Hcontext s (generic_axiom_and2 C p q)
      (generic_lk_classical_and2 Hclassical p q)).
  - intros p q. exact (@generic_contextual_to_proof S F E A
      (generic_neg C) D Hcontext s (generic_axiom_and3 C p q)
      (generic_lk_classical_and3 Hclassical p q)).
  - intros p q. exact (@generic_contextual_to_proof S F E A
      (generic_neg C) D Hcontext s (generic_axiom_or1 C p q)
      (generic_lk_classical_or1 Hclassical p q)).
  - intros p q. exact (@generic_contextual_to_proof S F E A
      (generic_neg C) D Hcontext s (generic_axiom_or2 C p q)
      (generic_lk_classical_or2 Hclassical p q)).
  - intros p q r. exact (@generic_contextual_to_proof S F E A
      (generic_neg C) D Hcontext s (generic_axiom_or3 C p q r)
      (generic_lk_classical_or3 Hclassical p q r)).
  - intro p. exact (@generic_contextual_to_proof S F E A
      (generic_neg C) D Hcontext s (generic_axiom_dne C p)
      (generic_lk_classical_dne Hclassical p)).
Defined.

(** Source declaration 40/43:
    [ContextualEntailment.empty_provable_iff_eprovable].  This argument is
    independent of every connective and calculus rule. *)
Lemma generic_contextual_empty_provable_iff_principal :
  forall (S P F : Type)
         (E : generic_entailment S F)
         (EP : generic_entailment P F)
         (A : generic_adjunctive_set F S)
         (neg : F -> F) (D : list F -> Type),
    generic_contextual_entailment E A neg D ->
    forall theory : P,
      generic_principal_entailment EP D theory ->
      forall p : F,
        generic_provable E (generic_adjunctive_empty A) p <->
        generic_provable EP theory p.
Proof.
  intros S P F E EP A neg D Hcontext theory Hprincipal p; split.
  - intros [b].
    destruct (generic_equiv_to
      (generic_contextual_equiv Hcontext
        (generic_adjunctive_empty A) p) b) as [[gamma Hgamma] d].
    assert (Hnil : gamma = []).
    { destruct gamma as [|q qs].
      - reflexivity.
      - exfalso. exact (generic_adjunctive_not_mem_empty A q
          (Hgamma q (or_introl eq_refl))). }
    subst gamma. simpl in d.
    constructor.
    exact (generic_equiv_from (generic_principal_equiv Hprincipal p) d).
  - intros [b]. constructor.
    apply (generic_equiv_from (generic_contextual_equiv Hcontext
      (generic_adjunctive_empty A) p)).
    pose (wempty :=
      (@exist (list F)
        (fun gamma => forall q,
          generic_list_member q gamma ->
          generic_adjunctive_member A q (generic_adjunctive_empty A)) []
        (fun (q : F) (Hq : generic_list_member q []) =>
          False_rect _ Hq) :
       generic_context_witness A (generic_adjunctive_empty A))).
    exact (existT _ wempty
      (generic_equiv_to (generic_principal_equiv Hprincipal p) b)).
Qed.

(** Finite De Morgan for singleton-normalized conjunction.  Declaration 41
    is the only consumer; exposing the lemma makes its exact law boundary
    explicit. *)
Lemma generic_neg_list_conj2 :
  forall (F : Type) (C : generic_connectives F),
    generic_neg_top_law C ->
    generic_neg_and_law C ->
    forall gamma : list F,
      generic_neg C (generic_list_conj2 C gamma) =
      generic_list_disj2 C (map (generic_neg C) gamma).
Proof.
  intros F C Hneg_top Hneg_and gamma.
  induction gamma as [|p ps IH].
  - simpl. exact Hneg_top.
  - destruct ps as [|q qs].
    + reflexivity.
    + simpl in IH |- *. rewrite Hneg_and, IH. reflexivity.
Qed.

(** Double negation through a mapped singleton-normalized disjunction. *)
Lemma generic_neg_mapped_list_disj2 :
  forall (F : Type) (C : generic_connectives F),
    generic_neg_involutive_law C ->
    generic_neg_bottom_law C ->
    generic_neg_or_law C ->
    forall gamma : list F,
      generic_neg C
        (generic_list_disj2 C (map (generic_neg C) gamma)) =
      generic_list_conj2 C gamma.
Proof.
  intros F C Hinv Hneg_bottom Hneg_or gamma.
  rewrite (@generic_neg_list_disj2 F C Hneg_bottom Hneg_or
    (map (generic_neg C) gamma)), map_map.
  induction gamma as [|p ps IH].
  - reflexivity.
  - destruct ps as [|q qs].
    + simpl. rewrite (Hinv p). reflexivity.
    + simpl in IH |- *. rewrite (Hinv p), IH. reflexivity.
Qed.

(** Type-valued finite-context proof used by source declaration 41. *)
Record generic_principal_context_proof {P F : Type}
    (E : generic_entailment P F)
    (C : generic_connectives F)
    (theory : P) (T : F -> Prop) (p : F) : Type := {
  generic_principal_context_formulas : list F;
  generic_principal_context_covers :
    forall q,
      generic_list_member q generic_principal_context_formulas -> T q;
  generic_principal_context_raw :
    generic_proof E theory
      (generic_imp C
        (generic_list_conj2 C generic_principal_context_formulas) p)
}.

Arguments generic_principal_context_formulas
  {P F E C theory T p} _.
Arguments generic_principal_context_covers
  {P F E C theory T p} _ _ _.
Arguments generic_principal_context_raw
  {P F E C theory T p} _.

(** Source declaration 41/43: [ContextualEntailment.iff_context]. *)
Lemma generic_contextual_iff_principal_context :
  forall (S P F : Type)
         (E : generic_entailment S F)
         (EP : generic_entailment P F)
         (A : generic_adjunctive_set F S)
         (C : generic_connectives F) (D : list F -> Type),
    generic_contextual_entailment E A (generic_neg C) D ->
    forall theory : P,
      generic_principal_entailment EP D theory ->
      generic_neg_involutive_law C ->
      generic_neg_top_law C ->
      generic_neg_bottom_law C ->
      generic_imp_as_or_law C ->
      generic_neg_and_law C ->
      generic_neg_or_law C ->
      generic_one_sided_lk_cut C D ->
      forall (s : S) (p : F),
        generic_provable E s p <->
        inhabited (generic_principal_context_proof EP C theory
          (generic_adjunctive_carrier A s) p).
Proof.
  intros S P F E EP A C D Hcontext theory Hprincipal
    Hinv Hneg_top Hneg_bottom Himp Hneg_and Hneg_or K s p; split.
  - intros [b].
    destruct (generic_equiv_to
      (generic_contextual_equiv Hcontext s p) b) as [w d].
    pose proof (generic_lk_rotate (generic_lk_cut_base K) d) as drot.
    pose proof (generic_lk_disj2 (generic_lk_cut_base K)
      (map (generic_neg C) (generic_context_witness_formulas w)) [p]
      drot) as ddisj.
    pose proof (generic_lk_or (generic_lk_cut_base K)
      (generic_list_disj2 C
        (map (generic_neg C) (generic_context_witness_formulas w)))
      p [] ddisj) as dnormalized.
    assert (enormalized :
      generic_or C
        (generic_list_disj2 C
          (map (generic_neg C) (generic_context_witness_formulas w))) p =
      generic_imp C
        (generic_list_conj2 C (generic_context_witness_formulas w)) p).
    { rewrite Himp,
        (@generic_neg_list_conj2 F C Hneg_top Hneg_and
          (generic_context_witness_formulas w)).
      reflexivity. }
    pose proof (@generic_lk_cast F D _ _ dnormalized
      (f_equal (fun r => [r]) enormalized)) as dimp.
    constructor.
    refine {| generic_principal_context_formulas :=
                generic_context_witness_formulas w;
              generic_principal_context_raw :=
                generic_equiv_from
                  (generic_principal_equiv Hprincipal
                    (generic_imp C
                      (generic_list_conj2 C
                        (generic_context_witness_formulas w)) p))
                  dimp |}.
    exact (generic_context_witness_covers w).
  - intros [w]. constructor.
    apply (generic_equiv_from (generic_contextual_equiv Hcontext s p)).
    refine (existT _
      (exist _ (generic_principal_context_formulas w)
        (generic_principal_context_covers w)) _).
    pose proof (generic_equiv_to
      (generic_principal_equiv Hprincipal
        (generic_imp C
          (generic_list_conj2 C
            (generic_principal_context_formulas w)) p))
      (generic_principal_context_raw w)) as dimp.
    assert (eformula :
      generic_imp C
        (generic_list_conj2 C
          (generic_principal_context_formulas w)) p =
      generic_or C
        (generic_list_disj2 C
          (map (generic_neg C)
            (generic_principal_context_formulas w))) p).
    { rewrite Himp,
        (@generic_neg_list_conj2 F C Hneg_top Hneg_and
          (generic_principal_context_formulas w)).
      reflexivity. }
    pose proof (@generic_lk_cast F D _ _ dimp
      (f_equal (fun r => [r]) eformula)) as dformula.
    assert (dconj : D
      (generic_list_conj2 C (generic_principal_context_formulas w) ::
       map (generic_neg C) (generic_principal_context_formulas w))).
    { apply (generic_lk_conj2 (generic_lk_cut_base K)
        (generic_principal_context_formulas w)
        (map (generic_neg C) (generic_principal_context_formulas w))).
      intros q Hq.
      apply (generic_lk_close (generic_lk_cut_base K) q).
      + now left.
      + right. exact (@generic_list_member_map_intro F F
          (generic_neg C) q (generic_principal_context_formulas w) Hq). }
    pose proof (generic_lk_rotate (generic_lk_cut_base K)
      (generic_lk_identity (generic_lk_cut_base K) p)) as dpair.
    pose proof (generic_lk_tensor (generic_lk_cut_base K) dconj dpair)
      as dcontra0.
    assert (Hreorder : generic_list_subset
      (generic_and C
        (generic_list_conj2 C (generic_principal_context_formulas w))
        (generic_neg C p) ::
       map (generic_neg C) (generic_principal_context_formulas w) ++ [p])
      (generic_and C
        (generic_list_conj2 C (generic_principal_context_formulas w))
        (generic_neg C p) ::
       p :: map (generic_neg C)
         (generic_principal_context_formulas w))).
    { intros r [Hr | Hr].
      - now left.
      - right. apply (proj1 (@generic_list_member_app_iff F r
          (map (generic_neg C) (generic_principal_context_formulas w))
          [p])) in Hr.
        destruct Hr as [Hr | [Hr | Hfalse]].
        + now right.
        + now left.
        + contradiction. }
    pose proof (generic_lk_contra (generic_lk_cut_base K)
      dcontra0 Hreorder) as dcontra.
    apply (generic_lk_extended_cut K dformula dcontra).
    rewrite Hneg_or,
      (@generic_neg_mapped_list_disj2 F C Hinv Hneg_bottom Hneg_or
        (generic_principal_context_formulas w)).
    reflexivity.
Qed.

(** Source declaration 42/43:
    [ContextualEntailment.of_principal_provable].  Direct empty-support
    transport removes every connective and Cut premise used by the source's
    route through declaration 41. *)
Lemma generic_contextual_of_principal_provable :
  forall (S P F : Type)
         (E : generic_entailment S F)
         (EP : generic_entailment P F)
         (A : generic_adjunctive_set F S)
         (neg : F -> F) (D : list F -> Type),
    generic_contextual_entailment E A neg D ->
    forall theory : P,
      generic_principal_entailment EP D theory ->
      forall (s : S) (p : F),
        generic_provable EP theory p -> generic_provable E s p.
Proof.
  intros S P F E EP A neg D Hcontext theory Hprincipal s p [b].
  constructor.
  exact (@generic_contextual_to_proof S F E A neg D Hcontext s p
    (generic_equiv_to (generic_principal_equiv Hprincipal p) b)).
Qed.

Arguments generic_contextual_classical
  {S F E A} C {D} _ _ _ _ _ _ _ _.
Arguments generic_contextual_empty_provable_iff_principal
  {S P F} E EP A neg D _ theory _ p.
Arguments generic_contextual_iff_principal_context
  {S P F} E EP A C D _ theory _ _ _ _ _ _ _ _ _ _.
Arguments generic_contextual_of_principal_provable
  {S P F} E EP A neg D _ theory _ s p _.
