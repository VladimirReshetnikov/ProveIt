(*
  Squaring the square: basic definitions.

  Coq port of the Lean module SquaredSquare.Basic.  An axis-parallel closed
  square in the real plane is recorded by its bottom-left corner (x, y) and
  its side s.  A dissection of [0, L] x [0, L] is a finite list of such
  squares with positive sides whose open interiors are pairwise disjoint and
  whose closed pieces cover the big square exactly.  A dissection is perfect
  when it has at least two pieces and the pieces are pairwise non-congruent.

  Congruence is taken in the strongest reasonable sense for the negative
  statements: two plane sets are congruent when some bijection between them
  preserves squared Euclidean distances.  Every plane isometry restricts to
  such a bijection, so ~ Congruent rules out congruence by arbitrary
  isometries as well.  The key elementary invariant is the squared diameter:
  a closed axis-parallel square of side s > 0 has maximal squared distance
  2 * s^2, attained by opposite corners, so congruent squares have equal
  sides.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import List.
From Stdlib Require Import Psatz.
Import ListNotations.

Open Scope R_scope.

Module LeanProofs.
Module SquaredSquare.

(* An axis-parallel square, described by its bottom-left corner and side. *)
Record Sq : Type := mkSq { qx : R; qy : R; qs : R }.

(* Membership of the point (u, v) in the closed square. *)
Definition InClosed (q : Sq) (u v : R) : Prop :=
  (qx q <= u <= qx q + qs q) /\ (qy q <= v <= qy q + qs q).

(* Membership of the point (u, v) in the open square: for 0 < qs q this is
   the topological interior of the closed square. *)
Definition InOpen (q : Sq) (u v : R) : Prop :=
  (qx q < u < qx q + qs q) /\ (qy q < v < qy q + qs q).

(* Membership in the big square [0, L] x [0, L] being dissected. *)
Definition InBig (L : R) (u v : R) : Prop :=
  (0 <= u <= L) /\ (0 <= v <= L).

(* Point sets in the plane. *)
Definition PlaneSet : Type := R * R -> Prop.

Definition SqSet (q : Sq) : PlaneSet :=
  fun p => InClosed q (fst p) (snd p).

Definition DisjointOpen (p q : Sq) : Prop :=
  forall u v, InOpen p u v -> InOpen q u v -> False.

(* IsDissection L l: the squares listed in l have positive sides, pairwise
   disjoint open interiors, and their closed pieces cover [0, L] x [0, L]
   exactly. *)
Record IsDissection (L : R) (l : list Sq) : Prop := mkIsDissection {
  diss_pos : forall q, In q l -> 0 < qs q;
  diss_disj : ForallOrdPairs DisjointOpen l;
  diss_cover : forall u v,
      InBig L u v <-> exists q, In q l /\ InClosed q u v
}.

(* Squared Euclidean distance in the plane. *)
Definition sqDist (p r : R * R) : R :=
  (fst p - fst r) * (fst p - fst r) + (snd p - snd r) * (snd p - snd r).

(* Two plane sets are congruent when some bijection between them preserves
   squared Euclidean distances. *)
Definition Congruent (A B : PlaneSet) : Prop :=
  exists f : R * R -> R * R,
    (forall p, A p -> B (f p)) /\
    (forall p r, A p -> A r -> f p = f r -> p = r) /\
    (forall b, B b -> exists p, A p /\ f p = b) /\
    (forall p r, A p -> A r -> sqDist (f p) (f r) = sqDist p r).

(* Any two points of a closed square of side s are at squared distance at
   most 2 * s * s. *)
Lemma sqDist_le_in_square (q : Sq) (p r : R * R) :
  SqSet q p -> SqSet q r -> sqDist p r <= 2 * (qs q * qs q).
Proof.
  unfold SqSet, InClosed, sqDist.
  destruct p as [a b]; destruct r as [c d]; simpl.
  intros [[H1 H2] [H3 H4]] [[H5 H6] [H7 H8]].
  assert (Hx1 : a - c <= qs q) by lra.
  assert (Hx2 : c - a <= qs q) by lra.
  assert (Hy1 : b - d <= qs q) by lra.
  assert (Hy2 : d - b <= qs q) by lra.
  nra.
Qed.

Lemma corner_bl_in (q : Sq) : 0 <= qs q -> SqSet q (qx q, qy q).
Proof.
  unfold SqSet, InClosed; simpl; lra.
Qed.

Lemma corner_tr_in (q : Sq) : 0 <= qs q -> SqSet q (qx q + qs q, qy q + qs q).
Proof.
  unfold SqSet, InClosed; simpl; lra.
Qed.

(* Opposite corners realize the squared diameter. *)
Lemma sqDist_corners (q : Sq) :
  sqDist (qx q, qy q) (qx q + qs q, qy q + qs q) = 2 * (qs q * qs q).
Proof.
  unfold sqDist; simpl; ring.
Qed.

(* Congruent squares with positive sides have equal sides. *)
Lemma side_eq_of_congruent (p q : Sq) :
  0 < qs p -> 0 < qs q -> Congruent (SqSet p) (SqSet q) -> qs p = qs q.
Proof.
  intros Hp Hq [f [Hmap [Hinj [Hsurj Hdist]]]].
  assert (Hfwd : 2 * (qs p * qs p) <= 2 * (qs q * qs q)).
  { pose proof (corner_bl_in p (Rlt_le _ _ Hp)) as Hc1.
    pose proof (corner_tr_in p (Rlt_le _ _ Hp)) as Hc2.
    pose proof (Hdist _ _ Hc1 Hc2) as Hd.
    rewrite sqDist_corners in Hd.
    pose proof (sqDist_le_in_square q _ _ (Hmap _ Hc1) (Hmap _ Hc2)) as Hb.
    lra. }
  assert (Hbwd : 2 * (qs q * qs q) <= 2 * (qs p * qs p)).
  { pose proof (corner_bl_in q (Rlt_le _ _ Hq)) as Hd1.
    pose proof (corner_tr_in q (Rlt_le _ _ Hq)) as Hd2.
    destruct (Hsurj _ Hd1) as [w1 [Hw1 Hfw1]].
    destruct (Hsurj _ Hd2) as [w2 [Hw2 Hfw2]].
    pose proof (Hdist _ _ Hw1 Hw2) as Hd.
    rewrite Hfw1, Hfw2, sqDist_corners in Hd.
    pose proof (sqDist_le_in_square p _ _ Hw1 Hw2) as Hb.
    lra. }
  assert (Hsq : qs p * qs p = qs q * qs q) by lra.
  assert (Hfac : (qs p - qs q) * (qs p + qs q) = 0) by nra.
  apply Rmult_integral in Hfac.
  destruct Hfac; lra.
Qed.

(* Squares of equal side are congruent, via the translation matching their
   bottom-left corners. *)
Lemma congruent_of_side_eq (p q : Sq) :
  qs p = qs q -> Congruent (SqSet p) (SqSet q).
Proof.
  intros Hs.
  exists (fun w => (fst w + (qx q - qx p), snd w + (qy q - qy p))).
  split; [| split; [| split]].
  - intros [a b] [[H1 H2] [H3 H4]].
    unfold SqSet, InClosed in *; simpl in *.
    lra.
  - intros [a b] [c d] _ _ H.
    injection H; intros; f_equal; lra.
  - intros [a b] Hab.
    unfold SqSet, InClosed in Hab; simpl in Hab.
    exists (a - (qx q - qx p), b - (qy q - qy p)).
    split.
    + unfold SqSet, InClosed; simpl; lra.
    + simpl; f_equal; ring.
  - intros [a b] [c d] _ _.
    unfold sqDist; simpl; ring.
Qed.

(* Squares of different positive sides are not congruent — not even via an
   arbitrary squared-distance-preserving bijection. *)
Lemma noncongruent_of_side_ne (p q : Sq) :
  0 < qs p -> 0 < qs q -> qs p <> qs q -> ~ Congruent (SqSet p) (SqSet q).
Proof.
  intros Hp Hq Hne Hc.
  apply Hne, (side_eq_of_congruent p q Hp Hq Hc).
Qed.

Definition PairwiseNoncongruent (l : list Sq) : Prop :=
  ForallOrdPairs (fun p q => ~ Congruent (SqSet p) (SqSet q)) l.

(* A perfect squared square of side L: a dissection of [0, L] x [0, L] into
   at least two squares that are pairwise non-congruent. *)
Definition IsPerfectSquaredSquare (L : R) (l : list Sq) : Prop :=
  IsDissection L l /\ (2 <= length l)%nat /\ PairwiseNoncongruent l.

(* Boolean pairwise checker used by the computational certificates. *)
Fixpoint pairwiseb {A : Type} (f : A -> A -> bool) (l : list A) : bool :=
  match l with
  | nil => true
  | x :: r => andb (forallb (f x) r) (pairwiseb f r)
  end.

Lemma pairwiseb_sound {A : Type} (f : A -> A -> bool) (R : A -> A -> Prop) :
  (forall a b, f a b = true -> R a b) ->
  forall l, pairwiseb f l = true -> ForallOrdPairs R l.
Proof.
  intros Hf l; induction l as [|x r IH]; simpl; intros H.
  - constructor.
  - apply andb_prop in H; destruct H as [H1 H2].
    constructor.
    + rewrite Forall_forall; intros b Hb.
      apply Hf.
      exact (proj1 (forallb_forall (f x) r) H1 b Hb).
    + exact (IH H2).
Qed.

Lemma ForallOrdPairs_map {A B : Type} (f : A -> B) (R : B -> B -> Prop)
    (l : list A) :
  ForallOrdPairs (fun a b => R (f a) (f b)) l ->
  ForallOrdPairs R (map f l).
Proof.
  induction 1; simpl; constructor; auto.
  rewrite Forall_map; assumption.
Qed.

End SquaredSquare.
End LeanProofs.
