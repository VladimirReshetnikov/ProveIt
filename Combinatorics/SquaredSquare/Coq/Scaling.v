(*
  Scaling a perfect squared square.

  Coq port of the Lean module SquaredSquare.Scaling: applying the dilation
  (u, v) |-> (c*u, c*v) for c > 0 to a dissection of [0, L]^2 yields a
  dissection of [0, c*L]^2, and non-congruence of pieces is preserved
  because congruences can be conjugated by the dilation.  Combined with
  Duijvestijn's dissection of the side-112 square this shows that every
  square of positive side can be cut into 21 pairwise non-congruent
  squares.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Psatz.
From SquaredSquare Require Import Defs Duijvestijn Intervals Minimality.
Import ListNotations.
Import Defs.LeanProofs.SquaredSquare.
Import Intervals.LeanProofs.SquaredSquare.
Import Minimality.LeanProofs.SquaredSquare.

Open Scope R_scope.

Module LeanProofs.
Module SquaredSquare.

Definition scaleSq (c : R) (q : Sq) : Sq :=
  mkSq (c * qx q) (c * qy q) (c * qs q).

(* Division helpers. *)

Lemma scale_le_l : forall c a u, 0 < c -> c * a <= u -> a <= u / c.
Proof.
  intros c a u Hc H.
  apply (Rmult_le_reg_l c); [lra |].
  replace (c * (u / c)) with u by (field; lra).
  exact H.
Qed.

Lemma scale_le_r : forall c a u, 0 < c -> u <= c * a -> u / c <= a.
Proof.
  intros c a u Hc H.
  apply (Rmult_le_reg_l c); [lra |].
  replace (c * (u / c)) with u by (field; lra).
  exact H.
Qed.

Lemma scale_lt_l : forall c a u, 0 < c -> c * a < u -> a < u / c.
Proof.
  intros c a u Hc H.
  apply (Rmult_lt_reg_l c); [lra |].
  replace (c * (u / c)) with u by (field; lra).
  exact H.
Qed.

Lemma scale_lt_r : forall c a u, 0 < c -> u < c * a -> u / c < a.
Proof.
  intros c a u Hc H.
  apply (Rmult_lt_reg_l c); [lra |].
  replace (c * (u / c)) with u by (field; lra).
  exact H.
Qed.

Lemma scale_back_le_l : forall c a u, 0 < c -> a <= u / c -> c * a <= u.
Proof.
  intros c a u Hc H.
  replace u with (c * (u / c)) by (field; lra).
  apply Rmult_le_compat_l; lra.
Qed.

Lemma scale_back_le_r : forall c a u, 0 < c -> u / c <= a -> u <= c * a.
Proof.
  intros c a u Hc H.
  replace u with (c * (u / c)) by (field; lra).
  apply Rmult_le_compat_l; lra.
Qed.

Lemma scale_back_lt_l : forall c a u, 0 < c -> a < u / c -> c * a < u.
Proof.
  intros c a u Hc H.
  replace u with (c * (u / c)) by (field; lra).
  apply Rmult_lt_compat_l; lra.
Qed.

Lemma scale_back_lt_r : forall c a u, 0 < c -> u / c < a -> u < c * a.
Proof.
  intros c a u Hc H.
  replace u with (c * (u / c)) by (field; lra).
  apply Rmult_lt_compat_l; lra.
Qed.

(* Membership transfers along the dilation. *)

Lemma InClosed_scale : forall c q u v, 0 < c ->
  (InClosed (scaleSq c q) u v <-> InClosed q (u / c) (v / c)).
Proof.
  intros c q u v Hc.
  unfold InClosed, scaleSq; simpl.
  split.
  - intros [[H1 H2] [H3 H4]].
    replace (c * qx q + c * qs q) with (c * (qx q + qs q)) in H2 by ring.
    replace (c * qy q + c * qs q) with (c * (qy q + qs q)) in H4 by ring.
    repeat split; auto using scale_le_l, scale_le_r.
  - intros [[H1 H2] [H3 H4]].
    replace (c * qx q + c * qs q) with (c * (qx q + qs q)) by ring.
    replace (c * qy q + c * qs q) with (c * (qy q + qs q)) by ring.
    repeat split; auto using scale_back_le_l, scale_back_le_r.
Qed.

Lemma InOpen_scale : forall c q u v, 0 < c ->
  (InOpen (scaleSq c q) u v <-> InOpen q (u / c) (v / c)).
Proof.
  intros c q u v Hc.
  unfold InOpen, scaleSq; simpl.
  split.
  - intros [[H1 H2] [H3 H4]].
    replace (c * qx q + c * qs q) with (c * (qx q + qs q)) in H2 by ring.
    replace (c * qy q + c * qs q) with (c * (qy q + qs q)) in H4 by ring.
    repeat split; auto using scale_lt_l, scale_lt_r.
  - intros [[H1 H2] [H3 H4]].
    replace (c * qx q + c * qs q) with (c * (qx q + qs q)) by ring.
    replace (c * qy q + c * qs q) with (c * (qy q + qs q)) by ring.
    repeat split; auto using scale_back_lt_l, scale_back_lt_r.
Qed.

Lemma InBig_scale : forall c L u v, 0 < c ->
  (InBig (c * L) u v <-> InBig L (u / c) (v / c)).
Proof.
  intros c L u v Hc.
  unfold InBig.
  split.
  - intros [[H1 H2] [H3 H4]].
    replace 0 with (c * 0) in H1 by ring.
    replace 0 with (c * 0) in H3 by ring.
    repeat split; auto using scale_le_l, scale_le_r.
  - intros [[H1 H2] [H3 H4]].
    split; split.
    + replace 0 with (c * 0) by ring.
      apply scale_back_le_l; assumption.
    + apply scale_back_le_r; assumption.
    + replace 0 with (c * 0) by ring.
      apply scale_back_le_l; assumption.
    + apply scale_back_le_r; assumption.
Qed.

(* Scaling a dissection. *)

Lemma IsDissection_scale : forall c L l, 0 < c ->
  IsDissection L l -> IsDissection (c * L) (map (scaleSq c) l).
Proof.
  intros c L l Hc hd.
  constructor.
  - intros q Hq.
    apply in_map_iff in Hq; destruct Hq as [r [Hr1 Hr2]]; subst q.
    unfold scaleSq; simpl.
    pose proof (diss_pos L l hd r Hr2).
    apply Rmult_lt_0_compat; assumption.
  - apply ForallOrdPairs_map.
    apply (FOP_imp_mem DisjointOpen); [exact (diss_disj L l hd) |].
    intros a b Ha Hb Hab u v H1 H2.
    apply (InOpen_scale c a u v Hc) in H1.
    apply (InOpen_scale c b u v Hc) in H2.
    exact (Hab (u / c) (v / c) H1 H2).
  - intros u v.
    rewrite (InBig_scale c L u v Hc).
    rewrite (diss_cover L l hd (u / c) (v / c)).
    split.
    + intros [q [Hq Hqc]].
      exists (scaleSq c q); split.
      * apply in_map; exact Hq.
      * apply (InClosed_scale c q u v Hc); exact Hqc.
    + intros [q [Hq Hqc]].
      apply in_map_iff in Hq; destruct Hq as [r [Hr1 Hr2]]; subst q.
      exists r; split; [exact Hr2 |].
      apply (InClosed_scale c r u v Hc); exact Hqc.
Qed.

(* Congruence descends along the dilation. *)

Lemma sqDist_scale : forall c a1 a2 b1 b2,
  sqDist (c * a1, c * a2) (c * b1, c * b2) = c * c * sqDist (a1, a2) (b1, b2).
Proof.
  intros; unfold sqDist; simpl; ring.
Qed.

Lemma congruent_of_scale_congruent : forall c p q, 0 < c ->
  Congruent (SqSet (scaleSq c p)) (SqSet (scaleSq c q)) ->
  Congruent (SqSet p) (SqSet q).
Proof.
  intros c p q Hc [f [Hmap [Hinj [Hsurj Hdist]]]].
  assert (Hcancel : forall w : R, c * w / c = w).
  { intros w; field; lra. }
  assert (Hto : forall w : R * R, SqSet p w ->
      SqSet (scaleSq c p) (c * fst w, c * snd w)).
  { intros [a b] Hw.
    unfold SqSet in *; simpl in *.
    apply (InClosed_scale c p (c * a) (c * b) Hc).
    rewrite !Hcancel; exact Hw. }
  assert (Hto' : forall w : R * R, SqSet q w ->
      SqSet (scaleSq c q) (c * fst w, c * snd w)).
  { intros [a b] Hw.
    unfold SqSet in *; simpl in *.
    apply (InClosed_scale c q (c * a) (c * b) Hc).
    rewrite !Hcancel; exact Hw. }
  exists (fun w => (fst (f (c * fst w, c * snd w)) / c,
                    snd (f (c * fst w, c * snd w)) / c)).
  split; [| split; [| split]].
  - (* maps into *)
    intros w Hw.
    pose proof (Hmap _ (Hto w Hw)) as Hf.
    unfold SqSet in Hf |- *; simpl.
    apply (InClosed_scale c q _ _ Hc) in Hf.
    exact Hf.
  - (* injective *)
    intros w1 w2 Hw1 Hw2 He.
    assert (Hfe : f (c * fst w1, c * snd w1) = f (c * fst w2, c * snd w2)).
    { apply injective_projections.
      - apply (Rmult_eq_reg_l (/ c)); [| apply Rinv_neq_0_compat; lra].
        pose proof (f_equal (@fst R R) He) as He1; simpl in He1.
        unfold Rdiv in He1; lra.
      - apply (Rmult_eq_reg_l (/ c)); [| apply Rinv_neq_0_compat; lra].
        pose proof (f_equal (@snd R R) He) as He2; simpl in He2.
        unfold Rdiv in He2; lra. }
    pose proof (Hinj _ _ (Hto w1 Hw1) (Hto w2 Hw2) Hfe) as Hp.
    apply injective_projections.
    + pose proof (f_equal (@fst R R) Hp) as Hp1; simpl in Hp1.
      apply (Rmult_eq_reg_l c); lra.
    + pose proof (f_equal (@snd R R) Hp) as Hp2; simpl in Hp2.
      apply (Rmult_eq_reg_l c); lra.
  - (* surjective *)
    intros b Hb.
    destruct (Hsurj (c * fst b, c * snd b) (Hto' b Hb)) as [w [Hw Hfw]].
    exists (fst w / c, snd w / c).
    split.
    + unfold SqSet in Hw |- *; simpl.
      apply (InClosed_scale c p _ _ Hc) in Hw.
      exact Hw.
    + simpl.
      replace (c * (fst w / c)) with (fst w) by (field; lra).
      replace (c * (snd w / c)) with (snd w) by (field; lra).
      rewrite <- (surjective_pairing w).
      rewrite Hfw; simpl.
      rewrite !Hcancel.
      apply injective_projections; simpl; reflexivity.
  - (* squared distances *)
    intros w1 w2 Hw1 Hw2.
    pose proof (Hdist _ _ (Hto w1 Hw1) (Hto w2 Hw2)) as Hd.
    unfold sqDist in *; simpl in *.
    assert (Hc2 : c * c <> 0) by (apply Rmult_integral_contrapositive; lra).
    apply (Rmult_eq_reg_l (c * c)); [| exact Hc2].
    replace (c * c *
      ((fst (f (c * fst w1, c * snd w1)) / c -
        fst (f (c * fst w2, c * snd w2)) / c) *
       (fst (f (c * fst w1, c * snd w1)) / c -
        fst (f (c * fst w2, c * snd w2)) / c) +
       (snd (f (c * fst w1, c * snd w1)) / c -
        snd (f (c * fst w2, c * snd w2)) / c) *
       (snd (f (c * fst w1, c * snd w1)) / c -
        snd (f (c * fst w2, c * snd w2)) / c)))
      with
      ((fst (f (c * fst w1, c * snd w1)) -
        fst (f (c * fst w2, c * snd w2))) *
       (fst (f (c * fst w1, c * snd w1)) -
        fst (f (c * fst w2, c * snd w2))) +
       (snd (f (c * fst w1, c * snd w1)) -
        snd (f (c * fst w2, c * snd w2))) *
       (snd (f (c * fst w1, c * snd w1)) -
        snd (f (c * fst w2, c * snd w2))))
      by (field; lra).
    rewrite Hd.
    ring.
Qed.

(* Scaling a perfect squared square. *)

Lemma IsPerfect_scale : forall c L l, 0 < c ->
  IsPerfectSquaredSquare L l ->
  IsPerfectSquaredSquare (c * L) (map (scaleSq c) l).
Proof.
  intros c L l Hc [hd [H2 Hnc]].
  split; [exact (IsDissection_scale c L l Hc hd) |].
  split.
  - rewrite length_map; exact H2.
  - unfold PairwiseNoncongruent.
    apply ForallOrdPairs_map.
    apply (FOP_imp_mem
      (fun p q => ~ Congruent (SqSet p) (SqSet q))); [exact Hnc |].
    intros a b Ha Hb Hab Hcong.
    exact (Hab (congruent_of_scale_congruent c a b Hc Hcong)).
Qed.

(* Every square of positive side can be cut into 21 pairwise
   non-congruent squares. *)
Theorem exists_perfect_squared_square_of_side : forall L, 0 < L ->
  exists l : list Sq, length l = 21%nat /\ IsPerfectSquaredSquare L l.
Proof.
  intros L HL.
  set (c := L / 112).
  assert (Hc : 0 < c) by (unfold c; lra).
  exists (map (scaleSq c) Duijvestijn.LeanProofs.SquaredSquare.duijvestijnTiles).
  split.
  - rewrite length_map.
    exact Duijvestijn.LeanProofs.SquaredSquare.duijvestijnTiles_length.
  - replace L with (c * 112) by (unfold c; field).
    apply (IsPerfect_scale c 112 _ Hc).
    exact Duijvestijn.LeanProofs.SquaredSquare.duijvestijn_perfect.
Qed.

End SquaredSquare.
End LeanProofs.
