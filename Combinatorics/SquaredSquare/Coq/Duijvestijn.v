(*
  Duijvestijn's perfect squared square of order 21.

  Coq port of the Lean module SquaredSquare.Duijvestijn.  The placement data
  (bottom-left corner and side of each piece, integer coordinates) decodes
  the Bouwkamp code

    (50, 35, 27) (8, 19) (15, 17, 11) (6, 24) (29, 25, 9, 2) (7, 18) (16)
    (42) (4, 37) (33)

  of A. J. W. Duijvestijn's 1978 dissection of the side-112 square into 21
  squares with pairwise distinct sides.

  All combinatorial facts about the data — in-bounds placement, pairwise
  separation of the open pieces, distinct sides, and coverage of every unit
  grid cell — are boolean statements about integers discharged by
  vm_compute.  The real-plane statements are then obtained by elementary
  lifting lemmas: a point of [0, 112]^2 lies in the unit cell of its
  coordinates' integer parts, and that cell is contained in one of the 21
  closed pieces.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Psatz.
From Stdlib Require Import Bool.
From SquaredSquare Require Import Defs.
Import ListNotations.
Import LeanProofs.SquaredSquare.

Open Scope R_scope.

Module LeanProofs.
Module SquaredSquare.

(* Bottom-left corners and sides (x, y, s) of the 21 pieces. *)
Definition tileData : list (Z * Z * Z) :=
  ((0, 62, 50) :: (50, 77, 35) :: (85, 85, 27) :: (85, 77, 8) :: (93, 66, 19)
   :: (50, 62, 15) :: (65, 60, 17) :: (82, 66, 11) :: (82, 60, 6)
   :: (88, 42, 24) :: (0, 33, 29) :: (29, 37, 25) :: (54, 53, 9)
   :: (63, 60, 2) :: (63, 53, 7) :: (70, 42, 18) :: (54, 37, 16)
   :: (70, 0, 42) :: (29, 33, 4) :: (33, 0, 37) :: (0, 0, 33) :: nil)%Z.

Definition px (t : Z * Z * Z) : Z := fst (fst t).
Definition py (t : Z * Z * Z) : Z := snd (fst t).
Definition side (t : Z * Z * Z) : Z := snd t.

(* ---------------------------------------------------------------------- *)
(* Boolean certificates, checked by vm_compute.                            *)
(* ---------------------------------------------------------------------- *)

Definition tileOkb (t : Z * Z * Z) : bool :=
  ((0 <? side t) && (0 <=? px t) && (0 <=? py t)
   && (px t + side t <=? 112) && (py t + side t <=? 112))%Z.

Definition sepb (t u : Z * Z * Z) : bool :=
  ((px t + side t <=? px u) || (px u + side u <=? px t)
   || (py t + side t <=? py u) || (py u + side u <=? py t))%Z.

Definition sidesb (t u : Z * Z * Z) : bool :=
  ((0 <? side t) && (0 <? side u) && negb (side t =? side u))%Z.

Definition coversb (i j : Z) (t : Z * Z * Z) : bool :=
  ((px t <=? i) && (i + 1 <=? px t + side t)
   && (py t <=? j) && (j + 1 <=? py t + side t))%Z.

Lemma tileData_ok : forallb tileOkb tileData = true.
Proof. vm_compute; reflexivity. Qed.

Lemma tileData_sep : pairwiseb sepb tileData = true.
Proof. vm_compute; reflexivity. Qed.

Lemma tileData_sides : pairwiseb sidesb tileData = true.
Proof. vm_compute; reflexivity. Qed.

(* Every unit grid cell of [0, 112]^2 is contained in one of the pieces. *)
Lemma tileData_cells :
  forallb (fun i => forallb
             (fun j => existsb (coversb (Z.of_nat i) (Z.of_nat j)) tileData)
             (seq 0 112))
          (seq 0 112) = true.
Proof. vm_compute; reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* Unpacking the certificates.                                             *)
(* ---------------------------------------------------------------------- *)

Lemma tileOk_spec : forall t, In t tileData ->
  (0 < side t /\ 0 <= px t /\ 0 <= py t
   /\ px t + side t <= 112 /\ py t + side t <= 112)%Z.
Proof.
  intros t Ht.
  pose proof (proj1 (forallb_forall tileOkb tileData) tileData_ok t Ht) as H.
  unfold tileOkb in H.
  apply andb_prop in H; destruct H as [H H5].
  apply andb_prop in H; destruct H as [H H4].
  apply andb_prop in H; destruct H as [H H3].
  apply andb_prop in H; destruct H as [H1 H2].
  apply Z.ltb_lt in H1.
  apply Z.leb_le in H2, H3, H4, H5.
  tauto.
Qed.

(* Interpret an integer data triple as a placed square in the plane. *)
Definition toSq (t : Z * Z * Z) : Sq :=
  mkSq (IZR (px t)) (IZR (py t)) (IZR (side t)).

(* The 21 pieces of Duijvestijn's dissection as real placed squares. *)
Definition duijvestijnTiles : list Sq := map toSq tileData.

Lemma duijvestijnTiles_length : length duijvestijnTiles = 21%nat.
Proof. reflexivity. Qed.

Lemma duijvestijn_pos : forall q, In q duijvestijnTiles -> 0 < qs q.
Proof.
  intros q Hq.
  unfold duijvestijnTiles in Hq.
  apply in_map_iff in Hq; destruct Hq as [t [Heq Ht]]; subst q.
  pose proof (tileOk_spec t Ht) as [Hs _].
  simpl.
  apply (IZR_lt 0), Hs.
Qed.

Lemma sep_disjoint : forall t u,
  sepb t u = true -> DisjointOpen (toSq t) (toSq u).
Proof.
  intros t u H a b [[Ht1 Ht2] [Ht3 Ht4]] [[Hu1 Hu2] [Hu3 Hu4]].
  unfold toSq in *; simpl in *.
  unfold sepb in H.
  apply orb_prop in H; destruct H as [H | H].
  2:{ apply Z.leb_le in H; apply IZR_le in H;
      rewrite plus_IZR in H; lra. }
  apply orb_prop in H; destruct H as [H | H].
  2:{ apply Z.leb_le in H; apply IZR_le in H;
      rewrite plus_IZR in H; lra. }
  apply orb_prop in H; destruct H as [H | H].
  - apply Z.leb_le in H; apply IZR_le in H;
      rewrite plus_IZR in H; lra.
  - apply Z.leb_le in H; apply IZR_le in H;
      rewrite plus_IZR in H; lra.
Qed.

Lemma duijvestijn_disj : ForallOrdPairs DisjointOpen duijvestijnTiles.
Proof.
  unfold duijvestijnTiles.
  apply ForallOrdPairs_map.
  exact (pairwiseb_sound sepb
           (fun a b => DisjointOpen (toSq a) (toSq b))
           sep_disjoint tileData tileData_sep).
Qed.

Lemma sides_noncongruent : forall t u, sidesb t u = true ->
  ~ Congruent (SqSet (toSq t)) (SqSet (toSq u)).
Proof.
  intros t u H.
  unfold sidesb in H.
  apply andb_prop in H; destruct H as [H H3].
  apply andb_prop in H; destruct H as [H1 H2].
  apply Z.ltb_lt in H1, H2.
  apply negb_true_iff in H3.
  apply Z.eqb_neq in H3.
  apply noncongruent_of_side_ne; simpl.
  - apply (IZR_lt 0), H1.
  - apply (IZR_lt 0), H2.
  - intro He; apply H3, eq_IZR, He.
Qed.

Theorem duijvestijn_noncongruent : PairwiseNoncongruent duijvestijnTiles.
Proof.
  unfold PairwiseNoncongruent, duijvestijnTiles.
  apply ForallOrdPairs_map.
  exact (pairwiseb_sound sidesb
           (fun a b => ~ Congruent (SqSet (toSq a)) (SqSet (toSq b)))
           sides_noncongruent tileData tileData_sides).
Qed.

(* ---------------------------------------------------------------------- *)
(* Coverage: lifting the unit-cell certificate to the real plane.          *)
(* ---------------------------------------------------------------------- *)

Lemma tile_in_big : forall t, In t tileData -> forall u v,
  InClosed (toSq t) u v -> InBig 112 u v.
Proof.
  intros t Ht u v [[H1 H2] [H3 H4]].
  pose proof (tileOk_spec t Ht) as [Hs [Hx [Hy [Hxs Hys]]]].
  unfold toSq in *; simpl in *.
  apply IZR_le in Hx, Hy, Hxs, Hys.
  rewrite plus_IZR in Hxs, Hys.
  unfold InBig.
  repeat split; lra.
Qed.

(* A coordinate of [0, 112] lies in the unit interval of its clamped
   integer part. *)
Lemma cell_of_coord : forall u, 0 <= u <= 112 ->
  exists z : Z, (0 <= z <= 111)%Z /\ IZR z <= u /\ u <= IZR z + 1.
Proof.
  intros u [Hu0 Hu1].
  destruct (base_Int_part u) as [Hle Hgt].
  assert (Hnn : (-1 < Int_part u)%Z).
  { apply lt_IZR; lra. }
  destruct (Z_le_gt_dec (Int_part u) 111) as [Hz | Hz].
  - exists (Int_part u).
    split; [lia | split; lra].
  - exists 111%Z.
    assert (H112 : IZR 112 <= IZR (Int_part u)) by (apply IZR_le; lia).
    split; [lia | split; lra].
Qed.

Lemma cells_exist : forall zi zj : Z,
  (0 <= zi <= 111)%Z -> (0 <= zj <= 111)%Z ->
  exists t, In t tileData /\
    (px t <= zi /\ zi + 1 <= px t + side t
     /\ py t <= zj /\ zj + 1 <= py t + side t)%Z.
Proof.
  intros zi zj Hzi Hzj.
  pose proof tileData_cells as H.
  assert (Hi : In (Z.to_nat zi) (seq 0 112)) by (apply in_seq; lia).
  assert (Hj : In (Z.to_nat zj) (seq 0 112)) by (apply in_seq; lia).
  pose proof (proj1 (forallb_forall _ _) H (Z.to_nat zi) Hi) as Hrow.
  pose proof (proj1 (forallb_forall _ _) Hrow (Z.to_nat zj) Hj) as Hcell.
  apply existsb_exists in Hcell.
  destruct Hcell as [t [Ht Hc]].
  exists t; split; [exact Ht |].
  unfold coversb in Hc.
  apply andb_prop in Hc; destruct Hc as [Hc H4].
  apply andb_prop in Hc; destruct Hc as [Hc H3].
  apply andb_prop in Hc; destruct Hc as [H1 H2].
  apply Z.leb_le in H1, H2, H3, H4.
  rewrite Z2Nat.id in H1, H2, H3, H4 by lia.
  tauto.
Qed.

Lemma big_in_tiles : forall u v, InBig 112 u v ->
  exists q, In q duijvestijnTiles /\ InClosed q u v.
Proof.
  intros u v [[Hu0 Hu1] [Hv0 Hv1]].
  destruct (cell_of_coord u (conj Hu0 Hu1)) as [zi [Hzib [Hzi1 Hzi2]]].
  destruct (cell_of_coord v (conj Hv0 Hv1)) as [zj [Hzjb [Hzj1 Hzj2]]].
  destruct (cells_exist zi zj Hzib Hzjb) as [t [Ht [H1 [H2 [H3 H4]]]]].
  exists (toSq t); split.
  - apply in_map, Ht.
  - unfold toSq, InClosed; simpl.
    apply IZR_le in H1, H2, H3, H4.
    rewrite !plus_IZR in H2, H4.
    repeat split; lra.
Qed.

Lemma duijvestijn_cover : forall u v,
  InBig 112 u v <-> exists q, In q duijvestijnTiles /\ InClosed q u v.
Proof.
  intros u v; split.
  - apply big_in_tiles.
  - intros [q [Hq Hc]].
    unfold duijvestijnTiles in Hq; apply in_map_iff in Hq.
    destruct Hq as [t [Heq Ht]]; subst q.
    exact (tile_in_big t Ht u v Hc).
Qed.

(* ---------------------------------------------------------------------- *)
(* Main results.                                                           *)
(* ---------------------------------------------------------------------- *)

(* Duijvestijn's 21 squares dissect the square of side 112. *)
Theorem duijvestijn_isDissection : IsDissection 112 duijvestijnTiles.
Proof.
  constructor.
  - exact duijvestijn_pos.
  - exact duijvestijn_disj.
  - exact duijvestijn_cover.
Qed.

(* Duijvestijn's perfect squared square: the square of side 112 is cut into
   21 pairwise non-congruent squares. *)
Theorem duijvestijn_perfect : IsPerfectSquaredSquare 112 duijvestijnTiles.
Proof.
  split; [exact duijvestijn_isDissection |].
  split; [rewrite duijvestijnTiles_length; lia |].
  exact duijvestijn_noncongruent.
Qed.

(* Squaring the square (existence): some square can be cut into finitely
   many pairwise non-congruent squares — indeed into 21 of them. *)
Theorem exists_perfect_squared_square :
  exists l : list Sq, length l = 21%nat /\ IsPerfectSquaredSquare 112 l.
Proof.
  exists duijvestijnTiles.
  split; [exact duijvestijnTiles_length | exact duijvestijn_perfect].
Qed.

End SquaredSquare.
End LeanProofs.
