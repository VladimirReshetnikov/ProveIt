(**
  Canonical finite converse-well-founded frame ranks.

  This module closes the representation gap left by [StructuralFrames]'s
  abstract [frame_rank_spec].  A data-carrying [finite_enumeration] and a
  proof that the converse accessibility relation is well founded determine
  the canonical [cwf_height] rank.  Transitivity gives precisely the two
  fields of [frame_rank_spec], so all path, terminal, rooted-height, and modal
  results already proved there apply without duplication.

  Foundation's [extendRoot n] uses [Fin n + World F].  The existing
  [FrameTransformations.extend_root_frame] is exactly that presentation, so
  the source-facing adapters below use it directly.  Its algebraic rank makes
  the general law

      rank (new root number k) = base height + k

  structural; uniqueness of [frame_rank_spec] then identifies that algebraic
  rank with the canonical [cwf_height] construction.  In particular, the
  source's [n = 1] lemmas are immediate special cases without an unproved
  representation equivalence.

  The pinned source asserts point-generated rank preservation as an axiom.
  Here it is a theorem: [StructuralFrames.point_generated_rank_spec] proves
  that restriction is a rank, and uniqueness of [frame_rank_spec] identifies
  it with the independently constructed canonical rank of the generated
  frame.

  Active declaration map for pinned [Modal/Kripke/Rank.lean] (24 entries):

  1  [Frame.rank]                         [finite_cwf_frame_rank]
  2  [Frame.height]                       [finite_cwf_frame_height]
  3  [rank_lt_of_rel]                     reused [rank_lt_of_rel]
  4  [exists_of_lt_height]                reused [rank_exists_of_lt]
  5  [height_lt_iff_relItr]               reused [rank_lt_iff_no_iter]
  6  [le_height_iff_relItr]               reused [rank_le_iff_iter]
  7  [height_eq_iff_relItr]               reused [rank_eq_iff_iter_terminal]
  8  [exists_rank_terminal]               reused [rank_terminal_exists]
  9  [terminal_rel_height]                reused [rank_path_endpoint_terminal]
  10 [rank_lt_whole_height]               reused [rank_lt_height_of_root_rel]
  11 [rank_le_whole_height]               reused [rank_le_height_of_root]
  12 [eq_height_root]                     reused [rank_eq_height_iff_root]
  13 [eq_extendRoot_height_...root]        [finite_cwf_extend_root_height_unfold]
  14 [extendRoot.height_pos]               [finite_cwf_extend_root_height_positive]
  15 [extendRoot.height_succ]              [finite_cwf_one_root_height_successor]
  16 [extendRoot.eq_original_height]       [finite_cwf_extend_root_rank_original]
  17 [extendRoot.eq_original_height_root]  [finite_cwf_extend_root_rank_base_root]
  18 [extendRoot.iff_eq_height_...root]     [finite_cwf_extend_root_eq_base_height_iff]
  19 point-generated [Fintype]             reused [point_generated_frame_finite]
     (and data form [point_generated_finite_enumeration] below)
  20 point-generated [IsTree]              [point_generated_frame_is_tree]
  21 [pointGenerate.eq_original_height]    [finite_cwf_point_generated_rank_original]
  22 [height_lt_iff_satisfies_boxbot]      reused [rank_lt_iff_satisfies_box_bottom]
  23 [height_pos_of_dia]                   reused [rank_positive_of_diamond]
  24 [Model.extendRoot.height_1]           the same frame theorem as entry 15;
     local models are represented by a frame and a separate valuation.
*)

From Stdlib Require Import Arith.Compare_dec Arith.PeanoNat Arith.Wf_nat Lia.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Wellfounded.Wellfounded.
From FoundationModal Require Import
  Kripke Correspondence Filtration Loeb FrameProperties RelationProperties Root
  ConverseWellFounded FrameTransformations StructuralFrames.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * From generic finite heights to frame ranks *)

(** A data-carrying enumeration implies the proposition-valued local notion
    of a finite frame.  The converse is intentionally absent: eliminating a
    [Prop]-valued existential into the computational [finite_enumeration]
    record would violate the same [Finite]/[Fintype] boundary present in the
    source. *)
Definition finite_enumeration_frame_finite
    (F : frame) (E : finite_enumeration (World F)) : finite_frame F :=
  ex_intro _ (finite_enum E) (finite_enum_complete E).

(** Bridge the older maximal-element frame interface to ordinary
    well-foundedness of the converse relation. *)
Definition frame_cwf_as_converse_well_founded
    (F : frame) (Hcwf : frame_converse_well_founded F)
    : converse_well_founded (Rel F) :=
  (proj1 (converse_well_founded_iff_well_founded_converse F)) Hcwf.

(** Any rank specification itself proves converse well-foundedness: every
    predecessor for the converse relation strictly lowers [rank]. *)
Lemma frame_rank_spec_converse_well_founded :
  forall F rank,
    frame_rank_spec F rank -> converse_well_founded (Rel F).
Proof.
  intros F rank Hrank. unfold converse_well_founded.
  apply (well_founded_lt_compat
    (World F) rank (relation_converse (Rel F))).
  intros x y Hyx. unfold relation_converse in Hyx.
  now apply (rank_rel_decreases Hrank y x Hyx).
Qed.

(** Source declarations 1/24 and 2/24. *)
Definition finite_cwf_frame_rank
    (F : frame) (E : finite_enumeration (World F))
    (Hwf : converse_well_founded (Rel F)) (x : World F) : nat :=
  cwf_height E (Rel F) Hwf x.

Arguments finite_cwf_frame_rank F E Hwf x : clear implicits.

Definition finite_cwf_frame_height
    (F : frame) (E : finite_enumeration (World F))
    (Hwf : converse_well_founded (Rel F)) (r : World F) : nat :=
  frame_height (finite_cwf_frame_rank F E Hwf) r.

Arguments finite_cwf_frame_height F E Hwf r : clear implicits.

Theorem finite_cwf_frame_rank_spec :
  forall (F : frame) (E : finite_enumeration (World F))
         (Hwf : converse_well_founded (Rel F)),
    frame_transitive F ->
    frame_rank_spec F (finite_cwf_frame_rank F E Hwf).
Proof.
  intros F E Hwf Htrans; constructor.
  - intros x y Hxy.
    exact (@cwf_height_gt_of (World F) E (Rel F) Hwf x y Hxy).
  - intros x n Hn.
    exact (@cwf_height_lt (World F) E (Rel F) Hwf Htrans x n Hn).
Qed.

(** Rank specifications are unique.  This turns an elegant algebraic rank
    proof into an equality with the canonical well-founded construction. *)
Theorem frame_rank_spec_unique :
  forall F (rank1 rank2 : World F -> nat),
    frame_rank_spec F rank1 -> frame_rank_spec F rank2 ->
    forall x, rank1 x = rank2 x.
Proof.
  intros F rank1 rank2 Hrank1 Hrank2 x. symmetry.
  apply (proj2 (rank_eq_iff_iter_terminal Hrank2 (rank1 x) x)).
  split.
  - exact (rank_terminal_exists Hrank1 x).
  - intros y Hxy z.
    exact (@rank_path_endpoint_terminal F rank1 Hrank1 x y Hxy z).
Qed.

(** * Point-generated canonical ranks *)

Definition point_generated_finite_enumeration
    (F : frame) (r : World F) (E : finite_enumeration (World F))
    : finite_enumeration (World (point_generated_frame F r)).
Proof.
  refine {| finite_enum :=
      point_generated_cover F r (finite_enum E) |}.
  apply point_generated_cover_complete.
  apply finite_enum_complete.
Defined.

Arguments point_generated_finite_enumeration F r E : clear implicits.

Theorem point_generated_frame_is_tree :
  forall (F : frame) (r : World F),
    frame_is_tree F -> frame_is_tree (point_generated_frame F r).
Proof.
  intros F r [_ [Hasym Htrans]]. repeat split.
  - apply point_generated_frame_rooted.
  - now apply point_generated_asymmetric.
  - now apply point_generated_transitive.
Qed.

Definition finite_cwf_point_generated_relation_cwf
    (F : frame) (E : finite_enumeration (World F))
    (Hwf : converse_well_founded (Rel F))
    (Htrans : frame_transitive F) (r : World F)
    : converse_well_founded (Rel (point_generated_frame F r)) :=
  frame_rank_spec_converse_well_founded
    (point_generated_rank_spec
      (finite_cwf_frame_rank_spec E Hwf Htrans) Htrans r).

Definition finite_cwf_point_generated_rank
    (F : frame) (E : finite_enumeration (World F))
    (Hwf : converse_well_founded (Rel F))
    (Htrans : frame_transitive F) (r : World F)
    (x : World (point_generated_frame F r)) : nat :=
  finite_cwf_frame_rank (point_generated_frame F r)
    (point_generated_finite_enumeration F r E)
    (@finite_cwf_point_generated_relation_cwf F E Hwf Htrans r) x.

Arguments finite_cwf_point_generated_rank F E Hwf Htrans r x
  : clear implicits.

Lemma finite_cwf_point_generated_rank_spec :
  forall (F : frame) (E : finite_enumeration (World F))
         (Hwf : converse_well_founded (Rel F))
         (Htrans : frame_transitive F) (r : World F),
    frame_rank_spec (point_generated_frame F r)
      (finite_cwf_point_generated_rank F E Hwf Htrans r).
Proof.
  intros F E Hwf Htrans r.
  unfold finite_cwf_point_generated_rank.
  apply finite_cwf_frame_rank_spec.
  now apply point_generated_transitive.
Qed.

(** Source declaration 21/24, proved rather than postulated. *)
Theorem finite_cwf_point_generated_rank_original :
  forall (F : frame) (E : finite_enumeration (World F))
         (Hwf : converse_well_founded (Rel F))
         (Htrans : frame_transitive F) (r : World F)
         (x : World (point_generated_frame F r)),
    finite_cwf_point_generated_rank F E Hwf Htrans r x =
    finite_cwf_frame_rank F E Hwf (proj1_sig x).
Proof.
  intros F E Hwf Htrans r x.
  change (finite_cwf_point_generated_rank F E Hwf Htrans r x =
    point_generated_rank (finite_cwf_frame_rank F E Hwf) r x).
  apply frame_rank_spec_unique.
  - apply finite_cwf_point_generated_rank_spec.
  - apply point_generated_rank_spec.
    + now apply finite_cwf_frame_rank_spec.
    + exact Htrans.
Qed.

(** * Exact adapters for [FrameTransformations.extend_root_frame] *)

Lemma fin_value_of_nat_lt :
  forall n k (Hk : k < n),
    fin_value (Fin.of_nat_lt Hk) = k.
Proof.
  intros n k Hk. unfold fin_value.
  now rewrite Fin.to_nat_of_nat.
Qed.

Definition extend_root_finite_enumeration
    (F : frame) (E : finite_enumeration (World F)) (n : nat)
    : finite_enumeration (World (extend_root_frame F n)).
Proof.
  refine {| finite_enum := extend_root_cover n (finite_enum E) |}.
  apply extend_root_cover_complete.
  apply finite_enum_complete.
Defined.

Arguments extend_root_finite_enumeration F E n : clear implicits.

(** Unlike the rooted height laws below, the canonical rank of an extension
    and preservation at embedded old worlds need no root in the base frame.
    This matches the source's explicit [omit IsRooted] boundary. *)
Definition finite_cwf_extend_root_relation_cwf
    (F : frame) (E : finite_enumeration (World F))
    (Hwf : converse_well_founded (Rel F))
    (Htrans : frame_transitive F) (n : nat)
    : converse_well_founded (Rel (extend_root_frame F n)) :=
  frame_cwf_as_converse_well_founded
    (@extend_root_converse_well_founded F n
      (@finite_enumeration_frame_finite F E)
      (rank_spec_irreflexive
        (finite_cwf_frame_rank_spec E Hwf Htrans))
      Htrans).

Definition finite_cwf_extend_root_rank
    (F : frame) (E : finite_enumeration (World F))
    (Hwf : converse_well_founded (Rel F))
    (Htrans : frame_transitive F) (n : nat)
    (x : World (extend_root_frame F n)) : nat :=
  finite_cwf_frame_rank (extend_root_frame F n)
    (extend_root_finite_enumeration F E n)
    (@finite_cwf_extend_root_relation_cwf F E Hwf Htrans n) x.

Arguments finite_cwf_extend_root_rank F E Hwf Htrans n x
  : clear implicits.

Lemma finite_cwf_extend_root_rank_spec :
  forall (F : frame) (E : finite_enumeration (World F))
         (Hwf : converse_well_founded (Rel F))
         (Htrans : frame_transitive F) n,
    frame_rank_spec (extend_root_frame F n)
      (finite_cwf_extend_root_rank F E Hwf Htrans n).
Proof.
  intros F E Hwf Htrans n.
  unfold finite_cwf_extend_root_rank.
  apply finite_cwf_frame_rank_spec.
  now apply extend_root_transitive.
Qed.

Definition finite_cwf_extend_root_embedded_rank
    (F : frame) (E : finite_enumeration (World F))
    (Hwf : converse_well_founded (Rel F))
    (Htrans : frame_transitive F) (n : nat)
    (x : World F) : nat :=
  finite_cwf_extend_root_rank F E Hwf Htrans n
    (@extend_root_embed F n x).

Arguments finite_cwf_extend_root_embedded_rank F E Hwf Htrans n x
  : clear implicits.

Lemma finite_cwf_extend_root_embedded_rank_spec :
  forall (F : frame) (E : finite_enumeration (World F))
         (Hwf : converse_well_founded (Rel F))
         (Htrans : frame_transitive F) n,
    frame_rank_spec F
      (finite_cwf_extend_root_embedded_rank F E Hwf Htrans n).
Proof.
  intros F E Hwf Htrans n.
  pose proof
    (finite_cwf_extend_root_rank_spec E Hwf Htrans n) as Hext.
  constructor.
  - intros x y Hxy. unfold finite_cwf_extend_root_embedded_rank.
    apply (rank_rel_decreases Hext
      (@extend_root_embed F n x) (@extend_root_embed F n y)).
    exact Hxy.
  - intros x k Hk.
    unfold finite_cwf_extend_root_embedded_rank in Hk.
    destruct (rank_realizes_lower_level Hext
      (@extend_root_embed F n x) k Hk) as [z [Hxz Hzrank]].
    destruct z as [i | y]; simpl in Hxz.
    + contradiction.
    + exists y; split; assumption.
Qed.

(** Source declaration 16/24, strengthened from one to any number of added
    roots.  Crucially, no rootedness premise occurs. *)
Theorem finite_cwf_extend_root_rank_original :
  forall (F : frame) (E : finite_enumeration (World F))
         (Hwf : converse_well_founded (Rel F))
         (Htrans : frame_transitive F) n (x : World F),
    finite_cwf_extend_root_rank F E Hwf Htrans n
      (@extend_root_embed F n x) =
    finite_cwf_frame_rank F E Hwf x.
Proof.
  intros F E Hwf Htrans n x.
  change (finite_cwf_extend_root_embedded_rank F E Hwf Htrans n x =
    finite_cwf_frame_rank F E Hwf x).
  apply frame_rank_spec_unique.
  - now apply finite_cwf_extend_root_embedded_rank_spec.
  - now apply finite_cwf_frame_rank_spec.
Qed.

(** The algebraic rank is used only for rooted height calculations. *)
Definition extend_root_algebraic_rank
    (F : frame) (rank : World F -> nat) (r : World F) (n : nat)
    (x : World (extend_root_frame F n)) : nat :=
  match x with
  | inl i => frame_height rank r + S (fin_value i)
  | inr y => rank y
  end.

Arguments extend_root_algebraic_rank F rank r n x : clear implicits.

Theorem extend_root_algebraic_rank_spec :
  forall F rank,
    frame_rank_spec F rank ->
    forall r,
      frame_root F r ->
      forall n,
        frame_rank_spec (extend_root_frame F n)
          (extend_root_algebraic_rank F rank r n).
Proof.
  intros F rank Hrank r Hroot n; constructor.
  - intros [i | x] [j | y] Hxy; simpl in *.
    + lia.
    + pose proof (rank_le_height_of_root Hrank Hroot y). lia.
    + contradiction.
    + now apply (rank_rel_decreases Hrank x y Hxy).
  - intros [i | x] k Hk; simpl in Hk |- *.
    + set (h := frame_height rank r) in *.
      destruct (le_lt_dec k h) as [Hkh | Hhk].
      * destruct (Nat.eq_dec k h) as [-> | Hneq].
        -- exists (@extend_root_embed F n r). simpl.
           split; [constructor | reflexivity].
        -- assert (Hlt : k < rank r).
           { unfold h, frame_height in *. lia. }
           destruct (rank_realizes_lower_level Hrank r k Hlt)
             as [y [Hry Hyrank]].
           exists (@extend_root_embed F n y). simpl.
           split; [constructor | exact Hyrank].
      * set (j := k - h - 1).
        assert (Hji : j < fin_value i).
        { unfold j. lia. }
        assert (Hin : fin_value i < n).
        { unfold fin_value. exact (proj2_sig (Fin.to_nat i)). }
        assert (Hjn : j < n) by lia.
        set (ji := Fin.of_nat_lt Hjn).
        exists (@extend_root_added F n ji). simpl.
        assert (Hjv : fin_value ji = j).
        { unfold ji. apply fin_value_of_nat_lt. }
        rewrite Hjv. split.
        -- exact Hji.
        -- unfold j. lia.
    + destruct (rank_realizes_lower_level Hrank x k Hk)
        as [y [Hxy Hyrank]].
      exists (@extend_root_embed F n y). simpl.
      split; assumption.
Qed.

Theorem finite_cwf_extend_root_rank_eq_algebraic :
  forall (F : frame) (E : finite_enumeration (World F))
         (Hwf : converse_well_founded (Rel F))
         (Htrans : frame_transitive F) (r : World F)
         (Hroot : frame_root F r) n
         (x : World (extend_root_frame F n)),
    finite_cwf_extend_root_rank F E Hwf Htrans n x =
    extend_root_algebraic_rank F
      (finite_cwf_frame_rank F E Hwf) r n x.
Proof.
  intros F E Hwf Htrans r Hroot n x.
  apply frame_rank_spec_unique.
  - now apply finite_cwf_extend_root_rank_spec.
  - apply extend_root_algebraic_rank_spec; [|exact Hroot].
    now apply finite_cwf_frame_rank_spec.
Qed.

Definition finite_cwf_extend_root_height
    (F : frame) (E : finite_enumeration (World F))
    (Hwf : converse_well_founded (Rel F))
    (Htrans : frame_transitive F) (n : nat) (Hn : 0 < n) : nat :=
  frame_height (finite_cwf_extend_root_rank F E Hwf Htrans n)
    (extend_root_top F n Hn).

Arguments finite_cwf_extend_root_height F E Hwf Htrans n Hn
  : clear implicits.

(** Source declaration 13/24. *)
Lemma finite_cwf_extend_root_height_unfold :
  forall (F : frame) (E : finite_enumeration (World F))
         (Hwf : converse_well_founded (Rel F))
         (Htrans : frame_transitive F) n (Hn : 0 < n),
    finite_cwf_extend_root_height F E Hwf Htrans n Hn =
    finite_cwf_extend_root_rank F E Hwf Htrans n
      (extend_root_top F n Hn).
Proof. reflexivity. Qed.

Theorem finite_cwf_extend_root_height_eq :
  forall (F : frame) (E : finite_enumeration (World F))
         (Hwf : converse_well_founded (Rel F))
         (Htrans : frame_transitive F) (r : World F)
         (Hroot : frame_root F r) n (Hn : 0 < n),
    finite_cwf_extend_root_height F E Hwf Htrans n Hn =
    finite_cwf_frame_height F E Hwf r + n.
Proof.
  intros F E Hwf Htrans r Hroot n Hn.
  unfold finite_cwf_extend_root_height, frame_height.
  rewrite (@finite_cwf_extend_root_rank_eq_algebraic
    F E Hwf Htrans r Hroot n (extend_root_top F n Hn)).
  unfold extend_root_algebraic_rank, extend_root_top, extend_root_added.
  simpl. rewrite fin_value_top_index.
  unfold finite_cwf_frame_height, frame_height. lia.
Qed.

(** Source declaration 14/24. *)
Lemma finite_cwf_extend_root_height_positive :
  forall (F : frame) (E : finite_enumeration (World F))
         (Hwf : converse_well_founded (Rel F))
         (Htrans : frame_transitive F) (r : World F)
         (Hroot : frame_root F r) n (Hn : 0 < n),
    0 < finite_cwf_extend_root_height F E Hwf Htrans n Hn.
Proof.
  intros F E Hwf Htrans r Hroot n Hn.
  rewrite (@finite_cwf_extend_root_height_eq
    F E Hwf Htrans r Hroot n Hn). lia.
Qed.

(** Source declarations 15/24 and 24/24. *)
Lemma finite_cwf_one_root_height_successor :
  forall (F : frame) (E : finite_enumeration (World F))
         (Hwf : converse_well_founded (Rel F))
         (Htrans : frame_transitive F) (r : World F)
         (Hroot : frame_root F r),
    finite_cwf_extend_root_height F E Hwf Htrans 1
      (Nat.lt_0_succ 0) =
    finite_cwf_frame_height F E Hwf r + 1.
Proof.
  intros F E Hwf Htrans r Hroot.
  exact (@finite_cwf_extend_root_height_eq
    F E Hwf Htrans r Hroot 1 (Nat.lt_0_succ 0)).
Qed.

(** Source declaration 17/24, generalized from one to every extension. *)
Lemma finite_cwf_extend_root_rank_base_root :
  forall (F : frame) (E : finite_enumeration (World F))
         (Hwf : converse_well_founded (Rel F))
         (Htrans : frame_transitive F) (r : World F)
         (Hroot : frame_root F r) n,
    finite_cwf_extend_root_rank F E Hwf Htrans n
      (@extend_root_embed F n r) =
    finite_cwf_frame_height F E Hwf r.
Proof.
  intros. unfold finite_cwf_frame_height, frame_height.
  apply finite_cwf_extend_root_rank_original.
Qed.

(** Source declaration 18/24, generalized from one to every extension. *)
Theorem finite_cwf_extend_root_eq_base_height_iff :
  forall (F : frame) (E : finite_enumeration (World F))
         (Hwf : converse_well_founded (Rel F))
         (Htrans : frame_transitive F) (r : World F)
         (Hroot : frame_root F r) n
         (x : World (extend_root_frame F n)),
    finite_cwf_extend_root_rank F E Hwf Htrans n x =
      finite_cwf_frame_height F E Hwf r <->
    x = @extend_root_embed F n r.
Proof.
  intros F E Hwf Htrans r Hroot n [i | y].
  - change
      (finite_cwf_extend_root_rank F E Hwf Htrans n
          (@extend_root_added F n i) =
         finite_cwf_frame_height F E Hwf r <->
       @extend_root_added F n i = @extend_root_embed F n r).
    rewrite (@finite_cwf_extend_root_rank_eq_algebraic
      F E Hwf Htrans r Hroot n (@extend_root_added F n i)).
    unfold extend_root_algebraic_rank, finite_cwf_frame_height.
    simpl. unfold frame_height.
    split; [lia | discriminate].
  - change
      (finite_cwf_extend_root_rank F E Hwf Htrans n
          (@extend_root_embed F n y) =
         finite_cwf_frame_height F E Hwf r <->
       @extend_root_embed F n y = @extend_root_embed F n r).
    rewrite finite_cwf_extend_root_rank_original.
    unfold finite_cwf_frame_height.
    rewrite (rank_eq_height_iff_root
      (finite_cwf_frame_rank_spec E Hwf Htrans) Hroot y).
    split; intro H.
    + now subst y.
    + now injection H.
Qed.
