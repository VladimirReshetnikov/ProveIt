(**
  Canonical completeness for S4.4McK.

  This module ports the complete theorem surface of the pinned Foundation
  file [Modal/Kripke/Logic/S4Point4McK.lean].  Its schema and framewise
  soundness were introduced earlier by [CanonicalTrivVer].  Canonicality
  combines the Point4/Sobocinski theorem from [CanonicalPoint4] with the
  proved generic McKinsey special-successor construction from [CanonicalMcK].
  The imported S4.3McK boundary and its own completeness theorem live in
  [CanonicalPoint3McK].
*)

From Stdlib Require Import Lists.List Logic.Classical_Prop.
From FoundationModal Require Import
  Syntax Axioms HilbertK Kripke Correspondence CorrespondenceExtensions
  NormalHilbert CanonicalExtensions CanonicalCombinations Boxdot Modality
  CanonicalPoint2 CanonicalPoint3 CanonicalPoint4 CanonicalMcK
  CanonicalTrivVer CanonicalPoint3McK.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Lemma S4Point4McK_frame_is_S4Point3McK :
  forall F,
    S4Point4McK_kripke_frame_class F -> S4Point3McK_frame_class F.
Proof.
  intros F [HR [HT [HSob HM]]]. repeat split; try assumption.
  now apply sobocinski_piecewise_strongly_connected.
Qed.

(** * S4.4McK canonicality and completeness *)

Theorem S4Point4McK_is_consistent :
  forall AtomType, ~ @S4Point4McK_proves AtomType Bottom.
Proof.
  intros AtomType Hbottom.
  assert (Hframe :
    S4Point4McK_kripke_frame_class reflexive_singleton_frame).
  {
    split; [exact reflexive_singleton_reflexive |].
    split; [exact reflexive_singleton_transitive |].
    split.
    - intros [] [] [] Hneq _ _. exfalso. apply Hneq. reflexivity.
    - intros []. exists tt; split.
      + constructor.
      + intros []; reflexivity.
  }
  pose proof (S4Point4McK_proves_sound_on_frame
    (F := reflexive_singleton_frame) Hframe Hbottom) as Hvalid.
  exact (Hvalid (fun _ _ => False) tt).
Qed.

Lemma S4Point4McK_canonical_frame :
  S4Point4McK_kripke_frame_class
    (normal_canonical_frame S4Point4McK_schema).
Proof.
  repeat split.
  - apply normal_canonical_reflexive_of_schema_T.
    intros A p Hp. left. left. now left.
  - apply normal_canonical_transitive_of_schema_Four.
    intros A p Hp. left. left. now right.
  - apply normal_canonical_sobocinski_of_schema_Point4.
    intros A p [q ->]. right. now exists q.
  - apply normal_canonical_mckinsey_of_K4McK_schemas.
    + intros A p Hp. left. left. now right.
    + intros A p [q ->]. left. right. now exists q.
Qed.

Theorem S4Point4McK_complete :
  forall p : formula nat,
    normal_valid_on_class S4Point4McK_kripke_frame_class p ->
    S4Point4McK_proves p.
Proof.
  unfold S4Point4McK_proves.
  apply (normal_complete_of_canonical_frame
    (Ax := S4Point4McK_schema)
    (C := S4Point4McK_kripke_frame_class)).
  - exact (@S4Point4McK_is_consistent nat).
  - exact S4Point4McK_canonical_frame.
Qed.

Theorem S4Point4McK_sound_complete :
  forall p : formula nat,
    S4Point4McK_proves p <->
    normal_valid_on_class S4Point4McK_kripke_frame_class p.
Proof.
  intro p; split.
  - intros Hp F HF. now apply S4Point4McK_proves_sound_on_frame.
  - apply S4Point4McK_complete.
Qed.

(** * Strict inclusions *)

Theorem S4Point3McK_weaker_than_S4Point4McK :
  forall p : formula nat,
    S4Point3McK_proves p -> S4Point4McK_proves p.
Proof.
  intros p Hp. apply S4Point4McK_complete.
  intros F HF. apply S4Point3McK_proves_sound_on_frame.
  - now apply S4Point4McK_frame_is_S4Point3McK.
  - exact Hp.
Qed.

Lemma point4_three_chain_mckinsey :
  frame_mckinsey point4_three_chain_frame.
Proof.
  intros x. exists P42; split.
  - destruct x; constructor.
  - intros z Hz. inversion Hz. reflexivity.
Qed.

Theorem S4Point3McK_strictly_weaker_S4Point4McK :
  normal_strictly_weaker S4Point3McK_proves S4Point4McK_proves.
Proof.
  split.
  - exact S4Point3McK_weaker_than_S4Point4McK.
  - exists (Point4 (Atom 0)); split.
    + apply Np_extra. right. exists (Atom 0). reflexivity.
    + intro HPoint3McK.
      pose proof (S4Point3McK_proves_sound_on_frame
        (F := point4_three_chain_frame)
        (p := Point4 (Atom 0))
        ltac:(repeat split;
          [ exact point4_three_chain_reflexive
          | exact point4_three_chain_transitive
          | exact point4_three_chain_piecewise_strongly_connected
          | exact point4_three_chain_mckinsey ])
        HPoint3McK) as Hvalid.
      apply point4_three_chain_not_sobocinski.
      now apply sobocinski_of_valid_Point4_atom.
Qed.

Theorem S4Point4_weaker_than_S4Point4McK :
  forall p : formula nat, S4Point4_proves p -> S4Point4McK_proves p.
Proof.
  intros p Hp. eapply normal_proves_weaken; [| exact Hp].
  intros A q Hq. destruct Hq as [Hbase | [r ->]].
  - destruct Hbase as [[r ->] | [r ->]].
    + left. left. left. now exists r.
    + left. left. right. now exists r.
  - right. now exists r.
Qed.

Lemma trivver_all_reflexive : frame_reflexive trivver_all_frame.
Proof. intros []; exact trivver_true. Qed.

Lemma trivver_all_sobocinski : frame_sobocinski trivver_all_frame.
Proof. intros [] [] [] _ _ _; exact trivver_true. Qed.

Theorem S4Point4_strictly_weaker_S4Point4McK :
  normal_strictly_weaker S4Point4_proves S4Point4McK_proves.
Proof.
  split.
  - exact S4Point4_weaker_than_S4Point4McK.
  - exists (McK (Atom 0)); split.
    + apply Np_extra. left. right. exists (Atom 0). reflexivity.
    + intro HPoint4.
      pose proof (S4Point4_proves_sound_on_frame
        trivver_all_reflexive trivver_all_transitive
        trivver_all_sobocinski HPoint4) as Hvalid.
      specialize (Hvalid (fun _ w => w = TV0) TV0).
      assert (Hboxdia : satisfies trivver_all_frame
        (fun _ w => w = TV0) TV0 (Box (Dia (Atom 0)))).
      {
        intros y _. apply satisfies_dia_intro.
        exists TV0; split; [exact trivver_true | reflexivity].
      }
      destruct (@satisfies_dia_elim nat trivver_all_frame
        (fun _ w => w = TV0) TV0 (Box (Atom 0)) (Hvalid Hboxdia))
        as [y [_ Hbox]].
      specialize (Hbox TV1 trivver_true). discriminate.
Qed.
