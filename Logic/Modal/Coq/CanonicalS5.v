(**
  Universal-frame completeness and strict predecessors of S5.

  The basic reflexive/right-Euclidean canonical completeness theorem lives in
  [Modality].  This module completes the pinned theorem surface of
  [Modal/Kripke/Logic/S5.lean]: a point-generated S5 frame is universal, so
  validity on universal frames is equivalent to validity on S5 frames, and
  KTB, KD45, KB4, S4.4, S4, and KT are all proper sublogics of S5.
*)

From FoundationModal Require Import
  Syntax Axioms HilbertK Kripke HilbertKSoundness Correspondence
  CorrespondenceExtensions
  NormalHilbert CanonicalExtensions CanonicalDB5 CanonicalCombinations
  CanonicalTB Modality Root CanonicalPoint2 CanonicalPoint3 CanonicalPoint4.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Universal frames *)

Definition frame_universal (F : frame) : Prop :=
  forall x y : World F, Rel F x y.

Lemma frame_universal_reflexive :
  forall F, frame_universal F -> frame_reflexive F.
Proof. intros F HU x. apply HU. Qed.

Lemma frame_universal_right_euclidean :
  forall F, frame_universal F -> frame_right_euclidean F.
Proof. intros F HU x y z _ _. apply HU. Qed.

Lemma point_generated_universal_of_s5 :
  forall (F : frame) (r : World F),
    frame_s5 F -> frame_universal (point_generated_frame F r).
Proof.
  intros F r [HR HE] [x hx] [y hy]; simpl.
  pose proof (frame_reflexive_right_euclidean_symmetric HR HE) as HS.
  destruct hx as [-> | Hrx]; destruct hy as [-> | Hry].
  - apply HR.
  - exact Hry.
  - now apply HS.
  - exact (HE r x y Hrx Hry).
Qed.

Theorem valid_on_universal_frames_iff_valid_on_s5_frames :
  forall p : formula nat,
    normal_valid_on_class frame_universal p <->
    normal_valid_on_class frame_s5 p.
Proof.
  intro p; split.
  - intros Huniv F HS5 V r.
    destruct HS5 as [HR HE].
    pose proof (frame_reflexive_right_euclidean_transitive HR HE) as HT.
    pose proof
      (Huniv (point_generated_frame F r)
        (@point_generated_universal_of_s5 F r (conj HR HE))
        (point_generated_valuation V r) (point_generated_root F r)) as Hp.
    exact (proj1 (point_generated_truth_at_root V r HT p) Hp).
  - intros HS5 F HU.
    apply HS5. split.
    + now apply frame_universal_reflexive.
    + now apply frame_universal_right_euclidean.
Qed.

Theorem S5_proves_sound_on_universal_frame :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    frame_universal F -> S5_proves p -> valid F p.
Proof.
  intros AtomType F p HU Hp.
  apply S5_proves_sound_on_reflexive_euclidean_frame.
  - now apply frame_universal_reflexive.
  - now apply frame_universal_right_euclidean.
  - exact Hp.
Qed.

Theorem S5_universal_complete :
  forall p : formula nat,
    normal_valid_on_class frame_universal p -> S5_proves p.
Proof.
  intros p Hp. apply S5_complete.
  now apply (proj1 (valid_on_universal_frames_iff_valid_on_s5_frames p)).
Qed.

Theorem S5_universal_sound_complete :
  forall p : formula nat,
    S5_proves p <-> normal_valid_on_class frame_universal p.
Proof.
  intro p; split.
  - intros Hp F HU. now apply S5_proves_sound_on_universal_frame.
  - apply S5_universal_complete.
Qed.

(** * Frame-class inclusions *)

Lemma S5_frame_is_KTB :
  forall F, frame_s5 F -> KTB_kripke_frame_class F.
Proof.
  intros F [HR HE]. split; [exact HR |].
  now apply frame_reflexive_right_euclidean_symmetric.
Qed.

Lemma S5_frame_is_KD45 :
  forall F, frame_s5 F -> KD45_frame_class F.
Proof.
  intros F [HR HE]. repeat split.
  - now apply frame_reflexive_serial.
  - now apply frame_reflexive_right_euclidean_transitive.
  - exact HE.
Qed.

Lemma S5_frame_is_KB4 :
  forall F, frame_s5 F -> KB4_frame_class F.
Proof.
  intros F [HR HE]. split.
  - now apply frame_reflexive_right_euclidean_symmetric.
  - now apply frame_reflexive_right_euclidean_transitive.
Qed.

Lemma S5_frame_is_S4Point4 :
  forall F, frame_s5 F -> S4Point4_frame_class F.
Proof.
  intros F [HR HE]. repeat split.
  - exact HR.
  - now apply frame_reflexive_right_euclidean_transitive.
  - now apply right_euclidean_sobocinski.
Qed.

Lemma KTB_weaker_than_S5 :
  forall p : formula nat, KTB_proves p -> S5_proves p.
Proof.
  intros p Hp. apply S5_complete. intros F HF.
  destruct (S5_frame_is_KTB HF) as [HR HS].
  now apply KTB_proves_sound_on_frame.
Qed.

Lemma KD45_weaker_than_S5 :
  forall p : formula nat, KD45_proves p -> S5_proves p.
Proof.
  intros p Hp. apply S5_complete. intros F HF.
  destruct (S5_frame_is_KD45 HF) as [HS [HT HE]].
  now apply KD45_proves_sound_on_frame.
Qed.

Lemma KB4_weaker_than_S5 :
  forall p : formula nat, KB4_proves p -> S5_proves p.
Proof.
  intros p Hp. apply S5_complete. intros F HF.
  destruct (S5_frame_is_KB4 HF) as [HS HT].
  now apply KB4_proves_sound_on_frame.
Qed.

Lemma S4Point4_weaker_than_S5 :
  forall p : formula nat, S4Point4_proves p -> S5_proves p.
Proof.
  intros p Hp. apply S5_complete. intros F HF.
  destruct (S5_frame_is_S4Point4 HF) as [HR [HT HSob]].
  now apply S4Point4_proves_sound_on_frame.
Qed.

Lemma S4_weaker_than_S5 :
  forall p : formula nat, S4_proves p -> S5_proves p.
Proof.
  intros p Hp. apply S5_complete. intros F [HR HE].
  apply S4_proves_sound_on_preorder_frame.
  - exact HR.
  - now apply frame_reflexive_right_euclidean_transitive.
  - exact Hp.
Qed.

(** * Finite strictness witnesses *)

Inductive s5_fork_world : Type := S5Root | S5Left | S5Right.

Inductive s5_fork_relation : s5_fork_world -> s5_fork_world -> Prop :=
| s5_fork_RR : s5_fork_relation S5Root S5Root
| s5_fork_RL : s5_fork_relation S5Root S5Left
| s5_fork_RQ : s5_fork_relation S5Root S5Right
| s5_fork_LR : s5_fork_relation S5Left S5Root
| s5_fork_LL : s5_fork_relation S5Left S5Left
| s5_fork_QR : s5_fork_relation S5Right S5Root
| s5_fork_QQ : s5_fork_relation S5Right S5Right.

Definition s5_fork_frame : frame :=
  {| World := s5_fork_world; Rel := s5_fork_relation |}.

Lemma s5_fork_reflexive : frame_reflexive s5_fork_frame.
Proof. intros []; constructor. Qed.

Lemma s5_fork_symmetric : frame_symmetric s5_fork_frame.
Proof. intros x y H; inversion H; constructor. Qed.

Lemma s5_fork_not_right_euclidean :
  ~ frame_right_euclidean s5_fork_frame.
Proof.
  intro HE.
  pose proof (HE S5Root S5Left S5Right s5_fork_RL s5_fork_RQ) as H.
  inversion H.
Qed.

Lemma combo_sink_not_reflexive_S5 :
  ~ frame_reflexive combo_sink_frame.
Proof. intro HR. specialize (HR DB0). discriminate. Qed.

Lemma combo_sink_serial_S5 : frame_serial combo_sink_frame.
Proof. intro x. exists DB1. reflexivity. Qed.

Lemma irreflexive_singleton_not_reflexive_S5 :
  ~ frame_reflexive irreflexive_singleton_frame.
Proof. intro HR. exact (HR tt). Qed.

Lemma tb_reflexive_chain_transitive_S5 :
  frame_transitive tb_reflexive_chain_frame.
Proof.
  intros x y z Hxy Hyz.
  destruct x, y, z; simpl in *; intuition discriminate.
Qed.

Lemma tb_reflexive_chain_sobocinski_S5 :
  frame_sobocinski tb_reflexive_chain_frame.
Proof.
  intros x y z Hneq Hxy Hxz.
  destruct x, y, z; simpl in *; intuition discriminate.
Qed.

Lemma tb_reflexive_chain_not_right_euclidean_S5 :
  ~ frame_right_euclidean tb_reflexive_chain_frame.
Proof.
  intro HE.
  pose proof (HE TB0 TB1 TB0
    (or_intror (conj eq_refl eq_refl)) (or_introl eq_refl)) as H.
  destruct H as [H | [H _]]; discriminate.
Qed.

(** * Strict predecessors of S5 *)

Theorem KTB_strictly_weaker_S5 :
  normal_strictly_weaker KTB_proves S5_proves.
Proof.
  split.
  - exact KTB_weaker_than_S5.
  - exists (Five (Atom 0)); split.
    + apply Np_extra. right. exists (Atom 0). reflexivity.
    + intro HKTB.
      pose proof (KTB_proves_sound_on_frame
        s5_fork_reflexive s5_fork_symmetric HKTB) as Hvalid.
      apply s5_fork_not_right_euclidean.
      now apply (proj1 (valid_Five_iff_right_euclidean s5_fork_frame)).
Qed.

Theorem KD45_strictly_weaker_S5 :
  normal_strictly_weaker KD45_proves S5_proves.
Proof.
  split.
  - exact KD45_weaker_than_S5.
  - exists (T (Atom 0)); split.
    + apply Np_extra. left. exists (Atom 0). reflexivity.
    + intro HKD45.
      pose proof (KD45_proves_sound_on_frame
        combo_sink_serial_S5 combo_sink_transitive
        combo_sink_right_euclidean HKD45) as Hvalid.
      apply combo_sink_not_reflexive_S5.
      now apply (proj1 (valid_T_iff_reflexive combo_sink_frame)).
Qed.

Theorem KB4_strictly_weaker_S5 :
  normal_strictly_weaker KB4_proves S5_proves.
Proof.
  split.
  - exact KB4_weaker_than_S5.
  - exists (T (Atom 0)); split.
    + apply Np_extra. left. exists (Atom 0). reflexivity.
    + intro HKB4.
      pose proof (KB4_proves_sound_on_frame
        irreflexive_singleton_symmetric irreflexive_singleton_transitive
        HKB4) as Hvalid.
      apply irreflexive_singleton_not_reflexive_S5.
      now apply (proj1 (valid_T_iff_reflexive irreflexive_singleton_frame)).
Qed.

Theorem S4Point4_strictly_weaker_S5 :
  normal_strictly_weaker S4Point4_proves S5_proves.
Proof.
  split.
  - exact S4Point4_weaker_than_S5.
  - exists (Five (Atom 0)); split.
    + apply Np_extra. right. exists (Atom 0). reflexivity.
    + intro HS4Point4.
      pose proof (S4Point4_proves_sound_on_frame
        tb_reflexive_chain_reflexive tb_reflexive_chain_transitive_S5
        tb_reflexive_chain_sobocinski_S5 HS4Point4) as Hvalid.
      apply tb_reflexive_chain_not_right_euclidean_S5.
      now apply (proj1
        (valid_Five_iff_right_euclidean tb_reflexive_chain_frame)).
Qed.

Theorem S4_strictly_weaker_S5 :
  normal_strictly_weaker S4_proves S5_proves.
Proof.
  split.
  - exact S4_weaker_than_S5.
  - exists (Five (Atom 0)); split.
    + apply Np_extra. right. exists (Atom 0). reflexivity.
    + intro HS4.
      pose proof (S4_proves_sound_on_preorder_frame
        tb_reflexive_chain_reflexive tb_reflexive_chain_transitive_S5
        HS4) as Hvalid.
      apply tb_reflexive_chain_not_right_euclidean_S5.
      now apply (proj1
        (valid_Five_iff_right_euclidean tb_reflexive_chain_frame)).
Qed.

Theorem KT_strictly_weaker_S5 :
  normal_strictly_weaker KT_proves S5_proves.
Proof.
  split.
  - intros p Hp. exact (@KT_weaker_than_S5 nat p Hp).
  - exists (Five (Atom 0)); split.
    + apply Np_extra. right. exists (Atom 0). reflexivity.
    + intro HKT.
      pose proof (KT_proves_sound_on_reflexive_frame
        tb_reflexive_chain_reflexive HKT) as Hvalid.
      apply tb_reflexive_chain_not_right_euclidean_S5.
      now apply (proj1
        (valid_Five_iff_right_euclidean tb_reflexive_chain_frame)).
Qed.
