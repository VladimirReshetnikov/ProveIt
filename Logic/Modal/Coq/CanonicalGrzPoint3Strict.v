(**
  The proved finite semantics of Grz.3 and its strict predecessors.

  This module ports the non-placeholder part of the pinned Foundation file
  [Modal/Kripke/Logic/GrzPoint3.lean].  In particular it deliberately does
  not postulate, assume, or prove Grz.3 completeness.  The inclusions are
  obtained proof-theoretically using the derived Grz laws T and Four;
  strictness over Grz.2 is witnessed by the four-world diamond partial
  order, and strictness over S4.3 uses the two-world universal preorder.

  Foundation distinguishes finite linearly ordered Grz frames from finite
  partial orders which are only locally strongly connected.  Both classes
  and their soundness theorems are exposed below.  Finiteness plus
  antisymmetry supplies the weak converse well-foundedness needed by Grz;
  Point3 is handled by its exact correspondence theorem.
*)

From Stdlib Require Import Bool.Bool Lists.List.
From FoundationModal Require Import
  Syntax Axioms HilbertK Kripke Correspondence CorrespondenceExtensions
  NormalHilbert CanonicalExtensions FrameProperties Root
  Filtration GLGrzDerivations Boxdot CanonicalPoint3 CanonicalGrzPoint2.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Finite Grz.3 frame classes *)

Definition GrzPoint3_finite_strong_frame_class (F : frame) : Prop :=
  finite_frame F /\ frame_is_partial_order F /\
  frame_strongly_connected F.

Definition GrzPoint3_finite_piecewise_strong_frame_class
    (F : frame) : Prop :=
  finite_frame F /\ frame_is_partial_order F /\
  frame_piecewise_strongly_connected F.

(** Source-facing aliases: Foundation's unprimed class is the globally
    strongly connected one, while the primed class is its piecewise form. *)
Definition GrzPoint3_finite_frame_class : frame -> Prop :=
  GrzPoint3_finite_strong_frame_class.

Definition GrzPoint3_finite_frame_class' : frame -> Prop :=
  GrzPoint3_finite_piecewise_strong_frame_class.

Lemma frame_strongly_connected_piecewise_strongly_connected :
  forall F,
    frame_strongly_connected F ->
    frame_piecewise_strongly_connected F.
Proof.
  intros F Hstrong x y z _ _. exact (Hstrong y z).
Qed.

(** A finite linear partial order is in particular a finite directed
    partial order.  This is the local counterpart of Foundation's
    [IsFiniteGrzPoint3 -> IsFiniteGrzPoint2] instance. *)
Lemma GrzPoint3_finite_frame_is_GrzPoint2 :
  forall F,
    GrzPoint3_finite_frame_class F ->
    GrzPoint2_finite_frame_class F.
Proof.
  intros F [Hfinite [Horder Hstrong]].
  split; [exact Hfinite |]. split; [exact Horder |].
  destruct Horder as [Hrefl _].
  intros x y z _ _.
  destruct (Hstrong y z) as [Hyz | Hzy].
  - exists z. split; [exact Hyz | now apply Hrefl].
  - exists y. split; [now apply Hrefl | exact Hzy].
Qed.

Theorem GrzPoint3_proves_sound_on_finite_piecewise_strong_frame :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    GrzPoint3_finite_piecewise_strong_frame_class F ->
    GrzPoint3_proves p -> valid F p.
Proof.
  intros AtomType F p [Hfinite [[Hrefl [Htrans Hanti]] Hpiece]] Hp.
  eapply normal_proves_sound_on_frame; [| exact Hp].
  apply schema_union_valid_on_frame.
  - apply schema_Grz_valid_on_Grz_frame.
    + exact Hrefl.
    + exact Htrans.
    + now apply finite_transitive_antisymmetric_weak_cwf.
  - now apply schema_Point3_valid_on_piecewise_strongly_connected.
Qed.

Theorem GrzPoint3_proves_sound_on_finite_strong_frame :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    GrzPoint3_finite_strong_frame_class F ->
    GrzPoint3_proves p -> valid F p.
Proof.
  intros AtomType F p [Hfinite [Horder Hstrong]] Hp.
  apply GrzPoint3_proves_sound_on_finite_piecewise_strong_frame.
  - split; [exact Hfinite |]. split; [exact Horder |].
    now apply frame_strongly_connected_piecewise_strongly_connected.
  - exact Hp.
Qed.

(** * Singleton consistency *)

Lemma grzpoint3_reflexive_singleton_finite :
  finite_frame reflexive_singleton_frame.
Proof. exists [tt]. intros []; simpl; auto. Qed.

Lemma grzpoint3_reflexive_singleton_antisymmetric :
  frame_antisymmetric reflexive_singleton_frame.
Proof. intros [] [] _ _. reflexivity. Qed.

Lemma grzpoint3_reflexive_singleton_strongly_connected :
  frame_strongly_connected reflexive_singleton_frame.
Proof. intros [] []; now left. Qed.

Lemma grzpoint3_reflexive_singleton_in_finite_class :
  GrzPoint3_finite_frame_class reflexive_singleton_frame.
Proof.
  split; [exact grzpoint3_reflexive_singleton_finite |].
  split.
  - split.
    + exact reflexive_singleton_reflexive.
    + split.
      * exact reflexive_singleton_transitive.
      * exact grzpoint3_reflexive_singleton_antisymmetric.
  - exact grzpoint3_reflexive_singleton_strongly_connected.
Qed.

Theorem GrzPoint3_is_consistent :
  forall AtomType, ~ @GrzPoint3_proves AtomType Bottom.
Proof.
  intros AtomType Hbottom.
  pose proof (GrzPoint3_proves_sound_on_finite_strong_frame
    (F := reflexive_singleton_frame)
    (p := @Bottom AtomType)
    grzpoint3_reflexive_singleton_in_finite_class Hbottom) as Hvalid.
  exact (Hvalid (fun _ _ => False) tt).
Qed.

(** * Direct proof-theoretic inclusion S4.3 <= Grz.3 *)

Lemma Grz_weaker_than_GrzPoint3 :
  forall p : formula nat, Grz_proves p -> GrzPoint3_proves p.
Proof.
  intros p Hp. eapply normal_proves_weaken; [| exact Hp].
  intros AtomType q Hq. now left.
Qed.

Lemma GrzPoint3_proves_Grz_axiom :
  forall p : formula nat, GrzPoint3_proves (Grz p).
Proof. intro p. apply Np_extra. left. now exists p. Qed.

Lemma GrzPoint3_proves_T :
  forall p : formula nat, GrzPoint3_proves (T p).
Proof. intro p. apply Grz_weaker_than_GrzPoint3, Grz_proves_T. Qed.

Lemma GrzPoint3_proves_Four :
  forall p : formula nat, GrzPoint3_proves (Four p).
Proof. intro p. apply Grz_weaker_than_GrzPoint3, Grz_proves_Four. Qed.

Lemma GrzPoint3_proves_Point3 :
  forall p q : formula nat, GrzPoint3_proves (Point3 p q).
Proof. intros p q. apply Np_extra. right. now exists p, q. Qed.

Theorem S4Point3_weaker_than_GrzPoint3 :
  forall p : formula nat,
    S4Point3_proves p -> GrzPoint3_proves p.
Proof.
  intros p Hp; induction Hp.
  - apply Np_imply_K.
  - apply Np_imply_S.
  - apply Np_elim_contra.
  - apply Np_modal_K.
  - destruct H as [HS4 | HPoint3].
    + destruct HS4 as [HT | HFour].
      * destruct HT as [q ->]. apply GrzPoint3_proves_T.
      * destruct HFour as [q ->]. apply GrzPoint3_proves_Four.
    + destruct HPoint3 as [q [r ->]].
      apply GrzPoint3_proves_Point3.
  - eapply Np_mp; eauto.
  - now apply Np_nec.
Qed.

(** * A finite S4.3 separator for the Grz axiom *)

Definition grzpoint3_universal_two_frame : frame :=
  {| World := bool; Rel := fun _ _ => True |}.

Definition grzpoint3_separator_valuation :
    valuation nat grzpoint3_universal_two_frame :=
  fun _ w => w = true.

Lemma grzpoint3_universal_two_finite :
  finite_frame grzpoint3_universal_two_frame.
Proof. exists [false; true]. intros []; simpl; auto. Qed.

Lemma grzpoint3_universal_two_reflexive :
  frame_reflexive grzpoint3_universal_two_frame.
Proof. intros []; constructor. Qed.

Lemma grzpoint3_universal_two_transitive :
  frame_transitive grzpoint3_universal_two_frame.
Proof. intros [] [] [] _ _; constructor. Qed.

Lemma grzpoint3_universal_two_piecewise_strongly_connected :
  frame_piecewise_strongly_connected grzpoint3_universal_two_frame.
Proof. intros x y z _ _. now left. Qed.

Lemma grzpoint3_universal_two_not_Grz_atom :
  ~ satisfies grzpoint3_universal_two_frame
      grzpoint3_separator_valuation false (Grz (Atom 0)).
Proof.
  unfold Grz. simpl. intro Hgrz.
  assert (Hfalse : grzpoint3_separator_valuation 0 false).
  {
    apply Hgrz; intros y _ Hinner.
    destruct y.
    - reflexivity.
    - specialize (Hinner true ltac:(constructor) eq_refl
        false ltac:(constructor)).
      unfold grzpoint3_separator_valuation in Hinner. discriminate.
  }
  unfold grzpoint3_separator_valuation in Hfalse. discriminate.
Qed.

Theorem S4Point3_does_not_prove_Grz_atom :
  ~ S4Point3_proves (Grz (Atom 0)).
Proof.
  intro HS4Point3.
  pose proof (S4Point3_proves_sound_on_frame
    grzpoint3_universal_two_reflexive
    grzpoint3_universal_two_transitive
    grzpoint3_universal_two_piecewise_strongly_connected
    HS4Point3) as Hvalid.
  exact (grzpoint3_universal_two_not_Grz_atom
    (Hvalid grzpoint3_separator_valuation false)).
Qed.

Theorem S4Point3_strictly_weaker_GrzPoint3 :
  normal_strictly_weaker S4Point3_proves GrzPoint3_proves.
Proof.
  split.
  - exact S4Point3_weaker_than_GrzPoint3.
  - exists (Grz (Atom 0)); split.
    + apply GrzPoint3_proves_Grz_axiom.
    + exact S4Point3_does_not_prove_Grz_atom.
Qed.

(** * The strict inclusion Grz.2 < Grz.3 *)

(** Point3 proves Point2 over S4, so the same checked derivation can be
    replayed inside Grz.3 using its derived T and Four laws.  This avoids
    relying on the deliberately omitted Grz.3 completeness claim. *)
Lemma GrzPoint2_weaker_than_GrzPoint3 :
  forall p : formula nat,
    GrzPoint2_proves p -> GrzPoint3_proves p.
Proof.
  intros p Hp; induction Hp.
  - apply Np_imply_K.
  - apply Np_imply_S.
  - apply Np_elim_contra.
  - apply Np_modal_K.
  - destruct H as [HGrz | HPoint2].
    + destruct HGrz as [q ->]. apply GrzPoint3_proves_Grz_axiom.
    + destruct HPoint2 as [q ->].
      apply S4Point3_weaker_than_GrzPoint3.
      apply S4Point2_weaker_than_S4Point3.
      apply Np_extra. right. now exists q.
  - eapply Np_mp; eauto.
  - now apply Np_nec.
Qed.

(** The following is the source's [Fin 4] frame
      x R y  iff  x = 0 or x = y or y = 3,
    presented by [point3_diamond_frame]'s named constructors.  The Point3
    correspondence reconstructs the source valuation from the two
    incomparable middle worlds. *)
Lemma grzpoint3_diamond_finite :
  finite_frame point3_diamond_frame.
Proof. exists [P30; P31; P32; P33]. intros []; simpl; auto. Qed.

Lemma grzpoint3_diamond_antisymmetric :
  frame_antisymmetric point3_diamond_frame.
Proof.
  intros x y Hxy Hyx. destruct x, y; simpl in *;
    intuition discriminate.
Qed.

Lemma grzpoint3_diamond_in_GrzPoint2_finite_frame_class :
  GrzPoint2_finite_frame_class point3_diamond_frame.
Proof.
  split; [exact grzpoint3_diamond_finite |]. split.
  - split; [exact point3_diamond_reflexive |]. split.
    + exact point3_diamond_transitive.
    + exact grzpoint3_diamond_antisymmetric.
  - exact point3_diamond_piecewise_strongly_convergent.
Qed.

Lemma GrzPoint2_does_not_prove_Point3_atoms :
  ~ GrzPoint2_proves (Point3 (Atom 0) (Atom 1)).
Proof.
  intro Hpoint3.
  pose proof (GrzPoint2_proves_sound_on_finite_frame
    grzpoint3_diamond_in_GrzPoint2_finite_frame_class Hpoint3) as Hvalid.
  apply point3_diamond_not_piecewise_strongly_connected.
  now apply (proj1 (valid_Point3_iff_piecewise_strong_connected
    point3_diamond_frame)).
Qed.

Theorem GrzPoint2_strictly_weaker_GrzPoint3 :
  normal_strictly_weaker GrzPoint2_proves GrzPoint3_proves.
Proof.
  split.
  - exact GrzPoint2_weaker_than_GrzPoint3.
  - exists (Point3 (Atom 0) (Atom 1)); split.
    + apply GrzPoint3_proves_Point3.
    + exact GrzPoint2_does_not_prove_Point3_atoms.
Qed.
