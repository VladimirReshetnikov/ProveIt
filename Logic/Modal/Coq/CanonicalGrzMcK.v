(**
  The strict inclusion S4McK < Grz.

  This module ports the final hierarchy result from Foundation's
  [Modal/Kripke/Logic/Grz/Completeness.lean].  The inclusion is an immediate
  consequence of finite Grz completeness: every finite partial order has the
  McKinsey terminal-successor property.

  Strictness is witnessed by Foundation's three-world frame.  Its first two
  worlds form a reflexive cluster and both see a terminal third world.  Thus
  the frame is reflexive, transitive, and McKinsey, but not antisymmetric.
  Since validity of the Grz atom forces antisymmetry, the Grz axiom separates
  S4McK from Grz on this frame.
*)

From Stdlib Require Import Lists.List.
From FoundationModal Require Import
  Syntax Axioms Kripke Filtration Correspondence CorrespondenceExtensions
  FrameProperties NormalHilbert LogicInfrastructure CanonicalExtensions
  GLGrzDerivations CanonicalGrz CanonicalMcK.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Inclusion *)

Theorem S4McK_weaker_than_Grz :
  forall p : formula nat, S4McK_proves p -> Grz_proves p.
Proof.
  intros p Hp. apply Grz_finite_complete.
  intros F [Hfinite Horder].
  destruct Horder as [HR [HT HA]].
  apply S4McK_proves_sound_on_frame.
  - exact HR.
  - exact HT.
  - apply finite_partial_order_mckinsey.
    + exact Hfinite.
    + now repeat split.
  - exact Hp.
Qed.

(** * Foundation's finite separating frame *)

Inductive grz_mck_three_world : Type :=
| GM0 | GM1 | GM2.

Definition grz_mck_three_relation
    (x y : grz_mck_three_world) : Prop :=
  y = GM2 \/ x = GM0 \/ x = GM1.

Definition grz_mck_three_frame : frame :=
  {| World := grz_mck_three_world;
     Rel := grz_mck_three_relation |}.

Lemma grz_mck_three_finite :
  finite_frame grz_mck_three_frame.
Proof.
  exists [GM0; GM1; GM2]. intros []; simpl; auto.
Qed.

Lemma grz_mck_three_reflexive :
  frame_reflexive grz_mck_three_frame.
Proof.
  intros []; simpl.
  - right; left; reflexivity.
  - right; right; reflexivity.
  - left; reflexivity.
Qed.

Lemma grz_mck_three_transitive :
  frame_transitive grz_mck_three_frame.
Proof.
  intros x y z Hxy Hyz.
  change (grz_mck_three_relation x y) in Hxy.
  change (grz_mck_three_relation y z) in Hyz.
  change (grz_mck_three_relation x z).
  unfold grz_mck_three_relation in *.
  destruct Hyz as [-> | [-> | ->]].
  - left; reflexivity.
  - destruct Hxy as [Hbad | Hx]; [discriminate |].
    now right.
  - destruct Hxy as [Hbad | Hx]; [discriminate |].
    now right.
Qed.

Lemma grz_mck_three_mckinsey :
  frame_mckinsey grz_mck_three_frame.
Proof.
  intro x. exists GM2. split.
  - left; reflexivity.
  - intros z Hz. change (grz_mck_three_relation GM2 z) in Hz.
    destruct z.
    + destruct Hz as [H | [H | H]]; discriminate.
    + destruct Hz as [H | [H | H]]; discriminate.
    + reflexivity.
Qed.

Lemma grz_mck_three_in_S4McK_frame_class :
  S4McK_frame_class grz_mck_three_frame.
Proof.
  repeat split.
  - exact grz_mck_three_reflexive.
  - exact grz_mck_three_transitive.
  - exact grz_mck_three_mckinsey.
Qed.

Lemma grz_mck_three_not_antisymmetric :
  ~ frame_antisymmetric grz_mck_three_frame.
Proof.
  intro HA.
  assert (H01 : Rel grz_mck_three_frame GM0 GM1).
  { right; left; reflexivity. }
  assert (H10 : Rel grz_mck_three_frame GM1 GM0).
  { right; right; reflexivity. }
  specialize (HA GM0 GM1 H01 H10). discriminate.
Qed.

Lemma grz_mck_three_not_valid_Grz_atom :
  ~ valid grz_mck_three_frame (Grz (Atom 0)).
Proof.
  intro Hvalid. apply grz_mck_three_not_antisymmetric.
  now apply antisymmetric_of_valid_Grz_atom.
Qed.

Theorem S4McK_not_proves_Grz_atom :
  ~ S4McK_proves (Grz (Atom 0)).
Proof.
  intro Hp. apply grz_mck_three_not_valid_Grz_atom.
  apply S4McK_proves_sound_on_frame.
  - exact grz_mck_three_reflexive.
  - exact grz_mck_three_transitive.
  - exact grz_mck_three_mckinsey.
  - exact Hp.
Qed.

(** * Strict hierarchy *)

Theorem S4McK_strictly_weaker_Grz :
  normal_strictly_weaker S4McK_proves Grz_proves.
Proof.
  split.
  - exact S4McK_weaker_than_Grz.
  - exists (Grz (Atom 0)); split.
    + apply Grz_proves_axiom.
    + exact S4McK_not_proves_Grz_atom.
Qed.

Theorem S4_strictly_weaker_Grz :
  normal_strictly_weaker S4_proves Grz_proves.
Proof.
  split.
  - exact S4_weaker_than_Grz.
  - exists (Grz (Atom 0)); split.
    + apply Grz_proves_axiom.
    + intro HS4. apply S4McK_not_proves_Grz_atom.
      now apply S4_weaker_than_S4McK.
Qed.
