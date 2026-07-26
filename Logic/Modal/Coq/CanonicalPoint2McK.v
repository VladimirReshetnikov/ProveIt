(**
  Canonical completeness for S4.2McK.

  This module ports the complete theorem surface of the pinned Foundation
  file [Modal/Kripke/Logic/S4Point2McK.lean].  It combines the canonical
  Point2/strong-confluence theorem from [CanonicalPoint2] with the proved
  McKinsey terminal-successor theorem from [CanonicalMcK].

  The two strict inclusions use the same finite frames as Foundation.  The
  three-world reflexive fork satisfies S4McK but is not strongly confluent;
  the two-world universal frame satisfies S4.2 but refutes McK under a
  valuation true at only one world.
*)

From Stdlib Require Import Lists.List Logic.Classical_Prop.
From FoundationModal Require Import
  Syntax Axioms HilbertK Kripke Correspondence CorrespondenceExtensions
  Root Filtration NormalHilbert CanonicalExtensions Boxdot CanonicalPoint2
  CanonicalCombinations CanonicalMcK.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Schema, calculus, and frame class *)

Definition S4Point2McK_schema : modal_axiom_schema :=
  schema_union S4McK_schema schema_Point2.

Definition S4Point2McK_proves {AtomType} : formula AtomType -> Prop :=
  @normal_proves S4Point2McK_schema AtomType.

Lemma S4Point2McK_schema_substitution_closed :
  schema_substitution_closed S4Point2McK_schema.
Proof.
  apply schema_union_substitution_closed.
  - exact S4McK_schema_substitution_closed.
  - exact schema_Point2_substitution_closed.
Qed.

Definition S4Point2McK_frame_class (F : frame) : Prop :=
  frame_reflexive F /\ frame_transitive F /\
  frame_mckinsey F /\ frame_piecewise_strongly_convergent F.

Lemma S4Point2McK_frame_is_S4McK :
  forall F,
    S4Point2McK_frame_class F -> S4McK_frame_class F.
Proof.
  intros F [HR [HT [HM _]]]. repeat split; assumption.
Qed.

Lemma S4Point2McK_frame_is_S4Point2 :
  forall F,
    S4Point2McK_frame_class F -> S4Point2_frame_class F.
Proof.
  intros F [HR [HT [_ HC]]]. repeat split; assumption.
Qed.

(** * Soundness and consistency *)

Theorem S4Point2McK_proves_sound_on_frame :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    S4Point2McK_frame_class F ->
    S4Point2McK_proves p -> valid F p.
Proof.
  intros AtomType F p [HR [HT [HM HC]]] Hp.
  eapply normal_proves_sound_on_frame; [| exact Hp].
  apply schema_union_valid_on_frame.
  - apply schema_union_valid_on_frame.
    + apply schema_union_valid_on_frame.
      * now apply schema_T_valid_on_reflexive.
      * now apply schema_Four_valid_on_transitive.
    + now apply McK_axiom_schema_valid_on_mckinsey.
  - now apply schema_Point2_valid_on_piecewise_strongly_convergent.
Qed.

Lemma point2mck_reflexive_singleton_strongly_convergent :
  frame_piecewise_strongly_convergent reflexive_singleton_frame.
Proof.
  intros [] [] [] _ _. exists tt; split; constructor.
Qed.

Theorem S4Point2McK_is_consistent :
  forall AtomType, ~ @S4Point2McK_proves AtomType Bottom.
Proof.
  apply (normal_consistent_of_sound_inhabited_frame
    (Ax := S4Point2McK_schema) (F := reflexive_singleton_frame)).
  - now exists tt.
  - apply schema_union_valid_on_frame.
    + apply schema_union_valid_on_frame.
      * apply schema_union_valid_on_frame.
        -- apply schema_T_valid_on_reflexive.
           exact reflexive_singleton_reflexive.
        -- apply schema_Four_valid_on_transitive.
           exact reflexive_singleton_transitive.
      * apply McK_axiom_schema_valid_on_mckinsey.
        exact base_mck_reflexive_singleton_mckinsey.
    + apply schema_Point2_valid_on_piecewise_strongly_convergent.
      exact point2mck_reflexive_singleton_strongly_convergent.
Qed.

(** * Canonicality and completeness *)

Lemma S4Point2McK_canonical_frame :
  S4Point2McK_frame_class
    (normal_canonical_frame S4Point2McK_schema).
Proof.
  repeat split.
  - apply normal_canonical_reflexive_of_schema_T.
    intros A p Hp. left. left. now left.
  - apply normal_canonical_transitive_of_schema_Four.
    intros A p Hp. left. left. now right.
  - apply normal_canonical_mckinsey_of_K4McK_schemas.
    + intros A p Hp. left. left. now right.
    + intros A p Hp. left. now right.
  - apply normal_canonical_strongly_confluent_of_schema_Point2.
    intros A p Hp. now right.
Qed.

Theorem S4Point2McK_complete :
  forall p : formula nat,
    normal_valid_on_class S4Point2McK_frame_class p ->
    S4Point2McK_proves p.
Proof.
  unfold S4Point2McK_proves.
  apply (normal_complete_of_canonical_frame
    (Ax := S4Point2McK_schema) (C := S4Point2McK_frame_class)).
  - exact (@S4Point2McK_is_consistent nat).
  - exact S4Point2McK_canonical_frame.
Qed.

Theorem S4Point2McK_sound_complete :
  forall p : formula nat,
    S4Point2McK_proves p <->
    normal_valid_on_class S4Point2McK_frame_class p.
Proof.
  intro p; split.
  - intros Hp F HF. now apply S4Point2McK_proves_sound_on_frame.
  - apply S4Point2McK_complete.
Qed.

(** * Logic inclusions *)

Lemma S4McK_weaker_than_S4Point2McK :
  forall (AtomType : Type) (p : formula AtomType),
    S4McK_proves p -> S4Point2McK_proves p.
Proof.
  intros AtomType p Hp. eapply normal_proves_weaken; [| exact Hp].
  intros A q Hq. now left.
Qed.

Lemma S4Point2_weaker_than_S4Point2McK :
  forall (AtomType : Type) (p : formula AtomType),
    S4Point2_proves p -> S4Point2McK_proves p.
Proof.
  intros AtomType p Hp. eapply normal_proves_weaken; [| exact Hp].
  intros A q [HS4 | HPoint2].
  - left. now left.
  - now right.
Qed.

(** * The finite S4McK fork separator *)

Lemma point2mck_fork_finite : finite_frame point2_fork_frame.
Proof.
  exists [W0; W1; W2]. intros []; simpl; auto.
Qed.

Lemma point2mck_fork_mckinsey : frame_mckinsey point2_fork_frame.
Proof.
  intros x.
  destruct x.
  - exists W1; split.
    + now left.
    + intros z [Hbad | ->]; [discriminate | reflexivity].
  - exists W1; split.
    + now right.
    + intros z [Hbad | ->]; [discriminate | reflexivity].
  - exists W2; split.
    + now right.
    + intros z [Hbad | ->]; [discriminate | reflexivity].
Qed.

Theorem S4McK_strictly_weaker_S4Point2McK :
  normal_strictly_weaker S4McK_proves S4Point2McK_proves.
Proof.
  split.
  - intros p Hp. now apply S4McK_weaker_than_S4Point2McK.
  - exists (Point2 (Atom 0)); split.
    + apply Np_extra. right. exists (Atom 0). reflexivity.
    + intro HS4McK.
      pose proof (S4McK_proves_sound_on_frame
        point2_fork_reflexive point2_fork_transitive
        point2mck_fork_mckinsey HS4McK) as Hvalid.
      apply point2_fork_not_piecewise_strongly_convergent.
      now apply (proj1 (valid_Point2_iff_strong_confluence
        point2_fork_frame)).
Qed.

(** * The finite S4.2 universal-frame separator *)

Lemma point2mck_universal_two_finite :
  finite_frame base_mck_universal_two_frame.
Proof.
  exists [false; true]. intros []; simpl; auto.
Qed.

Lemma point2mck_universal_two_strongly_convergent :
  frame_piecewise_strongly_convergent base_mck_universal_two_frame.
Proof.
  intros x y z _ _. exists false; split; constructor.
Qed.

Theorem S4Point2_strictly_weaker_S4Point2McK :
  normal_strictly_weaker S4Point2_proves S4Point2McK_proves.
Proof.
  split.
  - intros p Hp. now apply S4Point2_weaker_than_S4Point2McK.
  - exists (McK (Atom 0)); split.
    + apply Np_extra. left. right. exists (Atom 0). reflexivity.
    + intro HS4Point2.
      pose proof (S4Point2_proves_sound_on_frame
        base_mck_universal_two_reflexive
        base_mck_universal_two_transitive
        point2mck_universal_two_strongly_convergent HS4Point2)
        as Hvalid.
      specialize (Hvalid (fun _ w => w = false) false).
      assert (Hboxdia : satisfies base_mck_universal_two_frame
        (fun _ w => w = false) false (Box (Dia (Atom 0)))).
      {
        intros y _. apply satisfies_dia_intro.
        exists false; split; [constructor | reflexivity].
      }
      destruct (@satisfies_dia_elim nat base_mck_universal_two_frame
        (fun _ w => w = false) false (Box (Atom 0)) (Hvalid Hboxdia))
        as [y [_ Hbox]].
      specialize (Hbox true ltac:(constructor)). discriminate.
Qed.
