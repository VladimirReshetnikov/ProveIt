(**
  Canonical completeness for S4.3McK.

  This module ports the complete theorem surface of the pinned Foundation
  file [Modal/Kripke/Logic/S4Point3McK.lean].  Canonicality combines the
  Point3 theorem from [CanonicalPoint3] with the special McKinsey successor
  construction from [CanonicalMcK].

  The imported S4.2McK logic is reused from [CanonicalPoint2McK].
*)

From Stdlib Require Import Lists.List Logic.Classical_Prop.
From FoundationModal Require Import
  Syntax Axioms HilbertK Kripke Correspondence CorrespondenceExtensions Root
  NormalHilbert CanonicalExtensions CanonicalCombinations Boxdot Modality
  CanonicalPoint2 CanonicalPoint3 CanonicalMcK CanonicalPoint2McK
  CanonicalTrivVer.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * S4.3McK schema, calculus, and frame class *)

Definition S4Point3McK_schema : modal_axiom_schema :=
  schema_union
    (schema_union (schema_union schema_T schema_Four) schema_McK)
    schema_Point3.

Definition S4Point3McK_proves {AtomType} : formula AtomType -> Prop :=
  @normal_proves S4Point3McK_schema AtomType.

(** Foundation presents the connected component as piecewise connected.
    In the presence of reflexivity this is equivalent to the strong form;
    the strong form is the one used directly by Point3 soundness. *)
Definition S4Point3McK_frame_class (F : frame) : Prop :=
  frame_reflexive F /\ frame_transitive F /\
  frame_piecewise_strongly_connected F /\ frame_mckinsey F.

Lemma S4Point3McK_schema_substitution_closed :
  schema_substitution_closed S4Point3McK_schema.
Proof.
  repeat apply schema_union_substitution_closed.
  - exact schema_T_substitution_closed.
  - exact schema_Four_substitution_closed.
  - exact schema_McK_substitution_closed.
  - exact schema_Point3_substitution_closed.
Qed.

Theorem S4Point3McK_proves_sound_on_frame :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    S4Point3McK_frame_class F ->
    S4Point3McK_proves p -> valid F p.
Proof.
  intros AtomType F p [HR [HT [HC HM]]] Hp.
  eapply normal_proves_sound_on_frame; [| exact Hp].
  apply schema_union_valid_on_frame.
  - apply schema_union_valid_on_frame.
    + apply schema_union_valid_on_frame.
      * now apply schema_T_valid_on_reflexive.
      * now apply schema_Four_valid_on_transitive.
    + now apply schema_McK_valid_on_mckinsey.
  - now apply schema_Point3_valid_on_piecewise_strongly_connected.
Qed.

Lemma S4Point3McK_frame_is_S4Point2McK :
  forall F,
    S4Point3McK_frame_class F -> S4Point2McK_frame_class F.
Proof.
  intros F [HR [HT [HC HM]]].
  split; [exact HR |]. split; [exact HT |]. split.
  - exact HM.
  - now apply piecewise_strongly_connected_strongly_convergent_of_reflexive.
Qed.

(** * Consistency, canonicality, and completeness *)

Theorem S4Point3McK_is_consistent :
  forall AtomType, ~ @S4Point3McK_proves AtomType Bottom.
Proof.
  intros AtomType Hbottom.
  assert (Hframe : S4Point3McK_frame_class reflexive_singleton_frame).
  {
    split; [exact reflexive_singleton_reflexive |].
    split; [exact reflexive_singleton_transitive |].
    split.
    - intros [] [] [] _ _. now left.
    - exact base_mck_reflexive_singleton_mckinsey.
  }
  pose proof (S4Point3McK_proves_sound_on_frame
    (F := reflexive_singleton_frame) Hframe Hbottom) as Hvalid.
  exact (Hvalid (fun _ _ => False) tt).
Qed.

Lemma S4Point3McK_canonical_frame :
  S4Point3McK_frame_class
    (normal_canonical_frame S4Point3McK_schema).
Proof.
  repeat split.
  - apply normal_canonical_reflexive_of_schema_T.
    intros A p Hp. left. left. now left.
  - apply normal_canonical_transitive_of_schema_Four.
    intros A p Hp. left. left. now right.
  - apply normal_canonical_piecewise_strongly_connected_of_schema_Point3.
    intros A p Hp. now right.
  - apply normal_canonical_mckinsey_of_K4McK_schemas.
    + intros A p Hp. left. left. now right.
    + intros A p [q ->]. left. right. now exists q.
Qed.

Theorem S4Point3McK_complete :
  forall p : formula nat,
    normal_valid_on_class S4Point3McK_frame_class p ->
    S4Point3McK_proves p.
Proof.
  unfold S4Point3McK_proves.
  apply (normal_complete_of_canonical_frame
    (Ax := S4Point3McK_schema)
    (C := S4Point3McK_frame_class)).
  - exact (@S4Point3McK_is_consistent nat).
  - exact S4Point3McK_canonical_frame.
Qed.

Theorem S4Point3McK_sound_complete :
  forall p : formula nat,
    S4Point3McK_proves p <->
    normal_valid_on_class S4Point3McK_frame_class p.
Proof.
  intro p; split.
  - intros Hp F HF. now apply S4Point3McK_proves_sound_on_frame.
  - apply S4Point3McK_complete.
Qed.

(** * Logic inclusions *)

Theorem S4Point2McK_weaker_than_S4Point3McK :
  forall p : formula nat,
    S4Point2McK_proves p -> S4Point3McK_proves p.
Proof.
  intros p Hp. apply S4Point3McK_complete.
  intros F HF. apply S4Point2McK_proves_sound_on_frame.
  - now apply S4Point3McK_frame_is_S4Point2McK.
  - exact Hp.
Qed.

Lemma S4Point3_weaker_than_S4Point3McK :
  forall (AtomType : Type) (p : formula AtomType),
    S4Point3_proves p -> S4Point3McK_proves p.
Proof.
  intros AtomType p Hp. eapply normal_proves_weaken; [| exact Hp].
  intros A q [HS4 | HPoint3].
  - left. left. exact HS4.
  - right. exact HPoint3.
Qed.

(** * Explicit finite separators *)

Lemma point3_diamond_mckinsey :
  frame_mckinsey point3_diamond_frame.
Proof.
  intro x. exists P33; split.
  - now right; right.
  - intros z Hz. destruct Hz as [Hz | [Hz | Hz]].
    + exact Hz.
    + discriminate.
    + now symmetry.
Qed.

Lemma base_mck_universal_two_piecewise_strongly_connected :
  frame_piecewise_strongly_connected base_mck_universal_two_frame.
Proof. intros x y z _ _. now left. Qed.

(** * Strict inclusions *)

Theorem S4Point2McK_strictly_weaker_S4Point3McK :
  normal_strictly_weaker S4Point2McK_proves S4Point3McK_proves.
Proof.
  split.
  - exact S4Point2McK_weaker_than_S4Point3McK.
  - exists (Point3 (Atom 0) (Atom 1)); split.
    + apply Np_extra. right. exists (Atom 0), (Atom 1). reflexivity.
    + intro HPoint2McK.
      pose proof (S4Point2McK_proves_sound_on_frame
        (F := point3_diamond_frame)
        (p := Point3 (Atom 0) (Atom 1))
        ltac:(repeat split;
          [ exact point3_diamond_reflexive
          | exact point3_diamond_transitive
          | exact point3_diamond_mckinsey
          | exact point3_diamond_piecewise_strongly_convergent ])
        HPoint2McK) as Hvalid.
      apply point3_diamond_not_piecewise_strongly_connected.
      now apply (proj1 (valid_Point3_iff_piecewise_strong_connected
        point3_diamond_frame)).
Qed.

Theorem S4Point3_strictly_weaker_S4Point3McK :
  normal_strictly_weaker S4Point3_proves S4Point3McK_proves.
Proof.
  split.
  - intros p Hp. now apply S4Point3_weaker_than_S4Point3McK.
  - exists (McK (Atom 0)); split.
    + apply Np_extra. left. right. exists (Atom 0). reflexivity.
    + intro HPoint3.
      pose proof (S4Point3_proves_sound_on_frame
        base_mck_universal_two_reflexive
        base_mck_universal_two_transitive
        base_mck_universal_two_piecewise_strongly_connected
        HPoint3) as Hvalid.
      specialize (Hvalid (fun _ w => w = false) false).
      assert (Hboxdia : satisfies base_mck_universal_two_frame
        (fun _ w => w = false) false (Box (Dia (Atom 0)))).
      {
        intros y _. apply satisfies_dia_intro.
        exists false; split; [constructor | reflexivity].
      }
      destruct (@satisfies_dia_elim nat base_mck_universal_two_frame
        (fun _ w => w = false) false (Box (Atom 0))
        (Hvalid Hboxdia)) as [y [_ Hbox]].
      specialize (Hbox true ltac:(constructor)). discriminate.
Qed.
