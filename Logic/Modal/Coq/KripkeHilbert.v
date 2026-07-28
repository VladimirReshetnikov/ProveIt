(**
  Frame-class wrappers for normal Hilbert soundness and completeness.

  This module ports the active theorem surface of
  [Foundation/Modal/Kripke/Hilbert.lean].  Foundation bundles a nonempty
  world type into every frame.  The Coq [frame] record intentionally permits
  empty world types, so the two consistency results below make the required
  [inhabited_frame] witness explicit.

  The underlying induction on Hilbert derivations is already provided by
  [NormalHilbert.normal_proves_sound_on_frame].  The contribution here is
  the source-facing frame-class abstraction, its soundness/completeness
  packages, and the semantic comparison theorem between normal systems.
*)

From FoundationModal Require Import Syntax Kripke NormalHilbert KripkeSemantics.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Soundness and completeness packages *)

Record normal_frame_class_sound
    (Ax : modal_axiom_schema) (C : kripke_frame_class) : Prop := {
  normal_frame_class_soundness :
    forall (AtomType : Type) (p : formula AtomType),
      normal_proves Ax p -> kripke_frame_class_valid C p
}.

Arguments normal_frame_class_soundness {Ax C} _ {AtomType p} _.

Record normal_frame_sound
    (Ax : modal_axiom_schema) (F : frame) : Prop := {
  normal_frame_soundness :
    forall (AtomType : Type) (p : formula AtomType),
      normal_proves Ax p -> valid F p
}.

Arguments normal_frame_soundness {Ax F} _ {AtomType p} _.

Record normal_frame_class_complete
    (Ax : modal_axiom_schema) (C : kripke_frame_class) : Prop := {
  normal_frame_class_completeness :
    forall (AtomType : Type) (p : formula AtomType),
      kripke_frame_class_valid C p -> normal_proves Ax p
}.

Arguments normal_frame_class_completeness {Ax C} _ {AtomType p} _.

(** An atom-polymorphic counterpart of Foundation's entailment-level
    [WeakerThan] relation. *)
Definition normal_weaker_than
    (Ax1 Ax2 : modal_axiom_schema) : Prop :=
  forall (AtomType : Type) (p : formula AtomType),
    normal_proves Ax1 p -> normal_proves Ax2 p.

(** Foundation's consistency declaration is specialized to natural-number
    atoms.  Since the local normal calculus is atom-polymorphic, the stronger
    uniform formulation is available without any additional proof. *)
Definition normal_consistent_all_atoms
    (Ax : modal_axiom_schema) : Prop :=
  forall AtomType : Type, ~ normal_proves Ax (@Bottom AtomType).

(** * Axiom validity gives soundness *)

Theorem normal_soundness_of_frame_class_validates_axioms :
  forall (Ax : modal_axiom_schema) (C : kripke_frame_class),
    kripke_frame_class_validates_schema Ax C ->
    forall (AtomType : Type) (p : formula AtomType),
      normal_proves Ax p -> kripke_frame_class_valid C p.
Proof.
  intros Ax C HAx AtomType p Hp F HF.
  eapply normal_proves_sound_on_frame; [|exact Hp].
  intros A q Hq. exact (HAx A q Hq F HF).
Qed.

Definition normal_frame_class_sound_of_validates_axioms
    (Ax : modal_axiom_schema) (C : kripke_frame_class)
    (HAx : kripke_frame_class_validates_schema Ax C)
    : normal_frame_class_sound Ax C.
Proof.
  constructor. intros AtomType p Hp.
  exact
    (@normal_soundness_of_frame_class_validates_axioms
      Ax C HAx AtomType p Hp).
Defined.

Theorem normal_soundness_of_frame_validates_axioms :
  forall (Ax : modal_axiom_schema) (F : frame),
    schema_valid_on_frame Ax F ->
    forall (AtomType : Type) (p : formula AtomType),
      normal_proves Ax p -> valid F p.
Proof.
  intros Ax F HAx AtomType p Hp.
  now apply normal_proves_sound_on_frame with (Ax := Ax).
Qed.

Definition normal_frame_sound_of_validates_axioms
    (Ax : modal_axiom_schema) (F : frame)
    (HAx : schema_valid_on_frame Ax F)
    : normal_frame_sound Ax F.
Proof.
  constructor. intros AtomType p Hp.
  exact
    (@normal_soundness_of_frame_validates_axioms
      Ax F HAx AtomType p Hp).
Defined.

(** * Sound semantics give consistency *)

Theorem normal_consistent_of_sound_frame_class :
  forall (Ax : modal_axiom_schema) (C : kripke_frame_class),
    normal_frame_class_sound Ax C ->
    forall F : frame,
      C F -> inhabited_frame F -> normal_consistent_all_atoms Ax.
Proof.
  intros Ax C Hsound F HF [w _] AtomType Hbottom.
  pose proof
    (normal_frame_class_soundness Hsound Hbottom F HF
      (fun _ _ => False) w) as Hfalse.
  exact Hfalse.
Qed.

Theorem normal_consistent_of_sound_frame :
  forall (Ax : modal_axiom_schema) (F : frame),
    normal_frame_sound Ax F ->
    inhabited_frame F -> normal_consistent_all_atoms Ax.
Proof.
  intros Ax F Hsound [w _] AtomType Hbottom.
  pose proof
    (normal_frame_soundness Hsound Hbottom
      (fun _ _ => False) w) as Hfalse.
  exact Hfalse.
Qed.

(** * Comparing systems through nested frame classes *)

Theorem normal_weaker_than_of_subset_frame_class :
  forall (Ax1 Ax2 : modal_axiom_schema)
         (C1 C2 : kripke_frame_class),
    (forall F, C2 F -> C1 F) ->
    normal_frame_class_sound Ax1 C1 ->
    normal_frame_class_complete Ax2 C2 ->
    normal_weaker_than Ax1 Ax2.
Proof.
  intros Ax1 Ax2 C1 C2 HC Hsound Hcomplete AtomType p Hp.
  apply (normal_frame_class_completeness Hcomplete).
  intros F HF.
  apply (normal_frame_class_soundness Hsound Hp).
  now apply HC.
Qed.
