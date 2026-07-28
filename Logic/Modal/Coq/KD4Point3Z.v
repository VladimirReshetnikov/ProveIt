(**
  Soundness and consistency of KD4.3Z on the strict natural-number frame.

  This module ports the complete theorem surface of the pinned Foundation
  file [Modal/Kripke/Logic/KD4Point3Z.lean].  Normal modal logic already
  supplies K, so the concrete calculus is presented as the union of the D,
  Four, WeakPoint3, and Z schemata.  The upstream [natLT] frame is the local
  [nat_lt_frame].

  Foundation proves Z first at one distinguished atom and obtains arbitrary
  instances through uniform substitution.  We make that step explicit:
  [nat_lt_validates_Z] is transported by [valid_substitution], yielding an
  atom-polymorphic schema-validity theorem without reproving the descending
  induction from [StructuralFrames].
*)

From FoundationModal Require Import
  Syntax Axioms Kripke Correspondence Root NormalHilbert CanonicalCombinations
  WeakCorrespondence StructuralFrames.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Concrete calculus and substitution closure *)

Definition schema_Z : modal_axiom_schema :=
  fun AtomType p => exists q : formula AtomType, p = Z q.

Definition KD4Point3Z_schema : modal_axiom_schema :=
  schema_union
    (schema_union KD4_schema K4Point3_weak_schema)
    schema_Z.

Definition KD4Point3Z_proves {AtomType} : formula AtomType -> Prop :=
  @normal_proves KD4Point3Z_schema AtomType.

Lemma schema_Z_substitution_closed :
  schema_substitution_closed schema_Z.
Proof.
  intros A B sigma p [q ->].
  exists (substitute sigma q). reflexivity.
Qed.

Lemma KD4Point3Z_schema_substitution_closed :
  schema_substitution_closed KD4Point3Z_schema.
Proof.
  apply schema_union_substitution_closed.
  - apply schema_union_substitution_closed.
    + exact KD4_schema_substitution_closed.
    + exact K4Point3_weak_schema_substitution_closed.
  - exact schema_Z_substitution_closed.
Qed.

(** * Frame class and generic soundness *)

(** The local development exposes no standalone structural predicate for
    arbitrary Z frames.  Its semantic component is therefore recorded
    directly, alongside the D/Four/WeakPoint3 conditions. *)
Definition KD4Point3Z_frame_class (F : frame) : Prop :=
  frame_serial F /\
  frame_transitive F /\
  frame_piecewise_connected F /\
  schema_valid_on_frame schema_Z F.

Lemma KD4Point3Z_schema_valid_on_frame :
  forall F,
    KD4Point3Z_frame_class F ->
    schema_valid_on_frame KD4Point3Z_schema F.
Proof.
  intros F [Hserial [Htrans [Hpiece HZ]]].
  apply schema_union_valid_on_frame.
  - apply schema_union_valid_on_frame.
    + apply schema_union_valid_on_frame.
      * now apply schema_D_valid_on_serial.
      * now apply schema_Four_valid_on_transitive.
    + intros AtomType p [q [r ->]].
      now apply valid_WeakPoint3_of_piecewise_connected.
  - exact HZ.
Qed.

Theorem KD4Point3Z_proves_sound_on_frame :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    KD4Point3Z_frame_class F ->
    KD4Point3Z_proves p -> valid F p.
Proof.
  intros AtomType F p HF Hp.
  eapply normal_proves_sound_on_frame; [| exact Hp].
  now apply KD4Point3Z_schema_valid_on_frame.
Qed.

(** * The strict natural-number frame *)

Lemma schema_Z_valid_on_nat_lt :
  schema_valid_on_frame schema_Z nat_lt_frame.
Proof.
  intros AtomType p [q ->].
  change (valid nat_lt_frame
    (substitute (fun _ : nat => q) (Z (Atom 0)))).
  apply valid_substitution.
  exact nat_lt_validates_Z.
Qed.

Lemma nat_lt_is_KD4Point3Z_frame :
  KD4Point3Z_frame_class nat_lt_frame.
Proof.
  repeat split.
  - exact nat_lt_serial.
  - exact nat_lt_transitive.
  - exact nat_lt_piecewise_connected.
  - exact schema_Z_valid_on_nat_lt.
Qed.

(** This is the direct Coq analogue of Foundation's
    [Sound Modal.KD4Point3Z natLT] instance. *)
Theorem KD4Point3Z_proves_sound_on_nat_lt :
  forall (AtomType : Type) (p : formula AtomType),
    KD4Point3Z_proves p -> valid nat_lt_frame p.
Proof.
  intros AtomType p Hp.
  eapply KD4Point3Z_proves_sound_on_frame.
  - exact nat_lt_is_KD4Point3Z_frame.
  - exact Hp.
Qed.

(** This is the direct analogue of Foundation's consistency instance.  The
    witness frame is infinite but inhabited, which is all semantic
    consistency requires. *)
Theorem KD4Point3Z_is_consistent :
  forall AtomType, ~ @KD4Point3Z_proves AtomType Bottom.
Proof.
  apply (normal_consistent_of_sound_inhabited_frame
    (Ax := KD4Point3Z_schema) (F := nat_lt_frame)).
  - exists 0. constructor.
  - exact (KD4Point3Z_schema_valid_on_frame
      nat_lt_is_KD4Point3Z_frame).
Qed.

(** Source-facing aliases. *)
Corollary KD4Point3Z_sound_natLT :
  forall (AtomType : Type) (p : formula AtomType),
    KD4Point3Z_proves p -> valid nat_lt_frame p.
Proof. exact KD4Point3Z_proves_sound_on_nat_lt. Qed.

Corollary KD4Point3Z_consistent :
  forall AtomType, ~ @KD4Point3Z_proves AtomType Bottom.
Proof. exact KD4Point3Z_is_consistent. Qed.
