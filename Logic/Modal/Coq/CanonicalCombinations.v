(**
  Canonical completeness for combinations of D, B, Four, and Five.

  This module ports the mathematical surfaces of the pinned Foundation
  Kripke modules K45, KD4, KD5, KDB, KB4, KB5, and KD45.  The calculi are
  represented as unions of the corresponding polymorphic axiom schemata.
  Soundness and consistency are therefore atom-polymorphic; canonical
  completeness, like [CanonicalExtensions] and [CanonicalDB5], is stated for
  formulas whose atoms are natural numbers.

  The K45 source also compares K45 with K4Point3.  A local presentation of
  K4Point3 is included below, using the already checked WeakPoint3
  correspondence, so the complete theorem surfaces of all seven modules are
  represented.
*)

From FoundationModal Require Import
  Syntax Axioms HilbertK Kripke Correspondence HilbertKSoundness NormalHilbert
  CanonicalExtensions CanonicalDB5 Root WeakCorrespondence.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Combined schemata and calculi *)

Definition K45_schema : modal_axiom_schema :=
  schema_union schema_Four schema_Five.
Definition KD4_schema : modal_axiom_schema :=
  schema_union schema_D schema_Four.
Definition KD5_schema : modal_axiom_schema :=
  schema_union schema_D schema_Five.
Definition KDB_schema : modal_axiom_schema :=
  schema_union schema_D schema_B.
Definition KB4_schema : modal_axiom_schema :=
  schema_union schema_B schema_Four.
Definition KB5_schema : modal_axiom_schema :=
  schema_union schema_B schema_Five.
Definition KD45_schema : modal_axiom_schema :=
  schema_union KD4_schema schema_Five.

(** Local support for the comparison occurring in [K45.lean]. *)
Definition K4Point3_weak_schema : modal_axiom_schema :=
  fun AtomType p => exists q r : formula AtomType, p = WeakPoint3 q r.
Definition K4Point3_schema : modal_axiom_schema :=
  schema_union schema_Four K4Point3_weak_schema.

Definition K45_proves {AtomType} : formula AtomType -> Prop :=
  @normal_proves K45_schema AtomType.
Definition KD4_proves {AtomType} : formula AtomType -> Prop :=
  @normal_proves KD4_schema AtomType.
Definition KD5_proves {AtomType} : formula AtomType -> Prop :=
  @normal_proves KD5_schema AtomType.
Definition KDB_proves {AtomType} : formula AtomType -> Prop :=
  @normal_proves KDB_schema AtomType.
Definition KB4_proves {AtomType} : formula AtomType -> Prop :=
  @normal_proves KB4_schema AtomType.
Definition KB5_proves {AtomType} : formula AtomType -> Prop :=
  @normal_proves KB5_schema AtomType.
Definition KD45_proves {AtomType} : formula AtomType -> Prop :=
  @normal_proves KD45_schema AtomType.
Definition K4Point3_proves {AtomType} : formula AtomType -> Prop :=
  @normal_proves K4Point3_schema AtomType.

Lemma K45_schema_substitution_closed :
  schema_substitution_closed K45_schema.
Proof.
  apply schema_union_substitution_closed.
  - exact schema_Four_substitution_closed.
  - exact schema_Five_substitution_closed.
Qed.

Lemma KD4_schema_substitution_closed :
  schema_substitution_closed KD4_schema.
Proof.
  apply schema_union_substitution_closed.
  - exact schema_D_substitution_closed.
  - exact schema_Four_substitution_closed.
Qed.

Lemma KD5_schema_substitution_closed :
  schema_substitution_closed KD5_schema.
Proof.
  apply schema_union_substitution_closed.
  - exact schema_D_substitution_closed.
  - exact schema_Five_substitution_closed.
Qed.

Lemma KDB_schema_substitution_closed :
  schema_substitution_closed KDB_schema.
Proof.
  apply schema_union_substitution_closed.
  - exact schema_D_substitution_closed.
  - exact schema_B_substitution_closed.
Qed.

Lemma KB4_schema_substitution_closed :
  schema_substitution_closed KB4_schema.
Proof.
  apply schema_union_substitution_closed.
  - exact schema_B_substitution_closed.
  - exact schema_Four_substitution_closed.
Qed.

Lemma KB5_schema_substitution_closed :
  schema_substitution_closed KB5_schema.
Proof.
  apply schema_union_substitution_closed.
  - exact schema_B_substitution_closed.
  - exact schema_Five_substitution_closed.
Qed.

Lemma KD45_schema_substitution_closed :
  schema_substitution_closed KD45_schema.
Proof.
  apply schema_union_substitution_closed.
  - exact KD4_schema_substitution_closed.
  - exact schema_Five_substitution_closed.
Qed.

Lemma K4Point3_weak_schema_substitution_closed :
  schema_substitution_closed K4Point3_weak_schema.
Proof.
  intros A B sigma p [q [r ->]].
  exists (substitute sigma q), (substitute sigma r).
  reflexivity.
Qed.

Lemma K4Point3_schema_substitution_closed :
  schema_substitution_closed K4Point3_schema.
Proof.
  apply schema_union_substitution_closed.
  - exact schema_Four_substitution_closed.
  - exact K4Point3_weak_schema_substitution_closed.
Qed.

Lemma normal_proves_union_left :
  forall Ax Ay (AtomType : Type) (p : formula AtomType),
    normal_proves Ax p -> normal_proves (schema_union Ax Ay) p.
Proof.
  intros Ax Ay AtomType p Hp.
  apply (normal_proves_weaken (Ax := Ax) (Ay := schema_union Ax Ay)).
  - intros A q Hq. now left.
  - exact Hp.
Qed.

Lemma normal_proves_union_right :
  forall Ax Ay (AtomType : Type) (p : formula AtomType),
    normal_proves Ay p -> normal_proves (schema_union Ax Ay) p.
Proof.
  intros Ax Ay AtomType p Hp.
  apply (normal_proves_weaken (Ax := Ay) (Ay := schema_union Ax Ay)).
  - intros A q Hq. now right.
  - exact Hp.
Qed.

(** * Frame classes and soundness *)

Definition K45_frame_class (F : frame) : Prop :=
  frame_transitive F /\ frame_right_euclidean F.
Definition KD4_frame_class (F : frame) : Prop :=
  frame_serial F /\ frame_transitive F.
Definition KD5_frame_class (F : frame) : Prop :=
  frame_serial F /\ frame_right_euclidean F.
Definition KDB_frame_class (F : frame) : Prop :=
  frame_serial F /\ frame_symmetric F.
Definition KB4_frame_class (F : frame) : Prop :=
  frame_symmetric F /\ frame_transitive F.
Definition KB5_frame_class (F : frame) : Prop :=
  frame_symmetric F /\ frame_right_euclidean F.
Definition KD45_frame_class (F : frame) : Prop :=
  frame_serial F /\ frame_transitive F /\ frame_right_euclidean F.
Definition K4Point3_frame_class (F : frame) : Prop :=
  frame_transitive F /\ frame_piecewise_connected F.

Theorem K45_proves_sound_on_frame :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    frame_transitive F -> frame_right_euclidean F ->
    K45_proves p -> valid F p.
Proof.
  intros AtomType F p HT HE Hp.
  eapply normal_proves_sound_on_frame; [| exact Hp].
  apply schema_union_valid_on_frame.
  - now apply schema_Four_valid_on_transitive.
  - now apply schema_Five_valid_on_right_euclidean.
Qed.

Theorem KD4_proves_sound_on_frame :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    frame_serial F -> frame_transitive F -> KD4_proves p -> valid F p.
Proof.
  intros AtomType F p HS HT Hp.
  eapply normal_proves_sound_on_frame; [| exact Hp].
  apply schema_union_valid_on_frame.
  - now apply schema_D_valid_on_serial.
  - now apply schema_Four_valid_on_transitive.
Qed.

Theorem KD5_proves_sound_on_frame :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    frame_serial F -> frame_right_euclidean F ->
    KD5_proves p -> valid F p.
Proof.
  intros AtomType F p HS HE Hp.
  eapply normal_proves_sound_on_frame; [| exact Hp].
  apply schema_union_valid_on_frame.
  - now apply schema_D_valid_on_serial.
  - now apply schema_Five_valid_on_right_euclidean.
Qed.

Theorem KDB_proves_sound_on_frame :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    frame_serial F -> frame_symmetric F -> KDB_proves p -> valid F p.
Proof.
  intros AtomType F p HS HY Hp.
  eapply normal_proves_sound_on_frame; [| exact Hp].
  apply schema_union_valid_on_frame.
  - now apply schema_D_valid_on_serial.
  - now apply schema_B_valid_on_symmetric.
Qed.

Theorem KB4_proves_sound_on_frame :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    frame_symmetric F -> frame_transitive F -> KB4_proves p -> valid F p.
Proof.
  intros AtomType F p HS HT Hp.
  eapply normal_proves_sound_on_frame; [| exact Hp].
  apply schema_union_valid_on_frame.
  - now apply schema_B_valid_on_symmetric.
  - now apply schema_Four_valid_on_transitive.
Qed.

Theorem KB5_proves_sound_on_frame :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    frame_symmetric F -> frame_right_euclidean F ->
    KB5_proves p -> valid F p.
Proof.
  intros AtomType F p HS HE Hp.
  eapply normal_proves_sound_on_frame; [| exact Hp].
  apply schema_union_valid_on_frame.
  - now apply schema_B_valid_on_symmetric.
  - now apply schema_Five_valid_on_right_euclidean.
Qed.

Theorem KD45_proves_sound_on_frame :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    frame_serial F -> frame_transitive F -> frame_right_euclidean F ->
    KD45_proves p -> valid F p.
Proof.
  intros AtomType F p HS HT HE Hp.
  eapply normal_proves_sound_on_frame; [| exact Hp].
  apply schema_union_valid_on_frame.
  - apply schema_union_valid_on_frame.
    + now apply schema_D_valid_on_serial.
    + now apply schema_Four_valid_on_transitive.
  - now apply schema_Five_valid_on_right_euclidean.
Qed.

Theorem K4Point3_proves_sound_on_frame :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    frame_transitive F -> frame_piecewise_connected F ->
    K4Point3_proves p -> valid F p.
Proof.
  intros AtomType F p HT HC Hp.
  eapply normal_proves_sound_on_frame; [|exact Hp].
  apply schema_union_valid_on_frame.
  - now apply schema_Four_valid_on_transitive.
  - intros A q [r [s ->]].
    now apply valid_WeakPoint3_of_piecewise_connected.
Qed.

Lemma frame_right_euclidean_piecewise_connected :
  forall F,
    frame_right_euclidean F -> frame_piecewise_connected F.
Proof.
  intros F HE x y z Hxy Hxz.
  left. now apply (HE x y z).
Qed.

Corollary K45_frame_class_in_K4Point3 :
  forall F, K45_frame_class F -> K4Point3_frame_class F.
Proof.
  intros F [HT HE]; split; [exact HT |].
  now apply frame_right_euclidean_piecewise_connected.
Qed.

(** * Atom-polymorphic consistency *)

Theorem K45_is_consistent :
  forall AtomType, ~ @K45_proves AtomType Bottom.
Proof.
  apply (normal_consistent_of_sound_inhabited_frame
    (Ax := K45_schema) (F := reflexive_singleton_frame)).
  - now exists tt.
  - apply schema_union_valid_on_frame.
    + apply schema_Four_valid_on_transitive.
      exact reflexive_singleton_transitive.
    + apply schema_Five_valid_on_right_euclidean.
      exact reflexive_singleton_right_euclidean.
Qed.

Theorem KD4_is_consistent :
  forall AtomType, ~ @KD4_proves AtomType Bottom.
Proof.
  apply (normal_consistent_of_sound_inhabited_frame
    (Ax := KD4_schema) (F := reflexive_singleton_frame)).
  - now exists tt.
  - apply schema_union_valid_on_frame.
    + apply schema_D_valid_on_serial.
      exact reflexive_singleton_serial.
    + apply schema_Four_valid_on_transitive.
      exact reflexive_singleton_transitive.
Qed.

Theorem KD5_is_consistent :
  forall AtomType, ~ @KD5_proves AtomType Bottom.
Proof.
  apply (normal_consistent_of_sound_inhabited_frame
    (Ax := KD5_schema) (F := reflexive_singleton_frame)).
  - now exists tt.
  - apply schema_union_valid_on_frame.
    + apply schema_D_valid_on_serial.
      exact reflexive_singleton_serial.
    + apply schema_Five_valid_on_right_euclidean.
      exact reflexive_singleton_right_euclidean.
Qed.

Theorem KDB_is_consistent :
  forall AtomType, ~ @KDB_proves AtomType Bottom.
Proof.
  apply (normal_consistent_of_sound_inhabited_frame
    (Ax := KDB_schema) (F := reflexive_singleton_frame)).
  - now exists tt.
  - apply schema_union_valid_on_frame.
    + apply schema_D_valid_on_serial.
      exact reflexive_singleton_serial.
    + apply schema_B_valid_on_symmetric.
      exact reflexive_singleton_symmetric.
Qed.

Theorem KB4_is_consistent :
  forall AtomType, ~ @KB4_proves AtomType Bottom.
Proof.
  apply (normal_consistent_of_sound_inhabited_frame
    (Ax := KB4_schema) (F := reflexive_singleton_frame)).
  - now exists tt.
  - apply schema_union_valid_on_frame.
    + apply schema_B_valid_on_symmetric.
      exact reflexive_singleton_symmetric.
    + apply schema_Four_valid_on_transitive.
      exact reflexive_singleton_transitive.
Qed.

Theorem KB5_is_consistent :
  forall AtomType, ~ @KB5_proves AtomType Bottom.
Proof.
  apply (normal_consistent_of_sound_inhabited_frame
    (Ax := KB5_schema) (F := reflexive_singleton_frame)).
  - now exists tt.
  - apply schema_union_valid_on_frame.
    + apply schema_B_valid_on_symmetric.
      exact reflexive_singleton_symmetric.
    + apply schema_Five_valid_on_right_euclidean.
      exact reflexive_singleton_right_euclidean.
Qed.

Theorem KD45_is_consistent :
  forall AtomType, ~ @KD45_proves AtomType Bottom.
Proof.
  apply (normal_consistent_of_sound_inhabited_frame
    (Ax := KD45_schema) (F := reflexive_singleton_frame)).
  - now exists tt.
  - apply schema_union_valid_on_frame.
    + apply schema_union_valid_on_frame.
      * apply schema_D_valid_on_serial.
        exact reflexive_singleton_serial.
      * apply schema_Four_valid_on_transitive.
        exact reflexive_singleton_transitive.
    + apply schema_Five_valid_on_right_euclidean.
      exact reflexive_singleton_right_euclidean.
Qed.

(** * Canonical frame properties *)

Theorem normal_canonical_transitive_of_schema_Four :
  forall Ax,
    schema_included schema_Four Ax ->
    frame_transitive (normal_canonical_frame Ax).
Proof.
  intros Ax HFour M N O HMN HNO p Hbox.
  apply HNO. apply HMN. apply normal_mct_derivable_mem.
  eapply ND_mp.
  - apply ND_theorem. apply Np_extra. apply HFour.
    exists p. reflexivity.
  - apply ND_assumption. exact Hbox.
Qed.

Lemma K45_canonical_frame :
  K45_frame_class (normal_canonical_frame K45_schema).
Proof.
  split.
  - apply normal_canonical_transitive_of_schema_Four.
    intros A p Hp. now left.
  - apply normal_canonical_right_euclidean_of_schema_Five.
    intros A p Hp. now right.
Qed.

Lemma KD4_canonical_frame :
  KD4_frame_class (normal_canonical_frame KD4_schema).
Proof.
  split.
  - apply normal_canonical_serial_of_schema_D.
    intros A p Hp. now left.
  - apply normal_canonical_transitive_of_schema_Four.
    intros A p Hp. now right.
Qed.

Lemma KD5_canonical_frame :
  KD5_frame_class (normal_canonical_frame KD5_schema).
Proof.
  split.
  - apply normal_canonical_serial_of_schema_D.
    intros A p Hp. now left.
  - apply normal_canonical_right_euclidean_of_schema_Five.
    intros A p Hp. now right.
Qed.

Lemma KDB_canonical_frame :
  KDB_frame_class (normal_canonical_frame KDB_schema).
Proof.
  split.
  - apply normal_canonical_serial_of_schema_D.
    intros A p Hp. now left.
  - apply normal_canonical_symmetric_of_schema_B.
    intros A p Hp. now right.
Qed.

Lemma KB4_canonical_frame :
  KB4_frame_class (normal_canonical_frame KB4_schema).
Proof.
  split.
  - apply normal_canonical_symmetric_of_schema_B.
    intros A p Hp. now left.
  - apply normal_canonical_transitive_of_schema_Four.
    intros A p Hp. now right.
Qed.

Lemma KB5_canonical_frame :
  KB5_frame_class (normal_canonical_frame KB5_schema).
Proof.
  split.
  - apply normal_canonical_symmetric_of_schema_B.
    intros A p Hp. now left.
  - apply normal_canonical_right_euclidean_of_schema_Five.
    intros A p Hp. now right.
Qed.

Lemma KD45_canonical_frame :
  KD45_frame_class (normal_canonical_frame KD45_schema).
Proof.
  split.
  - apply normal_canonical_serial_of_schema_D.
    intros A p Hp. left. now left.
  - split.
    + apply normal_canonical_transitive_of_schema_Four.
      intros A p Hp. left. now right.
    + apply normal_canonical_right_euclidean_of_schema_Five.
      intros A p Hp. now right.
Qed.

(** * Completeness and soundness/completeness *)

Theorem K45_complete :
  forall p : formula nat,
    normal_valid_on_class K45_frame_class p -> K45_proves p.
Proof.
  unfold K45_proves.
  apply (normal_complete_of_canonical_frame
    (Ax := K45_schema) (C := K45_frame_class)).
  - exact (@K45_is_consistent nat).
  - exact K45_canonical_frame.
Qed.

Lemma K45_proves_WeakPoint3 :
  forall p q : formula nat,
    K45_proves (WeakPoint3 p q).
Proof.
  intros p q; apply K45_complete.
  intros F [_ HE].
  apply valid_WeakPoint3_of_piecewise_connected.
  now apply frame_right_euclidean_piecewise_connected.
Qed.

Theorem KD4_complete :
  forall p : formula nat,
    normal_valid_on_class KD4_frame_class p -> KD4_proves p.
Proof.
  unfold KD4_proves.
  apply (normal_complete_of_canonical_frame
    (Ax := KD4_schema) (C := KD4_frame_class)).
  - exact (@KD4_is_consistent nat).
  - exact KD4_canonical_frame.
Qed.

Theorem KD5_complete :
  forall p : formula nat,
    normal_valid_on_class KD5_frame_class p -> KD5_proves p.
Proof.
  unfold KD5_proves.
  apply (normal_complete_of_canonical_frame
    (Ax := KD5_schema) (C := KD5_frame_class)).
  - exact (@KD5_is_consistent nat).
  - exact KD5_canonical_frame.
Qed.

Theorem KDB_complete :
  forall p : formula nat,
    normal_valid_on_class KDB_frame_class p -> KDB_proves p.
Proof.
  unfold KDB_proves.
  apply (normal_complete_of_canonical_frame
    (Ax := KDB_schema) (C := KDB_frame_class)).
  - exact (@KDB_is_consistent nat).
  - exact KDB_canonical_frame.
Qed.

Theorem KB4_complete :
  forall p : formula nat,
    normal_valid_on_class KB4_frame_class p -> KB4_proves p.
Proof.
  unfold KB4_proves.
  apply (normal_complete_of_canonical_frame
    (Ax := KB4_schema) (C := KB4_frame_class)).
  - exact (@KB4_is_consistent nat).
  - exact KB4_canonical_frame.
Qed.

Theorem KB5_complete :
  forall p : formula nat,
    normal_valid_on_class KB5_frame_class p -> KB5_proves p.
Proof.
  unfold KB5_proves.
  apply (normal_complete_of_canonical_frame
    (Ax := KB5_schema) (C := KB5_frame_class)).
  - exact (@KB5_is_consistent nat).
  - exact KB5_canonical_frame.
Qed.

Theorem KD45_complete :
  forall p : formula nat,
    normal_valid_on_class KD45_frame_class p -> KD45_proves p.
Proof.
  unfold KD45_proves.
  apply (normal_complete_of_canonical_frame
    (Ax := KD45_schema) (C := KD45_frame_class)).
  - exact (@KD45_is_consistent nat).
  - exact KD45_canonical_frame.
Qed.

Theorem K45_sound_complete :
  forall p : formula nat,
    K45_proves p <-> normal_valid_on_class K45_frame_class p.
Proof.
  intro p; split.
  - intros Hp F [HT HE]. now apply K45_proves_sound_on_frame.
  - apply K45_complete.
Qed.

Theorem KD4_sound_complete :
  forall p : formula nat,
    KD4_proves p <-> normal_valid_on_class KD4_frame_class p.
Proof.
  intro p; split.
  - intros Hp F [HS HT]. now apply KD4_proves_sound_on_frame.
  - apply KD4_complete.
Qed.

Theorem KD5_sound_complete :
  forall p : formula nat,
    KD5_proves p <-> normal_valid_on_class KD5_frame_class p.
Proof.
  intro p; split.
  - intros Hp F [HS HE]. now apply KD5_proves_sound_on_frame.
  - apply KD5_complete.
Qed.

Theorem KDB_sound_complete :
  forall p : formula nat,
    KDB_proves p <-> normal_valid_on_class KDB_frame_class p.
Proof.
  intro p; split.
  - intros Hp F [HS HY]. now apply KDB_proves_sound_on_frame.
  - apply KDB_complete.
Qed.

Theorem KB4_sound_complete :
  forall p : formula nat,
    KB4_proves p <-> normal_valid_on_class KB4_frame_class p.
Proof.
  intro p; split.
  - intros Hp F [HS HT]. now apply KB4_proves_sound_on_frame.
  - apply KB4_complete.
Qed.

Theorem KB5_sound_complete :
  forall p : formula nat,
    KB5_proves p <-> normal_valid_on_class KB5_frame_class p.
Proof.
  intro p; split.
  - intros Hp F [HS HE]. now apply KB5_proves_sound_on_frame.
  - apply KB5_complete.
Qed.

Theorem KD45_sound_complete :
  forall p : formula nat,
    KD45_proves p <-> normal_valid_on_class KD45_frame_class p.
Proof.
  intro p; split.
  - intros Hp F [HS [HT HE]]. now apply KD45_proves_sound_on_frame.
  - apply KD45_complete.
Qed.

(** * Inclusions used by the source strict-order results *)

Lemma K4Point3_weaker_than_K45 :
  forall p : formula nat,
    K4Point3_proves p -> K45_proves p.
Proof.
  intros p Hp; unfold K4Point3_proves in Hp; unfold K45_proves.
  induction Hp.
  - apply Np_imply_K.
  - apply Np_imply_S.
  - apply Np_elim_contra.
  - apply Np_modal_K.
  - destruct H as [HFour | Hweak].
    + apply Np_extra. now left.
    + destruct Hweak as [q [r ->]].
      exact (K45_proves_WeakPoint3 q r).
  - eapply Np_mp; eauto.
  - now apply Np_nec.
Qed.

Lemma K5_weaker_than_K45 :
  forall (AtomType : Type) (p : formula AtomType),
    K5_proves p -> K45_proves p.
Proof.
  intros AtomType p Hp. unfold K5_proves, K45_proves in *.
  now apply normal_proves_union_right.
Qed.

Lemma KD_weaker_than_KD4 :
  forall (AtomType : Type) (p : formula AtomType),
    KD_proves p -> KD4_proves p.
Proof.
  intros AtomType p Hp. unfold KD_proves, KD4_proves in *.
  now apply normal_proves_union_left.
Qed.

Lemma K4_weaker_than_KD4 :
  forall (AtomType : Type) (p : formula AtomType),
    K4_proves p -> KD4_proves p.
Proof.
  intros AtomType p Hp. unfold K4_proves, KD4_proves in *.
  now apply normal_proves_union_right.
Qed.

Lemma KD_weaker_than_KD5 :
  forall (AtomType : Type) (p : formula AtomType),
    KD_proves p -> KD5_proves p.
Proof.
  intros AtomType p Hp. unfold KD_proves, KD5_proves in *.
  now apply normal_proves_union_left.
Qed.

Lemma K5_weaker_than_KD5 :
  forall (AtomType : Type) (p : formula AtomType),
    K5_proves p -> KD5_proves p.
Proof.
  intros AtomType p Hp. unfold K5_proves, KD5_proves in *.
  now apply normal_proves_union_right.
Qed.

Lemma KD_weaker_than_KDB :
  forall (AtomType : Type) (p : formula AtomType),
    KD_proves p -> KDB_proves p.
Proof.
  intros AtomType p Hp. unfold KD_proves, KDB_proves in *.
  now apply normal_proves_union_left.
Qed.

Lemma KB_weaker_than_KDB :
  forall (AtomType : Type) (p : formula AtomType),
    KB_proves p -> KDB_proves p.
Proof.
  intros AtomType p Hp. unfold KB_proves, KDB_proves in *.
  now apply normal_proves_union_right.
Qed.

Lemma KB_weaker_than_KB4 :
  forall (AtomType : Type) (p : formula AtomType),
    KB_proves p -> KB4_proves p.
Proof.
  intros AtomType p Hp. unfold KB_proves, KB4_proves in *.
  now apply normal_proves_union_left.
Qed.

Lemma KD4_weaker_than_KD45 :
  forall (AtomType : Type) (p : formula AtomType),
    KD4_proves p -> KD45_proves p.
Proof.
  intros AtomType p Hp. unfold KD4_proves, KD45_proves in *.
  now apply normal_proves_union_left.
Qed.

Lemma KD5_weaker_than_KD45 :
  forall (AtomType : Type) (p : formula AtomType),
    KD5_proves p -> KD45_proves p.
Proof.
  intros AtomType p Hp. unfold KD5_proves, KD45_proves in *.
  eapply normal_proves_weaken; [| exact Hp].
  intros A q [HD | HFive].
  - left. now left.
  - now right.
Qed.

Lemma K45_weaker_than_KD45 :
  forall (AtomType : Type) (p : formula AtomType),
    K45_proves p -> KD45_proves p.
Proof.
  intros AtomType p Hp. unfold K45_proves, KD45_proves in *.
  eapply normal_proves_weaken; [| exact Hp].
  intros A q [HFour | HFive].
  - left. now right.
  - now right.
Qed.

(** Symmetry and transitivity entail right Euclideanity.  This is the frame
    conversion used by Foundation's inclusion K45 < KB4. *)
Lemma frame_symmetric_transitive_right_euclidean :
  forall F,
    frame_symmetric F -> frame_transitive F -> frame_right_euclidean F.
Proof.
  intros F HS HT x y z Hxy Hxz.
  exact (HT y x z (HS x y Hxy) Hxz).
Qed.

Lemma K45_weaker_than_KB4 :
  forall p : formula nat, K45_proves p -> KB4_proves p.
Proof.
  intros p Hp. apply KB4_complete.
  intros F [HS HT].
  eapply K45_proves_sound_on_frame.
  - exact HT.
  - now apply frame_symmetric_transitive_right_euclidean.
  - exact Hp.
Qed.

(** * Finite separating frames *)

(** The two-cycle is serial and symmetric, but not transitive. *)
Definition combo_two_cycle_frame : frame :=
  {| World := db5_world;
     Rel := fun x y => x <> y |}.

Lemma combo_two_cycle_serial : frame_serial combo_two_cycle_frame.
Proof.
  intros [|].
  - exists DB1. discriminate.
  - exists DB0. discriminate.
Qed.

Lemma combo_two_cycle_symmetric : frame_symmetric combo_two_cycle_frame.
Proof.
  intros x y Hxy Heq. apply Hxy. now symmetry.
Qed.

Lemma combo_two_cycle_not_transitive :
  ~ frame_transitive combo_two_cycle_frame.
Proof.
  intro HT.
  assert (H01 : DB0 <> DB1) by discriminate.
  assert (H10 : DB1 <> DB0) by discriminate.
  pose proof (HT DB0 DB1 DB0 H01 H10) as Hbad.
  exact (Hbad eq_refl).
Qed.

(** The two-point preorder 0 <= 1 is serial and transitive, but neither
    symmetric nor right Euclidean. *)
Definition combo_two_preorder_frame : frame :=
  {| World := db5_world;
     Rel := fun x y => x = DB0 \/ y = DB1 |}.

Lemma combo_two_preorder_serial : frame_serial combo_two_preorder_frame.
Proof.
  intros [|].
  - exists DB0. now left.
  - exists DB1. now right.
Qed.

Lemma combo_two_preorder_transitive :
  frame_transitive combo_two_preorder_frame.
Proof.
  intros x y z [Hx | Hy] Hyz.
  - now left.
  - subst y. destruct Hyz as [Hbad | Hz].
    + discriminate.
    + now right.
Qed.

Lemma combo_two_preorder_not_symmetric :
  ~ frame_symmetric combo_two_preorder_frame.
Proof.
  intro HS.
  specialize (HS DB0 DB1 (or_introl eq_refl)).
  destruct HS as [H | H]; discriminate.
Qed.

Lemma combo_two_preorder_not_right_euclidean :
  ~ frame_right_euclidean combo_two_preorder_frame.
Proof.
  intro HE.
  specialize (HE DB0 DB1 DB0 (or_introl eq_refl) (or_introl eq_refl)).
  destruct HE as [H | H]; discriminate.
Qed.

(** The empty singleton relation supplies all vacuous properties except
    seriality. *)
Lemma irreflexive_singleton_symmetric :
  frame_symmetric irreflexive_singleton_frame.
Proof. intros [] [] H; contradiction. Qed.

Lemma irreflexive_singleton_right_euclidean :
  frame_right_euclidean irreflexive_singleton_frame.
Proof. intros [] [] [] H; contradiction. Qed.

(** A root pointing into a two-world complete cluster is serial and right
    Euclidean, but not transitive. *)
Definition combo_euclidean_nontransitive_frame : frame :=
  {| World := three_world;
     Rel := fun x y =>
       (x = W0 /\ y = W1) \/ (x <> W0 /\ y <> W0) |}.

Lemma combo_euclidean_nontransitive_serial :
  frame_serial combo_euclidean_nontransitive_frame.
Proof.
  intros [| |].
  - exists W1. left. now split.
  - exists W1. right. split; discriminate.
  - exists W1. right. split; discriminate.
Qed.

Lemma combo_euclidean_nontransitive_right_euclidean :
  frame_right_euclidean combo_euclidean_nontransitive_frame.
Proof.
  intros x y z Hxy Hxz.
  destruct Hxy as [[Hx Hy] | [Hx Hy]];
    destruct Hxz as [[Hx' Hz] | [Hx' Hz]].
  - subst x; subst y; subst z. right. split; discriminate.
  - exfalso. now apply Hx'.
  - exfalso. now apply Hx.
  - right. exact (conj Hy Hz).
Qed.

Lemma combo_euclidean_nontransitive_not_transitive :
  ~ frame_transitive combo_euclidean_nontransitive_frame.
Proof.
  intro HT.
  assert (H10 : W1 <> W0) by discriminate.
  assert (H20 : W2 <> W0) by discriminate.
  specialize (HT W0 W1 W2
    (or_introl (conj eq_refl eq_refl))
    (or_intror (conj H10 H20))).
  destruct HT as [[_ H21] | [H00 _]].
  - discriminate.
  - exact (H00 eq_refl).
Qed.

(** Every world points to the distinguished sink.  This is transitive and
    right Euclidean, but not symmetric. *)
Definition combo_sink_frame : frame :=
  {| World := db5_world;
     Rel := fun _ y => y = DB1 |}.

Lemma combo_sink_transitive : frame_transitive combo_sink_frame.
Proof. intros x y z _ Hz. exact Hz. Qed.

Lemma combo_sink_right_euclidean :
  frame_right_euclidean combo_sink_frame.
Proof. intros x y z _ Hz. exact Hz. Qed.

Lemma combo_sink_not_symmetric : ~ frame_symmetric combo_sink_frame.
Proof.
  intro HS. specialize (HS DB0 DB1 eq_refl). discriminate.
Qed.

(** The strict three-point order is transitive and piecewise connected, but
    fails right Euclideanity. *)
Definition combo_strict_three_frame : frame :=
  {| World := three_world;
     Rel := fun x y =>
       (x = W0 /\ y <> W0) \/ (x = W1 /\ y = W2) |}.

Lemma combo_strict_three_transitive :
  frame_transitive combo_strict_three_frame.
Proof.
  intros x y z Hxy Hyz.
  destruct x, y, z; simpl in *; intuition discriminate.
Qed.

Lemma combo_strict_three_piecewise_connected :
  frame_piecewise_connected combo_strict_three_frame.
Proof.
  intros x y z Hxy Hxz.
  destruct x, y, z; simpl in *; intuition discriminate.
Qed.

Lemma combo_strict_three_not_right_euclidean :
  ~ frame_right_euclidean combo_strict_three_frame.
Proof.
  intro HE.
  assert (H02 : Rel combo_strict_three_frame W0 W2).
  { left; split; [reflexivity | discriminate]. }
  assert (H01 : Rel combo_strict_three_frame W0 W1).
  { left; split; [reflexivity | discriminate]. }
  pose proof (HE W0 W2 W1 H02 H01) as Hbad.
  destruct Hbad as [[H20 _] | [H21 _]]; discriminate.
Qed.

(** * Strict inclusions from the pinned combination modules *)

Theorem K4Point3_strictly_weaker_K45 :
  normal_strictly_weaker K4Point3_proves K45_proves.
Proof.
  split.
  - exact K4Point3_weaker_than_K45.
  - exists (Five (Atom 0)); split.
    + apply Np_extra. right. exists (Atom 0). reflexivity.
    + intro HK4Point3.
      pose proof
        (K4Point3_proves_sound_on_frame
          combo_strict_three_transitive
          combo_strict_three_piecewise_connected HK4Point3) as Hvalid.
      apply combo_strict_three_not_right_euclidean.
      now apply (proj1
        (valid_Five_iff_right_euclidean combo_strict_three_frame)).
Qed.

Theorem K5_strictly_weaker_K45 :
  normal_strictly_weaker K5_proves K45_proves.
Proof.
  split.
  - apply K5_weaker_than_K45.
  - exists (Four (Atom 0)); split.
    + apply Np_extra. left. exists (Atom 0). reflexivity.
    + intro HK5.
      pose proof (K5_proves_sound_on_right_euclidean_frame
        combo_euclidean_nontransitive_right_euclidean HK5) as Hvalid.
      apply combo_euclidean_nontransitive_not_transitive.
      now apply (proj1 (valid_Four_iff_transitive
        combo_euclidean_nontransitive_frame)).
Qed.

Theorem KD_strictly_weaker_KD4 :
  normal_strictly_weaker KD_proves KD4_proves.
Proof.
  split.
  - apply KD_weaker_than_KD4.
  - exists (Four (Atom 0)); split.
    + apply Np_extra. right. exists (Atom 0). reflexivity.
    + intro HKD.
      pose proof (KD_proves_sound_on_serial_frame
        combo_two_cycle_serial HKD) as Hvalid.
      apply combo_two_cycle_not_transitive.
      now apply (proj1 (valid_Four_iff_transitive combo_two_cycle_frame)).
Qed.

Theorem K4_strictly_weaker_KD4 :
  normal_strictly_weaker K4_proves KD4_proves.
Proof.
  split.
  - apply K4_weaker_than_KD4.
  - exists (D (Atom 0)); split.
    + apply Np_extra. left. exists (Atom 0). reflexivity.
    + intro HK4.
      pose proof (K4_proves_sound_on_transitive_frame
        irreflexive_singleton_transitive HK4) as Hvalid.
      apply irreflexive_singleton_not_serial.
      now apply (proj1 (valid_D_iff_serial irreflexive_singleton_frame)).
Qed.

Theorem KD_strictly_weaker_KD5 :
  normal_strictly_weaker KD_proves KD5_proves.
Proof.
  split.
  - apply KD_weaker_than_KD5.
  - exists (Five (Atom 0)); split.
    + apply Np_extra. right. exists (Atom 0). reflexivity.
    + intro HKD.
      pose proof (KD_proves_sound_on_serial_frame
        combo_two_preorder_serial HKD) as Hvalid.
      apply combo_two_preorder_not_right_euclidean.
      now apply (proj1 (valid_Five_iff_right_euclidean
        combo_two_preorder_frame)).
Qed.

Theorem K5_strictly_weaker_KD5 :
  normal_strictly_weaker K5_proves KD5_proves.
Proof.
  split.
  - apply K5_weaker_than_KD5.
  - exists (D (Atom 0)); split.
    + apply Np_extra. left. exists (Atom 0). reflexivity.
    + intro HK5.
      pose proof (K5_proves_sound_on_right_euclidean_frame
        irreflexive_singleton_right_euclidean HK5) as Hvalid.
      apply irreflexive_singleton_not_serial.
      now apply (proj1 (valid_D_iff_serial irreflexive_singleton_frame)).
Qed.

Theorem KD_strictly_weaker_KDB :
  normal_strictly_weaker KD_proves KDB_proves.
Proof.
  split.
  - apply KD_weaker_than_KDB.
  - exists (B (Atom 0)); split.
    + apply Np_extra. right. exists (Atom 0). reflexivity.
    + intro HKD.
      pose proof (KD_proves_sound_on_serial_frame
        combo_two_preorder_serial HKD) as Hvalid.
      apply combo_two_preorder_not_symmetric.
      now apply (proj1 (valid_B_iff_symmetric combo_two_preorder_frame)).
Qed.

Theorem KB_strictly_weaker_KDB :
  normal_strictly_weaker KB_proves KDB_proves.
Proof.
  split.
  - apply KB_weaker_than_KDB.
  - exists (D (Atom 0)); split.
    + apply Np_extra. left. exists (Atom 0). reflexivity.
    + intro HKB.
      pose proof (KB_proves_sound_on_symmetric_frame
        irreflexive_singleton_symmetric HKB) as Hvalid.
      apply irreflexive_singleton_not_serial.
      now apply (proj1 (valid_D_iff_serial irreflexive_singleton_frame)).
Qed.

Theorem K45_strictly_weaker_KB4 :
  normal_strictly_weaker K45_proves KB4_proves.
Proof.
  split.
  - apply K45_weaker_than_KB4.
  - exists (B (Atom 0)); split.
    + apply Np_extra. left. exists (Atom 0). reflexivity.
    + intro HK45.
      pose proof (K45_proves_sound_on_frame combo_sink_transitive
        combo_sink_right_euclidean HK45) as Hvalid.
      apply combo_sink_not_symmetric.
      now apply (proj1 (valid_B_iff_symmetric combo_sink_frame)).
Qed.

Theorem KB_strictly_weaker_KB4 :
  normal_strictly_weaker KB_proves KB4_proves.
Proof.
  split.
  - apply KB_weaker_than_KB4.
  - exists (Four (Atom 0)); split.
    + apply Np_extra. right. exists (Atom 0). reflexivity.
    + intro HKB.
      pose proof (KB_proves_sound_on_symmetric_frame
        combo_two_cycle_symmetric HKB) as Hvalid.
      apply combo_two_cycle_not_transitive.
      now apply (proj1 (valid_Four_iff_transitive combo_two_cycle_frame)).
Qed.

Theorem KD4_strictly_weaker_KD45 :
  normal_strictly_weaker KD4_proves KD45_proves.
Proof.
  split.
  - apply KD4_weaker_than_KD45.
  - exists (Five (Atom 0)); split.
    + apply Np_extra. right. exists (Atom 0). reflexivity.
    + intro HKD4.
      pose proof (KD4_proves_sound_on_frame combo_two_preorder_serial
        combo_two_preorder_transitive HKD4) as Hvalid.
      apply combo_two_preorder_not_right_euclidean.
      now apply (proj1 (valid_Five_iff_right_euclidean
        combo_two_preorder_frame)).
Qed.

Theorem KD5_strictly_weaker_KD45 :
  normal_strictly_weaker KD5_proves KD45_proves.
Proof.
  split.
  - apply KD5_weaker_than_KD45.
  - exists (Four (Atom 0)); split.
    + apply Np_extra. left. right. exists (Atom 0). reflexivity.
    + intro HKD5.
      pose proof (KD5_proves_sound_on_frame
        combo_euclidean_nontransitive_serial
        combo_euclidean_nontransitive_right_euclidean HKD5) as Hvalid.
      apply combo_euclidean_nontransitive_not_transitive.
      now apply (proj1 (valid_Four_iff_transitive
        combo_euclidean_nontransitive_frame)).
Qed.

Theorem K45_strictly_weaker_KD45 :
  normal_strictly_weaker K45_proves KD45_proves.
Proof.
  split.
  - apply K45_weaker_than_KD45.
  - exists (D (Atom 0)); split.
    + apply Np_extra. left. left. exists (Atom 0). reflexivity.
    + intro HK45.
      pose proof (K45_proves_sound_on_frame
        irreflexive_singleton_transitive
        irreflexive_singleton_right_euclidean HK45) as Hvalid.
      apply irreflexive_singleton_not_serial.
      now apply (proj1 (valid_D_iff_serial irreflexive_singleton_frame)).
Qed.
