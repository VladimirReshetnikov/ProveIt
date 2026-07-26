(**
  Canonical completeness for KTB and KT4B.

  This file ports the theorem surfaces of the pinned Foundation modules

    - Modal/Kripke/Logic/KTB.lean, and
    - Modal/Kripke/Logic/KT4B.lean.

  The base normal calculus already contains propositional classical logic,
  necessitation, and axiom K.  Consequently the two systems below are
  represented by the additional schema unions T + B and T + Four + B.
  As in the other canonical modules, soundness and consistency are
  atom-polymorphic, while the Lindenbaum completeness construction is stated
  for the repository's enumerable atom type [nat].

  Foundation's finite completeness instances are retained.  KTB uses the
  finest filtration, which preserves reflexivity and symmetry.  KT4B uses
  the nonempty transitive closure of that filtration, which preserves an
  equivalence relation.
*)

From Stdlib Require Import Lists.List.
From FoundationModal Require Import
  Syntax Axioms HilbertK Kripke Correspondence HilbertKSoundness
  NormalHilbert CanonicalExtensions CanonicalDB5 Modality
  Filtration FiltrationExtensions CanonicalCombinations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Combined schemata and their inclusions *)

Definition KTB_schema : modal_axiom_schema :=
  schema_union schema_T schema_B.

Definition KT4B_schema : modal_axiom_schema :=
  schema_union (schema_union schema_T schema_Four) schema_B.

Definition KTB_proves {AtomType} : formula AtomType -> Prop :=
  @normal_proves KTB_schema AtomType.

Definition KT4B_proves {AtomType} : formula AtomType -> Prop :=
  @normal_proves KT4B_schema AtomType.

Lemma KTB_schema_substitution_closed :
  schema_substitution_closed KTB_schema.
Proof.
  apply schema_union_substitution_closed.
  - exact schema_T_substitution_closed.
  - exact schema_B_substitution_closed.
Qed.

Lemma KT4B_schema_substitution_closed :
  schema_substitution_closed KT4B_schema.
Proof.
  apply schema_union_substitution_closed.
  - apply schema_union_substitution_closed.
    + exact schema_T_substitution_closed.
    + exact schema_Four_substitution_closed.
  - exact schema_B_substitution_closed.
Qed.

Lemma schema_T_included_KTB : schema_included schema_T KTB_schema.
Proof. intros AtomType p Hp; now left. Qed.

Lemma schema_B_included_KTB : schema_included schema_B KTB_schema.
Proof. intros AtomType p Hp; now right. Qed.

Lemma schema_T_included_KT4B : schema_included schema_T KT4B_schema.
Proof. intros AtomType p Hp; now left; left. Qed.

Lemma schema_Four_included_KT4B :
  schema_included schema_Four KT4B_schema.
Proof. intros AtomType p Hp; now left; right. Qed.

Lemma schema_B_included_KT4B : schema_included schema_B KT4B_schema.
Proof. intros AtomType p Hp; now right. Qed.

Lemma S4_schema_included_KT4B : schema_included S4_schema KT4B_schema.
Proof.
  intros AtomType p [Hp | Hp].
  - now left; left.
  - now left; right.
Qed.

Lemma KTB_schema_included_KT4B : schema_included KTB_schema KT4B_schema.
Proof.
  intros AtomType p [Hp | Hp].
  - now left; left.
  - now right.
Qed.

Lemma KT_weaker_than_KTB :
  forall (AtomType : Type) (p : formula AtomType),
    KT_proves p -> KTB_proves p.
Proof.
  intros AtomType p.
  apply normal_proves_weaken. exact schema_T_included_KTB.
Qed.

Lemma KB_weaker_than_KTB :
  forall (AtomType : Type) (p : formula AtomType),
    KB_proves p -> KTB_proves p.
Proof.
  intros AtomType p.
  apply normal_proves_weaken. exact schema_B_included_KTB.
Qed.

Lemma S4_weaker_than_KT4B :
  forall (AtomType : Type) (p : formula AtomType),
    S4_proves p -> KT4B_proves p.
Proof.
  intros AtomType p.
  apply normal_proves_weaken. exact S4_schema_included_KT4B.
Qed.

Lemma KTB_weaker_than_KT4B :
  forall (AtomType : Type) (p : formula AtomType),
    KTB_proves p -> KT4B_proves p.
Proof.
  intros AtomType p.
  apply normal_proves_weaken. exact KTB_schema_included_KT4B.
Qed.

(** * Frame classes and elementary relational bridges *)

Definition KTB_kripke_frame_class (F : frame) : Prop :=
  frame_reflexive F /\ frame_symmetric F.

Definition KT4B_kripke_frame_class (F : frame) : Prop :=
  frame_equivalence F.

Definition finite_KTB_kripke_frame_class (F : frame) : Prop :=
  finite_frame F /\ KTB_kripke_frame_class F.

Definition finite_KT4B_kripke_frame_class (F : frame) : Prop :=
  finite_frame F /\ KT4B_kripke_frame_class F.

Lemma frame_reflexive_serial :
  forall F, frame_reflexive F -> frame_serial F.
Proof. intros F Hrefl x; exists x; apply Hrefl. Qed.

(** Foundation exposes this as the frame-class inclusion KTB -> KDB. *)
Lemma KTB_frame_is_serial_symmetric :
  forall F,
    KTB_kripke_frame_class F ->
    frame_serial F /\ frame_symmetric F.
Proof.
  intros F [Hrefl Hsym]; split.
  - now apply frame_reflexive_serial.
  - exact Hsym.
Qed.

Lemma frame_symmetric_transitive_right_euclidean_TB :
  forall F,
    frame_symmetric F -> frame_transitive F ->
    frame_right_euclidean F.
Proof.
  intros F Hsym Htrans x y z Hxy Hxz.
  exact (Htrans y x z (Hsym x y Hxy) Hxz).
Qed.

Lemma frame_reflexive_right_euclidean_symmetric :
  forall F,
    frame_reflexive F -> frame_right_euclidean F ->
    frame_symmetric F.
Proof.
  intros F Hrefl Heucl x y Hxy.
  exact (Heucl x y x Hxy (Hrefl x)).
Qed.

Lemma frame_reflexive_right_euclidean_transitive :
  forall F,
    frame_reflexive F -> frame_right_euclidean F ->
    frame_transitive F.
Proof.
  intros F Hrefl Heucl x y z Hxy Hyz.
  apply (Heucl y x z).
  - now apply frame_reflexive_right_euclidean_symmetric.
  - exact Hyz.
Qed.

Theorem KT4B_frame_class_iff_S5_frame_class :
  forall F,
    KT4B_kripke_frame_class F <-> frame_s5 F.
Proof.
  intros F; split.
  - intros [Hrefl [Htrans Hsym]]; split; [exact Hrefl |].
    now apply frame_symmetric_transitive_right_euclidean_TB.
  - intros [Hrefl Heucl]; repeat split.
    + exact Hrefl.
    + now apply frame_reflexive_right_euclidean_transitive.
    + now apply frame_reflexive_right_euclidean_symmetric.
Qed.

(** * Soundness and consistency *)

Theorem KTB_proves_sound_on_frame :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    frame_reflexive F -> frame_symmetric F ->
    KTB_proves p -> valid F p.
Proof.
  intros AtomType F p Hrefl Hsym Hp.
  eapply normal_proves_sound_on_frame; [|exact Hp].
  apply schema_union_valid_on_frame.
  - now apply schema_T_valid_on_reflexive.
  - now apply schema_B_valid_on_symmetric.
Qed.

Theorem KT4B_proves_sound_on_frame :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    frame_reflexive F -> frame_transitive F -> frame_symmetric F ->
    KT4B_proves p -> valid F p.
Proof.
  intros AtomType F p Hrefl Htrans Hsym Hp.
  eapply normal_proves_sound_on_frame; [|exact Hp].
  apply schema_union_valid_on_frame.
  - apply schema_union_valid_on_frame.
    + now apply schema_T_valid_on_reflexive.
    + now apply schema_Four_valid_on_transitive.
  - now apply schema_B_valid_on_symmetric.
Qed.

Theorem KTB_is_consistent :
  forall AtomType, ~ @KTB_proves AtomType Bottom.
Proof.
  apply (normal_consistent_of_sound_inhabited_frame
    (Ax := KTB_schema) (F := reflexive_singleton_frame)).
  - now exists tt.
  - apply schema_union_valid_on_frame.
    + apply schema_T_valid_on_reflexive.
      exact reflexive_singleton_reflexive.
    + apply schema_B_valid_on_symmetric.
      exact reflexive_singleton_symmetric.
Qed.

Theorem KT4B_is_consistent :
  forall AtomType, ~ @KT4B_proves AtomType Bottom.
Proof.
  apply (normal_consistent_of_sound_inhabited_frame
    (Ax := KT4B_schema) (F := reflexive_singleton_frame)).
  - now exists tt.
  - apply schema_union_valid_on_frame.
    + apply schema_union_valid_on_frame.
      * apply schema_T_valid_on_reflexive.
        exact reflexive_singleton_reflexive.
      * apply schema_Four_valid_on_transitive.
        exact reflexive_singleton_transitive.
    + apply schema_B_valid_on_symmetric.
      exact reflexive_singleton_symmetric.
Qed.

(** * Canonical frames *)

Lemma normal_canonical_reflexive_of_schema_T_TB :
  forall Ax,
    schema_included schema_T Ax ->
    frame_reflexive (normal_canonical_frame Ax).
Proof.
  intros Ax HT M p Hbox.
  apply normal_mct_derivable_mem. eapply ND_mp.
  - apply ND_theorem. apply Np_extra. apply HT.
    exists p. reflexivity.
  - apply ND_assumption. exact Hbox.
Qed.

Lemma normal_canonical_transitive_of_schema_Four_TB :
  forall Ax,
    schema_included schema_Four Ax ->
    frame_transitive (normal_canonical_frame Ax).
Proof.
  intros Ax HFour M N O HMN HNO p Hbox.
  apply HNO, HMN, normal_mct_derivable_mem. eapply ND_mp.
  - apply ND_theorem. apply Np_extra. apply HFour.
    exists p. reflexivity.
  - apply ND_assumption. exact Hbox.
Qed.

Lemma KTB_canonical_frame_reflexive :
  frame_reflexive (normal_canonical_frame KTB_schema).
Proof.
  apply normal_canonical_reflexive_of_schema_T_TB.
  exact schema_T_included_KTB.
Qed.

Lemma KTB_canonical_frame_symmetric :
  frame_symmetric (normal_canonical_frame KTB_schema).
Proof.
  apply normal_canonical_symmetric_of_schema_B.
  exact schema_B_included_KTB.
Qed.

Theorem KTB_canonical :
  KTB_kripke_frame_class (normal_canonical_frame KTB_schema).
Proof.
  split.
  - exact KTB_canonical_frame_reflexive.
  - exact KTB_canonical_frame_symmetric.
Qed.

Lemma KT4B_canonical_frame_reflexive :
  frame_reflexive (normal_canonical_frame KT4B_schema).
Proof.
  apply normal_canonical_reflexive_of_schema_T_TB.
  exact schema_T_included_KT4B.
Qed.

Lemma KT4B_canonical_frame_transitive :
  frame_transitive (normal_canonical_frame KT4B_schema).
Proof.
  apply normal_canonical_transitive_of_schema_Four_TB.
  exact schema_Four_included_KT4B.
Qed.

Lemma KT4B_canonical_frame_symmetric :
  frame_symmetric (normal_canonical_frame KT4B_schema).
Proof.
  apply normal_canonical_symmetric_of_schema_B.
  exact schema_B_included_KT4B.
Qed.

Theorem KT4B_canonical :
  KT4B_kripke_frame_class (normal_canonical_frame KT4B_schema).
Proof.
  repeat split.
  - exact KT4B_canonical_frame_reflexive.
  - exact KT4B_canonical_frame_transitive.
  - exact KT4B_canonical_frame_symmetric.
Qed.

(** * Completeness and finite completeness *)

Theorem KTB_complete :
  forall p : formula nat,
    normal_valid_on_class KTB_kripke_frame_class p -> KTB_proves p.
Proof.
  apply (normal_complete_of_canonical_frame
    (Ax := KTB_schema) (C := KTB_kripke_frame_class)).
  - exact (@KTB_is_consistent nat).
  - exact KTB_canonical.
Qed.

Theorem KT4B_complete :
  forall p : formula nat,
    normal_valid_on_class KT4B_kripke_frame_class p -> KT4B_proves p.
Proof.
  apply (normal_complete_of_canonical_frame
    (Ax := KT4B_schema) (C := KT4B_kripke_frame_class)).
  - exact (@KT4B_is_consistent nat).
  - exact KT4B_canonical.
Qed.

Theorem KTB_sound_complete :
  forall p : formula nat,
    KTB_proves p <-> normal_valid_on_class KTB_kripke_frame_class p.
Proof.
  intro p; split.
  - intros Hp F [Hrefl Hsym].
    now apply KTB_proves_sound_on_frame.
  - apply KTB_complete.
Qed.

Theorem KT4B_sound_complete :
  forall p : formula nat,
    KT4B_proves p <-> normal_valid_on_class KT4B_kripke_frame_class p.
Proof.
  intro p; split.
  - intros Hp F [Hrefl [Htrans Hsym]].
    now apply KT4B_proves_sound_on_frame.
  - apply KT4B_complete.
Qed.

Theorem KTB_finite_complete :
  forall p : formula nat,
    normal_valid_on_class finite_KTB_kripke_frame_class p ->
    KTB_proves p.
Proof.
  intros p Hfinite. apply KTB_complete.
  intros F [Hrefl Hsym] V w.
  apply (proj1 (@finest_filtration_truth_at_class
    nat F V p p (subformulas_self p) w)).
  apply (Hfinite (@finest_filtered_frame nat F V p)).
  - split.
    + exact (@finest_filtered_frame_finite nat F V p).
    + split.
      * now apply finest_preserves_reflexive.
      * now apply finest_preserves_symmetric.
Qed.

Theorem KT4B_finite_complete :
  forall p : formula nat,
    normal_valid_on_class finite_KT4B_kripke_frame_class p ->
    KT4B_proves p.
Proof.
  intros p Hfinite. apply KT4B_complete.
  intros F Hequiv V w.
  destruct Hequiv as [Hrefl [Htrans Hsym]].
  apply (proj1 (@finest_tc_filtration_truth_at_class
    nat F V p Htrans p (subformulas_self p) w)).
  apply (Hfinite (@finest_tc_filtered_frame nat F V p)).
  - split.
    + exact (@finest_tc_filtered_frame_finite nat F V p).
    + apply finest_tc_preserves_equivalence.
      repeat split; assumption.
Qed.

Theorem KTB_finite_sound_complete :
  forall p : formula nat,
    KTB_proves p <->
    normal_valid_on_class finite_KTB_kripke_frame_class p.
Proof.
  intro p; split.
  - intros Hp F [_ [Hrefl Hsym]].
    now apply KTB_proves_sound_on_frame.
  - apply KTB_finite_complete.
Qed.

Theorem KT4B_finite_sound_complete :
  forall p : formula nat,
    KT4B_proves p <->
    normal_valid_on_class finite_KT4B_kripke_frame_class p.
Proof.
  intro p; split.
  - intros Hp F [_ [Hrefl [Htrans Hsym]]].
    now apply KT4B_proves_sound_on_frame.
  - apply KT4B_finite_complete.
Qed.

(** S5 uses reflexivity plus right Euclideanness in [Modality].  The frame
    bridge above shows that this is extensionally the KT4B frame class. *)
Theorem S5_KT4B_equivalent :
  forall p : formula nat, S5_proves p <-> KT4B_proves p.
Proof.
  intro p; split.
  - intro Hp. apply KT4B_complete.
    intros F HKT4B.
    apply S5_proves_sound_on_reflexive_euclidean_frame.
    + exact (proj1 HKT4B).
    + apply (proj1 (KT4B_frame_class_iff_S5_frame_class F)).
      exact HKT4B.
    + exact Hp.
  - intro Hp. apply S5_complete.
    intros F HS5.
    pose proof
      ((proj2 (KT4B_frame_class_iff_S5_frame_class F)) HS5)
      as [_ [Htrans Hsym]].
    apply KT4B_proves_sound_on_frame.
    + exact (proj1 HS5).
    + exact Htrans.
    + exact Hsym.
    + exact Hp.
Qed.

Corollary S5_weaker_than_KT4B :
  forall p : formula nat, S5_proves p -> KT4B_proves p.
Proof. intros p; apply (proj1 (S5_KT4B_equivalent p)). Qed.

Corollary KT4B_weaker_than_S5 :
  forall p : formula nat, KT4B_proves p -> S5_proves p.
Proof. intros p; apply (proj2 (S5_KT4B_equivalent p)). Qed.

(** * Strict inclusions witnessed by two-world frames *)

Inductive tb_world : Type := TB0 | TB1.

Definition tb_reflexive_chain_frame : frame :=
  {| World := tb_world;
     Rel := fun x y => x = y \/ (x = TB0 /\ y = TB1) |}.

Lemma tb_reflexive_chain_reflexive :
  frame_reflexive tb_reflexive_chain_frame.
Proof. intro x; now left. Qed.

Lemma tb_reflexive_chain_not_symmetric :
  ~ frame_symmetric tb_reflexive_chain_frame.
Proof.
  intro Hsym.
  specialize (Hsym TB0 TB1 (or_intror (conj eq_refl eq_refl))).
  destruct Hsym as [H | [H _]]; discriminate.
Qed.

Definition tb_swap_frame : frame :=
  {| World := tb_world;
     Rel := fun x y => x <> y |}.

Lemma tb_swap_serial : frame_serial tb_swap_frame.
Proof.
  intros [|].
  - exists TB1. discriminate.
  - exists TB0. discriminate.
Qed.

Lemma tb_swap_symmetric : frame_symmetric tb_swap_frame.
Proof. intros x y Hxy Heq; subst y; now apply Hxy. Qed.

Lemma tb_swap_not_reflexive : ~ frame_reflexive tb_swap_frame.
Proof. intro Hrefl; exact (Hrefl TB0 eq_refl). Qed.

Lemma KDB_weaker_than_KTB :
  forall p : formula nat,
    KDB_proves p -> KTB_proves p.
Proof.
  intros p Hp. apply KTB_complete.
  intros F [Hrefl Hsym].
  apply KDB_proves_sound_on_frame.
  - now apply frame_reflexive_serial.
  - exact Hsym.
  - exact Hp.
Qed.

Theorem KT_strictly_weaker_KTB :
  normal_strictly_weaker (@KT_proves nat) (@KTB_proves nat).
Proof.
  split.
  - apply KT_weaker_than_KTB.
  - exists (B (Atom 0)); split.
    + apply Np_extra. right. exists (Atom 0). reflexivity.
    + intro HKT.
      pose proof (KT_proves_sound_on_reflexive_frame
        tb_reflexive_chain_reflexive HKT) as Hvalid.
      apply tb_reflexive_chain_not_symmetric.
      now apply (proj1 (valid_B_iff_symmetric tb_reflexive_chain_frame)).
Qed.

Theorem KDB_strictly_weaker_KTB :
  normal_strictly_weaker
    (@KDB_proves nat)
    (@KTB_proves nat).
Proof.
  split.
  - apply KDB_weaker_than_KTB.
  - exists (T (Atom 0)); split.
    + apply Np_extra. left. exists (Atom 0). reflexivity.
    + intro HKDB.
      pose proof (KDB_proves_sound_on_frame
        tb_swap_serial tb_swap_symmetric HKDB) as Hvalid.
      apply tb_swap_not_reflexive.
      now apply (proj1 (valid_T_iff_reflexive tb_swap_frame)).
Qed.
