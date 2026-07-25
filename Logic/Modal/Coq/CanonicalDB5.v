(**
  Canonical completeness for KD, KB, and K5.

  This module ports the mathematical theorem surfaces of
  Foundation/Modal/Kripke/Logic/{KD,KB,K5}.lean.  It complements
  [CanonicalExtensions], whose first tranche treats KT, K4, and S4.

  The canonical-property arguments are stated in a stronger reusable form:
  any normal schema containing D, B, or Five has, respectively, a serial,
  symmetric, or right-Euclidean canonical frame.  The named completeness and
  soundness/completeness theorems then follow from the generic canonical
  countermodel theorem.  As in the rest of the canonical port, completeness
  is over formulas with natural-number atoms; the already existing soundness
  and consistency theorems remain atom-polymorphic.
*)

From FoundationModal Require Import
  Syntax Axioms HilbertK Kripke Correspondence HilbertKSoundness NormalHilbert
  CanonicalExtensions Modality.

Set Implicit Arguments.
Unset Strict Implicit.

(** * Generic canonical-frame lemmas *)

Lemma normal_proves_box_dni :
  forall Ax (p : formula nat),
    normal_proves Ax (Imp (Box p) (Box (Neg (Neg p)))).
Proof.
  intros Ax p. eapply Np_mp.
  - apply Np_modal_K.
  - apply Np_nec. apply normal_proves_dni.
Qed.

Theorem normal_canonical_serial_of_schema_D :
  forall Ax,
    schema_included schema_D Ax ->
    frame_serial (normal_canonical_frame Ax).
Proof.
  intros Ax HD M.
  assert (Hbox_top : normal_mct_mem M (Box (@Top nat))).
  {
    apply normal_mct_derivable_mem. apply ND_theorem. apply Np_nec.
    unfold Top, Neg. apply normal_proves_identity.
  }
  assert (Hdia_top : normal_mct_mem M (Dia (@Top nat))).
  {
    apply normal_mct_derivable_mem. eapply ND_mp.
    - apply ND_theorem. apply Np_extra. apply HD.
      exists (@Top nat). reflexivity.
    - apply ND_assumption. exact Hbox_top.
  }
  change (normal_mct_mem M (Neg (Box (Neg (@Top nat))))) in Hdia_top.
  destruct (@normal_canonical_successor_of_neg_box Ax M
    (Neg (@Top nat)) Hdia_top) as [N [HMN _]].
  now exists N.
Qed.

Theorem normal_canonical_symmetric_of_schema_B :
  forall Ax,
    schema_included schema_B Ax ->
    frame_symmetric (normal_canonical_frame Ax).
Proof.
  intros Ax HB M N HMN p HboxN.
  destruct (@normal_mct_complete Ax M p) as [HpM | HnegpM].
  - exact HpM.
  - assert (HboxdiaM : normal_mct_mem M (Box (Dia (Neg p)))).
    {
      apply normal_mct_derivable_mem. eapply ND_mp.
      - apply ND_theorem. apply Np_extra. apply HB.
        exists (Neg p). reflexivity.
      - apply ND_assumption. exact HnegpM.
    }
    pose proof (HMN (Dia (Neg p)) HboxdiaM) as HdiaN.
    assert (HboxnnpN : normal_mct_mem N (Box (Neg (Neg p)))).
    {
      apply normal_mct_derivable_mem. eapply ND_mp.
      - apply ND_theorem. apply normal_proves_box_dni.
      - apply ND_assumption. exact HboxN.
    }
    change (normal_mct_mem N (Neg (Box (Neg (Neg p))))) in HdiaN.
    exfalso. apply (@normal_mct_consistent Ax N).
    eapply ND_mp.
    + apply ND_assumption. exact HdiaN.
    + apply ND_assumption. exact HboxnnpN.
Qed.

(** The Five bridge is already checked in [Modality] for K.  Schema
    inclusion transports its sole Five instance into any chosen extension. *)
Lemma normal_proves_neg_box_five_of_schema :
  forall Ax,
    schema_included schema_Five Ax ->
    forall p : formula nat,
      normal_proves Ax (Imp (Neg (Box p)) (Box (Neg (Box p)))).
Proof.
  intros Ax HFive p. eapply Np_mp.
  - apply K_proves_normal. apply K_proves_Five_neg_box_bridge.
  - apply Np_extra. apply HFive. exists (Neg p). reflexivity.
Qed.

Theorem normal_canonical_right_euclidean_of_schema_Five :
  forall Ax,
    schema_included schema_Five Ax ->
    frame_right_euclidean (normal_canonical_frame Ax).
Proof.
  intros Ax HFive M N O HMN HMO p HboxN.
  destruct (@normal_mct_complete Ax M (Box p))
    as [HboxM | HnegboxM].
  - exact (HMO p HboxM).
  - assert (HboxnegboxM : normal_mct_mem M (Box (Neg (Box p)))).
    {
      apply normal_mct_derivable_mem. eapply ND_mp.
      - apply ND_theorem.
        now apply normal_proves_neg_box_five_of_schema.
      - apply ND_assumption. exact HnegboxM.
    }
    pose proof (HMN (Neg (Box p)) HboxnegboxM) as HnegboxN.
    exfalso. exact (@normal_mct_not_both Ax N (Box p)
      HboxN HnegboxN).
Qed.

(** * Named canonicality, completeness, and soundness/completeness *)

Definition KD_frame_class : frame -> Prop := frame_serial.
Definition KB_frame_class : frame -> Prop := frame_symmetric.
Definition K5_frame_class : frame -> Prop := frame_right_euclidean.

Lemma KD_canonical_frame_serial :
  frame_serial (normal_canonical_frame schema_D).
Proof.
  apply normal_canonical_serial_of_schema_D.
  intros AtomType p Hp. exact Hp.
Qed.

Lemma KB_canonical_frame_symmetric :
  frame_symmetric (normal_canonical_frame schema_B).
Proof.
  apply normal_canonical_symmetric_of_schema_B.
  intros AtomType p Hp. exact Hp.
Qed.

Lemma K5_canonical_frame_right_euclidean :
  frame_right_euclidean (normal_canonical_frame schema_Five).
Proof.
  apply normal_canonical_right_euclidean_of_schema_Five.
  intros AtomType p Hp. exact Hp.
Qed.

Theorem KD_complete :
  forall p : formula nat,
    normal_valid_on_class KD_frame_class p -> KD_proves p.
Proof.
  apply (normal_complete_of_canonical_frame
    (Ax := schema_D) (C := KD_frame_class)).
  - exact (@KD_is_consistent nat).
  - exact KD_canonical_frame_serial.
Qed.

Theorem KB_complete :
  forall p : formula nat,
    normal_valid_on_class KB_frame_class p -> KB_proves p.
Proof.
  apply (normal_complete_of_canonical_frame
    (Ax := schema_B) (C := KB_frame_class)).
  - exact (@KB_is_consistent nat).
  - exact KB_canonical_frame_symmetric.
Qed.

Theorem K5_complete :
  forall p : formula nat,
    normal_valid_on_class K5_frame_class p -> K5_proves p.
Proof.
  apply (normal_complete_of_canonical_frame
    (Ax := schema_Five) (C := K5_frame_class)).
  - exact (@K5_is_consistent nat).
  - exact K5_canonical_frame_right_euclidean.
Qed.

Theorem KD_sound_complete :
  forall p : formula nat,
    KD_proves p <-> normal_valid_on_class KD_frame_class p.
Proof.
  intro p; split.
  - intros Hp F HF. now apply KD_proves_sound_on_serial_frame.
  - apply KD_complete.
Qed.

Theorem KB_sound_complete :
  forall p : formula nat,
    KB_proves p <-> normal_valid_on_class KB_frame_class p.
Proof.
  intro p; split.
  - intros Hp F HF. now apply KB_proves_sound_on_symmetric_frame.
  - apply KB_complete.
Qed.

Theorem K5_sound_complete :
  forall p : formula nat,
    K5_proves p <-> normal_valid_on_class K5_frame_class p.
Proof.
  intro p; split.
  - intros Hp F HF. now apply K5_proves_sound_on_right_euclidean_frame.
  - apply K5_complete.
Qed.

(** KD inherits the formula-free seriality principle P, which is the only
    substantive derived surface of the tiny pinned Entailment/KD module. *)
Theorem KD_proves_P : KD_proves (@P nat).
Proof.
  apply KD_complete. intros F Hserial V w Hbox_bottom.
  destruct (Hserial w) as [u Hwu]. exact (Hbox_bottom u Hwu).
Qed.

Corollary normal_proves_P_of_schema_D :
  forall Ax,
    schema_included schema_D Ax -> normal_proves Ax (@P nat).
Proof.
  intros Ax HD.
  eapply normal_proves_weaken; [exact HD | exact KD_proves_P].
Qed.

(** * Strict extensions of K *)

Lemma K_weaker_than_KD :
  forall (p : formula nat), K_normal_proves p -> KD_proves p.
Proof. apply K_weaker_than_normal. Qed.

Lemma K_weaker_than_KB :
  forall (p : formula nat), K_normal_proves p -> KB_proves p.
Proof. apply K_weaker_than_normal. Qed.

Lemma K_weaker_than_K5 :
  forall (p : formula nat), K_normal_proves p -> K5_proves p.
Proof. apply K_weaker_than_normal. Qed.

Lemma irreflexive_singleton_not_serial :
  ~ frame_serial irreflexive_singleton_frame.
Proof.
  intro Hserial. destruct (Hserial tt) as [u Hu]. exact Hu.
Qed.

Inductive db5_world : Type := DB0 | DB1.

Definition one_way_frame : frame :=
  {| World := db5_world;
     Rel := fun x y => x = DB0 /\ y = DB1 |}.

Lemma one_way_frame_not_symmetric :
  ~ frame_symmetric one_way_frame.
Proof.
  intro Hsym.
  specialize (Hsym DB0 DB1 (conj eq_refl eq_refl)).
  destruct Hsym as [H _]. discriminate.
Qed.

Definition two_fan_frame : frame :=
  {| World := db5_world;
     Rel := fun x _ => x = DB0 |}.

Lemma two_fan_frame_not_right_euclidean :
  ~ frame_right_euclidean two_fan_frame.
Proof.
  intro Heucl.
  specialize (Heucl DB0 DB1 DB0 eq_refl eq_refl).
  discriminate.
Qed.

Theorem K_strictly_weaker_KD :
  normal_strictly_weaker K_normal_proves KD_proves.
Proof.
  split.
  - apply K_weaker_than_KD.
  - exists (D (Atom 0)); split.
    + apply Np_extra. exists (Atom 0). reflexivity.
    + intro HK. apply (proj1 (empty_normal_proves_iff_K _)) in HK.
      pose proof (K_proves_sound_on_frame
        (F := irreflexive_singleton_frame) HK) as Hvalid.
      apply irreflexive_singleton_not_serial.
      now apply (proj1 (valid_D_iff_serial irreflexive_singleton_frame)).
Qed.

Theorem K_strictly_weaker_KB :
  normal_strictly_weaker K_normal_proves KB_proves.
Proof.
  split.
  - apply K_weaker_than_KB.
  - exists (B (Atom 0)); split.
    + apply Np_extra. exists (Atom 0). reflexivity.
    + intro HK. apply (proj1 (empty_normal_proves_iff_K _)) in HK.
      pose proof (K_proves_sound_on_frame (F := one_way_frame) HK)
        as Hvalid.
      apply one_way_frame_not_symmetric.
      now apply (proj1 (valid_B_iff_symmetric one_way_frame)).
Qed.

Theorem K_strictly_weaker_K5 :
  normal_strictly_weaker K_normal_proves K5_proves.
Proof.
  split.
  - apply K_weaker_than_K5.
  - exists (Five (Atom 0)); split.
    + apply Np_extra. exists (Atom 0). reflexivity.
    + intro HK. apply (proj1 (empty_normal_proves_iff_K _)) in HK.
      pose proof (K_proves_sound_on_frame (F := two_fan_frame) HK)
        as Hvalid.
      apply two_fan_frame_not_right_euclidean.
      now apply (proj1 (valid_Five_iff_right_euclidean two_fan_frame)).
Qed.
