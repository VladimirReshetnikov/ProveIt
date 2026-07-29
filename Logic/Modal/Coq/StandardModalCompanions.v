(** Named standard modal companions.

    This file ports the complete classical companion family from Foundation's
    [Modal/ModalCompanion/Standard/Cl.lean]: S5, S5Grz, Triv, and the boxdot
    presentation through Ver. *)

From Stdlib Require Import Logic.Classical_Prop.
From FoundationModal Require Import
  Syntax Axioms Kripke Correspondence FrameTransformations
  LogicInfrastructure EntailmentExtensions EntailmentS4
  NormalHilbert CanonicalTB Modality
  PropositionalFormula PropositionalBoolean PropositionalBooleanHilbert
  PropositionalHilbert GodelTranslation Boxdot CanonicalTrivVer CanonicalS5Grz.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition nat_pformula_codec : pformula_atom_codec nat :=
  {| pformula_atom_encode := fun n => n;
     pformula_atom_decode := fun n => Some n;
     pformula_atom_decode_encode := fun _ => eq_refl |}.

Definition S5_schema_closed : schema_substitution_closed S5_schema :=
  schema_union_substitution_closed
    schema_T_substitution_closed schema_Five_substitution_closed.

Definition S5_normal_logic : normal_logic (@S5_proves nat) :=
  normal_proves_logic_is_normal S5_schema_closed.

Lemma S5_has_T : has_T (@S5_proves nat).
Proof.
  constructor; intro p. apply Np_extra. left. now exists p.
Qed.

Lemma S5_has_Four : has_Four (@S5_proves nat).
Proof.
  constructor; intro p. apply S5_complete.
  intros F [Hrefl Heucl]. apply valid_Four_of_transitive.
  now apply frame_reflexive_right_euclidean_transitive.
Qed.

Definition S5_as_s4_entailment : s4_entailment (@S5_proves nat) :=
  {| s4_K := k_entailment_of_normal_logic S5_normal_logic;
     s4_T := S5_has_T;
     s4_Four := S5_has_Four |}.

(** The sole optional classical schema translates into S5. *)
Lemma S5_proves_godel_translated_LEM :
  forall p : pformula nat,
    S5_proves (godel_translate (ph_axiom_lem p)).
Proof.
  intro p; change (S5_proves
    (Or (godel_translate p) (Box (Imp (godel_translate p) Bottom)))).
  apply S5_complete. intros F [Hrefl Heucl] V x.
  apply satisfies_or.
  destruct (classic (satisfies F V x (godel_translate p))) as [Hp | Hnp].
  - now left.
  - right. intros y Rxy Hy. apply Hnp.
    eapply godel_translate_persistent.
    + now apply frame_reflexive_right_euclidean_transitive.
    + exact Hy.
    + now apply frame_reflexive_right_euclidean_symmetric.
Qed.

Lemma ph_cl_provable_godel_S5 :
  forall p : pformula nat,
    ph_hilbert_provable (ph_hilbert_cl nat) p ->
    S5_proves (godel_translate p).
Proof.
  intros p Hp.
  eapply godel_translate_hilbert_provable;
    [exact S5_as_s4_entailment | |exact Hp].
  intros q Hq; destruct Hq.
  - exact (godel_translate_efq S5_as_s4_entailment p0).
  - exact (S5_proves_godel_translated_LEM p0).
Qed.

Lemma godel_translate_reflexive_singleton_iff_boolean :
  forall (v : pvaluation nat) (p : pformula nat),
    satisfies reflexive_singleton_frame (fun a _ => v a) tt
      (godel_translate p) <-> pboolean_eval v p.
Proof.
  intros v p; induction p as
      [a| |p IHp q IHq|p IHp q IHq|p IHp q IHq].
  - cbn [godel_translate satisfies reflexive_singleton_frame]. split.
    + intro H. apply H with (u := tt). constructor.
    + intros Ha [] _. exact Ha.
  - reflexivity.
  - cbn [godel_translate pboolean_eval].
    rewrite satisfies_and, IHp, IHq. tauto.
  - cbn [godel_translate pboolean_eval].
    rewrite satisfies_or, IHp, IHq. tauto.
  - cbn [godel_translate satisfies reflexive_singleton_frame]. split.
    + intros H Hp. apply (proj1 IHq), H with (u := tt); [constructor |].
      now apply (proj2 IHp).
    + intros H [] _ Hp. apply (proj2 IHq), H.
      now apply (proj1 IHp).
Qed.

Lemma ph_cl_provable_of_godel_S5 :
  forall p : pformula nat,
    S5_proves (godel_translate p) ->
    ph_hilbert_provable (ph_hilbert_cl nat) p.
Proof.
  intros p Hp. apply (proj2
    (@ph_cl_provable_iff_tautology nat nat_pformula_codec p)).
  intro v.
  apply (proj1 (godel_translate_reflexive_singleton_iff_boolean v p)).
  exact (@S5_proves_sound_on_reflexive_euclidean_frame nat
    reflexive_singleton_frame (godel_translate p)
    reflexive_singleton_reflexive reflexive_singleton_right_euclidean
    Hp (fun a _ => v a) tt).
Qed.

Theorem ph_cl_modal_companion_S5 :
  godel_modal_companion
    (ph_hilbert_provable (ph_hilbert_cl nat)) (@S5_proves nat).
Proof.
  intro p; split.
  - apply ph_cl_provable_godel_S5.
  - apply ph_cl_provable_of_godel_S5.
Qed.

(** S5Grz contains S5, so the forward direction is inherited. *)
Lemma ph_cl_provable_godel_S5Grz :
  forall p : pformula nat,
    ph_hilbert_provable (ph_hilbert_cl nat) p ->
    S5Grz_proves (godel_translate p).
Proof.
  intros p Hp. apply S5_weaker_than_S5Grz.
  now apply ph_cl_provable_godel_S5.
Qed.

(** For translated propositional formulas, soundness on the one-world Triv
    frame gives the converse without requiring a general S5Grz-to-S5
    reduction. *)
Lemma ph_cl_provable_of_godel_S5Grz :
  forall p : pformula nat,
    S5Grz_proves (godel_translate p) ->
    ph_hilbert_provable (ph_hilbert_cl nat) p.
Proof.
  intros p Hp. apply (proj2
    (@ph_cl_provable_iff_tautology nat nat_pformula_codec p)).
  intro v.
  apply (proj1 (godel_translate_reflexive_singleton_iff_boolean v p)).
  eapply (@S5Grz_proves_sound_on_Triv_frame nat
    reflexive_singleton_frame (godel_translate p)).
  - split.
    + exact reflexive_singleton_reflexive.
    + exact reflexive_singleton_coreflexive.
  - exact Hp.
Qed.

Theorem ph_cl_modal_companion_S5Grz :
  godel_modal_companion
    (ph_hilbert_provable (ph_hilbert_cl nat)) (@S5Grz_proves nat).
Proof.
  intro p; split.
  - apply ph_cl_provable_godel_S5Grz.
  - apply ph_cl_provable_of_godel_S5Grz.
Qed.

(** The unconditional proof-theoretic collapse [S5Grz = Triv] transports the
    companion equivalence in both directions. *)
Theorem ph_cl_modal_companion_Triv :
  godel_modal_companion
    (ph_hilbert_provable (ph_hilbert_cl nat)) (@Triv_proves nat).
Proof.
  intro p; split.
  - intro Hp. apply S5Grz_weaker_than_Triv.
    now apply ph_cl_provable_godel_S5Grz.
  - intro Hp. apply ph_cl_provable_of_godel_S5Grz.
    now apply Triv_weaker_than_S5Grz.
Qed.

(** Boxdot converts the unconditional Ver/Triv equivalence into the final
    classical companion presentation. *)
Theorem ph_cl_boxdot_modal_companion_Ver :
  forall p : pformula nat,
    ph_hilbert_provable (ph_hilbert_cl nat) p <->
    Ver_proves (boxdot_translate (godel_translate p)).
Proof.
  intro p; split.
  - intro Hp.
    apply (proj2 (Ver_boxdot_iff_Triv_unconditional (godel_translate p))).
    now apply (proj1 (ph_cl_modal_companion_Triv p)).
  - intro Hp.
    apply (proj2 (ph_cl_modal_companion_Triv p)).
    now apply (proj1 (Ver_boxdot_iff_Triv_unconditional
      (godel_translate p))).
Qed.
