(** Named standard modal companions.

    This file ports the complete classical companion family from Foundation's
    [Modal/ModalCompanion/Standard/Cl.lean]: S5, S5Grz, Triv, and the boxdot
    presentation through Ver.  It also establishes the proof-transport half
    of the Int, KC, and LC companion families. *)

From Stdlib Require Import Logic.Classical_Prop.
From FoundationModal Require Import
  Syntax GenericForcingRelation Axioms Kripke Correspondence
  CorrespondenceExtensions FrameProperties FrameTransformations
  LogicInfrastructure EntailmentExtensions EntailmentS4
  NormalHilbert CanonicalTB Modality
  PropositionalFormula PropositionalBoolean PropositionalBooleanHilbert
  PropositionalHilbert PropositionalKripke PropositionalKripkeCanonical
  PropositionalKripkeFinite PropositionalGlivenko
  GodelTranslation Boxdot GLGrzDerivations
  CanonicalPoint2 CanonicalPoint3 CanonicalGrz CanonicalGrzPoint2
  CanonicalGrzPoint3Strict CanonicalGLPoint3 CanonicalTrivVer CanonicalS5Grz.

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

(** * Forward halves of the intuitionistic companion families *)

(** These entailment packages share the same construction.  Keeping them
    here makes all three proof-transport theorems instances of the single
    generic Hilbert recursor in [GodelTranslation]. *)
Definition S4_schema_closed : schema_substitution_closed S4_schema :=
  schema_union_substitution_closed
    schema_T_substitution_closed schema_Four_substitution_closed.

Definition S4_normal_logic : normal_logic (@S4_proves nat) :=
  normal_proves_logic_is_normal S4_schema_closed.

Lemma S4_has_T : has_T (@S4_proves nat).
Proof. constructor; intro p. apply Np_extra. left. now exists p. Qed.

Lemma S4_has_Four : has_Four (@S4_proves nat).
Proof. constructor; intro p. apply Np_extra. right. now exists p. Qed.

Definition S4_as_s4_entailment : s4_entailment (@S4_proves nat) :=
  {| s4_K := k_entailment_of_normal_logic S4_normal_logic;
     s4_T := S4_has_T;
     s4_Four := S4_has_Four |}.

Definition S4Point2_normal_logic : normal_logic (@S4Point2_proves nat) :=
  normal_proves_logic_is_normal S4Point2_schema_substitution_closed.

Lemma S4Point2_has_T : has_T (@S4Point2_proves nat).
Proof. constructor; intro p. apply Np_extra. left; left. now exists p. Qed.

Lemma S4Point2_has_Four : has_Four (@S4Point2_proves nat).
Proof. constructor; intro p. apply Np_extra. left; right. now exists p. Qed.

Definition S4Point2_as_s4_entailment :
    s4_entailment (@S4Point2_proves nat) :=
  {| s4_K := k_entailment_of_normal_logic S4Point2_normal_logic;
     s4_T := S4Point2_has_T;
     s4_Four := S4Point2_has_Four |}.

Definition S4Point3_normal_logic : normal_logic (@S4Point3_proves nat) :=
  normal_proves_logic_is_normal S4Point3_schema_substitution_closed.

Lemma S4Point3_has_T : has_T (@S4Point3_proves nat).
Proof. constructor; intro p. apply Np_extra. left; left. now exists p. Qed.

Lemma S4Point3_has_Four : has_Four (@S4Point3_proves nat).
Proof. constructor; intro p. apply Np_extra. left; right. now exists p. Qed.

Definition S4Point3_as_s4_entailment :
    s4_entailment (@S4Point3_proves nat) :=
  {| s4_K := k_entailment_of_normal_logic S4Point3_normal_logic;
     s4_T := S4Point3_has_T;
     s4_Four := S4Point3_has_Four |}.

Lemma ph_int_provable_godel_S4 :
  forall p : pformula nat,
    ph_hilbert_provable (ph_hilbert_int nat) p ->
    S4_proves (godel_translate p).
Proof. exact (godel_translate_int_provable S4_as_s4_entailment). Qed.

(** The concrete propositional models instantiate the generic forcing
    criterion once and for all.  Bundling frames with valuations as the model
    index avoids any choice of a privileged valuation. *)
Lemma ph_int_complete_from_all_pkripke_models :
  forall p : pformula nat,
    (forall M : pkripke_model nat, True ->
      generic_all_forces (pkripke_forcing_relation M) p) ->
    ph_hilbert_provable (ph_hilbert_int nat) p.
Proof.
  intros p Hall. apply ph_hilbert_int_pkripke_complete.
  intros F _ V w.
  apply (Hall
    {| pkripke_model_frame := F; pkripke_model_valuation := V |}).
  constructor.
Qed.

Lemma S4_sound_on_pkripke_forcing_models :
  forall f : formula nat, S4_proves f ->
    forall M : pkripke_model nat, True ->
    @model_valid nat
      (forcing_modal_frame
        (pkripke_access (pkripke_model_frame M)))
      (@forcing_modal_valuation
        (pkripke_world (pkripke_model_frame M)) nat
        (pkripke_forcing_relation M)
        (pkripke_access (pkripke_model_frame M))) f.
Proof.
  intros f Hf M _.
  pose (R := pkripke_access (pkripke_model_frame M)).
  assert (HR : frame_reflexive (forcing_modal_frame R)).
  { intro w. apply pkripke_access_refl. }
  assert (HT : frame_transitive (forcing_modal_frame R)).
  { intros x y z. apply pkripke_access_trans. }
  exact ((@S4_proves_sound_on_preorder_frame nat
    (forcing_modal_frame R) f HR HT Hf)
    (@forcing_modal_valuation
      (pkripke_world (pkripke_model_frame M)) nat
      (pkripke_forcing_relation M) R)).
Qed.

Theorem ph_int_modal_companion_S4 :
  godel_modal_companion
    (ph_hilbert_provable (ph_hilbert_int nat)) (@S4_proves nat).
Proof.
  eapply (@godel_modal_companion_via_forcing_semantics
    nat (pkripke_model nat)
    (fun M => pkripke_world (pkripke_model_frame M))
    (fun M => pkripke_forcing_relation M)
    (fun M => pkripke_access (pkripke_model_frame M))
    (fun _ => True)
    (ph_hilbert_provable (ph_hilbert_int nat)) (@S4_proves nat)).
  - intros M w. apply pkripke_access_refl.
  - intros M x y z. apply pkripke_access_trans.
  - intro M. apply pkripke_generic_int_forcing.
  - apply ph_int_provable_godel_S4.
  - apply ph_int_complete_from_all_pkripke_models.
  - apply S4_sound_on_pkripke_forcing_models.
Qed.

Lemma ph_int_provable_godel_Grz :
  forall p : pformula nat,
    ph_hilbert_provable (ph_hilbert_int nat) p ->
    Grz_proves (godel_translate p).
Proof.
  intros p Hp. apply S4_weaker_than_Grz.
  now apply ph_int_provable_godel_S4.
Qed.

Lemma ph_int_complete_from_finite_partial_pkripke_models :
  forall p : pformula nat,
    (forall M : pkripke_model nat,
      pkripke_finite_partial_order (pkripke_model_frame M) ->
      generic_all_forces (pkripke_forcing_relation M) p) ->
    ph_hilbert_provable (ph_hilbert_int nat) p.
Proof.
  intros p Hall.
  apply ph_hilbert_int_pkripke_finite_partial_order_complete.
  intros F HF V w.
  apply (Hall {| pkripke_model_frame := F;
    pkripke_model_valuation := V |} HF).
Qed.

Lemma Grz_sound_on_finite_partial_pkripke_forcing_models :
  forall f : formula nat, Grz_proves f ->
    forall M : pkripke_model nat,
    pkripke_finite_partial_order (pkripke_model_frame M) ->
    @model_valid nat
      (forcing_modal_frame
        (pkripke_access (pkripke_model_frame M)))
      (@forcing_modal_valuation
        (pkripke_world (pkripke_model_frame M)) nat
        (pkripke_forcing_relation M)
        (pkripke_access (pkripke_model_frame M))) f.
Proof.
  intros f Hf M [Hfinite Hanti].
  assert (HF : Grz_finite_frame_class
      (forcing_modal_frame
        (pkripke_access (pkripke_model_frame M)))).
  { split; [exact Hfinite |]. repeat split.
    - exact (pkripke_access_refl (pkripke_model_frame M)).
    - exact (pkripke_access_trans (pkripke_model_frame M)).
    - exact Hanti. }
  exact (((Grz_finite_sound Hf)
    (forcing_modal_frame
      (pkripke_access (pkripke_model_frame M))) HF)
    (@forcing_modal_valuation
      (pkripke_world (pkripke_model_frame M)) nat
      (pkripke_forcing_relation M)
      (pkripke_access (pkripke_model_frame M)))).
Qed.

Theorem ph_int_modal_companion_Grz :
  godel_modal_companion
    (ph_hilbert_provable (ph_hilbert_int nat)) (@Grz_proves nat).
Proof.
  eapply (@godel_modal_companion_via_forcing_semantics
    nat (pkripke_model nat)
    (fun M => pkripke_world (pkripke_model_frame M))
    (fun M => pkripke_forcing_relation M)
    (fun M => pkripke_access (pkripke_model_frame M))
    (fun M => pkripke_finite_partial_order
      (pkripke_model_frame M))
    (ph_hilbert_provable (ph_hilbert_int nat)) (@Grz_proves nat)).
  - intros M w. apply pkripke_access_refl.
  - intros M x y z. apply pkripke_access_trans.
  - intro M. apply pkripke_generic_int_forcing.
  - apply ph_int_provable_godel_Grz.
  - apply ph_int_complete_from_finite_partial_pkripke_models.
  - apply Grz_sound_on_finite_partial_pkripke_forcing_models.
Qed.

Theorem ph_int_boxdot_modal_companion_GL :
  forall p : pformula nat,
    ph_hilbert_provable (ph_hilbert_int nat) p <->
    GL_proves (boxdot_translate (godel_translate p)).
Proof.
  intro p; split.
  - intro Hp. apply (proj2 (GL_boxdot_iff_Grz (godel_translate p))).
    now apply (proj1 (ph_int_modal_companion_Grz p)).
  - intro Hp. apply (proj2 (ph_int_modal_companion_Grz p)).
    now apply (proj1 (GL_boxdot_iff_Grz (godel_translate p))).
Qed.

(** Glivenko turns the classical theoremhood of [p] into intuitionistic
    theoremhood of [~~p].  Its Goedel translation is [Box (Dia p^g)]; T and
    necessitation remove and restore that outer box. *)
Theorem ph_cl_provable_iff_S4_dia_godel :
  forall p : pformula nat,
    ph_hilbert_provable (ph_hilbert_cl nat) p <->
    S4_proves (Dia (godel_translate p)).
Proof.
  intro p; split.
  - intro Hp.
    pose proof (proj1 (ph_int_modal_companion_S4
      (pneg (pneg p))) (proj2 (@ph_glivenko nat p) Hp)) as Hboxdia.
    change (S4_proves (Box (Dia (godel_translate p)))) in Hboxdia.
    exact (Np_mp (has_T_axiom S4_has_T (Dia (godel_translate p))) Hboxdia).
  - intro Hdia. apply (proj1 (@ph_glivenko nat p)).
    apply (proj2 (ph_int_modal_companion_S4 (pneg (pneg p)))).
    change (S4_proves (Box (Dia (godel_translate p)))).
    now apply Np_nec.
Qed.

(** WLEM becomes valid on every convergent preorder. *)
Lemma S4Point2_proves_godel_translated_WLEM :
  forall p : pformula nat,
    S4Point2_proves (godel_translate (ph_axiom_wlem p)).
Proof.
  intro p. apply S4Point2_complete.
  intros F [Hrefl [Htrans Hconv]] V x.
  cbn [ph_axiom_wlem pneg godel_translate]. apply satisfies_or.
  destruct (classic (satisfies F V x
      (Box (Imp (godel_translate p) Bottom)))) as [Hneg | Hneg].
  - now left.
  - right. intros y Rxy Hyneg.
    assert (Hex : exists z, Rel F x z /\
        ~ satisfies F V z (Imp (godel_translate p) Bottom)).
    { apply NNPP. intro Hnone. apply Hneg. intros z Rxz.
      apply NNPP. intro Hbad. apply Hnone. exists z. split; assumption. }
    destruct Hex as [z [Rxz Hz]].
    assert (Hzp : satisfies F V z (godel_translate p)).
    { apply NNPP. intro Hzp. apply Hz. intro Hp. contradiction. }
    destruct (Hconv x y z Rxy Rxz) as [u [Ryu Rzu]].
    apply (Hyneg u Ryu).
    eapply godel_translate_persistent; eauto.
Qed.

Lemma ph_kc_provable_godel_S4Point2 :
  forall p : pformula nat,
    ph_hilbert_provable (ph_hilbert_kc nat) p ->
    S4Point2_proves (godel_translate p).
Proof.
  intros p Hp.
  eapply godel_translate_hilbert_provable;
    [exact S4Point2_as_s4_entailment | |exact Hp].
  intros q Hq; destruct Hq.
  - exact (godel_translate_efq S4Point2_as_s4_entailment p0).
  - exact (S4Point2_proves_godel_translated_WLEM p0).
Qed.

Lemma ph_kc_complete_from_convergent_pkripke_models :
  forall p : pformula nat,
    (forall M : pkripke_model nat,
      pkripke_frame_strongly_convergent (pkripke_model_frame M) ->
      generic_all_forces (pkripke_forcing_relation M) p) ->
    ph_hilbert_provable (ph_hilbert_kc nat) p.
Proof.
  intros p Hall. apply ph_hilbert_kc_pkripke_complete.
  intros F HF V w.
  apply (Hall
    {| pkripke_model_frame := F; pkripke_model_valuation := V |}).
  exact HF.
Qed.

Lemma S4Point2_sound_on_convergent_pkripke_forcing_models :
  forall f : formula nat, S4Point2_proves f ->
    forall M : pkripke_model nat,
    pkripke_frame_strongly_convergent (pkripke_model_frame M) ->
    @model_valid nat
      (forcing_modal_frame
        (pkripke_access (pkripke_model_frame M)))
      (@forcing_modal_valuation
        (pkripke_world (pkripke_model_frame M)) nat
        (pkripke_forcing_relation M)
        (pkripke_access (pkripke_model_frame M))) f.
Proof.
  intros f Hf M HC.
  pose (R := pkripke_access (pkripke_model_frame M)).
  assert (HR : frame_reflexive (forcing_modal_frame R)).
  { intro w. apply pkripke_access_refl. }
  assert (HT : frame_transitive (forcing_modal_frame R)).
  { intros x y z. apply pkripke_access_trans. }
  exact ((@S4Point2_proves_sound_on_frame nat
    (forcing_modal_frame R) f HR HT HC Hf)
    (@forcing_modal_valuation
      (pkripke_world (pkripke_model_frame M)) nat
      (pkripke_forcing_relation M) R)).
Qed.

Theorem ph_kc_modal_companion_S4Point2 :
  godel_modal_companion
    (ph_hilbert_provable (ph_hilbert_kc nat))
    (@S4Point2_proves nat).
Proof.
  eapply (@godel_modal_companion_via_forcing_semantics
    nat (pkripke_model nat)
    (fun M => pkripke_world (pkripke_model_frame M))
    (fun M => pkripke_forcing_relation M)
    (fun M => pkripke_access (pkripke_model_frame M))
    (fun M => pkripke_frame_strongly_convergent
      (pkripke_model_frame M))
    (ph_hilbert_provable (ph_hilbert_kc nat))
    (@S4Point2_proves nat)).
  - intros M w. apply pkripke_access_refl.
  - intros M x y z. apply pkripke_access_trans.
  - intro M. apply pkripke_generic_int_forcing.
  - apply ph_kc_provable_godel_S4Point2.
  - apply ph_kc_complete_from_convergent_pkripke_models.
  - apply S4Point2_sound_on_convergent_pkripke_forcing_models.
Qed.

Lemma ph_kc_provable_godel_GrzPoint2 :
  forall p : pformula nat,
    ph_hilbert_provable (ph_hilbert_kc nat) p ->
    GrzPoint2_proves (godel_translate p).
Proof.
  intros p Hp. apply S4Point2_weaker_than_GrzPoint2.
  now apply ph_kc_provable_godel_S4Point2.
Qed.

Lemma ph_kc_complete_from_finite_partial_convergent_pkripke_models :
  forall p : pformula nat,
    (forall M : pkripke_model nat,
      pkripke_finite_partial_order_convergent
        (pkripke_model_frame M) ->
      generic_all_forces (pkripke_forcing_relation M) p) ->
    ph_hilbert_provable (ph_hilbert_kc nat) p.
Proof.
  intros p Hall.
  apply ph_hilbert_kc_pkripke_finite_partial_order_complete.
  intros F HF V w.
  apply (Hall {| pkripke_model_frame := F;
    pkripke_model_valuation := V |} HF).
Qed.

Lemma GrzPoint2_sound_on_finite_partial_convergent_pkripke_models :
  forall f : formula nat, GrzPoint2_proves f ->
    forall M : pkripke_model nat,
    pkripke_finite_partial_order_convergent
      (pkripke_model_frame M) ->
    @model_valid nat
      (forcing_modal_frame
        (pkripke_access (pkripke_model_frame M)))
      (@forcing_modal_valuation
        (pkripke_world (pkripke_model_frame M)) nat
        (pkripke_forcing_relation M)
        (pkripke_access (pkripke_model_frame M))) f.
Proof.
  intros f Hf M [Hfinite [Hanti Hconv]].
  assert (HF : GrzPoint2_finite_frame_class
      (forcing_modal_frame
        (pkripke_access (pkripke_model_frame M)))).
  { split; [exact Hfinite |]. split.
    - repeat split.
      + exact (pkripke_access_refl (pkripke_model_frame M)).
      + exact (pkripke_access_trans (pkripke_model_frame M)).
      + exact Hanti.
    - exact Hconv. }
  exact ((@GrzPoint2_proves_sound_on_finite_frame nat
    (forcing_modal_frame
      (pkripke_access (pkripke_model_frame M))) f HF Hf)
    (@forcing_modal_valuation
      (pkripke_world (pkripke_model_frame M)) nat
      (pkripke_forcing_relation M)
      (pkripke_access (pkripke_model_frame M)))).
Qed.

Theorem ph_kc_modal_companion_GrzPoint2 :
  godel_modal_companion
    (ph_hilbert_provable (ph_hilbert_kc nat))
    (@GrzPoint2_proves nat).
Proof.
  eapply (@godel_modal_companion_via_forcing_semantics
    nat (pkripke_model nat)
    (fun M => pkripke_world (pkripke_model_frame M))
    (fun M => pkripke_forcing_relation M)
    (fun M => pkripke_access (pkripke_model_frame M))
    (fun M => pkripke_finite_partial_order_convergent
      (pkripke_model_frame M))
    (ph_hilbert_provable (ph_hilbert_kc nat))
    (@GrzPoint2_proves nat)).
  - intros M w. apply pkripke_access_refl.
  - intros M x y z. apply pkripke_access_trans.
  - intro M. apply pkripke_generic_int_forcing.
  - apply ph_kc_provable_godel_GrzPoint2.
  - apply ph_kc_complete_from_finite_partial_convergent_pkripke_models.
  - apply GrzPoint2_sound_on_finite_partial_convergent_pkripke_models.
Qed.

(** Dummett's axiom becomes valid on every locally connected preorder. *)
Lemma S4Point3_proves_godel_translated_Dummett :
  forall p q : pformula nat,
    S4Point3_proves (godel_translate (ph_axiom_dummett p q)).
Proof.
  intros p q. apply S4Point3_complete.
  intros F [Hrefl [Htrans Hconn]] V x.
  cbn [ph_axiom_dummett godel_translate]. apply satisfies_or.
  apply NNPP. intro Hneither.
  apply Decidable.not_or in Hneither as [Hpq Hqp].
  assert (Hy : exists y, Rel F x y /\
      satisfies F V y (godel_translate p) /\
      ~ satisfies F V y (godel_translate q)).
  { apply NNPP. intro Hnone. apply Hpq. intros y Rxy Hyp.
    apply NNPP. intro Hynq. apply Hnone. exists y. repeat split; assumption. }
  assert (Hz : exists z, Rel F x z /\
      satisfies F V z (godel_translate q) /\
      ~ satisfies F V z (godel_translate p)).
  { apply NNPP. intro Hnone. apply Hqp. intros z Rxz Hzq.
    apply NNPP. intro Hznp. apply Hnone. exists z. repeat split; assumption. }
  destruct Hy as [y [Rxy [Hyp Hynq]]].
  destruct Hz as [z [Rxz [Hzq Hznp]]].
  destruct (Hconn x y z Rxy Rxz) as [Ryz | Rzy].
  - apply Hznp. eapply godel_translate_persistent; eauto.
  - apply Hynq. eapply godel_translate_persistent; eauto.
Qed.

Lemma ph_lc_provable_godel_S4Point3 :
  forall p : pformula nat,
    ph_hilbert_provable (ph_hilbert_lc nat) p ->
    S4Point3_proves (godel_translate p).
Proof.
  intros p Hp.
  eapply godel_translate_hilbert_provable;
    [exact S4Point3_as_s4_entailment | |exact Hp].
  intros q Hq; destruct Hq as [r | r s].
  - exact (godel_translate_efq S4Point3_as_s4_entailment r).
  - exact (S4Point3_proves_godel_translated_Dummett r s).
Qed.

Lemma ph_lc_complete_from_connected_pkripke_models :
  forall p : pformula nat,
    (forall M : pkripke_model nat,
      pkripke_frame_strongly_connected (pkripke_model_frame M) ->
      generic_all_forces (pkripke_forcing_relation M) p) ->
    ph_hilbert_provable (ph_hilbert_lc nat) p.
Proof.
  intros p Hall. apply ph_hilbert_lc_pkripke_complete.
  intros F HF V w.
  apply (Hall
    {| pkripke_model_frame := F; pkripke_model_valuation := V |}).
  exact HF.
Qed.

Lemma S4Point3_sound_on_connected_pkripke_forcing_models :
  forall f : formula nat, S4Point3_proves f ->
    forall M : pkripke_model nat,
    pkripke_frame_strongly_connected (pkripke_model_frame M) ->
    @model_valid nat
      (forcing_modal_frame
        (pkripke_access (pkripke_model_frame M)))
      (@forcing_modal_valuation
        (pkripke_world (pkripke_model_frame M)) nat
        (pkripke_forcing_relation M)
        (pkripke_access (pkripke_model_frame M))) f.
Proof.
  intros f Hf M HC.
  pose (R := pkripke_access (pkripke_model_frame M)).
  assert (HR : frame_reflexive (forcing_modal_frame R)).
  { intro w. apply pkripke_access_refl. }
  assert (HT : frame_transitive (forcing_modal_frame R)).
  { intros x y z. apply pkripke_access_trans. }
  exact ((@S4Point3_proves_sound_on_frame nat
    (forcing_modal_frame R) f HR HT HC Hf)
    (@forcing_modal_valuation
      (pkripke_world (pkripke_model_frame M)) nat
      (pkripke_forcing_relation M) R)).
Qed.

Theorem ph_lc_modal_companion_S4Point3 :
  godel_modal_companion
    (ph_hilbert_provable (ph_hilbert_lc nat))
    (@S4Point3_proves nat).
Proof.
  eapply (@godel_modal_companion_via_forcing_semantics
    nat (pkripke_model nat)
    (fun M => pkripke_world (pkripke_model_frame M))
    (fun M => pkripke_forcing_relation M)
    (fun M => pkripke_access (pkripke_model_frame M))
    (fun M => pkripke_frame_strongly_connected
      (pkripke_model_frame M))
    (ph_hilbert_provable (ph_hilbert_lc nat))
    (@S4Point3_proves nat)).
  - intros M w. apply pkripke_access_refl.
  - intros M x y z. apply pkripke_access_trans.
  - intro M. apply pkripke_generic_int_forcing.
  - apply ph_lc_provable_godel_S4Point3.
  - apply ph_lc_complete_from_connected_pkripke_models.
  - apply S4Point3_sound_on_connected_pkripke_forcing_models.
Qed.

Lemma ph_lc_provable_godel_GrzPoint3 :
  forall p : pformula nat,
    ph_hilbert_provable (ph_hilbert_lc nat) p ->
    GrzPoint3_proves (godel_translate p).
Proof.
  intros p Hp. apply S4Point3_weaker_than_GrzPoint3.
  now apply ph_lc_provable_godel_S4Point3.
Qed.

Lemma ph_lc_complete_from_finite_partial_connected_pkripke_models :
  forall p : pformula nat,
    (forall M : pkripke_model nat,
      pkripke_finite_partial_order_connected
        (pkripke_model_frame M) ->
      generic_all_forces (pkripke_forcing_relation M) p) ->
    ph_hilbert_provable (ph_hilbert_lc nat) p.
Proof.
  intros p Hall.
  apply ph_hilbert_lc_pkripke_finite_partial_order_complete.
  intros F HF V w.
  apply (Hall {| pkripke_model_frame := F;
    pkripke_model_valuation := V |} HF).
Qed.

Lemma GrzPoint3_sound_on_finite_partial_connected_pkripke_models :
  forall f : formula nat, GrzPoint3_proves f ->
    forall M : pkripke_model nat,
    pkripke_finite_partial_order_connected
      (pkripke_model_frame M) ->
    @model_valid nat
      (forcing_modal_frame
        (pkripke_access (pkripke_model_frame M)))
      (@forcing_modal_valuation
        (pkripke_world (pkripke_model_frame M)) nat
        (pkripke_forcing_relation M)
        (pkripke_access (pkripke_model_frame M))) f.
Proof.
  intros f Hf M [Hfinite [Hanti Hconn]].
  assert (HF : GrzPoint3_finite_piecewise_strong_frame_class
      (forcing_modal_frame
        (pkripke_access (pkripke_model_frame M)))).
  { split; [exact Hfinite |]. split.
    - repeat split.
      + exact (pkripke_access_refl (pkripke_model_frame M)).
      + exact (pkripke_access_trans (pkripke_model_frame M)).
      + exact Hanti.
    - exact Hconn. }
  exact ((@GrzPoint3_proves_sound_on_finite_piecewise_strong_frame nat
    (forcing_modal_frame
      (pkripke_access (pkripke_model_frame M))) f HF Hf)
    (@forcing_modal_valuation
      (pkripke_world (pkripke_model_frame M)) nat
      (pkripke_forcing_relation M)
      (pkripke_access (pkripke_model_frame M)))).
Qed.

Theorem ph_lc_modal_companion_GrzPoint3 :
  godel_modal_companion
    (ph_hilbert_provable (ph_hilbert_lc nat))
    (@GrzPoint3_proves nat).
Proof.
  eapply (@godel_modal_companion_via_forcing_semantics
    nat (pkripke_model nat)
    (fun M => pkripke_world (pkripke_model_frame M))
    (fun M => pkripke_forcing_relation M)
    (fun M => pkripke_access (pkripke_model_frame M))
    (fun M => pkripke_finite_partial_order_connected
      (pkripke_model_frame M))
    (ph_hilbert_provable (ph_hilbert_lc nat))
    (@GrzPoint3_proves nat)).
  - intros M w. apply pkripke_access_refl.
  - intros M x y z. apply pkripke_access_trans.
  - intro M. apply pkripke_generic_int_forcing.
  - apply ph_lc_provable_godel_GrzPoint3.
  - apply ph_lc_complete_from_finite_partial_connected_pkripke_models.
  - apply GrzPoint3_sound_on_finite_partial_connected_pkripke_models.
Qed.

Lemma GLPoint3_boxdot_sound_on_finite_partial_connected_pkripke_models :
  forall f : formula nat,
    GLPoint3_proves (boxdot_translate f) ->
    forall M : pkripke_model nat,
    pkripke_finite_partial_order_connected
      (pkripke_model_frame M) ->
    @model_valid nat
      (forcing_modal_frame
        (pkripke_access (pkripke_model_frame M)))
      (@forcing_modal_valuation
        (pkripke_world (pkripke_model_frame M)) nat
        (pkripke_forcing_relation M)
        (pkripke_access (pkripke_model_frame M))) f.
Proof.
  intros f Hf M [Hfinite [Hanti Hconn]].
  set (F := forcing_modal_frame
    (pkripke_access (pkripke_model_frame M))).
  assert (Hrefl : frame_reflexive F).
  { exact (pkripke_access_refl (pkripke_model_frame M)). }
  assert (Htrans : frame_transitive F).
  { exact (pkripke_access_trans (pkripke_model_frame M)). }
  assert (HGrz3 : boxdot_finite_GrzPoint3_frame F).
  { split.
    - split; [exact Hfinite |]. split; [exact Hrefl |]. split.
      + exact Htrans.
      + now apply finite_transitive_antisymmetric_weak_cwf.
    - exact Hconn. }
  assert (HGL3 : boxdot_finite_GLPoint3_frame
      (irreflexivize_frame F)).
  { now apply finite_GrzPoint3_to_irreflexivize_finite_GLPoint3. }
  assert (Hvalid_i : valid (irreflexivize_frame F)
      (boxdot_translate f)).
  { now apply GLPoint3_proves_sound_on_finite_frame. }
  assert (Hvalid_r : valid
      (frame_refl_gen (irreflexivize_frame F)) f).
  { now apply (proj1 (boxdot_reflexive_closure_valid_iff
      (irreflexivize_frame F) f)). }
  assert (Hvalid_F : valid F f).
  { now apply (proj2 (@irreflexivize_reflexive_valid_iff nat F f Hrefl)). }
  exact (Hvalid_F
    (@forcing_modal_valuation
      (pkripke_world (pkripke_model_frame M)) nat
      (pkripke_forcing_relation M)
      (pkripke_access (pkripke_model_frame M)))).
Qed.

Theorem ph_lc_boxdot_modal_companion_GLPoint3 :
  forall p : pformula nat,
    ph_hilbert_provable (ph_hilbert_lc nat) p <->
    GLPoint3_proves (boxdot_translate (godel_translate p)).
Proof.
  intro p; split.
  - intro Hp. apply GrzPoint3_proves_to_GLPoint3_boxdot_unconditional.
    now apply (proj1 (ph_lc_modal_companion_GrzPoint3 p)).
  - intro Hp.
    apply ph_hilbert_lc_pkripke_finite_partial_order_complete.
    intros F HF V w.
    set (M := {| pkripke_model_frame := F;
      pkripke_model_valuation := V |}).
    apply (proj2 (@pkripke_forces_iff_forcing_modal_godel nat M p w)).
    exact (@GLPoint3_boxdot_sound_on_finite_partial_connected_pkripke_models
      (godel_translate p) Hp M HF w).
Qed.
