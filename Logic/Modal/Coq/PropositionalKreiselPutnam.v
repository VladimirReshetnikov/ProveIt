(** Kreisel--Putnam propositional Kripke semantics and its strict position
    below KC.

    The frame condition is stated over the generalized preorder frames used
    by this port.  Its soundness proof follows the source argument, while a
    three-world rooted fork gives a compact strictness witness. *)

From Stdlib Require Import Logic.Classical_Prop.
From FoundationModal Require Import
  PropositionalFormula PropositionalHilbert PropositionalKripke
  PropositionalKripkeCanonical.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition pkripke_frame_kreisel_putnam (F : pkripke_frame) : Prop :=
  forall x y z,
    pkripke_access F x y -> pkripke_access F x z ->
    ~ pkripke_access F y z -> ~ pkripke_access F z y ->
    exists u,
      pkripke_access F x u /\
      pkripke_access F u y /\
      pkripke_access F u z /\
      forall v, pkripke_access F u v ->
        exists w, pkripke_access F v w /\
          (pkripke_access F y w \/ pkripke_access F z w).

Theorem pkripke_KP_valid_of_condition :
  forall (Atom : Type) (F : pkripke_frame),
    pkripke_frame_kreisel_putnam F ->
    forall p q r : pformula Atom,
      pkripke_frame_valid F (ph_axiom_kreisel_putnam p q r).
Proof.
  intros Atom F HKP p q r V x y Rxy Hdisj.
  cbn [ph_axiom_kreisel_putnam pneg] in *.
  apply NNPP. intro Hneither.
  apply Decidable.not_or in Hneither as [Hleft Hright].
  assert (Hz1 : exists z1,
      pkripke_access F y z1 /\
      pkripke_forces
        {| pkripke_model_frame := F; pkripke_model_valuation := V |}
        z1 (pneg p) /\
      ~ pkripke_forces
        {| pkripke_model_frame := F; pkripke_model_valuation := V |} z1 q).
  { apply NNPP. intro Hnone. apply Hleft. intros z1 Ryz1 Hz1neg.
    apply NNPP. intro Hz1q. apply Hnone. exists z1. repeat split; assumption. }
  assert (Hz2 : exists z2,
      pkripke_access F y z2 /\
      pkripke_forces
        {| pkripke_model_frame := F; pkripke_model_valuation := V |}
        z2 (pneg p) /\
      ~ pkripke_forces
        {| pkripke_model_frame := F; pkripke_model_valuation := V |} z2 r).
  { apply NNPP. intro Hnone. apply Hright. intros z2 Ryz2 Hz2neg.
    apply NNPP. intro Hz2r. apply Hnone. exists z2. repeat split; assumption. }
  destruct Hz1 as [z1 [Ryz1 [Hz1neg Hz1q]]].
  destruct Hz2 as [z2 [Ryz2 [Hz2neg Hz2r]]].
  assert (Hnz1z2 : ~ pkripke_access F z1 z2).
  { intro Rz1z2. destruct (Hdisj z1 Ryz1 Hz1neg) as [Hq | Hr].
    - exact (Hz1q Hq).
    - apply Hz2r. eapply pkripke_forces_persistent; eauto. }
  assert (Hnz2z1 : ~ pkripke_access F z2 z1).
  { intro Rz2z1. destruct (Hdisj z2 Ryz2 Hz2neg) as [Hq | Hr].
    - apply Hz1q. eapply pkripke_forces_persistent; eauto.
    - exact (Hz2r Hr). }
  destruct (HKP y z1 z2 Ryz1 Ryz2 Hnz1z2 Hnz2z1)
    as [u [Ryu [Ruz1 [Ruz2 Hu]]]].
  assert (Huneg : ~ pkripke_forces
      {| pkripke_model_frame := F; pkripke_model_valuation := V |}
      u (pneg p)).
  { intro Huneg. destruct (Hdisj u Ryu Huneg) as [Hq | Hr].
    - apply Hz1q. eapply pkripke_forces_persistent; eauto.
    - apply Hz2r. eapply pkripke_forces_persistent; eauto. }
  assert (Hv : exists v, pkripke_access F u v /\
      pkripke_forces
        {| pkripke_model_frame := F; pkripke_model_valuation := V |} v p).
  { apply NNPP. intro Hnone. apply Huneg. intros v Ruv Hvp.
    apply Hnone. now exists v. }
  destruct Hv as [v [Ruv Hvp]].
  destruct (Hu v Ruv) as [w [Rvw [Rz1w | Rz2w]]].
  - apply (Hz1neg w Rz1w).
    eapply pkripke_forces_persistent; [exact Rvw | exact Hvp].
  - apply (Hz2neg w Rz2w).
    eapply pkripke_forces_persistent; [exact Rvw | exact Hvp].
Qed.

Theorem pkripke_kreisel_putnam_of_strongly_convergent :
  forall F, pkripke_frame_strongly_convergent F ->
    pkripke_frame_kreisel_putnam F.
Proof.
  intros F HC x y z Rxy Rxz _ _.
  exists x. repeat split.
  - apply pkripke_access_refl.
  - exact Rxy.
  - exact Rxz.
  - intros v Rxv. destruct (HC x y v Rxy Rxv) as [w [Ryw Rvw]].
    exists w. split; [exact Rvw | now left].
Qed.

Theorem ph_hilbert_kp_pkripke_sound :
  forall (Atom : Type) p,
    ph_hilbert_provable (ph_hilbert_kp Atom) p ->
    pkripke_frame_class_valid pkripke_frame_kreisel_putnam p.
Proof.
  intros Atom p Hp.
  eapply ph_hilbert_pkripke_sound; [| exact Hp].
  intros q Hq; destruct Hq; intros F HF.
  - intros V. apply pkripke_model_valid_efq.
  - now apply pkripke_KP_valid_of_condition.
Qed.

Lemma pkripke_singleton_kreisel_putnam :
  pkripke_frame_kreisel_putnam pkripke_singleton_frame.
Proof. intros [] [] [] _ _ Hnot _. exfalso. apply Hnot. exact I. Qed.

Theorem ph_hilbert_kp_consistent_via_pkripke :
  ~ ph_hilbert_provable (ph_hilbert_kp nat) PFalsum.
Proof.
  eapply ph_hilbert_consistent_of_nonempty_pkripke_class.
  - exact (@ph_hilbert_kp_pkripke_sound nat).
  - exists pkripke_singleton_frame. split.
    + exact pkripke_singleton_kreisel_putnam.
    + constructor. exact tt.
Qed.

Inductive pkripke_fork_world : Type :=
| PKF_root | PKF_left | PKF_right.

Definition pkripke_fork_access
    (x y : pkripke_fork_world) : Prop :=
  x = PKF_root \/ x = y.

Definition pkripke_fork_frame : pkripke_frame.
Proof.
  refine {| pkripke_world := pkripke_fork_world;
            pkripke_access := pkripke_fork_access |}.
  - intro x. now right.
  - intros x y z Hxy Hyz. destruct Hxy as [-> | ->].
    + now left.
    + exact Hyz.
Defined.

Lemma pkripke_fork_kreisel_putnam :
  pkripke_frame_kreisel_putnam pkripke_fork_frame.
Proof.
  intros x y z Rxy Rxz Hnyz Hnzy.
  assert (Hyroot : y <> PKF_root).
  { intro Hy. subst y. apply Hnyz. now left. }
  assert (Hzroot : z <> PKF_root).
  { intro Hz. subst z. apply Hnzy. now left. }
  assert (Hyz : y <> z).
  { intro Hyz. subst z. apply Hnyz. now right. }
  assert (Hxroot : x = PKF_root).
  { destruct x; [reflexivity | |].
    - destruct Rxy as [H | H]; [discriminate | subst y].
      destruct Rxz as [H | H]; [discriminate | subst z]. contradiction.
    - destruct Rxy as [H | H]; [discriminate | subst y].
      destruct Rxz as [H | H]; [discriminate | subst z]. contradiction. }
  subst x. destruct y; [contradiction | |]; destruct z;
    try contradiction; try (exfalso; apply Hyz; reflexivity).
  - exists PKF_root. repeat split; try (now left).
    intros v _. destruct v.
    + exists PKF_left. split; [now left | left; now right].
    + exists PKF_left. split; [now right | left; now right].
    + exists PKF_right. split; [now right | right; now right].
  - exists PKF_root. repeat split; try (now left).
    intros v _. destruct v.
    + exists PKF_right. split; [now left | left; now right].
    + exists PKF_left. split; [now right | right; now right].
    + exists PKF_right. split; [now right | left; now right].
Qed.

Lemma pkripke_fork_not_strongly_convergent :
  ~ pkripke_frame_strongly_convergent pkripke_fork_frame.
Proof.
  intro HC.
  destruct (HC PKF_root PKF_left PKF_right
    (or_introl eq_refl) (or_introl eq_refl)) as [u [HL HR]].
  destruct HL as [H | H]; [discriminate | subst u].
  destruct HR as [H | H]; discriminate.
Qed.

Theorem ph_hilbert_kp_logic_included_kc :
  ph_hilbert_logic_included (ph_hilbert_kp nat) (ph_hilbert_kc nat).
Proof.
  intros p Hp.
  eapply ph_hilbert_provable_of_provable_schema; [| exact Hp].
  intros q Hq; destruct Hq.
  - constructor. exact (ph_hilbert_kc_efq p0).
  - apply ph_hilbert_kc_pkripke_complete.
    intros F HF. apply pkripke_KP_valid_of_condition.
    now apply pkripke_kreisel_putnam_of_strongly_convergent.
Qed.

Theorem ph_hilbert_kp_strictly_included_kc :
  ph_hilbert_logic_strictly_included
    (ph_hilbert_kp nat) (ph_hilbert_kc nat).
Proof.
  split; [exact ph_hilbert_kp_logic_included_kc |].
  exists (ph_axiom_wlem (PAtom 0)). split.
  - constructor. exact (ph_hilbert_kc_wlem (PAtom 0)).
  - intro HKP. apply pkripke_fork_not_strongly_convergent.
    apply pkripke_strongly_convergent_of_WLEM_valid.
    exact (ph_hilbert_kp_pkripke_sound HKP
      pkripke_fork_kreisel_putnam).
Qed.

(** * Int is strictly below Kreisel--Putnam *)

Inductive pkripke_kp5_world : Type :=
| PKP5_root | PKP5_branch
| PKP5_atom0 | PKP5_atom1 | PKP5_atom2.

Definition pkripke_kp5_access
    (x y : pkripke_kp5_world) : Prop :=
  match x with
  | PKP5_root => True
  | PKP5_branch => y <> PKP5_root
  | PKP5_atom0 => y = PKP5_atom0
  | PKP5_atom1 => y = PKP5_atom1
  | PKP5_atom2 => y = PKP5_atom2
  end.

Definition pkripke_kp5_frame : pkripke_frame.
Proof.
  refine {| pkripke_world := pkripke_kp5_world;
            pkripke_access := pkripke_kp5_access |}.
  - intros []; cbn; try exact I; try reflexivity; discriminate.
  - intros [] [] [] Rxy Ryz; cbn in *; try contradiction; congruence.
Defined.

Definition pkripke_kp5_valuation :
    pkripke_valuation nat pkripke_kp5_frame.
Proof.
  refine (@Build_pkripke_valuation nat pkripke_kp5_frame (fun a w =>
    match a with
    | 0 => w = PKP5_atom0
    | 1 => w = PKP5_atom1
    | 2 => w = PKP5_atom2
    | _ => False
    end) _).
  intros [|[|[|a]]] [] [] Rxy Ha; cbn in *;
    try contradiction; congruence.
Defined.

Definition pkripke_kp5_model : pkripke_model nat :=
  {| pkripke_model_frame := pkripke_kp5_frame;
     pkripke_model_valuation := pkripke_kp5_valuation |}.

Lemma pkripke_kp5_refutes_KP_axiom :
  ~ pkripke_forces pkripke_kp5_model PKP5_root
      (ph_axiom_kreisel_putnam
        (PAtom 0) (PAtom 1) (PAtom 2)).
Proof.
  intro HKP.
  cbn [pkripke_kp5_model pkripke_kp5_frame
    pkripke_kp5_access ph_axiom_kreisel_putnam pneg] in HKP.
  specialize (HKP PKP5_branch I).
  assert (Hante : forall v : pkripke_kp5_world,
      v <> PKP5_root ->
      (forall u : pkripke_kp5_world,
        pkripke_kp5_access v u -> u <> PKP5_atom0) ->
      v = PKP5_atom1 \/ v = PKP5_atom2).
  { intros [] Hv Hneg; cbn in *; try contradiction.
    - exfalso. apply (Hneg PKP5_atom0); [congruence | reflexivity].
    - exfalso. apply (Hneg PKP5_atom0); [reflexivity | reflexivity].
    - now left.
    - now right. }
  specialize (HKP Hante). destruct HKP as [Hleft | Hright].
  - assert (Hba2 : pkripke_access pkripke_kp5_frame
        PKP5_branch PKP5_atom2) by (cbn; discriminate).
    specialize (Hleft PKP5_atom2 Hba2).
    assert (Hneg0 : forall u : pkripke_kp5_world,
        pkripke_kp5_access PKP5_atom2 u -> u <> PKP5_atom0).
    { intros [] Hu; cbn in Hu; congruence. }
    specialize (Hleft Hneg0). discriminate.
  - assert (Hba1 : pkripke_access pkripke_kp5_frame
        PKP5_branch PKP5_atom1) by (cbn; discriminate).
    specialize (Hright PKP5_atom1 Hba1).
    assert (Hneg0 : forall u : pkripke_kp5_world,
        pkripke_kp5_access PKP5_atom1 u -> u <> PKP5_atom0).
    { intros [] Hu; cbn in Hu; congruence. }
    specialize (Hright Hneg0). discriminate.
Qed.

Theorem ph_hilbert_int_strictly_included_kp :
  ph_hilbert_logic_strictly_included
    (ph_hilbert_int nat) (ph_hilbert_kp nat).
Proof.
  split.
  - intros p. apply ph_hilbert_provable_of_schema_inclusion.
    exact (@ph_hilbert_int_le_kp nat).
  - exists (ph_axiom_kreisel_putnam
      (PAtom 0) (PAtom 1) (PAtom 2)). split.
    + constructor. exact (ph_hilbert_kp_axiom
        (PAtom 0) (PAtom 1) (PAtom 2)).
    + intro HInt. apply pkripke_kp5_refutes_KP_axiom.
      exact (@ph_hilbert_int_pkripke_sound nat
        (ph_axiom_kreisel_putnam (PAtom 0) (PAtom 1) (PAtom 2)) HInt
        pkripke_kp5_frame I pkripke_kp5_valuation PKP5_root).
Qed.
