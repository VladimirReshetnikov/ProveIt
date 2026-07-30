(** Kreisel--Putnam propositional Kripke semantics and its strict position
    below KC.

    The frame condition is stated over the generalized preorder frames used
    by this port.  Its soundness proof follows the source argument, while a
    three-world rooted fork gives a compact strictness witness. *)

From Stdlib Require Import Lists.List Logic.Classical_Prop.
From FoundationModal Require Import
  PropositionalFormula PropositionalEntailmentAxioms
  PropositionalEntailmentMinimal PropositionalEntailmentInt
  PropositionalHilbert PropositionalConsistentTableau
  PropositionalKripke PropositionalKripkeCanonical
  PropositionalKripkeTableauCanonical.

Import ListNotations.

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

(** * Two-sided canonical KP seed *)

Definition psct_unneg {Atom : Type} (p : pformula Atom) : pformula Atom :=
  match p with
  | PImp q PFalsum => q
  | _ => PFalsum
  end.

Definition psct_common_neg {Atom : Type} {H : ph_hilbert Atom}
    (Y Z : psctableau H) (p : pformula Atom) : Prop :=
  match p with
  | PImp _ PFalsum => psct_positive Y p /\ psct_positive Z p
  | _ => False
  end.

Lemma psct_common_neg_shape :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (Y Z : psctableau H) p,
    psct_common_neg Y Z p -> p = pneg (psct_unneg p).
Proof.
  intros Atom H Y Z p. destruct p as [a| |p q|p q|p q]; cbn;
    try contradiction.
  destruct q; cbn; try contradiction. now intros.
Qed.

Lemma psct_common_neg_left :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (Y Z : psctableau H) p,
    psct_common_neg Y Z p -> psct_positive Y p.
Proof.
  intros Atom H Y Z p Hp. destruct p as [a| |p q|p q|p q]; cbn in *;
    try contradiction. destruct q; cbn in *; try contradiction. tauto.
Qed.

Lemma psct_common_neg_right :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (Y Z : psctableau H) p,
    psct_common_neg Y Z p -> psct_positive Z p.
Proof.
  intros Atom H Y Z p Hp. destruct p as [a| |p q|p q|p q]; cbn in *;
    try contradiction. destruct q; cbn in *; try contradiction. tauto.
Qed.

Lemma psct_common_neg_roundtrip :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (Y Z : psctableau H) gamma,
    pct_list_covered (psct_common_neg Y Z) gamma ->
    map (@pneg Atom) (map (@psct_unneg Atom) gamma) = gamma.
Proof.
  intros Atom H Y Z gamma Hcovered. induction gamma as [|p gamma IH].
  - reflexivity.
  - apply pct_list_covered_cons in Hcovered as [Hp Htail]. cbn.
    rewrite (psct_common_neg_shape Hp), (IH Htail). reflexivity.
Qed.

Definition psct_kp_seed {Atom : Type} {H : ph_hilbert Atom}
    (W Y Z : psctableau H) : pctableau Atom :=
  ((fun p => psct_positive W p \/ psct_common_neg Y Z p),
   (fun p => psct_negative Y p \/ psct_negative Z p)).

Theorem psct_kp_seed_consistent :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (efq : forall p, ph_hilbert_proof H (ph_axiom_efq p))
      (hkp : forall p q r,
        ph_hilbert_proof H (ph_axiom_kreisel_putnam p q r))
      (W Y Z : psctableau H),
    (forall p, psct_positive W p -> psct_positive Y p) ->
    (forall p, psct_positive W p -> psct_positive Z p) ->
    pctableau_consistent H (psct_kp_seed W Y Z).
Proof.
  intros Atom H efq hkp W Y Z HWY HWZ gamma delta Hgamma Hdelta [d].
  change (pct_list_covered
    (fun p => psct_positive W p \/ psct_common_neg Y Z p) gamma)
    in Hgamma.
  change (pct_list_covered
    (fun p => psct_negative Y p \/ psct_negative Z p) delta)
    in Hdelta.
  set (gx := fst (pct_partition (psct_positive W) gamma)).
  set (gn := snd (pct_partition (psct_positive W) gamma)).
  set (dy := fst (pct_partition (psct_negative Y) delta)).
  set (dz := snd (pct_partition (psct_negative Y) delta)).
  set (under := map (@psct_unneg Atom) gn).
  set (A := pct_disj under).
  set (B := pct_disj dy).
  set (C := pct_disj dz).
  assert (Hgx : pct_list_covered (psct_positive W) gx).
  { intros p hp. unfold gx.
    exact (pct_partition_left_holds hp). }
  assert (Hgn : pct_list_covered (psct_common_neg Y Z) gn).
  { intros p hp. unfold gn in hp.
    pose proof (pct_partition_right_origin hp) as horigin.
    destruct (Hgamma p horigin) as [hpW | hpcommon]; [|exact hpcommon].
    exact (False_rect _ (pct_partition_right_not_left hp hpW)). }
  assert (Hdy : pct_list_covered (psct_negative Y) dy).
  { intros p hp. unfold dy.
    exact (pct_partition_left_holds hp). }
  assert (Hdz : pct_list_covered (psct_negative Z) dz).
  { intros p hp. unfold dz in hp.
    pose proof (pct_partition_right_origin hp) as horigin.
    destruct (Hdelta p horigin) as [hpY | hpZ]; [|exact hpZ].
    exact (False_rect _ (pct_partition_right_not_left hp hpY)). }
  assert (Hround : map (@pneg Atom) under = gn).
  { unfold under. exact (psct_common_neg_roundtrip Hgn). }
  pose (Hm := ph_hilbert_generic_minimal H).
  pose (Hi := @ph_hilbert_generic_intuitionistic Atom H efq).
  assert (dmain : ph_hilbert_proof H
      (PImp (PAnd (pct_conj gx) (pct_conj gn)) (POr B C))).
  { pose (dconj := generic_minimal_and_to_list_conj2_append_raw Hm gx gn).
    pose (dsubset := generic_minimal_list_conj2_subset_raw Hm gamma
      (gx ++ gn) (fun p hp =>
        pct_partition_original_included (psct_positive W) hp)).
    pose (ddisj := generic_intuitionistic_list_disj2_subset_raw Hi delta
      (dy ++ dz) (fun p hp =>
        pct_partition_original_included (psct_negative Y) hp)).
    pose (dappend := generic_intuitionistic_list_disj2_append_to_or_raw
      Hi dy dz).
    unfold B, C.
    exact (ph_hilbert_imp_trans dconj
      (ph_hilbert_imp_trans dsubset
        (ph_hilbert_imp_trans d
          (ph_hilbert_imp_trans ddisj dappend)))). }
  assert (dneg_to_gn : ph_hilbert_proof H
      (PImp (pneg A) (pct_conj gn))).
  { pose proof (generic_intuitionistic_neg_disj2_to_conj2_neg_raw
      Hi under) as dx.
    change (ph_hilbert_proof H
      (PImp (pneg (pct_disj under))
        (pct_conj (map (@pneg Atom) under)))) in dx.
    rewrite Hround in dx. exact dx. }
  assert (dgn_to_neg : ph_hilbert_proof H
      (PImp (pct_conj gn) (pneg A))).
  { pose proof (generic_intuitionistic_conj2_neg_to_neg_disj2_raw
      Hi under) as dx.
    change (ph_hilbert_proof H
      (PImp (pct_conj (map (@pneg Atom) under))
        (pneg (pct_disj under)))) in dx.
    rewrite Hround in dx. exact dx. }
  assert (dpremise : ph_hilbert_proof H
      (PImp (pct_conj gx) (PImp (pneg A) (POr B C)))).
  { pose (dmap := @generic_minimal_and_map_axiom_raw
      (ph_hilbert Atom) (pformula Atom)
      (ph_hilbert_entailment Atom) (pformula_connectives Atom) H Hm
      (pct_conj gx) (pct_conj gx) (pneg A) (pct_conj gn)
      (ph_hilbert_identity H (pct_conj gx)) dneg_to_gn).
    pose (dcombined := ph_hilbert_imp_trans dmap dmain).
    exact (@generic_minimal_curry_raw
      (ph_hilbert Atom) (pformula Atom)
      (ph_hilbert_entailment Atom) (pformula_connectives Atom) H Hm
      (pct_conj gx) (pneg A) (POr B C) dcombined). }
  assert (Hpremise : psct_positive W (PImp (pneg A) (POr B C))).
  { pose (dctx := @ph_hilbert_context_of_conj2 Atom H gx
      (PImp (pneg A) (POr B C)) dpremise).
    pose (draw := @pct_list_derivation_bind_raw Atom H gx
      (generic_proof_relevant_context (psct_positive W))
      (fun p hp => GTCD_assumption (exist _ tt (Hgx p hp)))
      (PImp (pneg A) (POr B C)) dctx).
    exact (@psct_context_positive_raw Atom H W (psct_positive W)
      (fun p hp => hp) (PImp (pneg A) (POr B C)) draw). }
  pose proof (@psct_theorem_positive_raw Atom H W
    (ph_axiom_kreisel_putnam A B C) (hkp A B C)) as HKP.
  pose proof (@psct_mdp_positive Atom H W
    (PImp (pneg A) (POr B C))
    (POr (PImp (pneg A) B) (PImp (pneg A) C))
    HKP Hpremise) as Hchoice.
  destruct (proj1 (@psct_or_positive_iff Atom H W
    (PImp (pneg A) B) (PImp (pneg A) C)) Hchoice)
    as [Hleft | Hright].
  - assert (HgnY : psct_positive Y (pct_conj gn)).
    { apply (proj2 (psct_conj_positive_iff Y gn)).
      intros p hp. exact (psct_common_neg_left (Hgn p hp)). }
    pose proof (@psct_mdp_theorem_positive Atom H Y
      (pct_conj gn) (pneg A) dgn_to_neg HgnY) as HnegA.
    pose proof (@psct_mdp_positive Atom H Y (pneg A) B
      (HWY _ Hleft) HnegA) as HB.
    exact (@psct_not_both Atom H Y B
      (conj HB (proj2 (psct_disj_negative_iff Y dy) Hdy))).
  - assert (HgnZ : psct_positive Z (pct_conj gn)).
    { apply (proj2 (psct_conj_positive_iff Z gn)).
      intros p hp. exact (psct_common_neg_right (Hgn p hp)). }
    pose proof (@psct_mdp_theorem_positive Atom H Z
      (pct_conj gn) (pneg A) dgn_to_neg HgnZ) as HnegA.
    pose proof (@psct_mdp_positive Atom H Z (pneg A) C
      (HWZ _ Hright) HnegA) as HC.
    exact (@psct_not_both Atom H Z C
      (conj HC (proj2 (psct_disj_negative_iff Z dz) Hdz))).
Qed.

Definition psct_positive_union_seed {Atom : Type} {H : ph_hilbert Atom}
    (Y V : psctableau H) : pctableau Atom :=
  ((fun p => psct_positive Y p \/ psct_positive V p), fun _ => False).

Lemma psct_positive_union_extension :
  forall (Atom : Type) (K : pformula_atom_codec Atom)
      (H : ph_hilbert Atom)
      (efq : forall p, ph_hilbert_proof H (ph_axiom_efq p))
      (Y V : psctableau H),
    pctableau_consistent H (psct_positive_union_seed Y V) ->
    exists X : psctableau H,
      (forall p, psct_positive V p -> psct_positive X p) /\
      (forall p, psct_positive Y p -> psct_positive X p).
Proof.
  intros Atom K H efq Y V Hcon.
  destruct (@psct_lindenbaum Atom K H efq
    (psct_positive_union_seed Y V) Hcon) as [X Hsub].
  exists X. split; intros p Hp; apply (proj1 Hsub p).
  - now right.
  - now left.
Qed.

(** Failure of a common positive extension has one finite conjunction as a
    separating witness.  Factoring this extraction keeps the final canonical
    tail argument independent of the finite support chosen by inconsistency. *)
Lemma psct_no_positive_union_witness :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (Y V : psctableau H),
    ~ pctableau_consistent H (psct_positive_union_seed Y V) ->
    exists a, psct_positive V a /\ psct_positive Y (pneg a).
Proof.
  intros Atom H Y V Hinc.
  assert (Hex : exists gamma delta,
      pct_list_covered
        (fun p => psct_positive Y p \/ psct_positive V p) gamma /\
      pct_list_covered (fun _ : pformula Atom => False) delta /\
      ph_hilbert_provable H (PImp (pct_conj gamma) (pct_disj delta))).
  { apply NNPP. intro Hnone. apply Hinc.
    intros gamma delta Hgamma Hdelta Hproof.
    apply Hnone. now exists gamma, delta. }
  destruct Hex as [gamma [delta [Hgamma [Hdelta [d]]]]].
  apply pctableau_false_covered_nil in Hdelta. subst delta.
  set (gy := fst (pct_partition (psct_positive Y) gamma)).
  set (gv := snd (pct_partition (psct_positive Y) gamma)).
  assert (Hgy : pct_list_covered (psct_positive Y) gy).
  { intros p hp. unfold gy. exact (pct_partition_left_holds hp). }
  assert (Hgv : pct_list_covered (psct_positive V) gv).
  { intros p hp. unfold gv in hp.
    pose proof (pct_partition_right_origin hp) as horigin.
    destruct (Hgamma p horigin) as [hpY | hpV]; [|exact hpV].
    exact (False_rect _ (pct_partition_right_not_left hp hpY)). }
  set (a := pct_conj gv).
  exists a. split.
  - unfold a. now apply (proj2 (psct_conj_positive_iff V gv)).
  - pose (Hm := ph_hilbert_generic_minimal H).
    pose (dconj := generic_minimal_and_to_list_conj2_append_raw Hm gy gv).
    pose (dsubset := generic_minimal_list_conj2_subset_raw Hm gamma
      (gy ++ gv) (fun p hp =>
        pct_partition_original_included (psct_positive Y) hp)).
    pose (dand := ph_hilbert_imp_trans dconj
      (ph_hilbert_imp_trans dsubset d)).
    assert (dctxraw : ph_hilbert_proof H
        (PImp (pct_conj gy) (pneg a))).
    { unfold a. exact (@generic_minimal_curry_raw
        (ph_hilbert Atom) (pformula Atom)
        (ph_hilbert_entailment Atom) (pformula_connectives Atom) H Hm
        (pct_conj gy) (pct_conj gv) PFalsum dand). }
    pose (dctx := @ph_hilbert_context_of_conj2 Atom H gy (pneg a) dctxraw).
    pose (draw := @pct_list_derivation_bind_raw Atom H gy
      (generic_proof_relevant_context (psct_positive Y))
      (fun p hp => GTCD_assumption (exist _ tt (Hgy p hp)))
      (pneg a) dctx).
    exact (@psct_context_positive_raw Atom H Y (psct_positive Y)
      (fun p hp => hp) (pneg a) draw).
Qed.

Theorem psct_canonical_frame_kreisel_putnam :
  forall (Atom : Type) (K : pformula_atom_codec Atom)
      (H : ph_hilbert Atom)
      (efq : forall p, ph_hilbert_proof H (ph_axiom_efq p))
      (hkp : forall p q r,
        ph_hilbert_proof H (ph_axiom_kreisel_putnam p q r)),
    pkripke_frame_kreisel_putnam (psct_canonical_frame H).
Proof.
  intros Atom K H efq hkp W Y Z HWY HWZ _ _.
  destruct (@psct_lindenbaum Atom K H efq (psct_kp_seed W Y Z)
    (@psct_kp_seed_consistent Atom H efq hkp W Y Z HWY HWZ))
    as [U Hsub].
  exists U. repeat split.
  - intros p Hp. apply (proj1 Hsub p). now left.
  - intros p Hp.
    apply (proj1 (psct_not_negative_iff_positive Y p)). intro Hpn.
    exact (@psct_not_both Atom H U p
      (conj Hp (proj2 Hsub p (or_introl Hpn)))).
  - intros p Hp.
    apply (proj1 (psct_not_negative_iff_positive Z p)). intro Hpn.
    exact (@psct_not_both Atom H U p
      (conj Hp (proj2 Hsub p (or_intror Hpn)))).
  - intros V HUV.
    destruct (classic
      (pctableau_consistent H (psct_positive_union_seed Y V))) as [HYV | HnYV].
    + destruct (@psct_positive_union_extension Atom K H efq Y V HYV)
        as [X [HVX HYX]].
      exists X. split; [exact HVX | now left].
    + destruct (classic
        (pctableau_consistent H (psct_positive_union_seed Z V))) as [HZV | HnZV].
      * destruct (@psct_positive_union_extension Atom K H efq Z V HZV)
          as [X [HVX HZX]].
        exists X. split; [exact HVX | now right].
      * destruct (@psct_no_positive_union_witness Atom H Y V HnYV)
          as [a [HaV HnaY]].
        destruct (@psct_no_positive_union_witness Atom H Z V HnZV)
          as [b [HbV HnbZ]].
        assert (HnabY : psct_positive Y (pneg (PAnd a b))).
        { eapply (@psct_mdp_theorem_positive Atom H Y).
          - exact (generic_minimal_contraposition_raw
              (ph_hilbert_generic_minimal H) (PAnd a b) a
              (PHPAndElimL a b)).
          - exact HnaY. }
        assert (HnabZ : psct_positive Z (pneg (PAnd a b))).
        { eapply (@psct_mdp_theorem_positive Atom H Z).
          - exact (generic_minimal_contraposition_raw
              (ph_hilbert_generic_minimal H) (PAnd a b) b
              (PHPAndElimR a b)).
          - exact HnbZ. }
        assert (Hcommon : psct_common_neg Y Z (pneg (PAnd a b))).
        { cbn. now split. }
        pose proof (proj1 Hsub (pneg (PAnd a b)) (or_intror Hcommon))
          as HnegU.
        pose proof (HUV (pneg (PAnd a b)) HnegU) as HnegV.
        pose proof (proj2 (@psct_and_positive_iff Atom H V a b)
          (conj HaV HbV)) as HabV.
        pose proof (@psct_neg_positive_implies_negative Atom H V
          (PAnd a b) HnegV) as HabN.
        exfalso. exact (@psct_not_both Atom H V (PAnd a b)
          (conj HabV HabN)).
Qed.

(** The canonical construction is reusable for any Hilbert calculus that has
    raw EFQ and Kreisel--Putnam proofs; no schema datatype or proof-irrelevance
    premise is involved. *)
Theorem ph_hilbert_pkripke_kp_complete_of_axioms :
  forall (Atom : Type) (K : pformula_atom_codec Atom)
      (H : ph_hilbert Atom)
      (efq : forall p, ph_hilbert_proof H (ph_axiom_efq p))
      (hkp : forall p q r,
        ph_hilbert_proof H (ph_axiom_kreisel_putnam p q r)),
    pkripke_complete H pkripke_frame_kreisel_putnam.
Proof.
  intros Atom K H efq hkp.
  apply (@ph_hilbert_pkripke_complete_of_psct_canonical
    Atom K H efq pkripke_frame_kreisel_putnam).
  exact (@psct_canonical_frame_kreisel_putnam Atom K H efq hkp).
Qed.

Theorem ph_hilbert_kp_pkripke_complete_of_codec :
  forall (Atom : Type) (K : pformula_atom_codec Atom),
    pkripke_complete (ph_hilbert_kp Atom)
      pkripke_frame_kreisel_putnam.
Proof.
  intros Atom K.
  exact (@ph_hilbert_pkripke_kp_complete_of_axioms Atom K
    (ph_hilbert_kp Atom) (@ph_hilbert_kp_efq Atom)
    (@ph_hilbert_kp_axiom Atom)).
Qed.

Theorem ph_hilbert_kp_pkripke_complete :
  pkripke_complete (ph_hilbert_kp nat)
    pkripke_frame_kreisel_putnam.
Proof.
  exact (@ph_hilbert_kp_pkripke_complete_of_codec nat pki_nat_codec).
Qed.

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

Theorem ph_hilbert_kp_pkripke_sound_complete :
  forall p : pformula nat,
    ph_hilbert_provable (ph_hilbert_kp nat) p <->
    pkripke_frame_class_valid pkripke_frame_kreisel_putnam p.
Proof.
  intro p; split.
  - apply ph_hilbert_kp_pkripke_sound.
  - apply ph_hilbert_kp_pkripke_complete.
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
