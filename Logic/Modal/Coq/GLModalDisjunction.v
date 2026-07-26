(**
  The modal disjunction property of GL.

  This file ports the mathematical surface of the pinned Foundation module
  [Modal/Kripke/Logic/GL/MDP.lean].  Given two finite rooted GL models, its
  central construction forms their disjoint union and adds one fresh root
  below every old world.  The two inclusions are bounded morphisms, so truth
  at all old worlds is unchanged.  Combining countermodels in this way
  proves the boxed finite-context disjunction lemma and hence GL's modal
  disjunction property.

  Foundation obtains finiteness through type classes.  Here it is witnessed
  by an explicit list containing the fresh root followed by the two mapped
  source covers.  The final step reuses the separately checked port of the
  source's preceding unnecessitation theorem.
*)

From Stdlib Require Import Lists.List.
From Stdlib Require Import Logic.Classical_Prop.
From FoundationModal Require Import
  Syntax HilbertK Kripke Preservation Filtration Correspondence
  FrameProperties Root NormalHilbert CanonicalExtensions FiniteMaximalContext
  FiniteCanonicalSupport LogicInfrastructure GLGrzDerivations CanonicalGL
  FrameTransformations GLUnnecessitation.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * The fresh-root coproduct frame *)

Inductive mdp_counterexample_world (F1 F2 : frame) : Type :=
| mdp_fresh_root
| mdp_left_world : World F1 -> mdp_counterexample_world F1 F2
| mdp_right_world : World F2 -> mdp_counterexample_world F1 F2.

Arguments mdp_fresh_root {F1 F2}.
Arguments mdp_left_world {F1 F2} _.
Arguments mdp_right_world {F1 F2} _.

Definition mdp_counterexample_frame (F1 F2 : frame) : frame :=
  {| World := mdp_counterexample_world F1 F2;
     Rel := fun x y =>
       match x, y with
       | mdp_left_world u, mdp_left_world v => Rel F1 u v
       | mdp_right_world u, mdp_right_world v => Rel F2 u v
       | mdp_fresh_root, mdp_left_world _ => True
       | mdp_fresh_root, mdp_right_world _ => True
       | _, _ => False
       end |}.

Arguments mdp_counterexample_frame F1 F2 : clear implicits.

Definition mdp_counterexample_root (F1 F2 : frame)
    : World (mdp_counterexample_frame F1 F2) := mdp_fresh_root.

Arguments mdp_counterexample_root F1 F2 : clear implicits.

Lemma mdp_counterexample_frame_asymmetric :
  forall F1 F2,
    frame_asymmetric F1 -> frame_asymmetric F2 ->
    frame_asymmetric (mdp_counterexample_frame F1 F2).
Proof.
  intros F1 F2 H1 H2 x y Hxy;
    destruct x, y; simpl in *; try contradiction; try tauto.
  - now apply (H1 w w0).
  - now apply (H2 w w0).
Qed.

Lemma mdp_counterexample_frame_irreflexive :
  forall F1 F2,
    frame_irreflexive F1 -> frame_irreflexive F2 ->
    frame_irreflexive (mdp_counterexample_frame F1 F2).
Proof.
  intros F1 F2 H1 H2 x; destruct x; simpl.
  - tauto.
  - apply H1.
  - apply H2.
Qed.

Lemma mdp_counterexample_frame_transitive :
  forall F1 F2,
    frame_transitive F1 -> frame_transitive F2 ->
    frame_transitive (mdp_counterexample_frame F1 F2).
Proof.
  intros F1 F2 H1 H2 x y z Hxy Hyz;
    destruct x, y, z; simpl in *; try contradiction; try tauto.
  - eapply H1; eauto.
  - eapply H2; eauto.
Qed.

Lemma mdp_counterexample_root_is_root :
  forall F1 F2,
    frame_root (mdp_counterexample_frame F1 F2)
      (mdp_counterexample_root F1 F2).
Proof.
  intros F1 F2 x Hneq. destruct x; simpl; [contradiction | tauto | tauto].
Qed.

Theorem mdp_counterexample_frame_point_rooted :
  forall F1 F2,
    frame_point_rooted (mdp_counterexample_frame F1 F2).
Proof.
  intros F1 F2. exists (mdp_counterexample_root F1 F2); split.
  - apply mdp_counterexample_root_is_root.
  - intros r Hr. destruct r; [reflexivity | |].
    + exfalso. specialize (Hr (mdp_fresh_root :
        World (mdp_counterexample_frame F1 F2))).
      simpl in Hr. apply Hr. discriminate.
    + exfalso. specialize (Hr (mdp_fresh_root :
        World (mdp_counterexample_frame F1 F2))).
      simpl in Hr. apply Hr. discriminate.
Qed.

Definition mdp_counterexample_cover {F1 F2 : frame}
    (xs : list (World F1)) (ys : list (World F2))
    : list (World (mdp_counterexample_frame F1 F2)) :=
  mdp_fresh_root :: map mdp_left_world xs ++ map mdp_right_world ys.

Lemma mdp_counterexample_cover_complete :
  forall F1 F2 (xs : list (World F1)) (ys : list (World F2)),
    (forall x, In x xs) -> (forall y, In y ys) ->
    forall z, In z (mdp_counterexample_cover xs ys).
Proof.
  intros F1 F2 xs ys Hxs Hys z. destruct z; simpl.
  - now left.
  - right. apply in_or_app; left. now apply in_map.
  - right. apply in_or_app; right. now apply in_map.
Qed.

Theorem mdp_counterexample_frame_finite :
  forall F1 F2,
    finite_frame F1 -> finite_frame F2 ->
    finite_frame (mdp_counterexample_frame F1 F2).
Proof.
  intros F1 F2 [xs Hxs] [ys Hys].
  exists (mdp_counterexample_cover xs ys).
  now apply mdp_counterexample_cover_complete.
Qed.

(** The old components embed as generated subframes. *)
Definition mdp_left_p_morphism (F1 F2 : frame) :
    p_morphism F1 (mdp_counterexample_frame F1 F2).
Proof.
  refine {| pmap := fun x : World F1 =>
                       (@mdp_left_world F1 F2 x :
                         World (mdp_counterexample_frame F1 F2)) |}.
  - intros x y Hxy. exact Hxy.
  - intros x z Hxz. destruct z; simpl in Hxz; try contradiction.
    exists w; split; [reflexivity | exact Hxz].
Defined.

Arguments mdp_left_p_morphism F1 F2 : clear implicits.

Definition mdp_right_p_morphism (F1 F2 : frame) :
    p_morphism F2 (mdp_counterexample_frame F1 F2).
Proof.
  refine {| pmap := fun x : World F2 =>
                       (@mdp_right_world F1 F2 x :
                         World (mdp_counterexample_frame F1 F2)) |}.
  - intros x y Hxy. exact Hxy.
  - intros x z Hxz. destruct z; simpl in Hxz; try contradiction.
    exists w; split; [reflexivity | exact Hxz].
Defined.

Arguments mdp_right_p_morphism F1 F2 : clear implicits.

(** A successor of the fresh root lies either at an old root or strictly
    above that root in the corresponding component. *)
Lemma mdp_through_original_root :
  forall F1 F2 (r1 : World F1) (r2 : World F2),
    frame_root F1 r1 -> frame_root F2 r2 ->
    forall x,
      Rel (mdp_counterexample_frame F1 F2)
        (mdp_counterexample_root F1 F2) x ->
      (x = mdp_left_world r1 \/
       Rel (mdp_counterexample_frame F1 F2) (mdp_left_world r1) x) \/
      (x = mdp_right_world r2 \/
       Rel (mdp_counterexample_frame F1 F2) (mdp_right_world r2) x).
Proof.
  intros F1 F2 r1 r2 Hr1 Hr2 x Hroot. destruct x; simpl in Hroot.
  - contradiction.
  - left. destruct (classic (w = r1)) as [-> | Hneq].
    + now left.
    + right. apply Hr1. exact Hneq.
  - right. destruct (classic (w = r2)) as [-> | Hneq].
    + now left.
    + right. apply Hr2. exact Hneq.
Qed.

(** * The combined valuation and truth on old worlds *)

Definition mdp_counterexample_valuation {AtomType : Type}
    {F1 F2 : frame} (V1 : valuation AtomType F1)
    (V2 : valuation AtomType F2)
    : valuation AtomType (mdp_counterexample_frame F1 F2) :=
  fun a x =>
    match x with
    | mdp_fresh_root => True
    | mdp_left_world u => V1 a u
    | mdp_right_world v => V2 a v
    end.

Lemma mdp_left_truth :
  forall (AtomType : Type) F1 F2
         (V1 : valuation AtomType F1) (V2 : valuation AtomType F2)
         x (p : formula AtomType),
    satisfies F1 V1 x p <->
    satisfies (mdp_counterexample_frame F1 F2)
      (mdp_counterexample_valuation V1 V2) (mdp_left_world x) p.
Proof.
  intros AtomType F1 F2 V1 V2 x p.
  exact (p_morphism_truth (mdp_left_p_morphism F1 F2)
    (mdp_counterexample_valuation V1 V2) x p).
Qed.

Lemma mdp_right_truth :
  forall (AtomType : Type) F1 F2
         (V1 : valuation AtomType F1) (V2 : valuation AtomType F2)
         x (p : formula AtomType),
    satisfies F2 V2 x p <->
    satisfies (mdp_counterexample_frame F1 F2)
      (mdp_counterexample_valuation V1 V2) (mdp_right_world x) p.
Proof.
  intros AtomType F1 F2 V1 V2 x p.
  exact (p_morphism_truth (mdp_right_p_morphism F1 F2)
    (mdp_counterexample_valuation V1 V2) x p).
Qed.

(** * Modal disjunction *)

Lemma GL_MDP_boxed_antecedent :
  forall c p q : formula nat,
    GL_proves (Imp (Box c) (Or (Box p) (Box q))) ->
    GL_proves (Imp (Box c) (Box p)) \/
    GL_proves (Imp (Box c) (Box q)).
Proof.
  intros c p q Hdisj.
  destruct (classic (GL_proves (Imp (Box c) (Box p)))) as [Hp | Hnp];
    [now left |].
  destruct (classic (GL_proves (Imp (Box c) (Box q)))) as [Hq | Hnq];
    [now right |].
  exfalso.
  assert (Hnp_plain : ~ GL_proves (Imp (Boxdot c) p)).
  { intro Hplain. apply Hnp.
    now apply GL_proves_box_box_of_boxdot_plain. }
  assert (Hnq_plain : ~ GL_proves (Imp (Boxdot c) q)).
  { intro Hplain. apply Hnq.
    now apply GL_proves_box_box_of_boxdot_plain. }
  apply (proj1 (GL_unprovable_iff_exists_finite_rooted_countermodel
    (Imp (Boxdot c) p))) in Hnp_plain.
  apply (proj1 (GL_unprovable_iff_exists_finite_rooted_countermodel
    (Imp (Boxdot c) q))) in Hnq_plain.
  destruct Hnp_plain as
    [F1 [V1 [r1 [Hfin1 [Htrans1 [Hirr1 [Hroot1 Hcounter1]]]]]]].
  destruct Hnq_plain as
    [F2 [V2 [r2 [Hfin2 [Htrans2 [Hirr2 [Hroot2 Hcounter2]]]]]]].
  set (F0 := mdp_counterexample_frame F1 F2).
  set (V0 := mdp_counterexample_valuation V1 V2).
  set (r0 := mdp_counterexample_root F1 F2).
  assert (Hboxdot1 : satisfies F1 V1 r1 (Boxdot c)).
  { apply NNPP. intro Hnot. apply Hcounter1. simpl. tauto. }
  assert (Hnotp : ~ satisfies F1 V1 r1 p).
  { intro Hsat. apply Hcounter1. simpl. tauto. }
  assert (Hboxdot2 : satisfies F2 V2 r2 (Boxdot c)).
  { apply NNPP. intro Hnot. apply Hcounter2. simpl. tauto. }
  assert (Hnotq : ~ satisfies F2 V2 r2 q).
  { intro Hsat. apply Hcounter2. simpl. tauto. }
  assert (Hboxc : satisfies F0 V0 r0 (Box c)).
  { intros x Hrx.
    destruct (@mdp_through_original_root F1 F2 r1 r2
      Hroot1 Hroot2 x Hrx) as [[-> | Hsucc] | [-> | Hsucc]].
    - apply (proj1 (mdp_left_truth V1 V2 r1 c)).
      exact (proj1 (proj1 (@satisfies_and nat F1 V1 r1 c (Box c))
        Hboxdot1)).
    - destruct x; simpl in Hsucc; try contradiction.
      apply (proj1 (mdp_left_truth V1 V2 w c)).
      exact ((proj2 (proj1 (@satisfies_and nat F1 V1 r1 c (Box c))
        Hboxdot1)) w Hsucc).
    - apply (proj1 (mdp_right_truth V1 V2 r2 c)).
      exact (proj1 (proj1 (@satisfies_and nat F2 V2 r2 c (Box c))
        Hboxdot2)).
    - destruct x; simpl in Hsucc; try contradiction.
      apply (proj1 (mdp_right_truth V1 V2 w c)).
      exact ((proj2 (proj1 (@satisfies_and nat F2 V2 r2 c (Box c))
        Hboxdot2)) w Hsucc). }
  assert (Hnotboxp : ~ satisfies F0 V0 r0 (Box p)).
  { intro Hboxp. apply Hnotp.
    apply (proj2 (mdp_left_truth V1 V2 r1 p)).
    apply Hboxp. simpl. tauto. }
  assert (Hnotboxq : ~ satisfies F0 V0 r0 (Box q)).
  { intro Hboxq. apply Hnotq.
    apply (proj2 (mdp_right_truth V1 V2 r2 q)).
    apply Hboxq. simpl. tauto. }
  assert (Hsound := GL_proves_sound_on_transitive_cwf_frame
    (F := F0) (p := Imp (Box c) (Or (Box p) (Box q)))).
  specialize (Hsound
    (mdp_counterexample_frame_transitive Htrans1 Htrans2)).
  specialize (Hsound
    (finite_transitive_irreflexive_cwf
      (mdp_counterexample_frame_finite Hfin1 Hfin2)
      (mdp_counterexample_frame_transitive Htrans1 Htrans2)
      (mdp_counterexample_frame_irreflexive Hirr1 Hirr2))).
  specialize (Hsound Hdisj V0 r0).
  pose proof (Hsound Hboxc) as Hor.
  apply (proj1 (@satisfies_or nat F0 V0 r0 (Box p) (Box q))) in Hor.
  tauto.
Qed.

(** * Finite support and contextual modal disjunction *)

(** Every contextual derivation uses only finitely many assumptions.  This
    generic result follows the derivation tree and is useful independently
    of GL.  The extracted list need not be duplicate-free: [finite_theory]
    interprets it extensionally, so multiplicity is immaterial. *)
Lemma normal_derives_finite_support :
  forall Ax (Gamma : theory nat) p,
    normal_derives Ax Gamma p ->
    exists Delta : list (formula nat),
      (forall q, In q Delta -> Gamma q) /\
      normal_derives Ax (finite_theory Delta) p.
Proof.
  intros Ax Gamma p Hder.
  induction Hder as
    [p Hp | p Hp | p q Hpq IHpq Hp IHp].
  - exists [p]. split.
    + intros r [-> | []]. exact Hp.
    + apply ND_assumption. simpl. now left.
  - exists []. split.
    + intros r Hr. contradiction.
    + apply ND_theorem. exact Hp.
  - destruct IHpq as [Delta1 [Hsub1 Hder1]].
    destruct IHp as [Delta2 [Hsub2 Hder2]].
    exists (Delta1 ++ Delta2). split.
    + intros r Hr. apply in_app_or in Hr.
      destruct Hr as [Hr | Hr]; [now apply Hsub1 | now apply Hsub2].
    + eapply ND_mp.
      * eapply normal_derives_finite_weaken; [|exact Hder1].
        intros r Hr. apply in_or_app. now left.
      * eapply normal_derives_finite_weaken; [|exact Hder2].
        intros r Hr. apply in_or_app. now right.
Qed.

(** The finite-list core of Foundation's [MDP_Aux]. *)

Lemma GL_derives_own_list_conjunction :
  forall Gamma : list (formula nat),
    normal_derives schema_L (finite_theory Gamma)
      (logic_list_conj Gamma).
Proof.
  intro Gamma; induction Gamma as [|p Gamma IH].
  - cbn [logic_list_conj]. apply ND_theorem.
    exact (logic_mem_top GL_classical_logic).
  - simpl. assert (Hp : normal_derives schema_L
      (finite_theory (p :: Gamma)) p).
    { apply ND_assumption. simpl. now left. }
    assert (Hrest : normal_derives schema_L
      (finite_theory (p :: Gamma)) (logic_list_conj Gamma)).
    { eapply normal_derives_weaken; [|exact IH].
      intros x Hx. simpl. now right. }
    eapply ND_mp; [|exact Hrest].
    eapply ND_mp; [|exact Hp].
    apply ND_theorem.
    apply (logic_classical_tautology GL_classical_logic).
    intro rho. unfold And, Neg; simpl; tauto.
Qed.

Lemma GL_derives_boxed_list_conjunction :
  forall Gamma : list (formula nat),
    normal_derives schema_L
      (finite_theory (formula_list_box Gamma))
      (Box (logic_list_conj Gamma)).
Proof.
  intro Gamma. apply normal_derives_finite_box.
  apply GL_derives_own_list_conjunction.
Qed.

Lemma GL_finite_boxed_context_to_implication :
  forall (Gamma : list (formula nat)) (p : formula nat),
    normal_derives schema_L
      (finite_theory (formula_list_box Gamma)) p ->
    GL_proves (Imp (Box (logic_list_conj Gamma)) p).
Proof.
  intros Gamma p Hder.
  apply (proj1 (normal_derives_empty_iff schema_L
    (Imp (Box (logic_list_conj Gamma)) p))).
  apply normal_derives_deduction.
  eapply normal_derives_context_cut; [|exact Hder].
  intros z Hz. unfold finite_theory in Hz.
  unfold formula_list_box in Hz. apply in_map_iff in Hz.
  destruct Hz as [a [Hz Ha]]. subst z.
  eapply (@ND_mp schema_L _
    (Box (logic_list_conj Gamma)) (Box a)).
  - apply ND_theorem. apply logic_box_regularity; [exact GL_normal_logic |].
    apply (logic_classical_tautology GL_classical_logic).
    intro rho. change
      (classical_eval rho (logic_list_conj Gamma) -> classical_eval rho a).
    intro Hall. apply (proj1 (classical_eval_list_conj rho Gamma)) in Hall.
    rewrite Forall_forall in Hall. now apply Hall.
  - apply ND_assumption. now left.
Qed.

Theorem GL_MDP_Aux_finite :
  forall (Gamma : list (formula nat)) p q,
    normal_derives schema_L
      (finite_theory (formula_list_box Gamma))
      (Or (Box p) (Box q)) ->
    normal_derives schema_L
      (finite_theory (formula_list_box Gamma)) (Box p) \/
    normal_derives schema_L
      (finite_theory (formula_list_box Gamma)) (Box q).
Proof.
  intros Gamma p q Hdisj.
  pose proof (GL_finite_boxed_context_to_implication
    (Gamma := Gamma) (p := Or (Box p) (Box q)) Hdisj) as Htheorem.
  destruct (GL_MDP_boxed_antecedent Htheorem) as [Hp | Hq].
  - left. eapply ND_mp; [apply ND_theorem; exact Hp |].
    apply GL_derives_boxed_list_conjunction.
  - right. eapply ND_mp; [apply ND_theorem; exact Hq |].
    apply GL_derives_boxed_list_conjunction.
Qed.

(** Foundation's exact arbitrary-context surface.  Finite support first
    selects a list [Delta] of boxed assumptions.  Unboxing [Delta] supplies
    the finite context required above, and the selected disjunct is then
    weakened back to the original boxed theory. *)
Theorem GL_MDP_Aux :
  forall (X : theory nat) p q,
    normal_derives schema_L (boxed_theory X)
      (Or (Box p) (Box q)) ->
    normal_derives schema_L (boxed_theory X) (Box p) \/
    normal_derives schema_L (boxed_theory X) (Box q).
Proof.
  intros X p q Hdisj.
  destruct (normal_derives_finite_support Hdisj)
    as [Delta [HDelta Hfinite]].
  assert (Hsupport :
    list_subset Delta
      (formula_list_box (formula_list_unbox Delta))).
  { intros z Hz.
    specialize (HDelta z Hz).
    destruct HDelta as [a [Ha Hzbox]]. subst z.
    apply formula_list_box_member.
    apply (proj2 (formula_list_unbox_spec Delta a)).
    exact Hz. }
  pose proof (normal_derives_finite_weaken Hsupport Hfinite)
    as Hfinite_disj.
  destruct (GL_MDP_Aux_finite Hfinite_disj) as [Hp | Hq].
  - left. eapply normal_derives_weaken; [|exact Hp].
    intros z Hz. unfold finite_theory, formula_list_box in Hz.
    apply in_map_iff in Hz. destruct Hz as [a [Hz Ha]]. subst z.
    apply HDelta.
    apply (proj1 (formula_list_unbox_spec Delta a)). exact Ha.
  - right. eapply normal_derives_weaken; [|exact Hq].
    intros z Hz. unfold finite_theory, formula_list_box in Hz.
    apply in_map_iff in Hz. destruct Hz as [a [Hz Ha]]. subst z.
    apply HDelta.
    apply (proj1 (formula_list_unbox_spec Delta a)). exact Ha.
Qed.

(** Source-facing alias. *)
Definition MDP_Aux := GL_MDP_Aux.

Definition modal_disjunctive (L : formula nat -> Prop) : Prop :=
  forall p q : formula nat,
    L (Or (Box p) (Box q)) -> L p \/ L q.

Theorem GL_modal_disjunction :
  forall p q : formula nat,
    GL_proves (Or (Box p) (Box q)) -> GL_proves p \/ GL_proves q.
Proof.
  intros p q Hdisj.
  assert (Hctx : normal_derives schema_L
      (finite_theory (formula_list_box []))
      (Or (Box p) (Box q))).
  { simpl. apply ND_theorem. exact Hdisj. }
  destruct (GL_MDP_Aux_finite Hctx) as [Hp | Hq].
  - left. apply GL_unnecessitation.
    apply (proj1 (normal_derives_empty_iff schema_L (Box p))).
    simpl in Hp. exact Hp.
  - right. apply GL_unnecessitation.
    apply (proj1 (normal_derives_empty_iff schema_L (Box q))).
    simpl in Hq. exact Hq.
Qed.

Theorem GL_modal_disjunctive : modal_disjunctive (@GL_proves nat).
Proof. exact GL_modal_disjunction. Qed.

Definition GL_modal_disjunctive_instance := GL_modal_disjunctive.
