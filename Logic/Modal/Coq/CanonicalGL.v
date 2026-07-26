(**
  Finite mini-canonical completeness for GL.

  This module ports the active theorem surface of Foundation's pinned
  [Modal/Kripke/Logic/GL/Completeness.lean].  Its worlds are the finite,
  complement-closed consistent contexts for the subformulas of the target
  formula.  The accessibility relation remembers both [q] and [Box q] at
  successors and requires one genuinely new boxed formula.  Consequently it
  is transitive and irreflexive by construction, rather than by filtration.

  The only specifically GL proof-theoretic ingredients are Loeb's axiom and
  its derived Four law, supplied by [GLGrzDerivations].  In the successor-
  consistency argument Four replays every twice-boxed finite premise in the
  predecessor context.  No GL completeness theorem or conditional Boxdot
  result is used.
*)

From Stdlib Require Import Lists.List.
From Stdlib Require Import Logic.ClassicalDescription Logic.Classical_Prop.
From FoundationModal Require Import
  Syntax Complement Axioms HilbertK Kripke Filtration Correspondence Loeb
  FrameProperties NormalHilbert CanonicalExtensions FiniteMaximalContext
  GLGrzDerivations Root.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * The finite mini-canonical frame *)

Definition gl_box_core (target : formula nat)
    (X : finite_maximal_context schema_L (subformulas target))
    : theory nat :=
  fun r =>
    exists q,
      In (Box q) (subformulas target) /\
      fmc_mem X (Box q) /\
      (r = q \/ r = Box q).

Arguments gl_box_core target X r : clear implicits.

Definition gl_core_items (target : formula nat)
    (X : finite_maximal_context schema_L (subformulas target))
    : list (formula nat) :=
  flat_map
    (fun r =>
      match r with
      | Box q =>
          if fmc_mem_dec X (Box q) then [q; Box q] else []
      | _ => []
      end)
    (subformulas target).

Arguments gl_core_items target X : clear implicits.

Lemma gl_core_items_intro :
  forall target
    (X : finite_maximal_context schema_L (subformulas target)) q,
    In (Box q) (subformulas target) ->
    fmc_mem X (Box q) ->
    In q (gl_core_items target X) /\
    In (Box q) (gl_core_items target X).
Proof.
  intros target X q Hsub Hmem. unfold gl_core_items.
  destruct (fmc_mem_dec X (Box q)) as [Hyes | Hno].
  - split.
    + apply in_flat_map. exists (Box q). split; [exact Hsub |].
      simpl. destruct (fmc_mem_dec X (Box q)); simpl; auto; contradiction.
    + apply in_flat_map. exists (Box q). split; [exact Hsub |].
      simpl. destruct (fmc_mem_dec X (Box q)); simpl; auto; contradiction.
  - contradiction.
Qed.

Lemma gl_core_items_elim :
  forall target
    (X : finite_maximal_context schema_L (subformulas target)) r,
    In r (gl_core_items target X) -> gl_box_core target X r.
Proof.
  intros target X r Hr. unfold gl_core_items in Hr.
  apply in_flat_map in Hr.
  destruct Hr as [s [Hsub Hr]].
  destruct s as [a | | s t | q]; simpl in Hr; try contradiction.
  destruct (fmc_mem_dec X (Box q)) as [Hmem | Hnot];
    simpl in Hr; try contradiction.
  destruct Hr as [Hr | [Hr | []]].
  - subst r. exists q. repeat split; auto.
  - subst r. exists q. repeat split; auto.
Qed.

Definition gl_successor_seed (target : formula nat)
    (X : finite_maximal_context schema_L (subformulas target))
    (q : formula nat) : list (formula nat) :=
  complement q :: Box q :: gl_core_items target X.

Arguments gl_successor_seed target X q : clear implicits.

Lemma gl_box_subformula_content :
  forall target q : formula nat,
    In (Box q) (subformulas target) -> In q (subformulas target).
Proof.
  intros target q Hbox.
  eapply subformulas_trans; [exact Hbox |].
  apply subformulas_box. apply subformulas_self.
Qed.

Lemma gl_successor_seed_subset :
  forall target
    (X : finite_maximal_context schema_L (subformulas target)) q,
    In (Box q) (subformulas target) ->
    list_subset (gl_successor_seed target X q)
      (complementary (subformulas target)).
Proof.
  intros target X q Hbox r Hr.
  unfold gl_successor_seed in Hr. simpl in Hr.
  destruct Hr as [Hr | [Hr | Hr]].
  - subst r. apply complementary_comp.
    now apply gl_box_subformula_content in Hbox.
  - subst r. now apply complementary_mem.
  - apply gl_core_items_elim in Hr.
    destruct Hr as [s [Hsbox [_ [Hr | Hr]]]].
    + subst r. apply complementary_mem.
      now apply gl_box_subformula_content in Hsbox.
    + subst r. now apply complementary_mem.
Qed.

Lemma gl_successor_seed_included :
  forall target
    (X : finite_maximal_context schema_L (subformulas target)) q,
    theory_included
      (finite_theory (gl_successor_seed target X q))
      (theory_insert
        (theory_insert (gl_box_core target X) (Box q))
        (complement q)).
Proof.
  intros target X q r Hr.
  unfold finite_theory, gl_successor_seed in Hr. simpl in Hr.
  destruct Hr as [Hr | [Hr | Hr]].
  - subst r. now left.
  - subst r. right. now left.
  - right. right. now apply gl_core_items_elim.
Qed.

(** A boxed derivation from the core can be replayed in [X].  Core formulas
    occur in pairs [q, Box q], so after contextual necessitation its
    assumptions are [Box q] and [Box (Box q)].  The former belongs to [X]
    and the latter follows from it by GL's derived Four. *)
Lemma gl_boxed_core_derivable_in_predecessor :
  forall target
    (X : finite_maximal_context schema_L (subformulas target)) r,
    normal_derives schema_L (boxed_theory (gl_box_core target X)) r ->
    normal_derives schema_L (fmc_mem X) r.
Proof.
  intros target X r Hder. induction Hder as
    [r Hr | r Hr | p q Hpq IHpq Hp IHp].
  - destruct Hr as [s [Hs ->]].
    destruct Hs as [q [Hsub [Hmem [-> | ->]]]].
    + now apply ND_assumption.
    + eapply ND_mp.
      * apply ND_theorem. apply GL_proves_Four.
      * now apply ND_assumption.
  - now apply ND_theorem.
  - eapply ND_mp; eauto.
Qed.

Lemma gl_successor_seed_consistent :
  forall target
    (X : finite_maximal_context schema_L (subformulas target)) q,
    In (Box q) (subformulas target) ->
    ~ fmc_mem X (Box q) ->
    finite_consistent schema_L (gl_successor_seed target X q).
Proof.
  intros target X q Hbox Hnot.
  unfold finite_consistent, normal_theory_consistent. intro Hbottom.
  pose proof (@normal_derives_weaken schema_L
    (finite_theory (gl_successor_seed target X q))
    (theory_insert
      (theory_insert (gl_box_core target X) (Box q))
      (complement q)) Bottom
    (@gl_successor_seed_included target X q) Hbottom) as Hseed.
  pose proof (@normal_derives_deduction schema_L
    (theory_insert (gl_box_core target X) (Box q))
    (complement q) Bottom Hseed) as Hnegcomp.
  pose proof (normal_derives_of_neg_complement Hnegcomp) as Hq.
  pose proof (@normal_derives_deduction schema_L
    (gl_box_core target X) (Box q) q Hq) as Hstep.
  pose proof (normal_derives_boxed Hstep) as Hboxed_step.
  pose proof (gl_boxed_core_derivable_in_predecessor
    Hboxed_step) as HXboxed_step.
  assert (HXbox : normal_derives schema_L (fmc_mem X) (Box q)).
  { eapply ND_mp; [|exact HXboxed_step].
    apply ND_theorem. apply GL_proves_L. }
  apply Hnot.
  apply (proj2 (@fmc_membership_iff_derivable schema_L
    (subformulas target) X (Box q) Hbox)).
  exact HXbox.
Qed.

Definition gl_mini_relation (target : formula nat)
    (X Y : finite_maximal_context schema_L (subformulas target)) : Prop :=
  (forall q,
      In (Box q) (subformulas target) ->
      fmc_mem X (Box q) ->
      fmc_mem Y q /\ fmc_mem Y (Box q)) /\
  exists q,
    In (Box q) (subformulas target) /\
    ~ fmc_mem X (Box q) /\
    fmc_mem Y (Box q).

Arguments gl_mini_relation target X Y : clear implicits.

Definition gl_mini_canonical_frame (target : formula nat) : frame :=
  {| World := finite_maximal_context schema_L (subformulas target);
     Rel := gl_mini_relation target |}.

Arguments gl_mini_canonical_frame target : clear implicits.

Definition gl_mini_canonical_valuation (target : formula nat)
    : valuation nat (gl_mini_canonical_frame target) :=
  fun a X => fmc_mem X (Atom a).

Arguments gl_mini_canonical_valuation target : clear implicits.

Lemma gl_mini_canonical_finite :
  forall target, finite_frame (gl_mini_canonical_frame target).
Proof.
  intro target.
  exists (finite_maximal_context_cover schema_L (subformulas target)).
  intro X. apply finite_maximal_context_explicit_cover.
Qed.

Lemma gl_mini_canonical_irreflexive :
  forall target, frame_irreflexive (gl_mini_canonical_frame target).
Proof.
  intros target X [_ [q [_ [Hnot Hmem]]]]. contradiction.
Qed.

Lemma gl_mini_canonical_transitive :
  forall target, frame_transitive (gl_mini_canonical_frame target).
Proof.
  intros target X Y Z [HXY [q [Hq [HnotX HqY]]]]
    [HYZ Hnew]. split.
  - intros p Hp HpX.
    destruct (HXY p Hp HpX) as [_ HpY].
    exact (HYZ p Hp HpY).
  - exists q. repeat split; try assumption.
    exact (proj2 (HYZ q Hq HqY)).
Qed.

Corollary gl_mini_canonical_converse_well_founded :
  forall target,
    frame_converse_well_founded (gl_mini_canonical_frame target).
Proof.
  intro target. apply finite_transitive_irreflexive_cwf.
  - apply gl_mini_canonical_finite.
  - apply gl_mini_canonical_transitive.
  - apply gl_mini_canonical_irreflexive.
Qed.

(** * Existence of canonical successors and the truth lemma *)

Theorem gl_mini_successor_of_missing_box :
  forall target
    (X : World (gl_mini_canonical_frame target)) q,
    In (Box q) (subformulas target) ->
    ~ fmc_mem X (Box q) ->
    exists Y : World (gl_mini_canonical_frame target),
      gl_mini_relation target X Y /\
      fmc_mem Y (complement q).
Proof.
  intros target X q Hbox Hnot.
  destruct (@finite_context_lindenbaum schema_L
    (gl_successor_seed target X q) (subformulas target))
    as [Y HY].
  - now apply gl_successor_seed_subset.
  - now apply gl_successor_seed_consistent.
  - exists Y. split.
    + split.
      * intros p Hp HpX.
        destruct (@gl_core_items_intro target X p Hp HpX) as [Hp1 Hp2].
        split; apply HY; unfold gl_successor_seed; simpl; auto.
      * exists q. repeat split; try assumption.
        apply HY. unfold gl_successor_seed; simpl; auto.
    + apply HY. unfold gl_successor_seed; simpl; auto.
Qed.

Theorem gl_mini_truth_lemma :
  forall target p,
    In p (subformulas target) ->
    forall X : World (gl_mini_canonical_frame target),
      satisfies (gl_mini_canonical_frame target)
        (gl_mini_canonical_valuation target) X p <->
      fmc_mem X p.
Proof.
  intros target p. revert target.
  induction p as [a | | p IHp q IHq | p IHp];
    intros target Hsub X; simpl.
  - reflexivity.
  - split; [contradiction |].
    intro Hbottom. exact (@fmc_bottom_absent schema_L
      (subformulas target) X Hbottom).
  - assert (Hp : In p (subformulas target)).
    { eapply subformulas_trans; [exact Hsub |].
      apply subformulas_imp_left. apply subformulas_self. }
    assert (Hq : In q (subformulas target)).
    { eapply subformulas_trans; [exact Hsub |].
      apply subformulas_imp_right. apply subformulas_self. }
    specialize (IHp target Hp X).
    specialize (IHq target Hq X).
    split.
    + intro Hsemantic.
      apply (proj2 (@fmc_mem_imp_iff schema_L
        (subformulas target) X p q Hsub Hp Hq)).
      intro HpX.
      apply (proj1 (@fmc_mem_iff_not_mem_complement schema_L
        (subformulas target) X q Hq)).
      apply (proj1 IHq). apply Hsemantic. now apply (proj2 IHp).
    + intros Hmem Hsatp.
      apply (proj2 IHq).
      apply (proj2 (@fmc_mem_iff_not_mem_complement schema_L
        (subformulas target) X q Hq)).
      apply (proj1 (@fmc_mem_imp_iff schema_L
        (subformulas target) X p q Hsub Hp Hq) Hmem).
      now apply (proj1 IHp).
  - assert (Hp : In p (subformulas target)).
    { eapply subformulas_trans; [exact Hsub |].
      apply subformulas_box. apply subformulas_self. }
    split.
    + intro Hsemantic.
      destruct (classic (fmc_mem X (Box p))) as [Hmem | Hnot];
        [exact Hmem |].
      destruct (@gl_mini_successor_of_missing_box target X p Hsub Hnot)
        as [Y [RXY Hcomp]].
      assert (Hnotp : ~ fmc_mem Y p).
      { apply (proj2 (@fmc_not_mem_iff_mem_complement schema_L
          (subformulas target) Y p Hp)). exact Hcomp. }
      exfalso. apply Hnotp. apply (proj1 (IHp target Hp Y)).
      exact (Hsemantic Y RXY).
    + intros Hmem Y RXY.
      apply (proj2 (IHp target Hp Y)).
      exact (proj1 ((proj1 RXY) p Hsub Hmem)).
Qed.

(** * Canonical countermodels and finite completeness *)

Theorem GL_mini_canonical_countermodel :
  forall p : formula nat,
    ~ GL_proves p ->
    exists X : World (gl_mini_canonical_frame p),
      ~ satisfies (gl_mini_canonical_frame p)
          (gl_mini_canonical_valuation p) X p.
Proof.
  intros p Hunprovable.
  assert (Hconsistent : finite_consistent schema_L [complement p]).
  { apply (proj2 (finite_singleton_complement_consistent_iff_unprovable
      schema_L p)). exact Hunprovable. }
  destruct (@finite_context_lindenbaum schema_L [complement p]
    (subformulas p)) as [X HX].
  - intros q Hq. simpl in Hq.
    destruct Hq as [Hq | []]. subst q.
    apply complementary_comp. apply subformulas_self.
  - exact Hconsistent.
  - exists X. intro Hsat.
    assert (Hmem : fmc_mem X p).
    { apply (proj1 (@gl_mini_truth_lemma p p
        (subformulas_self p) X)). exact Hsat. }
    assert (Hcomp : fmc_mem X (complement p)).
    { apply HX. simpl. auto. }
    exact ((proj1 (@fmc_mem_iff_not_mem_complement schema_L
      (subformulas p) X p (subformulas_self p)) Hmem) Hcomp).
Qed.

Definition GL_frame_class (F : frame) : Prop :=
  frame_transitive F /\ frame_converse_well_founded F.

Definition GL_finite_frame_class (F : frame) : Prop :=
  finite_frame F /\ frame_transitive F /\ frame_irreflexive F.

Definition GL_finite_rooted_frame_class (F : frame) : Prop :=
  finite_frame F /\ frame_transitive F /\ frame_irreflexive F /\
  frame_rooted F.

Theorem GL_finite_complete :
  forall p : formula nat,
    normal_valid_on_class GL_finite_frame_class p -> GL_proves p.
Proof.
  intros p Hvalid. apply NNPP. intro Hunprovable.
  destruct (GL_mini_canonical_countermodel Hunprovable) as [X Hcounter].
  apply Hcounter. apply Hvalid. unfold GL_finite_frame_class.
  split; [apply gl_mini_canonical_finite |].
  split; [apply gl_mini_canonical_transitive |].
  apply gl_mini_canonical_irreflexive.
Qed.

Theorem GL_finite_sound :
  forall p : formula nat,
    GL_proves p -> normal_valid_on_class GL_finite_frame_class p.
Proof.
  intros p Hp F [Hfinite [Htrans Hirr]].
  apply GL_proves_sound_on_transitive_cwf_frame.
  - exact Htrans.
  - now apply finite_transitive_irreflexive_cwf.
  - exact Hp.
Qed.

Theorem GL_finite_sound_complete :
  forall p : formula nat,
    GL_proves p <-> normal_valid_on_class GL_finite_frame_class p.
Proof. intro p; split; [apply GL_finite_sound | apply GL_finite_complete]. Qed.

Theorem GL_complete :
  forall p : formula nat,
    normal_valid_on_class GL_frame_class p -> GL_proves p.
Proof.
  intros p Hvalid. apply GL_finite_complete.
  intros F [Hfinite [Htrans Hirr]]. apply Hvalid.
  unfold GL_frame_class. split; [exact Htrans |].
  now apply finite_transitive_irreflexive_cwf.
Qed.

Theorem GL_sound :
  forall p : formula nat,
    GL_proves p -> normal_valid_on_class GL_frame_class p.
Proof.
  intros p Hp F [Htrans Hcwf].
  now apply GL_proves_sound_on_transitive_cwf_frame.
Qed.

Theorem GL_sound_complete :
  forall p : formula nat,
    GL_proves p <-> normal_valid_on_class GL_frame_class p.
Proof. intro p; split; [apply GL_sound | apply GL_complete]. Qed.

(** * Rooted finite countermodels *)

Definition canonical_gl_point_generated_cover (F : frame) (r : World F)
    (xs : list (World F)) :
    list (World (point_generated_frame F r)) :=
  @sig_filter (World F) (point_generated_member F r)
    (fun x => excluded_middle_informative (point_generated_member F r x)) xs.

Arguments canonical_gl_point_generated_cover F r xs : clear implicits.

Lemma canonical_gl_point_generated_cover_complete :
  forall F r (xs : list (World F)),
    (forall x, In x xs) ->
    forall y : World (point_generated_frame F r),
      In y (canonical_gl_point_generated_cover F r xs).
Proof.
  intros F r xs Hcover y.
  unfold canonical_gl_point_generated_cover.
  apply sig_filter_complete. apply Hcover.
Qed.

Lemma canonical_gl_point_generated_finite :
  forall F r,
    finite_frame F -> finite_frame (point_generated_frame F r).
Proof.
  intros F r [xs Hcover].
  exists (canonical_gl_point_generated_cover F r xs).
  now apply canonical_gl_point_generated_cover_complete.
Qed.

Theorem GL_unprovable_exists_finite_rooted_countermodel :
  forall p : formula nat,
    ~ GL_proves p ->
    exists (F : frame) (V : valuation nat F) (r : World F),
      finite_frame F /\
      frame_transitive F /\
      frame_irreflexive F /\
      frame_root F r /\
      ~ satisfies F V r p.
Proof.
  intros p Hunprovable.
  destruct (GL_mini_canonical_countermodel Hunprovable) as [X Hcounter].
  set (G := gl_mini_canonical_frame p).
  set (VG := gl_mini_canonical_valuation p).
  set (F := point_generated_frame G X).
  set (V := point_generated_valuation VG X).
  set (r := point_generated_root G X).
  exists F, V, r. split.
  - unfold F. apply canonical_gl_point_generated_finite.
    unfold G. apply gl_mini_canonical_finite.
  - split.
    + unfold F, G. apply point_generated_transitive.
      apply gl_mini_canonical_transitive.
    + split.
      * unfold F, G. apply point_generated_irreflexive.
        apply gl_mini_canonical_irreflexive.
      * split.
        -- unfold F, r, G. apply point_generated_rooted.
        -- intro Hsat. apply Hcounter.
           apply (proj1 (@point_generated_truth_at_root nat G VG X
             (@gl_mini_canonical_transitive p) p)).
           exact Hsat.
Qed.

Theorem GL_unprovable_iff_exists_finite_rooted_countermodel :
  forall p : formula nat,
    ~ GL_proves p <->
    exists (F : frame) (V : valuation nat F) (r : World F),
      finite_frame F /\
      frame_transitive F /\
      frame_irreflexive F /\
      frame_root F r /\
      ~ satisfies F V r p.
Proof.
  intro p; split.
  - apply GL_unprovable_exists_finite_rooted_countermodel.
  - intros [F [V [r [Hfinite [Htrans [Hirr [_ Hcounter]]]]]]] Hprovable.
    apply Hcounter.
    eapply GL_proves_sound_on_transitive_cwf_frame;
      [exact Htrans | | exact Hprovable].
    now apply finite_transitive_irreflexive_cwf.
Qed.

Definition GL_valid_on_finite_rooted_models_at_root
    (p : formula nat) : Prop :=
  forall (F : frame) (V : valuation nat F) (r : World F),
    finite_frame F ->
    frame_transitive F ->
    frame_irreflexive F ->
    frame_root F r ->
    satisfies F V r p.

Theorem GL_finite_rooted_model_sound_complete :
  forall p : formula nat,
    GL_proves p <-> GL_valid_on_finite_rooted_models_at_root p.
Proof.
  intro p; split.
  - intros Hp F V r Hfinite Htrans Hirr Hroot.
    eapply GL_proves_sound_on_transitive_cwf_frame;
      [exact Htrans | | exact Hp].
    now apply finite_transitive_irreflexive_cwf.
  - intro Hrootvalid. apply NNPP. intro Hunprovable.
    destruct (GL_unprovable_exists_finite_rooted_countermodel Hunprovable)
      as [F [V [r [Hfinite [Htrans [Hirr [Hroot Hcounter]]]]]]].
    apply Hcounter. now apply (Hrootvalid F V r Hfinite Htrans Hirr Hroot).
Qed.

Theorem GL_finite_rooted_complete :
  forall p : formula nat,
    normal_valid_on_class GL_finite_rooted_frame_class p -> GL_proves p.
Proof.
  intros p Hvalid. apply NNPP. intro Hunprovable.
  destruct (GL_unprovable_exists_finite_rooted_countermodel Hunprovable)
    as [F [V [r [Hfinite [Htrans [Hirr [Hroot Hcounter]]]]]]].
  apply Hcounter. apply (Hvalid F).
  unfold GL_finite_rooted_frame_class.
  split; [exact Hfinite |]. split; [exact Htrans |].
  split; [exact Hirr |]. now exists r.
Qed.

Theorem GL_finite_rooted_sound_complete :
  forall p : formula nat,
    GL_proves p <->
    normal_valid_on_class GL_finite_rooted_frame_class p.
Proof.
  intro p; split.
  - intros Hp F [Hfinite [Htrans [Hirr Hrooted]]].
    eapply GL_proves_sound_on_transitive_cwf_frame;
      [exact Htrans | | exact Hp].
    now apply finite_transitive_irreflexive_cwf.
  - apply GL_finite_rooted_complete.
Qed.
