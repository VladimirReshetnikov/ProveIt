(**
  Finite mini-canonical completeness for Grzegorczyk logic.

  The ordinary canonical frame of Grz need not be a Grz frame.  Following
  Foundation's finite construction, worlds here are complement-closed
  consistent contexts over an enriched subformula closure.  The accessibility
  relation remembers the relevant boxed formulas and identifies worlds when
  the reverse inclusion also holds.  This makes the finite frame a partial
  order before the modal truth argument is considered.

  The structural construction is kept explicit because it is also useful for
  schema-generic extensions of Grz.  The seed-consistency and truth lemmas are
  developed below this frame layer.
*)

From Stdlib Require Import Lists.List Logic.Classical_Prop.
From FoundationModal Require Import
  Syntax Complement Axioms HilbertK Kripke Correspondence Filtration
  NormalHilbert CanonicalExtensions FiniteMaximalContext FrameProperties
  CorrespondenceExtensions LogicInfrastructure FiniteCanonicalSupport
  GLGrzDerivations.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition grz_enriched_subformulas (p : formula nat)
    : list (formula nat) :=
  grz_subformulas p.

Lemma grz_enriched_contains_subformula :
  forall p q,
    In q (subformulas p) -> In q (grz_enriched_subformulas p).
Proof.
  intros p q Hq. apply grz_subformulas_base. exact Hq.
Qed.

Lemma grz_enriched_self :
  forall p, In p (grz_enriched_subformulas p).
Proof.
  intro p. apply grz_subformulas_self.
Qed.

Lemma grz_enriched_box_imp_box :
  forall p q,
    In (Box q) (subformulas p) ->
    In (Box (Imp q (Box q))) (grz_enriched_subformulas p).
Proof.
  intros p q Hbox. now apply grz_subformulas_generated.
Qed.

(** * The finite partial-order mini-canonical frame *)

Definition grz_relevant_box (root q : formula nat) : Prop :=
  In (Box q) (grz_enriched_subformulas root).

Definition grz_mini_relation (root : formula nat)
    (X Y : finite_maximal_context schema_Grz
      (grz_enriched_subformulas root)) : Prop :=
  (forall q, grz_relevant_box root q ->
      fmc_mem X (Box q) -> fmc_mem Y (Box q)) /\
  ((forall q, grz_relevant_box root q ->
      fmc_mem Y (Box q) -> fmc_mem X (Box q)) -> X = Y).

Definition grz_mini_frame (root : formula nat) : frame :=
  {| World := finite_maximal_context schema_Grz
       (grz_enriched_subformulas root);
     Rel := @grz_mini_relation root |}.

Definition grz_mini_valuation (root : formula nat)
    : valuation nat (grz_mini_frame root) :=
  fun a X => fmc_mem X (Atom a).

Lemma grz_mini_frame_reflexive :
  forall root, frame_reflexive (grz_mini_frame root).
Proof.
  intros root X. split.
  - intros q _ Hq. exact Hq.
  - intros _. reflexivity.
Qed.

Lemma grz_mini_frame_antisymmetric :
  forall root, frame_antisymmetric (grz_mini_frame root).
Proof.
  intros root X Y HXY HYX.
  apply (proj2 HXY). exact (proj1 HYX).
Qed.

Lemma grz_mini_frame_transitive :
  forall root, frame_transitive (grz_mini_frame root).
Proof.
  intros root X Y Z HXY HYZ. split.
  - intros q Hq HXq.
    exact (proj1 HYZ q Hq (proj1 HXY q Hq HXq)).
  - intro HZX.
    assert (HXYeq : X = Y).
    {
      apply (proj2 HXY). intros q Hq HYq.
      exact (HZX q Hq (proj1 HYZ q Hq HYq)).
    }
    assert (HYZeq : Y = Z).
    {
      apply (proj2 HYZ). intros q Hq HZq.
      exact (proj1 HXY q Hq (HZX q Hq HZq)).
    }
    now rewrite HXYeq, HYZeq.
Qed.

Lemma grz_mini_frame_finite :
  forall root, finite_frame (grz_mini_frame root).
Proof.
  intro root. exists (finite_maximal_context_cover schema_Grz
    (grz_enriched_subformulas root)).
  apply finite_maximal_context_explicit_cover.
Qed.

Lemma grz_mini_frame_weak_cwf :
  forall root, frame_weak_converse_well_founded (grz_mini_frame root).
Proof.
  intro root. apply finite_transitive_antisymmetric_weak_cwf.
  - apply grz_mini_frame_finite.
  - apply grz_mini_frame_transitive.
  - apply grz_mini_frame_antisymmetric.
Qed.

Definition Grz_frame_class (F : frame) : Prop :=
  frame_reflexive F /\ frame_transitive F /\
  frame_weak_converse_well_founded F.

(** This is the exact finite class used by Foundation: finite partial
    orders.  On finite transitive frames it is equivalent to the weak-CWF
    presentation used for unrestricted Grz soundness. *)
Definition Grz_finite_frame_class (F : frame) : Prop :=
  finite_frame F /\ frame_is_partial_order F.

Theorem Grz_sound :
  forall p : formula nat,
    Grz_proves p -> normal_valid_on_class Grz_frame_class p.
Proof.
  intros p Hp F [HR [HT HW]].
  now apply Grz_proves_sound_on_reflexive_transitive_weak_cwf_frame.
Qed.

Theorem Grz_finite_sound :
  forall p : formula nat,
    Grz_proves p -> normal_valid_on_class Grz_finite_frame_class p.
Proof.
  intros p Hp F [Hfinite Horder].
  destruct Horder as [HR [HT HA]].
  apply Grz_proves_sound_on_reflexive_transitive_weak_cwf_frame.
  - exact HR.
  - exact HT.
  - now apply finite_transitive_antisymmetric_weak_cwf.
  - exact Hp.
Qed.

Lemma grz_mini_frame_in_finite_class :
  forall root, Grz_finite_frame_class (grz_mini_frame root).
Proof.
  intro root. split.
  - apply grz_mini_frame_finite.
  - split.
    + apply grz_mini_frame_reflexive.
    + split.
      * apply grz_mini_frame_transitive.
      * apply grz_mini_frame_antisymmetric.
Qed.

(** * Modal successor seeds *)

Definition grz_successor_seed (root : formula nat)
    (X : finite_maximal_context schema_Grz
      (grz_enriched_subformulas root))
    (p : formula nat) : list (formula nat) :=
  complement p :: Box (Imp p (Box p)) :: fmc_relevant_boxed X.

Lemma grz_successor_seed_subset :
  forall root
    (X : finite_maximal_context schema_Grz
      (grz_enriched_subformulas root)) p,
    In (Box p) (subformulas root) ->
    list_subset (grz_successor_seed X p)
      (complementary (grz_enriched_subformulas root)).
Proof.
  intros root X p Hbox q Hq. unfold grz_successor_seed in Hq.
  simpl in Hq. destruct Hq as [Hq | [Hq | Hq]].
  - subst q. apply complementary_comp.
    apply grz_subformulas_original_box_body. exact Hbox.
  - subst q. apply complementary_mem.
    exact (grz_enriched_box_imp_box Hbox).
  - exact (@fmc_relevant_boxed_subset_complementary
      schema_Grz (grz_enriched_subformulas root) X q Hq).
Qed.

Lemma grz_successor_seed_consistent :
  forall root
    (X : finite_maximal_context schema_Grz
      (grz_enriched_subformulas root)) p,
    In (Box p) (subformulas root) ->
    ~ fmc_mem X (Box p) ->
    finite_consistent schema_Grz (grz_successor_seed X p).
Proof.
  intros root X p Hbox Hnotbox.
  unfold finite_consistent, normal_theory_consistent.
  intro Hbottom.
  set (Gamma := fmc_relevant_boxed X).
  set (B := Box (Imp p (Box p))).
  assert (Hbottom_insert :
    normal_derives schema_Grz
      (theory_insert (finite_theory (B :: Gamma)) (complement p))
      Bottom).
  {
    apply (proj1 (@normal_derives_extensional schema_Grz
      (finite_theory (complement p :: B :: Gamma))
      (theory_insert (finite_theory (B :: Gamma)) (complement p))
      Bottom (fun q => finite_theory_cons_iff_insert
        (complement p) (B :: Gamma) q))).
    exact Hbottom.
  }
  pose proof (normal_derives_deduction Hbottom_insert) as Hnegcomp.
  pose proof (normal_derives_of_neg_complement Hnegcomp) as Hp_with_B.
  assert (Hp_insert :
    normal_derives schema_Grz
      (theory_insert (finite_theory Gamma) B) p).
  {
    apply (proj1 (@normal_derives_extensional schema_Grz
      (finite_theory (B :: Gamma))
      (theory_insert (finite_theory Gamma) B) p
      (fun q => finite_theory_cons_iff_insert B Gamma q))).
    exact Hp_with_B.
  }
  pose proof (normal_derives_deduction Hp_insert) as Himp.
  assert (Hcollapse : forall q,
    normal_derives schema_Grz
      (finite_theory (formula_list_box Gamma)) q ->
    normal_derives schema_Grz (finite_theory Gamma) q).
  {
    intros q Hq. eapply normal_derives_finite_context_cut; [|exact Hq].
    intros r Hr. unfold formula_list_box in Hr.
    apply in_map_iff in Hr. destruct Hr as [s [Hsr Hs]]. subst r.
    unfold Gamma, fmc_relevant_boxed, formula_list_box in Hs.
    apply in_map_iff in Hs. destruct Hs as [t [Hts Ht]]. subst s.
    eapply ND_mp.
    - apply ND_theorem. apply Grz_proves_Four.
    - apply ND_assumption. unfold Gamma, fmc_relevant_boxed,
        formula_list_box. apply in_map_iff.
      exists t. now split.
  }
  assert (Hboxed_imp :
    normal_derives schema_Grz (finite_theory Gamma)
      (Box (Imp B p))).
  {
    apply Hcollapse. apply normal_derives_finite_box.
    exact Himp.
  }
  assert (Hp : normal_derives schema_Grz (finite_theory Gamma) p).
  {
    eapply ND_mp.
    - apply ND_theorem. unfold B. apply Grz_proves_axiom.
    - exact Hboxed_imp.
  }
  assert (Hboxp : normal_derives schema_Grz
      (finite_theory Gamma) (Box p)).
  {
    apply Hcollapse. now apply normal_derives_finite_box.
  }
  assert (Hboxp_X : normal_derives schema_Grz (fmc_mem X) (Box p)).
  {
    eapply normal_derives_weaken; [|exact Hboxp].
    intros q Hq. unfold Gamma, fmc_relevant_boxed,
      formula_list_box in Hq.
    apply in_map_iff in Hq. destruct Hq as [r [Hr Hrin]]. subst q.
    apply (proj1 (fmc_relevant_unboxed_spec X r)) in Hrin.
    exact (proj2 Hrin).
  }
  apply Hnotbox.
  apply (proj2 (@fmc_membership_iff_derivable schema_Grz
    (grz_enriched_subformulas root) X (Box p)
    (grz_enriched_contains_subformula Hbox))).
  exact Hboxp_X.
Qed.

Theorem grz_mini_successor_of_missing_box :
  forall root
    (X : World (grz_mini_frame root)) p,
    In (Box p) (subformulas root) ->
    fmc_mem X p ->
    ~ fmc_mem X (Box p) ->
    exists Y : World (grz_mini_frame root),
      Rel (grz_mini_frame root) X Y /\
      fmc_mem Y (complement p).
Proof.
  intros root X p Hbox HpX Hnotbox.
  destruct (@finite_context_lindenbaum schema_Grz
    (grz_successor_seed X p) (grz_enriched_subformulas root))
    as [Y HY].
  - now apply grz_successor_seed_subset.
  - now apply grz_successor_seed_consistent.
  - exists Y. split.
    + split.
      * intros q Hrelevant HboxX.
        apply HY. unfold grz_successor_seed; simpl. right; right.
        apply (proj2 (fmc_relevant_boxed_spec X q)).
        split; [exact Hrelevant | exact HboxX].
      * intro Hreverse. exfalso. apply Hnotbox.
        set (B := Box (Imp p (Box p))).
        assert (HrelevantB :
          grz_relevant_box root (Imp p (Box p))).
        { unfold grz_relevant_box.
          exact (grz_enriched_box_imp_box Hbox). }
        assert (HBY : fmc_mem Y B).
        { apply HY. unfold grz_successor_seed, B; simpl. now right; left. }
        assert (HBX : fmc_mem X B).
        { exact (Hreverse (Imp p (Box p)) HrelevantB HBY). }
        assert (Hand_intro :
          Grz_proves (Imp p (Imp B (And p B)))).
        {
          apply (logic_classical_tautology Grz_classical_logic).
          intro rho. unfold And, Neg; simpl; tauto.
        }
        apply (proj2 (@fmc_membership_iff_derivable schema_Grz
          (grz_enriched_subformulas root) X (Box p)
          (grz_enriched_contains_subformula Hbox))).
        eapply ND_mp.
        -- apply ND_theorem. apply Grz_proves_truth_box_bridge.
        -- eapply ND_mp.
           ++ eapply ND_mp.
              ** apply ND_theorem. exact Hand_intro.
              ** now apply ND_assumption.
           ++ now apply ND_assumption.
    + apply HY. unfold grz_successor_seed; simpl. now left.
Qed.

(** * Truth in the finite model *)

Theorem grz_mini_truth_lemma :
  forall target p,
    In p (subformulas target) ->
    forall X : World (grz_mini_frame target),
      satisfies (grz_mini_frame target)
        (@grz_mini_valuation target) X p <->
      fmc_mem X p.
Proof.
  intros target p. revert target.
  induction p as [a | | p IHp q IHq | p IHp];
    intros target Hsub X; simpl.
  - reflexivity.
  - split; [contradiction |].
    intro Hbottom. exact (@fmc_bottom_absent schema_Grz
      (grz_enriched_subformulas target) X Hbottom).
  - assert (Hp : In p (subformulas target)).
    { eapply subformulas_trans; [exact Hsub |].
      apply subformulas_imp_left. apply subformulas_self. }
    assert (Hq : In q (subformulas target)).
    { eapply subformulas_trans; [exact Hsub |].
      apply subformulas_imp_right. apply subformulas_self. }
    assert (HimpE : In (Imp p q) (grz_enriched_subformulas target)).
    { now apply grz_enriched_contains_subformula. }
    assert (HpE : In p (grz_enriched_subformulas target)).
    { now apply grz_enriched_contains_subformula. }
    assert (HqE : In q (grz_enriched_subformulas target)).
    { now apply grz_enriched_contains_subformula. }
    specialize (IHp target Hp X).
    specialize (IHq target Hq X).
    split.
    + intro Hsemantic.
      apply (proj2 (@fmc_mem_imp_iff schema_Grz
        (grz_enriched_subformulas target) X p q HimpE HpE HqE)).
      intro HpX.
      apply (proj1 (@fmc_mem_iff_not_mem_complement schema_Grz
        (grz_enriched_subformulas target) X q HqE)).
      apply (proj1 IHq). apply Hsemantic. exact ((proj2 IHp) HpX).
    + intros Hmem Hsatp.
      apply (proj2 IHq).
      apply (proj2 (@fmc_mem_iff_not_mem_complement schema_Grz
        (grz_enriched_subformulas target) X q HqE)).
      apply (proj1 (@fmc_mem_imp_iff schema_Grz
        (grz_enriched_subformulas target) X p q HimpE HpE HqE)
        Hmem).
      now apply (proj1 IHp).
  - assert (Hp : In p (subformulas target)).
    { eapply subformulas_trans; [exact Hsub |].
      apply subformulas_box. apply subformulas_self. }
    assert (HboxE : In (Box p) (grz_enriched_subformulas target)).
    { now apply grz_enriched_contains_subformula. }
    assert (HpE : In p (grz_enriched_subformulas target)).
    { now apply grz_enriched_contains_subformula. }
    split.
    + intro Hsemantic.
      destruct (classic (fmc_mem X (Box p))) as [HboxX | Hnotbox];
        [exact HboxX |].
      destruct (classic (fmc_mem X p)) as [HpX | Hnotp].
      * destruct (@grz_mini_successor_of_missing_box target X p
          Hsub HpX Hnotbox) as [Y [RXY Hcomp]].
        assert (HnotpY : ~ fmc_mem Y p).
        { apply (proj2 (@fmc_not_mem_iff_mem_complement schema_Grz
            (grz_enriched_subformulas target) Y p HpE)).
          exact Hcomp. }
        exfalso. apply HnotpY. apply (proj1 (IHp target Hp Y)).
        exact (Hsemantic Y RXY).
      * exfalso. apply Hnotp. apply (proj1 (IHp target Hp X)).
        apply Hsemantic. apply grz_mini_frame_reflexive.
    + intros HboxX Y RXY.
      apply (proj2 (IHp target Hp Y)).
      apply (proj2 (@fmc_membership_iff_derivable schema_Grz
        (grz_enriched_subformulas target) Y p HpE)).
      eapply ND_mp.
      * apply ND_theorem. apply Grz_proves_T.
      * apply ND_assumption.
        exact (proj1 RXY p HboxE HboxX).
Qed.

(** * Finite and unrestricted completeness *)

Theorem grz_mini_countermodel :
  forall p : formula nat,
    ~ Grz_proves p ->
    exists X : World (grz_mini_frame p),
      ~ satisfies (grz_mini_frame p) (@grz_mini_valuation p) X p.
Proof.
  intros p Hunprovable.
  destruct (@finite_context_lindenbaum schema_Grz
    [complement p] (grz_enriched_subformulas p)) as [X HX].
  - intros q Hq. simpl in Hq. destruct Hq as [Hq | []]. subst q.
    apply complementary_comp. apply grz_enriched_self.
  - now apply finite_singleton_complement_consistent_iff_unprovable.
  - exists X. intro Hsat.
    assert (Hnotmem : ~ fmc_mem X p).
    {
      apply (proj2 (@fmc_not_mem_iff_mem_complement schema_Grz
        (grz_enriched_subformulas p) X p (grz_enriched_self p))).
      apply HX. now left.
    }
    apply Hnotmem.
    apply (proj1 (grz_mini_truth_lemma (subformulas_self p) X)).
    exact Hsat.
Qed.

Theorem Grz_finite_complete :
  forall p : formula nat,
    normal_valid_on_class Grz_finite_frame_class p -> Grz_proves p.
Proof.
  intros p Hvalid. apply NNPP. intro Hunprovable.
  destruct (grz_mini_countermodel Hunprovable) as [X Hnot].
  apply Hnot. exact (Hvalid (grz_mini_frame p)
    (grz_mini_frame_in_finite_class p)
    (@grz_mini_valuation p) X).
Qed.

Theorem Grz_finite_sound_complete :
  forall p : formula nat,
    Grz_proves p <-> normal_valid_on_class Grz_finite_frame_class p.
Proof.
  intro p; split.
  - apply Grz_finite_sound.
  - apply Grz_finite_complete.
Qed.

Theorem Grz_complete :
  forall p : formula nat,
    normal_valid_on_class Grz_frame_class p -> Grz_proves p.
Proof.
  intros p Hvalid. apply Grz_finite_complete.
  intros F [Hfinite [HR [HT HA]]]. apply Hvalid. split.
  - exact HR.
  - split; [exact HT |].
    now apply finite_transitive_antisymmetric_weak_cwf.
Qed.

Theorem Grz_sound_complete :
  forall p : formula nat,
    Grz_proves p <-> normal_valid_on_class Grz_frame_class p.
Proof.
  intro p; split.
  - apply Grz_sound.
  - apply Grz_complete.
Qed.

(** Every finite partial order has the terminal-successor property used by
    McKinsey's axiom.  Maximize the reflexive cone above the given world and
    use transitivity to show that every successor of the maximum is still in
    that cone. *)
Theorem finite_partial_order_mckinsey :
  forall F : frame,
    finite_frame F -> frame_is_partial_order F -> frame_mckinsey F.
Proof.
  intros F Hfinite [HR [HT HA]] x.
  pose proof (finite_transitive_antisymmetric_weak_cwf
    Hfinite HT HA) as Hweak.
  destruct (Hweak (fun y => Rel F x y)) as [m [Rxm Hmax]].
  - exists x. apply HR.
  - exists m. split; [exact Rxm |].
    intros z Rmz. apply Hmax.
    + eapply HT; eauto.
    + exact Rmz.
Qed.
