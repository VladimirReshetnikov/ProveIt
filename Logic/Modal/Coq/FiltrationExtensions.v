(**
  Finest and transitive-closure filtrations.

  This file continues the port of
  Foundation/Modal/Kripke/Filtration.lean after the coarsest filtration.
  As in [Filtration], quotient classes are represented by realised Boolean
  truth profiles.  The finest filtered relation is exactly the image of the
  original accessibility relation on those classes.  Its nonempty transitive
  closure gives the filtration used for transitive logics.

  Ported here are the truth lemmas, the inherited finite cover and exponential
  bound, preservation of reflexivity/seriality/symmetry by the finest
  filtration, and preservation of transitivity together with the corresponding
  elementary frame properties by the transitive-closure filtration.

  Foundation additionally proves rooted preservation results for piecewise
  strong confluence and connectedness.  They are intentionally not stated
  here: this Coq semantic layer has no rooted-frame/restriction API yet.  No
  weaker unrooted replacement is presented as if it were that result.
*)

From Stdlib Require Import Arith.PeanoNat Lia.
From Stdlib Require Import Lists.List.
From FoundationModal Require Import Syntax Kripke Filtration Correspondence.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Finest filtration *)

Section FinestFiltration.

Context {AtomType : Type} (F : frame) (V : valuation AtomType F)
        (target : formula AtomType).

(** The image of an original edge on profile classes.  This is Foundation's
    finest filtration relation, expressed without quotient types.  Equality
    is stated on the underlying profiles, not their irrelevant realisation
    proofs, so this relation itself does not require proof irrelevance. *)
Definition finest_filtered_rel
    (X Y : @filtered_world AtomType F V target) : Prop :=
  exists x y : World F,
    proj1_sig X = @truth_profile AtomType F V target x /\
    proj1_sig Y = @truth_profile AtomType F V target y /\
    Rel F x y.

Definition finest_filtered_frame : frame :=
  {| World := @filtered_world AtomType F V target;
     Rel := finest_filtered_rel |}.

Definition finest_filtered_valuation :
    valuation AtomType finest_filtered_frame :=
  fun a X => satisfies F V (@representative AtomType F V target X) (Atom a).

Lemma finest_filtered_rel_forth :
  forall x y,
    Rel F x y ->
    finest_filtered_rel
      (@profile_class AtomType F V target x)
      (@profile_class AtomType F V target y).
Proof.
  intros x y Rxy. exists x, y. auto.
Qed.

(** An edge of the finest filtration has the usual filtration back property. *)
Lemma finest_filtered_rel_back :
  forall X Y p,
    finest_filtered_rel X Y ->
    In (Box p) (subformulas target) ->
    satisfies F V (@representative AtomType F V target X) (Box p) ->
    satisfies F V (@representative AtomType F V target Y) p.
Proof.
  intros X Y p [x [y [HX [HY Rxy]]]] Hbox_in Hbox.
  assert (Hx_box : satisfies F V x (Box p)).
  {
    assert (Hprofiles :
      @truth_profile AtomType F V target
        (@representative AtomType F V target X) =
      @truth_profile AtomType F V target x).
    { rewrite representative_spec. exact HX. }
    exact (proj1 (@truth_profile_agreement AtomType F V target
      (@representative AtomType F V target X) x (Box p)
      Hprofiles Hbox_in) Hbox).
  }
  assert (Hy : satisfies F V y p) by exact (Hx_box y Rxy).
  assert (Hp_in : In p (subformulas target)).
  {
    eapply (@child_is_target_subformula AtomType target (Box p) p).
    - exact Hbox_in.
    - simpl. right. apply subformulas_self.
  }
  assert (Hprofiles :
    @truth_profile AtomType F V target y =
    @truth_profile AtomType F V target
      (@representative AtomType F V target Y)).
  { rewrite representative_spec. symmetry. exact HY. }
  exact (proj1 (@truth_profile_agreement AtomType F V target y
    (@representative AtomType F V target Y) p Hprofiles Hp_in) Hy).
Qed.

Theorem finest_filtration_truth :
  forall p,
    In p (subformulas target) ->
    forall X,
      satisfies finest_filtered_frame finest_filtered_valuation X p <->
      satisfies F V (@representative AtomType F V target X) p.
Proof.
  intros p; induction p as [a | | p IHp q IHq | p IHp];
    intros Hin X; simpl.
  - reflexivity.
  - tauto.
  - assert (Hp : In p (subformulas target)).
    {
      eapply (@child_is_target_subformula AtomType target
        (Imp p q) p); [exact Hin |].
      simpl. right. apply in_or_app. left. apply subformulas_self.
    }
    assert (Hq : In q (subformulas target)).
    {
      eapply (@child_is_target_subformula AtomType target
        (Imp p q) q); [exact Hin |].
      simpl. right. apply in_or_app. right. apply subformulas_self.
    }
    rewrite IHp by exact Hp. rewrite IHq by exact Hq. reflexivity.
  - assert (Hp : In p (subformulas target)).
    {
      eapply (@child_is_target_subformula AtomType target
        (Box p) p); [exact Hin |].
      simpl. auto using subformulas_self.
    }
    split.
    + intros Hfiltered y Rxy.
      specialize (Hfiltered (@profile_class AtomType F V target y)).
      assert (Hedge : finest_filtered_rel X
        (@profile_class AtomType F V target y)).
      {
        exists (@representative AtomType F V target X), y.
        split.
        - symmetry. apply representative_spec.
        - split; [reflexivity | exact Rxy].
      }
      specialize (Hfiltered Hedge).
      assert (Hprofiles :
        @truth_profile AtomType F V target
          (@representative AtomType F V target
            (@profile_class AtomType F V target y)) =
        @truth_profile AtomType F V target y).
      { apply profile_class_spec. }
      apply (proj1 (@truth_profile_agreement AtomType F V target
        (@representative AtomType F V target
          (@profile_class AtomType F V target y)) y p Hprofiles Hp)).
      apply (proj1 (IHp Hp
        (@profile_class AtomType F V target y))). exact Hfiltered.
    + intros Hbox Y HXY.
      apply (proj2 (IHp Hp Y)).
      eapply finest_filtered_rel_back; eauto.
Qed.

Corollary finest_filtration_truth_at_class :
  forall p,
    In p (subformulas target) ->
    forall w,
      satisfies finest_filtered_frame finest_filtered_valuation
        (@profile_class AtomType F V target w) p <->
      satisfies F V w p.
Proof.
  intros p Hin w.
  rewrite finest_filtration_truth by exact Hin.
  apply (@truth_profile_agreement AtomType F V target
    (@representative AtomType F V target
      (@profile_class AtomType F V target w)) w p).
  - apply profile_class_spec.
  - exact Hin.
Qed.

(** The finest filtration has exactly the same finite carrier and cover as
    the coarsest filtration. *)
Corollary finest_filtered_frame_finite :
  finite_frame finest_filtered_frame.
Proof.
  exists (@filtered_world_cover AtomType F V target).
  exact (proj1 (proj2
    (@filtered_world_cover_bound AtomType F V target))).
Qed.

Theorem finest_filtered_frame_cover_bound :
  exists cover : list (World finest_filtered_frame),
    NoDup cover /\
    (forall X, In X cover) /\
    length cover <= 2 ^ length (subformulas target).
Proof.
  exists (@filtered_world_cover AtomType F V target).
  apply filtered_world_cover_bound.
Qed.

Lemma finest_preserves_reflexive :
  frame_reflexive F -> frame_reflexive finest_filtered_frame.
Proof.
  intros Hrefl X.
  exists (@representative AtomType F V target X),
         (@representative AtomType F V target X).
  repeat split.
  - symmetry. apply representative_spec.
  - symmetry. apply representative_spec.
  - apply Hrefl.
Qed.

Lemma finest_preserves_serial :
  frame_serial F -> frame_serial finest_filtered_frame.
Proof.
  intros Hserial X.
  destruct (Hserial (@representative AtomType F V target X))
    as [y Rxy].
  exists (@profile_class AtomType F V target y).
  exists (@representative AtomType F V target X), y.
  repeat split.
  - symmetry. apply representative_spec.
  - exact Rxy.
Qed.

Lemma finest_preserves_symmetric :
  frame_symmetric F -> frame_symmetric finest_filtered_frame.
Proof.
  intros Hsym X Y [x [y [HX [HY Rxy]]]].
  exists y, x. repeat split; auto.
Qed.

(** * Nonempty transitive closure of the finest relation *)

Definition positive_closure {A : Type} (R : A -> A -> Prop)
    (x y : A) : Prop :=
  exists n, 0 < n /\ rel_iter R n x y.

Lemma positive_closure_single :
  forall (A : Type) (R : A -> A -> Prop) x y,
    R x y -> positive_closure R x y.
Proof.
  intros A R x y Rxy. exists 1. split; [lia |].
  apply rel_iter_one. exact Rxy.
Qed.

Lemma positive_closure_transitive :
  forall (A : Type) (R : A -> A -> Prop) x y z,
    positive_closure R x y ->
    positive_closure R y z ->
    positive_closure R x z.
Proof.
  intros A R x y z [n [Hn Hxy]] [m [Hm Hyz]].
  exists (n + m). split; [lia |].
  apply (proj2 (rel_iter_plus R n m x z)).
  exists y. auto.
Qed.

Lemma rel_iter_reverse :
  forall (A : Type) (R : A -> A -> Prop),
    (forall x y, R x y -> R y x) ->
    forall n x y, rel_iter R n x y -> rel_iter R n y x.
Proof.
  intros A R Hsym n; induction n as [|n IH]; intros x y Hxy.
  - simpl in *. now subst y.
  - destruct Hxy as [z [Rxz Hzy]].
    eapply rel_iter_step_right.
    + apply IH. exact Hzy.
    + apply Hsym. exact Rxz.
Qed.

Lemma positive_closure_symmetric :
  forall (A : Type) (R : A -> A -> Prop),
    (forall x y, R x y -> R y x) ->
    forall x y, positive_closure R x y -> positive_closure R y x.
Proof.
  intros A R Hsym x y [n [Hn Hxy]].
  exists n. split; [exact Hn |].
  now apply rel_iter_reverse.
Qed.

Definition finest_tc_filtered_rel
    (X Y : @filtered_world AtomType F V target) : Prop :=
  positive_closure finest_filtered_rel X Y.

Definition finest_tc_filtered_frame : frame :=
  {| World := @filtered_world AtomType F V target;
     Rel := finest_tc_filtered_rel |}.

Definition finest_tc_filtered_valuation :
    valuation AtomType finest_tc_filtered_frame :=
  fun a X => satisfies F V (@representative AtomType F V target X) (Atom a).

Lemma finest_filtered_rel_preserves_box :
  frame_transitive F ->
  forall X Y p,
    finest_filtered_rel X Y ->
    In (Box p) (subformulas target) ->
    satisfies F V (@representative AtomType F V target X) (Box p) ->
    satisfies F V (@representative AtomType F V target Y) (Box p).
Proof.
  intros Htrans X Y p [x [y [HX [HY Rxy]]]] Hbox_in Hbox.
  assert (Hx_box : satisfies F V x (Box p)).
  {
    assert (Hprofiles :
      @truth_profile AtomType F V target
        (@representative AtomType F V target X) =
      @truth_profile AtomType F V target x).
    { rewrite representative_spec. exact HX. }
    exact (proj1 (@truth_profile_agreement AtomType F V target
      (@representative AtomType F V target X) x (Box p)
      Hprofiles Hbox_in) Hbox).
  }
  assert (Hy_box : satisfies F V y (Box p)).
  {
    intros z Ryz. apply Hx_box.
    eapply Htrans; eauto.
  }
  assert (Hprofiles :
    @truth_profile AtomType F V target y =
    @truth_profile AtomType F V target
      (@representative AtomType F V target Y)).
  { rewrite representative_spec. symmetry. exact HY. }
  exact (proj1 (@truth_profile_agreement AtomType F V target y
    (@representative AtomType F V target Y) (Box p)
    Hprofiles Hbox_in) Hy_box).
Qed.

(** Along a nonempty finest path, an original box supplies its body at the
    final class.  Transitivity is exactly what propagates the box through
    intermediate edges. *)
Lemma finest_positive_path_back :
  frame_transitive F ->
  forall X Y p,
    finest_tc_filtered_rel X Y ->
    In (Box p) (subformulas target) ->
    satisfies F V (@representative AtomType F V target X) (Box p) ->
    satisfies F V (@representative AtomType F V target Y) p.
Proof.
  intros Htrans X Y p [n [Hpositive Hpath]].
  destruct n as [|n]; [lia |].
  revert X Y Hpath.
  induction n as [|n IH]; intros X Y Hpath Hbox_in Hbox.
  - pose proof (proj1 (rel_iter_one finest_filtered_rel X Y) Hpath)
      as Hedge.
    exact (finest_filtered_rel_back Hedge Hbox_in Hbox).
  - destruct Hpath as [Z [HXZ HZY]].
    eapply IH; [lia | exact HZY | exact Hbox_in |].
    eapply finest_filtered_rel_preserves_box; eauto.
Qed.

Lemma finest_tc_filtered_rel_forth :
  forall x y,
    Rel F x y ->
    finest_tc_filtered_rel
      (@profile_class AtomType F V target x)
      (@profile_class AtomType F V target y).
Proof.
  intros x y Rxy. apply positive_closure_single.
  now apply finest_filtered_rel_forth.
Qed.

Theorem finest_tc_filtration_truth :
  frame_transitive F ->
  forall p,
    In p (subformulas target) ->
    forall X,
      satisfies finest_tc_filtered_frame finest_tc_filtered_valuation X p <->
      satisfies F V (@representative AtomType F V target X) p.
Proof.
  intros Htrans p; induction p as [a | | p IHp q IHq | p IHp];
    intros Hin X; simpl.
  - reflexivity.
  - tauto.
  - assert (Hp : In p (subformulas target)).
    {
      eapply (@child_is_target_subformula AtomType target
        (Imp p q) p); [exact Hin |].
      simpl. right. apply in_or_app. left. apply subformulas_self.
    }
    assert (Hq : In q (subformulas target)).
    {
      eapply (@child_is_target_subformula AtomType target
        (Imp p q) q); [exact Hin |].
      simpl. right. apply in_or_app. right. apply subformulas_self.
    }
    rewrite IHp by exact Hp. rewrite IHq by exact Hq. reflexivity.
  - assert (Hp : In p (subformulas target)).
    {
      eapply (@child_is_target_subformula AtomType target
        (Box p) p); [exact Hin |].
      simpl. auto using subformulas_self.
    }
    split.
    + intros Hfiltered y Rxy.
      specialize (Hfiltered (@profile_class AtomType F V target y)).
      assert (Hedge : finest_tc_filtered_rel X
        (@profile_class AtomType F V target y)).
      {
        apply positive_closure_single.
        exists (@representative AtomType F V target X), y.
        split.
        - symmetry. apply representative_spec.
        - split; [reflexivity | exact Rxy].
      }
      specialize (Hfiltered Hedge).
      assert (Hprofiles :
        @truth_profile AtomType F V target
          (@representative AtomType F V target
            (@profile_class AtomType F V target y)) =
        @truth_profile AtomType F V target y).
      { apply profile_class_spec. }
      apply (proj1 (@truth_profile_agreement AtomType F V target
        (@representative AtomType F V target
          (@profile_class AtomType F V target y)) y p Hprofiles Hp)).
      apply (proj1 (IHp Hp
        (@profile_class AtomType F V target y))). exact Hfiltered.
    + intros Hbox Y HXY.
      apply (proj2 (IHp Hp Y)).
      eapply finest_positive_path_back; eauto.
Qed.

Corollary finest_tc_filtration_truth_at_class :
  frame_transitive F ->
  forall p,
    In p (subformulas target) ->
    forall w,
      satisfies finest_tc_filtered_frame finest_tc_filtered_valuation
        (@profile_class AtomType F V target w) p <->
      satisfies F V w p.
Proof.
  intros Htrans p Hin w.
  rewrite finest_tc_filtration_truth by assumption.
  apply (@truth_profile_agreement AtomType F V target
    (@representative AtomType F V target
      (@profile_class AtomType F V target w)) w p).
  - apply profile_class_spec.
  - exact Hin.
Qed.

Corollary finest_tc_filtered_frame_finite :
  finite_frame finest_tc_filtered_frame.
Proof.
  exists (@filtered_world_cover AtomType F V target).
  exact (proj1 (proj2
    (@filtered_world_cover_bound AtomType F V target))).
Qed.

Theorem finest_tc_filtered_frame_cover_bound :
  exists cover : list (World finest_tc_filtered_frame),
    NoDup cover /\
    (forall X, In X cover) /\
    length cover <= 2 ^ length (subformulas target).
Proof.
  exists (@filtered_world_cover AtomType F V target).
  apply filtered_world_cover_bound.
Qed.

Lemma finest_tc_is_transitive :
  frame_transitive finest_tc_filtered_frame.
Proof.
  intros X Y Z HXY HYZ.
  change (positive_closure finest_filtered_rel X Z).
  change (positive_closure finest_filtered_rel X Y) in HXY.
  change (positive_closure finest_filtered_rel Y Z) in HYZ.
  exact (positive_closure_transitive HXY HYZ).
Qed.

Lemma finest_tc_preserves_reflexive :
  frame_reflexive F -> frame_reflexive finest_tc_filtered_frame.
Proof.
  intros Hrefl X. apply positive_closure_single.
  apply finest_preserves_reflexive. exact Hrefl.
Qed.

Lemma finest_tc_preserves_serial :
  frame_serial F -> frame_serial finest_tc_filtered_frame.
Proof.
  intros Hserial X.
  destruct (finest_preserves_serial Hserial X) as [Y HXY].
  exists Y. now apply positive_closure_single.
Qed.

Lemma finest_tc_preserves_symmetric :
  frame_symmetric F -> frame_symmetric finest_tc_filtered_frame.
Proof.
  intros Hsym X Y HXY.
  eapply positive_closure_symmetric; [|exact HXY].
  now apply finest_preserves_symmetric.
Qed.

Definition frame_preorder (G : frame) : Prop :=
  frame_reflexive G /\ frame_transitive G.

Definition frame_equivalence (G : frame) : Prop :=
  frame_reflexive G /\ frame_transitive G /\ frame_symmetric G.

Corollary finest_tc_preserves_preorder :
  frame_preorder F -> frame_preorder finest_tc_filtered_frame.
Proof.
  intros [Hrefl _]. split.
  - now apply finest_tc_preserves_reflexive.
  - apply finest_tc_is_transitive.
Qed.

Corollary finest_tc_preserves_equivalence :
  frame_equivalence F -> frame_equivalence finest_tc_filtered_frame.
Proof.
  intros [Hrefl [_ Hsym]]. repeat split.
  - now apply finest_tc_preserves_reflexive.
  - apply finest_tc_is_transitive.
  - now apply finest_tc_preserves_symmetric.
Qed.

End FinestFiltration.
