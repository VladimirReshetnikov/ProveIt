(**
  Structural Kripke frames: clusters, linear examples, unravellings, ranks,
  and balloons.

  This module ports the mathematical theorem surfaces of Foundation's
  [Modal/Kripke/Cluster.lean], [LinearFrame.lean], [Tree.lean], [Rank.lean],
  and [Balloon.lean] at the pinned revision.  Coq has no primitive quotient
  type, so a cluster is represented extensionally by its characteristic
  predicate together with the proposition that it is an equivalence class.
  This gives an actual skeleton [frame], at the standard cost of functional
  and propositional extensionality plus proof irrelevance.

  The local [frame] record has neither a finite-world enumeration nor Lean's
  [Fintype]/[Finite] type classes; its semantic [finite_frame] predicate uses
  an explicit list cover instead.  Point-generated frames, cluster skeletons,
  and bounded linear frames below provide such covers.  The rank section
  exposes the exact algebraic specification of the finite
  converse-well-founded height and proves all path/rank theorems from that
  specification; construction from a [Fintype] is representation specific
  and intentionally not postulated.  The general multi-root
  [extendRoot n] construction belongs to a separate upstream module that is
  not yet present locally; the one-fresh-root case needed for the rank
  successor law is provided below.

  Tree paths are inductive snoc paths rather than list subtypes.  Thus the
  source's list-prefix/[IsChain] characterization is built into constructors;
  its mathematical consequences appear as positive-reachability and exact
  path-length lemmas rather than as a duplicate list-normal-form theorem.
  Foundation's asserted point-generated rank equality is an upstream axiom;
  here rank restriction is definitional and its full rank specification is
  proved.
*)

From Stdlib Require Import Arith.Compare_dec Arith.PeanoNat Lia.
From Stdlib Require Import Arith.Wf_nat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Logic.ClassicalDescription.
From Stdlib Require Import Logic.Classical_Prop.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.PropExtensionality.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Wellfounded.Wellfounded.
From FoundationModal Require Import
  Syntax Axioms Kripke Correspondence Preservation FrameProperties Filtration
  Root Loeb.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Explicit finite covers inherited by generated subframes *)

Definition point_generated_cover (F : frame) (r : World F)
    (xs : list (World F)) : list (World (point_generated_frame F r)) :=
  @sig_filter (World F) (point_generated_member F r)
    (fun x => excluded_middle_informative (point_generated_member F r x)) xs.

Arguments point_generated_cover F r xs : clear implicits.

Lemma point_generated_cover_complete :
  forall F r (xs : list (World F)),
    (forall x, In x xs) ->
    forall y : World (point_generated_frame F r),
      In y (point_generated_cover F r xs).
Proof.
  intros F r xs Hcover y. unfold point_generated_cover.
  apply sig_filter_complete. apply Hcover.
Qed.

Lemma point_generated_cover_nodup :
  forall F r (xs : list (World F)),
    NoDup xs -> NoDup (point_generated_cover F r xs).
Proof.
  intros F r xs Hnodup. unfold point_generated_cover.
  now apply sig_filter_nodup.
Qed.

Theorem point_generated_frame_finite :
  forall F r,
    finite_frame F -> finite_frame (point_generated_frame F r).
Proof.
  intros F r [xs Hcover].
  exists (point_generated_cover F r xs).
  now apply point_generated_cover_complete.
Qed.

(** * Clusters and skeletons *)

Definition cluster_equiv (F : frame) (x y : World F) : Prop :=
  x = y \/ (Rel F x y /\ Rel F y x).

Arguments cluster_equiv F x y : clear implicits.

Lemma cluster_equiv_refl :
  forall (F : frame) x, cluster_equiv F x x.
Proof. intros; now left. Qed.

Lemma cluster_equiv_sym :
  forall (F : frame) x y,
    cluster_equiv F x y -> cluster_equiv F y x.
Proof.
  intros F x y [-> | [Hxy Hyx]].
  - now left.
  - right; auto.
Qed.

Lemma cluster_equiv_trans :
  forall (F : frame),
    frame_transitive F ->
    forall x y z,
      cluster_equiv F x y -> cluster_equiv F y z ->
      cluster_equiv F x z.
Proof.
  intros F Htrans x y z Hxy Hyz.
  destruct Hxy as [-> | [Hxy Hyx]].
  - exact Hyz.
  - destruct Hyz as [-> | [Hyz Hzy]].
    + right; auto.
    + right; split.
      * eapply Htrans; eauto.
      * eapply Htrans; eauto.
Qed.

Definition cluster (F : frame) : Type :=
  { C : World F -> Prop |
      exists c : World F,
        forall x, C x <-> cluster_equiv F c x }.

Arguments cluster F : clear implicits.

Definition cluster_member {F : frame} (C : cluster F) (x : World F) : Prop :=
  proj1_sig C x.

Definition cluster_of (F : frame) (x : World F) : cluster F.
Proof.
  exists (fun y => cluster_equiv F x y).
  exists x; reflexivity.
Defined.

Arguments cluster_of F x : clear implicits.

Lemma cluster_ext :
  forall (F : frame) (C D : cluster F),
    (forall x, cluster_member C x <-> cluster_member D x) -> C = D.
Proof.
  intros F [C HC] [D HD] Hext; simpl in Hext.
  assert (C = D) as ->.
  { apply functional_extensionality; intro x.
    apply propositional_extensionality, Hext. }
  f_equal. apply proof_irrelevance.
Qed.

Lemma cluster_has_representative :
  forall (F : frame) (C : cluster F),
    exists c : World F, C = cluster_of F c.
Proof.
  intros F [C HC]. destruct HC as [c Hc].
  exists c. apply cluster_ext. exact Hc.
Qed.

Lemma cluster_of_eq_iff :
  forall (F : frame),
    frame_transitive F ->
    forall x y,
      cluster_of F x = cluster_of F y <-> cluster_equiv F x y.
Proof.
  intros F Htrans x y; split.
  - intro Heq.
    assert (cluster_member (cluster_of F x) y).
    { rewrite Heq. apply cluster_equiv_refl. }
    exact H.
  - intro Hxy. apply cluster_ext. intro z; simpl.
    split; intro Hxz.
    + eapply cluster_equiv_trans.
      * exact Htrans.
      * apply cluster_equiv_sym. exact Hxy.
      * exact Hxz.
    + eapply cluster_equiv_trans; eauto.
Qed.

Lemma cluster_of_member_iff :
  forall (F : frame) y x,
    cluster_member (cluster_of F y) x <->
    y = x \/ (Rel F y x /\ Rel F x y).
Proof. reflexivity. Qed.

Lemma cluster_member_iff_cluster_of :
  forall F,
    frame_transitive F ->
    forall (C : cluster F) x,
      cluster_member C x <-> C = cluster_of F x.
Proof.
  intros F Htrans C x; split.
  - intro Hx.
    destruct (cluster_has_representative C) as [c ->].
    apply (proj2 (cluster_of_eq_iff Htrans c x)). exact Hx.
  - intro Heq. rewrite Heq. apply cluster_equiv_refl.
Qed.

Lemma cluster_nonempty :
  forall (F : frame) (C : cluster F),
    exists x, cluster_member C x.
Proof.
  intros F C. destruct (cluster_has_representative C) as [c ->].
  exists c. apply cluster_equiv_refl.
Qed.

Definition cluster_rel (F : frame) (C D : cluster F) : Prop :=
  exists x y : World F,
    cluster_member C x /\ cluster_member D y /\ Rel F x y.

Arguments cluster_rel F C D : clear implicits.

Lemma cluster_rel_of_representatives_iff :
  forall (F : frame),
    frame_transitive F ->
    forall x y,
      cluster_rel F (cluster_of F x) (cluster_of F y) <-> Rel F x y.
Proof.
  intros F Htrans x y; split.
  - intros [a [b [Hxa [Hyb Hab]]]].
    destruct Hxa as [Hxa | [Hxa Hax]].
    + subst a. destruct Hyb as [Hyb | [Hyb Hby]].
      * now subst b.
      * eapply Htrans; eauto.
    + destruct Hyb as [Hyb | [Hyb Hby]].
      * subst b. eapply Htrans; eauto.
      * eapply Htrans; [exact Hxa |].
      eapply Htrans; eauto.
  - intro Hxy. exists x, y; split.
    + apply cluster_equiv_refl.
    + split; [apply cluster_equiv_refl | exact Hxy].
Qed.

Lemma cluster_rel_transitive :
  forall F,
    frame_transitive F ->
    forall C D E,
      cluster_rel F C D -> cluster_rel F D E -> cluster_rel F C E.
Proof.
  intros F Htrans C D E HCD HDE.
  destruct (cluster_has_representative C) as [x ->].
  destruct (cluster_has_representative D) as [y ->].
  destruct (cluster_has_representative E) as [z ->].
  apply (proj2 (cluster_rel_of_representatives_iff Htrans x z)).
  eapply Htrans.
  - now apply (proj1 (cluster_rel_of_representatives_iff Htrans x y)).
  - now apply (proj1 (cluster_rel_of_representatives_iff Htrans y z)).
Qed.

Lemma cluster_rel_antisymmetric :
  forall F,
    frame_transitive F ->
    forall C D,
      cluster_rel F C D -> cluster_rel F D C -> C = D.
Proof.
  intros F Htrans C D HCD HDC.
  destruct (cluster_has_representative C) as [x ->].
  destruct (cluster_has_representative D) as [y ->].
  apply (proj2 (cluster_of_eq_iff Htrans x y)). right; split.
  - now apply (proj1 (cluster_rel_of_representatives_iff Htrans x y)).
  - now apply (proj1 (cluster_rel_of_representatives_iff Htrans y x)).
Qed.

Lemma cluster_rel_reflexive :
  forall F,
    frame_reflexive F -> forall C, cluster_rel F C C.
Proof.
  intros F Hrefl C.
  destruct (cluster_nonempty C) as [x Hx].
  exists x, x; auto.
Qed.

Lemma cluster_rel_total :
  forall F,
    frame_strongly_connected F ->
    forall C D, cluster_rel F C D \/ cluster_rel F D C.
Proof.
  intros F Htotal C D.
  destruct (cluster_nonempty C) as [x Hx].
  destruct (cluster_nonempty D) as [y Hy].
  destruct (Htotal x y) as [Hxy | Hyx].
  - left. exists x, y; auto.
  - right. exists y, x; auto.
Qed.

Definition cluster_strict_rel (F : frame) (C D : cluster F) : Prop :=
  cluster_rel F C D /\ C <> D.

Arguments cluster_strict_rel F C D : clear implicits.

Lemma cluster_strict_rel_transitive :
  forall F,
    frame_transitive F ->
    forall C D E,
      cluster_strict_rel F C D -> cluster_strict_rel F D E ->
      cluster_strict_rel F C E.
Proof.
  intros F Htrans C D E [HCD HneqCD] [HDE HneqDE].
  split.
  - eapply cluster_rel_transitive; eauto.
  - intro Heq. subst E.
    assert (C = D).
    { eapply cluster_rel_antisymmetric; eauto. }
    contradiction.
Qed.

Lemma cluster_strict_rel_irreflexive :
  forall F C, ~ cluster_strict_rel F C C.
Proof. firstorder. Qed.

Lemma cluster_strict_rel_asymmetric :
  forall F,
    frame_transitive F ->
    forall C D,
      cluster_strict_rel F C D -> ~ cluster_strict_rel F D C.
Proof.
  intros F Htrans C D [HCD Hneq] [HDC _].
  apply Hneq. eapply cluster_rel_antisymmetric; eauto.
Qed.

Lemma cluster_strict_rel_trichotomous :
  forall F,
    frame_transitive F -> frame_connected F ->
    forall C D,
      cluster_strict_rel F C D \/ C = D \/ cluster_strict_rel F D C.
Proof.
  intros F Htrans Hconn C D.
  destruct (cluster_has_representative C) as [x ->].
  destruct (cluster_has_representative D) as [y ->].
  destruct (Hconn x y) as [Hxy | [-> | Hyx]].
  - destruct (classic (cluster_of F x = cluster_of F y)) as [Heq | Hneq].
    + now right; left.
    + left; split; [apply cluster_rel_of_representatives_iff; auto | exact Hneq].
  - now right; left.
  - destruct (classic (cluster_of F x = cluster_of F y)) as [Heq | Hneq].
    + now right; left.
    + right; right; split.
      * apply cluster_rel_of_representatives_iff; auto.
      * intro Heq. apply Hneq. symmetry. exact Heq.
Qed.

Definition skeleton_frame (F : frame) : frame :=
  {| World := cluster F; Rel := cluster_rel F |}.

Definition strict_skeleton_frame (F : frame) : frame :=
  {| World := cluster F; Rel := cluster_strict_rel F |}.

Arguments skeleton_frame F : clear implicits.
Arguments strict_skeleton_frame F : clear implicits.

Lemma skeleton_transitive :
  forall F, frame_transitive F -> frame_transitive (skeleton_frame F).
Proof. exact cluster_rel_transitive. Qed.

Lemma skeleton_antisymmetric :
  forall F, frame_transitive F -> frame_antisymmetric (skeleton_frame F).
Proof. exact cluster_rel_antisymmetric. Qed.

Lemma skeleton_reflexive :
  forall F, frame_reflexive F -> frame_reflexive (skeleton_frame F).
Proof. exact cluster_rel_reflexive. Qed.

Lemma skeleton_partial_order :
  forall F,
    frame_reflexive F -> frame_transitive F ->
    frame_is_partial_order (skeleton_frame F).
Proof.
  intros F Hrefl Htrans; repeat split.
  - now apply skeleton_reflexive.
  - now apply skeleton_transitive.
  - now apply skeleton_antisymmetric.
Qed.

Lemma skeleton_total :
  forall F,
    frame_strongly_connected F ->
    frame_strongly_connected (skeleton_frame F).
Proof. exact cluster_rel_total. Qed.

Lemma strict_skeleton_transitive :
  forall F,
    frame_transitive F -> frame_transitive (strict_skeleton_frame F).
Proof. exact cluster_strict_rel_transitive. Qed.

Lemma strict_skeleton_irreflexive :
  forall F, frame_irreflexive (strict_skeleton_frame F).
Proof. exact cluster_strict_rel_irreflexive. Qed.

Lemma strict_skeleton_asymmetric :
  forall F,
    frame_transitive F -> frame_asymmetric (strict_skeleton_frame F).
Proof. exact cluster_strict_rel_asymmetric. Qed.

Lemma strict_skeleton_connected :
  forall F,
    frame_transitive F -> frame_connected F ->
    frame_connected (strict_skeleton_frame F).
Proof. exact cluster_strict_rel_trichotomous. Qed.

(** A list cover is the local counterpart of Foundation's inherited
    [Finite (Cluster F)] instance. *)
Definition cluster_cover (F : frame) (xs : list (World F))
    : list (cluster F) :=
  map (cluster_of F) xs.

Arguments cluster_cover F xs : clear implicits.

Lemma cluster_cover_complete :
  forall F,
    frame_transitive F ->
    forall (xs : list (World F)),
      (forall x, In x xs) ->
      forall C : cluster F, In C (cluster_cover F xs).
Proof.
  intros F Htrans xs Hcover C.
  destruct (cluster_nonempty C) as [x Hx].
  apply (proj1 (cluster_member_iff_cluster_of Htrans C x)) in Hx.
  subst C. unfold cluster_cover. apply in_map. apply Hcover.
Qed.

Theorem skeleton_finite :
  forall F,
    frame_transitive F -> finite_frame F ->
    finite_frame (skeleton_frame F).
Proof.
  intros F Htrans [xs Hcover].
  exists (cluster_cover F xs).
  now apply cluster_cover_complete.
Qed.

Theorem strict_skeleton_finite :
  forall F,
    frame_transitive F -> finite_frame F ->
    finite_frame (strict_skeleton_frame F).
Proof.
  intros F Htrans [xs Hcover].
  exists (cluster_cover F xs).
  now apply cluster_cover_complete.
Qed.

(** * Membership and the three cluster shapes *)

Lemma cluster_members_same :
  forall F,
    frame_transitive F ->
    forall (C : cluster F) x y,
      cluster_member C x -> cluster_member C y ->
      y = x \/ (Rel F y x /\ Rel F x y).
Proof.
  intros F Htrans C x y Hx Hy.
  destruct (cluster_has_representative C) as [c ->].
  destruct Hx as [Hcx | [Hcx Hxc]];
    destruct Hy as [Hcy | [Hcy Hyc]]; subst; auto.
  right; split; eapply Htrans; eauto.
Qed.

Lemma cluster_reflexive_of_self_rel :
  forall F,
    frame_transitive F ->
    forall (C : cluster F),
      cluster_rel F C C ->
      forall x, cluster_member C x -> Rel F x x.
Proof.
  intros F Htrans C HCC x Hx.
  destruct HCC as [a [b [Ha [Hb Hab]]]].
  destruct (@cluster_members_same F Htrans C x a Hx Ha)
    as [Haxeq | [Hax Hxa]].
  - subst a.
    destruct (@cluster_members_same F Htrans C x b Hx Hb)
      as [Hbeq | [Hbx Hxb]].
    + now subst b.
    + eapply Htrans; eauto.
  - eapply Htrans; eauto.
Qed.

Lemma cluster_reflexive_if_multiple :
  forall F,
    frame_transitive F ->
    forall (C : cluster F),
      (exists x y,
          x <> y /\ cluster_member C x /\ cluster_member C y) ->
      forall z, cluster_member C z -> Rel F z z.
Proof.
  intros F Htrans C [x [y [Hneq [Hx Hy]]]] z Hz.
  apply cluster_reflexive_of_self_rel with (C := C); auto.
  destruct (@cluster_members_same F Htrans C x y Hx Hy)
    as [Heq | [Hyx Hxy]].
  - exfalso. apply Hneq. symmetry. exact Heq.
  - exists x, y; auto.
Qed.

Definition cluster_degenerate {F : frame} (C : cluster F) : Prop :=
  ~ cluster_rel F C C.

Definition cluster_simple {F : frame} (C : cluster F) : Prop :=
  exists x,
    cluster_member C x /\ Rel F x x /\
    forall y, cluster_member C y /\ Rel F y y -> y = x.

Definition cluster_proper {F : frame} (C : cluster F) : Prop :=
  exists x y,
    x <> y /\ cluster_member C x /\ cluster_member C y.

Lemma cluster_degenerate_no_multiple :
  forall F,
    frame_transitive F ->
    forall C : cluster F, cluster_degenerate C -> ~ cluster_proper C.
Proof.
  intros F Htrans C Hdeg Hproper.
  apply Hdeg.
  destruct Hproper as [x [y [Hneq [Hx Hy]]]].
  destruct (@cluster_members_same F Htrans C x y Hx Hy)
    as [Heq | [Hyx Hxy]].
  - exfalso. apply Hneq. symmetry. exact Heq.
  - exists x, y; auto.
Qed.

Theorem cluster_degenerate_iff_unique_irreflexive :
  forall F,
    frame_transitive F ->
    forall C : cluster F,
      cluster_degenerate C <->
      exists x,
        cluster_member C x /\ ~ Rel F x x /\
        forall y, cluster_member C y /\ ~ Rel F y y -> y = x.
Proof.
  intros F Htrans C; split.
  - intro Hdeg.
    destruct (cluster_nonempty C) as [x Hx].
    exists x; split; [exact Hx |].
    split.
    + intro Hxx. apply Hdeg. exists x, x; auto.
    + intros y [Hy Hyy].
      destruct (classic (y = x)) as [Heq | Hneq]; auto.
      exfalso. apply (@cluster_degenerate_no_multiple F Htrans C Hdeg).
      exists x, y; auto.
  - intros [x [Hx [Hirr Hunique]]] HCC.
    apply Hirr.
    now apply (@cluster_reflexive_of_self_rel F Htrans C HCC x Hx).
Qed.

Lemma cluster_not_degenerate_of_simple :
  forall F,
    frame_transitive F ->
    forall C : cluster F, cluster_simple C -> ~ cluster_degenerate C.
Proof.
  intros F Htrans C [x [Hx [Hxx Hunique]]] Hdeg.
  apply Hdeg. exists x, x; auto.
Qed.

Lemma cluster_reflexive_in_simple :
  forall F,
    frame_transitive F ->
    forall C : cluster F, cluster_simple C ->
    forall x, cluster_member C x -> Rel F x x.
Proof.
  intros F Htrans C [y [Hy [Hyy Hunique]]] x Hx.
  destruct (@cluster_members_same F Htrans C x y Hx Hy)
    as [-> | [Hyx Hxy]]; auto.
  eapply Htrans; eauto.
Qed.

Lemma cluster_not_degenerate_of_proper :
  forall F,
    frame_transitive F ->
    forall C : cluster F, cluster_proper C -> ~ cluster_degenerate C.
Proof.
  intros F Htrans C Hproper Hdeg.
  exact (@cluster_degenerate_no_multiple F Htrans C Hdeg Hproper).
Qed.

Lemma cluster_reflexive_in_proper :
  forall F,
    frame_transitive F ->
    forall C : cluster F, cluster_proper C ->
    forall x, cluster_member C x -> Rel F x x.
Proof. exact cluster_reflexive_if_multiple. Qed.

Lemma cluster_simple_or_proper_of_non_degenerate :
  forall F,
    frame_transitive F ->
    forall C : cluster F, ~ cluster_degenerate C ->
      cluster_simple C \/ cluster_proper C.
Proof.
  intros F Htrans C Hnondeg.
  destruct (cluster_nonempty C) as [x Hx].
  destruct (classic (exists y, y <> x /\ cluster_member C y))
    as [[y [Hneq Hy]] | Hsingle].
  - right. exists x, y; auto.
  - left. exists x; split; [exact Hx |].
    assert (HCC : cluster_rel F C C) by
      (apply NNPP; exact Hnondeg).
    split.
    + now apply (@cluster_reflexive_of_self_rel F Htrans C HCC x Hx).
    + intros y [Hy Hyy].
      destruct (classic (y = x)) as [Heq | Hneq]; auto.
      exfalso. apply Hsingle. now exists y.
Qed.

Lemma cluster_reflexive_of_non_degenerate :
  forall F,
    frame_transitive F ->
    forall C : cluster F, ~ cluster_degenerate C ->
    forall x, cluster_member C x -> Rel F x x.
Proof.
  intros F Htrans C Hnondeg x Hx.
  destruct (@cluster_simple_or_proper_of_non_degenerate F Htrans C Hnondeg)
    as [Hsimple | Hproper].
  - now apply (@cluster_reflexive_in_simple F Htrans C Hsimple x Hx).
  - now apply (@cluster_reflexive_in_proper F Htrans C Hproper x Hx).
Qed.

Theorem cluster_shape_trichotomy :
  forall F,
    frame_transitive F ->
    forall C : cluster F,
      cluster_degenerate C \/ cluster_simple C \/ cluster_proper C.
Proof.
  intros F Htrans C.
  destruct (classic (cluster_degenerate C)) as [Hdeg | Hnondeg].
  - now left.
  - right. now apply cluster_simple_or_proper_of_non_degenerate.
Qed.

(** * Standard linear frames *)

Definition nat_lt_frame : frame :=
  {| World := nat; Rel := lt |}.

Definition nat_le_frame : frame :=
  {| World := nat; Rel := le |}.

Lemma nat_lt_transitive : frame_transitive nat_lt_frame.
Proof. intros x y z; apply Nat.lt_trans. Qed.

Lemma nat_lt_irreflexive : frame_irreflexive nat_lt_frame.
Proof. exact Nat.lt_irrefl. Qed.

Lemma nat_lt_asymmetric : frame_asymmetric nat_lt_frame.
Proof.
  exact (@irreflexive_transitive_asymmetric
    nat_lt_frame nat_lt_irreflexive nat_lt_transitive).
Qed.

Lemma nat_lt_serial : frame_serial nat_lt_frame.
Proof. intro x; exists (S x); change (x < S x); lia. Qed.

Lemma nat_lt_piecewise_connected :
  frame_piecewise_connected nat_lt_frame.
Proof.
  intros x y z Hxy Hxz.
  destruct (Nat.lt_trichotomy y z) as [Hyz | [Heq | Hzy]]; auto.
Qed.

Lemma nat_lt_root : frame_root nat_lt_frame 0.
Proof. intros x Hneq; change (0 < x); lia. Qed.

Lemma nat_lt_rooted : frame_rooted nat_lt_frame.
Proof. exists 0; apply nat_lt_root. Qed.

Lemma nat_le_transitive : frame_transitive nat_le_frame.
Proof. intros x y z; apply Nat.le_trans. Qed.

Lemma nat_le_reflexive : frame_reflexive nat_le_frame.
Proof. exact Nat.le_refl. Qed.

Lemma nat_le_antisymmetric : frame_antisymmetric nat_le_frame.
Proof. intros x y; apply Nat.le_antisymm. Qed.

Lemma nat_le_root : frame_root nat_le_frame 0.
Proof. intros x Hneq; change (0 <= x); lia. Qed.

Lemma nat_le_rooted : frame_rooted nat_le_frame.
Proof. exists 0; apply nat_le_root. Qed.

Definition bounded_nat (n : nat) : Type := { k : nat | k < n }.

Definition fin_lt_frame (n : nat) : frame :=
  {| World := bounded_nat n;
     Rel := fun x y => proj1_sig x < proj1_sig y |}.

Definition fin_le_frame (n : nat) : frame :=
  {| World := bounded_nat n;
     Rel := fun x y => proj1_sig x <= proj1_sig y |}.

Lemma fin_lt_transitive :
  forall n, frame_transitive (fin_lt_frame n).
Proof. intros n x y z; apply Nat.lt_trans. Qed.

Lemma fin_lt_irreflexive :
  forall n, frame_irreflexive (fin_lt_frame n).
Proof. intros n [x Hx]; apply Nat.lt_irrefl. Qed.

Lemma fin_le_transitive :
  forall n, frame_transitive (fin_le_frame n).
Proof. intros n x y z; apply Nat.le_trans. Qed.

Lemma fin_le_reflexive :
  forall n, frame_reflexive (fin_le_frame n).
Proof. intros n [x Hx]; apply Nat.le_refl. Qed.

Lemma fin_le_antisymmetric :
  forall n, frame_antisymmetric (fin_le_frame n).
Proof.
  intros n [x Hx] [y Hy] Hxy Hyx; simpl in *.
  assert (x = y) as -> by lia.
  f_equal. apply proof_irrelevance.
Qed.

(** The bounded carrier is enumerated explicitly, retaining both the bound
    proofs and duplicate-freedom. *)
Definition bounded_nat_cover (n : nat) : list (bounded_nat n) :=
  @sig_filter nat (fun k => k < n) (fun k => lt_dec k n) (seq 0 n).

Arguments bounded_nat_cover n : clear implicits.

Lemma bounded_nat_cover_nodup :
  forall n, NoDup (bounded_nat_cover n).
Proof.
  intro n. unfold bounded_nat_cover.
  apply sig_filter_nodup, seq_NoDup.
Qed.

Lemma bounded_nat_cover_complete :
  forall n (x : bounded_nat n), In x (bounded_nat_cover n).
Proof.
  intros n x. unfold bounded_nat_cover.
  apply sig_filter_complete.
  apply in_seq. destruct x as [x Hx]; simpl. lia.
Qed.

Theorem bounded_nat_finite_cover :
  forall n,
    NoDup (bounded_nat_cover n) /\
    forall x : bounded_nat n, In x (bounded_nat_cover n).
Proof.
  intro n; split.
  - apply bounded_nat_cover_nodup.
  - apply bounded_nat_cover_complete.
Qed.

Corollary fin_lt_finite :
  forall n, finite_frame (fin_lt_frame n).
Proof.
  intro n. exists (bounded_nat_cover n).
  apply bounded_nat_cover_complete.
Qed.

Corollary fin_le_finite :
  forall n, finite_frame (fin_le_frame n).
Proof.
  intro n. exists (bounded_nat_cover n).
  apply bounded_nat_cover_complete.
Qed.

(** Goldblatt, Exercise 8.1(1).  The descending induction is over the finite
    interval between the queried successor and the witness for [◇□p]. *)
Theorem nat_lt_validates_Z :
  valid nat_lt_frame (Z (Atom 0)).
Proof.
  intros V x.
  unfold Z; simpl.
  intros Hstep Hdia y Hxy.
  assert (Hex : exists z, x < z /\ forall u, z < u -> V 0 u).
  { apply NNPP. intro Hnone. apply Hdia.
    intros z Hxz Hz. apply Hnone. exists z; auto. }
  destruct Hex as [z [Hxz Hz]].
  assert (Hback :
    forall d y,
      z - y = d -> x < y -> y <= z -> V 0 y).
  {
    intro d. induction d using lt_wf_ind.
    intros y' Hdist Hxy' Hyz.
    apply Hstep; [exact Hxy' |].
    intros u Hyu.
    destruct (Nat.le_gt_cases u z) as [Huz | Hzu].
    - apply (H (z - u)).
      + lia.
      + reflexivity.
      + lia.
      + exact Huz.
    - apply Hz. exact Hzu.
  }
  destruct (Nat.le_gt_cases y z) as [Hyz | Hzy].
  - exact (Hback (z - y) y eq_refl Hxy Hyz).
  - apply Hz. exact Hzy.
Qed.

(** Goldblatt, Exercise 8.9.  As in Foundation, reflexive accessibility makes
    the induction invariant slightly stronger: every already-established
    point also establishes the boxed persistence premise needed one step
    below it. *)
Theorem nat_le_validates_Dum :
  valid nat_le_frame (Dum (Atom 0)).
Proof.
  intros V x.
  unfold Dum; simpl.
  intros Hstep Hdia.
  assert (Hex : exists y, x <= y /\ forall z, y <= z -> V 0 z).
  { apply NNPP. intro Hnone. apply Hdia.
    intros y Hxy Hy. apply Hnone. exists y; auto. }
  destruct Hex as [y [Hxy Hy]].
  assert (Hback :
    forall d u,
      y - u = d -> x <= u -> u <= y -> V 0 u).
  {
    intro d. induction d using lt_wf_ind.
    intros u Hdist Hxu Huy.
    apply Hstep; [exact Hxu |].
    intros v Huv Hv w Hvw.
    destruct (Nat.le_gt_cases y w) as [Hyw | Hwy].
    - apply Hy. exact Hyw.
    - assert (Hwy_le : w <= y) by lia.
      destruct (Nat.eq_dec w u) as [-> | Hwu].
      + assert (v = u) by lia. now subst v.
      + apply (H (y - w)).
        * lia.
        * reflexivity.
        * lia.
        * exact Hwy_le.
  }
  exact (Hback (y - x) x eq_refl (Nat.le_refl x) Hxy).
Qed.

(** * Tree unravellings *)

(** A rooted path is indexed by its endpoint.  This is equivalent to the
    nonempty chained-list subtype used by Foundation, but records the chain
    proof structurally. *)
Inductive rooted_path (F : frame) (r : World F) : World F -> Type :=
| rooted_path_root : @rooted_path F r r
| rooted_path_snoc :
    forall x, @rooted_path F r x ->
    forall y, Rel F x y -> @rooted_path F r y.

Arguments rooted_path F r x : clear implicits.
Arguments rooted_path_root F r : clear implicits.
Arguments rooted_path_snoc F r x p y h : clear implicits.

Definition tree_world (F : frame) (r : World F) : Type :=
  { x : World F & rooted_path F r x }.

Arguments tree_world F r : clear implicits.

Definition tree_endpoint {F : frame} {r : World F}
    (p : tree_world F r) : World F := projT1 p.

Definition tree_root (F : frame) (r : World F) : tree_world F r :=
  existT _ r (rooted_path_root F r).

Arguments tree_root F r : clear implicits.

Definition tree_snoc {F : frame} {r : World F}
    (p : tree_world F r) (y : World F)
    (h : Rel F (tree_endpoint p) y) : tree_world F r :=
  existT _ y
    (rooted_path_snoc F r (tree_endpoint p) (projT2 p) y h).

Arguments tree_snoc {F r} p y h.

Definition tree_immediate_rel (F : frame) (r : World F)
    (p q : tree_world F r) : Prop :=
  exists h : Rel F (tree_endpoint p) (tree_endpoint q),
    q = tree_snoc p (tree_endpoint q) h.

Arguments tree_immediate_rel F r p q : clear implicits.

Definition tree_unravelling (F : frame) (r : World F) : frame :=
  {| World := tree_world F r;
     Rel := tree_immediate_rel F r |}.

Arguments tree_unravelling F r : clear implicits.

Definition trans_tree_unravelling (F : frame) (r : World F) : frame :=
  frame_trans_gen (tree_unravelling F r).

Arguments trans_tree_unravelling F r : clear implicits.

Fixpoint rooted_path_length {F : frame} {r x : World F}
    (p : rooted_path F r x) : nat :=
  match p with
  | rooted_path_root _ _ => 0
  | rooted_path_snoc _ _ _ p' _ _ => S (rooted_path_length p')
  end.

Definition tree_length {F : frame} {r : World F}
    (p : tree_world F r) : nat := rooted_path_length (projT2 p).

Fixpoint rooted_path_nodes {F : frame} {r x : World F}
    (p : rooted_path F r x) : list (World F) :=
  match p with
  | rooted_path_root _ _ => [r]
  | rooted_path_snoc _ _ _ p' y _ => rooted_path_nodes p' ++ [y]
  end.

Definition tree_nodes {F : frame} {r : World F}
    (p : tree_world F r) : list (World F) := rooted_path_nodes (projT2 p).

Lemma rooted_path_nodes_nonempty :
  forall (F : frame) (r x : World F) (p : rooted_path F r x),
    rooted_path_nodes p <> [].
Proof.
  intros F r x p; induction p; simpl.
  - discriminate.
  - intro Hnil. apply app_eq_nil in Hnil. tauto.
Qed.

Lemma tree_nodes_nonempty :
  forall (F : frame) (r : World F) (p : tree_world F r),
    tree_nodes p <> [].
Proof. intros F r [x p]; apply rooted_path_nodes_nonempty. Qed.

Lemma tree_length_snoc :
  forall (F : frame) (r : World F) (p : tree_world F r)
         (y : World F) (h : Rel F (tree_endpoint p) y),
    tree_length (tree_snoc p y h) = S (tree_length p).
Proof. reflexivity. Qed.

Lemma tree_immediate_length :
  forall (F : frame) (r : World F)
         (p q : World (tree_unravelling F r)),
    Rel (tree_unravelling F r) p q ->
    tree_length p < tree_length q.
Proof.
  intros F r p q [h ->]. rewrite tree_length_snoc. lia.
Qed.

Lemma tree_immediate_irreflexive :
  forall (F : frame) (r : World F),
    frame_irreflexive (tree_unravelling F r).
Proof.
  intros F r p Hpp.
  pose proof (tree_immediate_length Hpp). lia.
Qed.

Lemma tree_immediate_asymmetric :
  forall (F : frame) (r : World F),
    frame_asymmetric (tree_unravelling F r).
Proof.
  intros F r p q Hpq Hqp.
  pose proof (tree_immediate_length Hpq).
  pose proof (tree_immediate_length Hqp). lia.
Qed.

Lemma tree_root_or_positive :
  forall (F : frame) (r : World F)
         (p : World (tree_unravelling F r)),
    p = tree_root F r \/
    relation_positive_closure (Rel (tree_unravelling F r))
      (tree_root F r) p.
Proof.
  intros F r [x p]. induction p.
  - now left.
  - right.
    set (q := existT (fun z => rooted_path F r z) x p).
    assert (Hstep :
      Rel (tree_unravelling F r) q (tree_snoc q y r0)).
    { exists r0. reflexivity. }
    destruct IHp as [Heq | Hpos].
    + rewrite <- Heq. now apply positive_closure_base.
    + eapply positive_closure_transitive.
      * exact Hpos.
      * now apply positive_closure_base.
Qed.

Theorem tree_unravelling_trans_rooted :
  forall (F : frame) (r : World F),
    frame_trans_rooted (tree_unravelling F r).
Proof.
  intros F r. exists (tree_root F r).
  intros p Hneq.
  destruct (@tree_root_or_positive F r p) as [Heq | Hpos];
    [contradiction | exact Hpos].
Qed.

Theorem trans_tree_unravelling_rooted :
  forall (F : frame) (r : World F),
    frame_rooted (trans_tree_unravelling F r).
Proof.
  intros F r. exists (tree_root F r).
  intros p Hneq.
  destruct (@tree_root_or_positive F r p) as [Heq | Hpos];
    [contradiction | exact Hpos].
Qed.

Lemma tree_rel_iter_length :
  forall (F : frame) (r : World F) n
         (p q : World (tree_unravelling F r)),
    rel_iter (Rel (tree_unravelling F r)) n p q ->
    tree_length q = tree_length p + n.
Proof.
  intros F r n; induction n as [|n IH]; intros p q Hpq.
  - simpl in Hpq. subst q. lia.
  - destruct Hpq as [u [Hpu Huq]].
    rewrite (IH u q Huq).
    pose proof (tree_immediate_length Hpu).
    destruct Hpu as [h ->]. rewrite tree_length_snoc. lia.
Qed.

Lemma tree_positive_length :
  forall (F : frame) (r : World F)
         (p q : World (tree_unravelling F r)),
    relation_positive_closure (Rel (tree_unravelling F r)) p q ->
    tree_length p < tree_length q.
Proof.
  intros F r p q [n [Hn Hpq]].
  rewrite (tree_rel_iter_length Hpq). lia.
Qed.

Lemma trans_tree_transitive :
  forall (F : frame) (r : World F),
    frame_transitive (trans_tree_unravelling F r).
Proof. intros; apply frame_trans_gen_transitive. Qed.

Lemma trans_tree_irreflexive :
  forall (F : frame) (r : World F),
    frame_irreflexive (trans_tree_unravelling F r).
Proof.
  intros F r p Hpp.
  exact (Nat.lt_irrefl _ (tree_positive_length Hpp)).
Qed.

Lemma trans_tree_asymmetric :
  forall (F : frame) (r : World F),
    frame_asymmetric (trans_tree_unravelling F r).
Proof.
  intros F r.
  apply irreflexive_transitive_asymmetric.
  - apply trans_tree_irreflexive.
  - apply trans_tree_transitive.
Qed.

Definition frame_is_tree (F : frame) : Prop :=
  frame_rooted F /\ frame_asymmetric F /\ frame_transitive F.

Theorem trans_tree_is_tree :
  forall (F : frame) (r : World F),
    frame_is_tree (trans_tree_unravelling F r).
Proof.
  intros; repeat split.
  - apply trans_tree_unravelling_rooted.
  - apply trans_tree_asymmetric.
  - apply trans_tree_transitive.
Qed.

Definition tree_endpoint_p_morphism (F : frame) (r : World F)
    : p_morphism (tree_unravelling F r) F.
Proof.
  refine {| pmap := fun p : World (tree_unravelling F r) =>
                       tree_endpoint p |}.
  - intros p q [h ->]. exact h.
  - intros p y Hpy.
    exists (tree_snoc p y Hpy); split; [reflexivity |].
    exists Hpy. reflexivity.
Defined.

Arguments tree_endpoint_p_morphism F r : clear implicits.

Definition trans_tree_endpoint_p_morphism
    (F : frame) (r : World F) (Htrans : frame_transitive F)
    : p_morphism (trans_tree_unravelling F r) F.
Proof.
  refine {| pmap := fun p : World (trans_tree_unravelling F r) =>
                       tree_endpoint p |}.
  - intros p q Hpq.
    apply (proj1 (positive_closure_of_transitive_iff Htrans _ _)).
    destruct Hpq as [n [Hn Hpq]].
    exists n; split; [exact Hn |].
    exact (p_morphism_forth_iter (tree_endpoint_p_morphism F r) Hpq).
  - intros p y Hpy.
    exists (tree_snoc p y Hpy); split; [reflexivity |].
    apply positive_closure_base. exists Hpy. reflexivity.
Defined.

Arguments trans_tree_endpoint_p_morphism F r Htrans : clear implicits.

Definition tree_valuation {AtomType}
    (F : frame) (V : valuation AtomType F) (r : World F)
    : valuation AtomType (tree_unravelling F r) :=
  fun a p => V a (tree_endpoint p).

Definition trans_tree_valuation {AtomType}
    (F : frame) (V : valuation AtomType F) (r : World F)
    : valuation AtomType (trans_tree_unravelling F r) :=
  fun a p => V a (tree_endpoint p).

Arguments tree_valuation {AtomType F} V r.
Arguments trans_tree_valuation {AtomType F} V r.

Theorem tree_unravelling_truth :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F)
         (r : World F) (p : World (tree_unravelling F r))
         (A : formula AtomType),
    satisfies (tree_unravelling F r) (tree_valuation V r) p A <->
    satisfies F V (tree_endpoint p) A.
Proof.
  intros. exact (p_morphism_truth (tree_endpoint_p_morphism F r) V p A).
Qed.

Theorem trans_tree_unravelling_truth :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F)
         (r : World F) (Htrans : frame_transitive F)
         (p : World (trans_tree_unravelling F r))
         (A : formula AtomType),
    satisfies (trans_tree_unravelling F r)
      (trans_tree_valuation V r) p A <->
    satisfies F V (tree_endpoint p) A.
Proof.
  intros.
  exact (p_morphism_truth
    (trans_tree_endpoint_p_morphism F r Htrans) V p A).
Qed.

Theorem trans_tree_unravelling_truth_at_root :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F)
         (r : World F) (Htrans : frame_transitive F)
         (A : formula AtomType),
    satisfies (trans_tree_unravelling F r)
      (trans_tree_valuation V r) (tree_root F r) A <->
    satisfies F V r A.
Proof.
  intros.
  exact (@trans_tree_unravelling_truth AtomType F V r Htrans
    (tree_root F r) A).
Qed.

(** * Finite converse-well-founded ranks *)

(** These are exactly the two characteristic properties of Foundation's
    [cwfHeight] on a finite transitive frame: accessibility strictly lowers
    rank, and every lower level is represented by an accessible world. *)
Record frame_rank_spec (F : frame) (rank : World F -> nat) : Prop := {
  rank_rel_decreases :
    forall x y, Rel F x y -> rank y < rank x;
  rank_realizes_lower_level :
    forall x n, n < rank x ->
      exists y, Rel F x y /\ rank y = n
}.

Arguments frame_rank_spec F rank : clear implicits.
Arguments rank_rel_decreases {F rank} _ x y _.
Arguments rank_realizes_lower_level {F rank} _ x n _.

Lemma rank_lt_of_rel :
  forall F rank,
    frame_rank_spec F rank ->
    forall x y, Rel F x y -> rank y < rank x.
Proof. intros F rank Hrank x y Hxy; exact (rank_rel_decreases Hrank x y Hxy). Qed.

Lemma rank_exists_of_lt :
  forall F rank,
    frame_rank_spec F rank ->
    forall x n, n < rank x ->
      exists y, Rel F x y /\ rank y = n.
Proof.
  intros F rank Hrank x n Hn.
  exact (rank_realizes_lower_level Hrank x n Hn).
Qed.

Lemma rank_spec_irreflexive :
  forall F rank,
    frame_rank_spec F rank -> frame_irreflexive F.
Proof.
  intros F rank Hrank x Hxx.
  pose proof (rank_rel_decreases Hrank x x Hxx). lia.
Qed.

Lemma rank_iter_bound :
  forall F rank,
    frame_rank_spec F rank ->
    forall n x y,
      rel_iter (Rel F) n x y -> n + rank y <= rank x.
Proof.
  intros F rank Hrank n; induction n as [|n IH]; intros x y Hxy.
  - simpl in Hxy. subst y. lia.
  - destruct Hxy as [z [Hxz Hzy]].
    pose proof (rank_rel_decreases Hrank x z Hxz).
    pose proof (IH z y Hzy). lia.
Qed.

Lemma rank_path_exists :
  forall F rank,
    frame_rank_spec F rank ->
    forall n x, n <= rank x ->
      exists y, rel_iter (Rel F) n x y.
Proof.
  intros F rank Hrank n; induction n as [|n IH]; intros x Hnx.
  - exists x; reflexivity.
  - assert (Hlower : n < rank x) by lia.
    destruct (rank_realizes_lower_level Hrank x n Hlower)
      as [z [Hxz Hzrank]].
    destruct (IH z) as [y Hzy]; [lia |].
    exists y. exists z; auto.
Qed.

Theorem rank_lt_iff_no_iter :
  forall F rank,
    frame_rank_spec F rank ->
    forall n x,
      rank x < n <->
      forall y, ~ rel_iter (Rel F) n x y.
Proof.
  intros F rank Hrank n x; split.
  - intros Hlt y Hpath.
    pose proof (rank_iter_bound Hrank Hpath). lia.
  - intro Hnone.
    destruct (Nat.lt_ge_cases (rank x) n) as [Hlt | Hge]; auto.
    destruct (rank_path_exists Hrank Hge) as [y Hpath].
    exfalso. exact (Hnone y Hpath).
Qed.

Theorem rank_le_iff_iter :
  forall F rank,
    frame_rank_spec F rank ->
    forall n x,
      n <= rank x <-> exists y, rel_iter (Rel F) n x y.
Proof.
  intros F rank Hrank n x; split.
  - apply rank_path_exists; exact Hrank.
  - intros [y Hpath].
    pose proof (rank_iter_bound Hrank Hpath). lia.
Qed.

Lemma rel_iter_succ_decompose_right :
  forall (A : Type) (R : A -> A -> Prop) n x z,
    rel_iter R (S n) x z ->
    exists y, rel_iter R n x y /\ R y z.
Proof.
  intros A R n x z Hpath.
  replace (S n) with (n + 1) in Hpath by lia.
  apply (proj1 (rel_iter_plus R n 1 x z)) in Hpath.
  destruct Hpath as [y [Hxy Hyz]].
  exists y; split; [exact Hxy |].
  now apply (proj1 (rel_iter_one R y z)).
Qed.

Theorem rank_eq_iff_iter_terminal :
  forall F rank,
    frame_rank_spec F rank ->
    forall n x,
      rank x = n <->
      (exists y, rel_iter (Rel F) n x y) /\
      (forall y, rel_iter (Rel F) n x y ->
         forall z, ~ Rel F y z).
Proof.
  intros F rank Hrank n x; split.
  - intro Heq; split.
    + apply (proj1 (rank_le_iff_iter Hrank n x)). lia.
    + intros y Hxy z Hyz.
      assert (Hlong : rel_iter (Rel F) (S n) x z).
      { eapply rel_iter_step_right; eauto. }
      pose proof (rank_iter_bound Hrank Hlong). lia.
  - intros [[y Hpath] Hterminal].
    assert (Hle : n <= rank x).
    { apply (proj2 (rank_le_iff_iter Hrank n x)). now exists y. }
    destruct (Nat.eq_dec (rank x) n) as [Heq | Hneq]; auto.
    assert (Hsucc : S n <= rank x) by lia.
    destruct (rank_path_exists Hrank Hsucc) as [z Hlong].
    destruct (rel_iter_succ_decompose_right Hlong)
      as [u [Hxu Huz]].
    exfalso. exact (Hterminal u Hxu z Huz).
Qed.

Lemma rank_terminal_exists :
  forall F rank,
    frame_rank_spec F rank ->
    forall x,
      exists y, rel_iter (Rel F) (rank x) x y.
Proof.
  intros F rank Hrank x.
  apply (proj1 (rank_le_iff_iter Hrank (rank x) x)); lia.
Qed.

Lemma rank_path_endpoint_terminal :
  forall F rank,
    frame_rank_spec F rank ->
    forall x y,
      rel_iter (Rel F) (rank x) x y ->
      forall z, ~ Rel F y z.
Proof.
  intros F rank Hrank x y Hxy z Hyz.
  assert (Hlong : rel_iter (Rel F) (S (rank x)) x z).
  { eapply rel_iter_step_right; eauto. }
  pose proof (rank_iter_bound Hrank Hlong). lia.
Qed.

Definition frame_height {F : frame} (rank : World F -> nat)
    (r : World F) : nat := rank r.

Lemma rank_lt_height_of_root_rel :
  forall F rank,
    frame_rank_spec F rank ->
    forall r x, Rel F r x ->
      rank x < frame_height rank r.
Proof. intros; now apply (rank_rel_decreases H r x). Qed.

Lemma rank_le_height_of_root :
  forall F rank,
    frame_rank_spec F rank ->
    forall r,
      frame_root F r ->
      forall x, rank x <= frame_height rank r.
Proof.
  intros F rank Hrank r Hroot x.
  unfold frame_height.
  destruct (classic (x = r)) as [-> | Hneq]; [lia |].
  pose proof (rank_rel_decreases Hrank r x (Hroot x Hneq)). lia.
Qed.

Theorem rank_eq_height_iff_root :
  forall F rank,
    frame_rank_spec F rank ->
    forall r,
      frame_root F r ->
      forall x,
        rank x = frame_height rank r <-> x = r.
Proof.
  intros F rank Hrank r Hroot x; split.
  - intro Heq.
    destruct (classic (x = r)) as [Hxr | Hneq]; auto.
    pose proof (rank_rel_decreases Hrank r x (Hroot x Hneq)).
    unfold frame_height in Heq. lia.
  - now intros ->.
Qed.

Theorem rank_lt_iff_satisfies_box_bottom :
  forall F rank,
    frame_rank_spec F rank ->
    forall (AtomType : Type) (V : valuation AtomType F) n x,
      rank x < n <->
      satisfies F V x (box_iter n Bottom).
Proof.
  intros F rank Hrank AtomType V n x.
  rewrite satisfies_box_iter.
  split.
  - intros Hlt y Hpath.
    exfalso. exact ((proj1 (rank_lt_iff_no_iter Hrank n x) Hlt) y Hpath).
  - intros Hbox.
    apply (proj2 (rank_lt_iff_no_iter Hrank n x)).
    intros y Hpath.
    exact (@satisfies_bottom AtomType F V y (Hbox y Hpath)).
Qed.

Lemma rank_positive_of_diamond :
  forall F rank,
    frame_rank_spec F rank ->
    forall (AtomType : Type) (V : valuation AtomType F)
           (A : formula AtomType) x,
      satisfies F V x (Dia A) -> 0 < rank x.
Proof.
  intros F rank Hrank AtomType V A x Hdia.
  destruct (satisfies_dia_elim Hdia) as [y [Hxy Hy]].
  pose proof (rank_rel_decreases Hrank x y Hxy). lia.
Qed.

Definition point_generated_rank {F : frame} (rank : World F -> nat)
    (r : World F) (x : World (point_generated_frame F r)) : nat :=
  rank (proj1_sig x).

Arguments point_generated_rank {F} rank r x.

Theorem point_generated_rank_spec :
  forall F rank,
    frame_rank_spec F rank -> frame_transitive F ->
    forall r,
      frame_rank_spec (point_generated_frame F r)
        (point_generated_rank rank r).
Proof.
  intros F rank Hrank Htrans r; constructor.
  - intros [x hx] [y hy] Hxy; simpl in *.
    now apply (rank_rel_decreases Hrank x y Hxy).
  - intros [x hx] n Hn; simpl in Hn.
    destruct (rank_realizes_lower_level Hrank x n Hn)
      as [y [Hxy Hyrank]].
    assert (hy : point_generated_member F r y).
    { eapply point_generated_member_successor; eauto. }
    exists (exist _ y hy); split; auto.
Qed.

Lemma point_generated_rank_original :
  forall F rank r (x : World (point_generated_frame F r)),
    point_generated_rank rank r x = rank (proj1_sig x).
Proof. reflexivity. Qed.

(** One fresh root, the [n = 1] case of Foundation's [extendRoot]. *)
Definition one_root_extension (F : frame) : frame :=
  {| World := option (World F);
     Rel := fun x y =>
       match x, y with
       | None, Some _ => True
       | Some u, Some v => Rel F u v
       | _, _ => False
       end |}.

Definition one_root_rank {F : frame} (rank : World F -> nat)
    (r : World F) (x : World (one_root_extension F)) : nat :=
  match x with
  | None => S (rank r)
  | Some y => rank y
  end.

Arguments one_root_rank {F} rank r x.

Lemma one_root_extension_root :
  forall F, frame_root (one_root_extension F) None.
Proof.
  intros F [x |] Hneq; simpl; auto.
Qed.

Lemma one_root_extension_transitive :
  forall F,
    frame_transitive F -> frame_transitive (one_root_extension F).
Proof.
  intros F Htrans [x |] [y |] [z |]; simpl; try tauto.
  now apply Htrans.
Qed.

Lemma one_root_extension_irreflexive :
  forall F,
    frame_irreflexive F -> frame_irreflexive (one_root_extension F).
Proof. intros F Hirr [x |]; simpl; auto. Qed.

Theorem one_root_rank_spec :
  forall F rank,
    frame_rank_spec F rank ->
    forall r,
      frame_root F r ->
      frame_rank_spec (one_root_extension F) (one_root_rank rank r).
Proof.
  intros F rank Hrank r Hroot; constructor.
  - intros [x |] [y |] Hxy; simpl in *; try contradiction.
    + now apply (rank_rel_decreases Hrank x y Hxy).
    + pose proof
        (@rank_le_height_of_root F rank Hrank r Hroot y) as Hle.
      unfold frame_height in Hle. lia.
  - intros [x |] n Hn; simpl in Hn.
    + destruct (rank_realizes_lower_level Hrank x n Hn)
        as [y [Hxy Hyrank]].
      exists (Some y); simpl; auto.
    + destruct (Nat.eq_dec n (rank r)) as [-> | Hneq].
      * exists (Some r); simpl; auto.
      * assert (Hlt : n < rank r) by lia.
        destruct (rank_realizes_lower_level Hrank r n Hlt)
          as [y [Hry Hyrank]].
        exists (Some y); simpl; auto.
Qed.

Lemma one_root_height_successor :
  forall F rank (r : World F),
    one_root_rank rank r None = S (frame_height rank r).
Proof. reflexivity. Qed.

(** * Balloons *)

Lemma cluster_rel_between_members :
  forall F,
    frame_transitive F ->
    forall (C D : cluster F),
      cluster_rel F C D ->
      forall x y,
        cluster_member C x -> cluster_member D y -> Rel F x y.
Proof.
  intros F Htrans C D HCD x y Hx Hy.
  destruct HCD as [a [b [Ha [Hb Hab]]]].
  destruct (@cluster_members_same F Htrans C x a Hx Ha)
    as [Hax | [Hax Hxa]].
  - subst a.
    destruct (@cluster_members_same F Htrans D b y Hb Hy)
      as [Hyb | [Hyb Hby]].
    + now subst y.
    + eapply Htrans; eauto.
  - destruct (@cluster_members_same F Htrans D b y Hb Hy)
      as [Hyb | [Hyb Hby]].
    + subst y. eapply Htrans; eauto.
    + eapply Htrans; [exact Hxa |].
      eapply Htrans; eauto.
Qed.

(** Foundation's declaration asks for a strict total order on the original
    frame while simultaneously requiring a nondegenerate (hence reflexive)
    envelope cluster.  Those assumptions are inconsistent.  The coherent
    mathematical notion is a transitive connected preorder whose *strict
    cluster skeleton* terminates at a unique nondegenerate envelope; this is
    the formulation below. *)
Record frame_balloon (F : frame) (envelope : cluster F) : Prop := {
  balloon_transitive : frame_transitive F;
  balloon_connected : frame_connected F;
  balloon_terminated :
    frame_terminated (strict_skeleton_frame F) envelope;
  balloon_envelope_nondegenerate :
    ~ cluster_degenerate envelope;
  balloon_other_clusters_degenerate :
    forall C : cluster F, C <> envelope -> cluster_degenerate C
}.

Arguments frame_balloon F envelope : clear implicits.

Lemma irreflexive_clusters_degenerate :
  forall F,
    frame_transitive F -> frame_irreflexive F ->
    forall C : cluster F, cluster_degenerate C.
Proof.
  intros F Htrans Hirr C HCC.
  destruct (cluster_nonempty C) as [x Hx].
  exact (Hirr x
    (@cluster_reflexive_of_self_rel F Htrans C HCC x Hx)).
Qed.

Theorem source_balloon_order_assumptions_inconsistent :
  forall F,
    frame_transitive F -> frame_irreflexive F ->
    forall e : cluster F, ~ cluster_degenerate e -> False.
Proof.
  intros F Htrans Hirr e Hnondeg.
  exact (Hnondeg
    (@irreflexive_clusters_degenerate F Htrans Hirr e)).
Qed.

Lemma balloon_strict_skeleton_transitive :
  forall F e,
    frame_balloon F e ->
    frame_transitive (strict_skeleton_frame F).
Proof.
  intros F e B. apply strict_skeleton_transitive.
  exact (balloon_transitive B).
Qed.

Lemma balloon_strict_skeleton_connected :
  forall F e,
    frame_balloon F e ->
    frame_connected (strict_skeleton_frame F).
Proof.
  intros F e B. apply strict_skeleton_connected.
  - exact (balloon_transitive B).
  - exact (balloon_connected B).
Qed.

Lemma balloon_envelope_reflexive :
  forall F e,
    frame_balloon F e ->
    forall x, cluster_member e x -> Rel F x x.
Proof.
  intros F e B x Hx.
  eapply cluster_reflexive_of_non_degenerate.
  - exact (balloon_transitive B).
  - exact (balloon_envelope_nondegenerate B).
  - exact Hx.
Qed.

(** Every world sees every point of the envelope. *)
Theorem balloon_covers_envelope :
  forall F e,
    frame_balloon F e ->
    forall x t,
      cluster_member e t -> Rel F x t.
Proof.
  intros F e B x t Ht.
  set (C := cluster_of F x).
  destruct (classic (C = e)) as [HCe | HCe].
  - assert (Hx : cluster_member e x).
    { rewrite <- HCe. apply cluster_equiv_refl. }
    destruct (@cluster_members_same F (balloon_transitive B)
      e x t Hx Ht) as [Htx | [Htx Hxt]].
    + subst t. now apply (balloon_envelope_reflexive B Hx).
    + exact Hxt.
  - pose proof
      (@directly_terminated_of_transitive
        (strict_skeleton_frame F) e
        (balloon_strict_skeleton_transitive B)
        (balloon_terminated B)) as Hdirect.
    specialize (Hdirect C HCe).
    destruct Hdirect as [HCe_rel Hneq].
    eapply cluster_rel_between_members.
    + exact (balloon_transitive B).
    + exact HCe_rel.
    + apply cluster_equiv_refl.
    + exact Ht.
Qed.

(** Successors of an envelope point remain in the envelope. *)
Theorem balloon_envelope_successor_closed :
  forall F e,
    frame_balloon F e ->
    forall x y,
      cluster_member e x -> Rel F x y -> cluster_member e y.
Proof.
  intros F e B x y Hx Hxy.
  set (C := cluster_of F y).
  assert (HeC : cluster_rel F e C).
  { exists x, y; split; [exact Hx |].
    split; [apply cluster_equiv_refl | exact Hxy]. }
  destruct (classic (C = e)) as [HCe | HCe].
  - rewrite <- HCe. apply cluster_equiv_refl.
  - pose proof
      (@directly_terminated_of_transitive
        (strict_skeleton_frame F) e
        (balloon_strict_skeleton_transitive B)
        (balloon_terminated B)) as Hdirect.
    specialize (Hdirect C HCe).
    destruct Hdirect as [HCe_rel Hneq].
    assert (e = C).
    { eapply cluster_rel_antisymmetric.
      - exact (balloon_transitive B).
      - exact HeC.
      - exact HCe_rel. }
    exfalso. apply HCe. symmetry. exact H.
Qed.

(** The source's [farthermost_point_of_not_box] is admitted and is false as
    stated on arbitrary strict orders (the natural-number strict order is a
    counterexample).  Converse well-foundedness is the missing hypothesis;
    with it, the intended theorem is immediate from maximality. *)
Theorem farthest_counterexample_of_not_box :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F)
         (A : formula AtomType),
    frame_transitive F -> frame_converse_well_founded F ->
    forall x,
      ~ satisfies F V x (Box A) ->
      exists y,
        Rel F x y /\ ~ satisfies F V y A /\ satisfies F V y (Box A).
Proof.
  intros AtomType F V A Htrans Hcwf x Hnotbox.
  assert (Hex : exists y, Rel F x y /\ ~ satisfies F V y A).
  { apply NNPP. intro Hnone. apply Hnotbox.
    intros y Hxy. apply NNPP. intro HnotA.
    apply Hnone. now exists y. }
  destruct (Hcwf (fun y => Rel F x y /\ ~ satisfies F V y A) Hex)
    as [y [[Hxy HnotA] Hmax]].
  exists y; repeat split; auto.
  intros z Hyz. apply NNPP. intro Hnotz.
  apply (Hmax z); [split | exact Hyz].
  - eapply Htrans; eauto.
  - exact Hnotz.
Qed.

Theorem nat_lt_has_no_farthest_bottom :
  forall (V : valuation nat nat_lt_frame) x,
    ~ satisfies nat_lt_frame V x (Box Bottom) /\
    ~ exists y,
        Rel nat_lt_frame x y /\
        ~ satisfies nat_lt_frame V y Bottom /\
        satisfies nat_lt_frame V y (Box Bottom).
Proof.
  intros V x; split.
  - intro Hbox. exact (@satisfies_bottom nat nat_lt_frame V (S x)
      (Hbox (S x) (ltac:(change (x < S x); lia)))).
  - intros [y [Hxy [Hbottom Hbox]]].
    exact (@satisfies_bottom nat nat_lt_frame V (S y)
      (Hbox (S y) (ltac:(change (y < S y); lia)))).
Qed.

(** Converse well-founded transitive frames validate [Z], since Löb's axiom
    already yields its consequent [□p]. *)
Theorem valid_Z_of_transitive_cwf :
  forall (AtomType : Type) (F : frame) (A : formula AtomType),
    frame_transitive F -> frame_converse_well_founded F ->
    valid F (Z A).
Proof.
  intros AtomType F A Htrans Hcwf V x.
  unfold Z; simpl.
  intros Hstep Hdia.
  pose proof
    (@valid_Loeb_of_transitive_cwf AtomType F A Htrans Hcwf V x)
    as Hloeb.
  unfold Loeb in Hloeb; simpl in Hloeb.
  exact (Hloeb Hstep).
Qed.

Theorem balloon_validates_Z_of_cwf :
  forall (F : frame) (e : cluster F),
    frame_balloon F e -> frame_converse_well_founded F ->
    valid F (Z (Atom 0)).
Proof.
  intros F e B Hcwf.
  apply valid_Z_of_transitive_cwf.
  - exact (balloon_transitive B).
  - exact Hcwf.
Qed.
