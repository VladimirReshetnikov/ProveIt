(**
  Roots and point-generated Kripke frames.

  This module ports the semantic content of
  [Foundation/Modal/Kripke/Root.lean] at the pinned Foundation revision.
  The source represents generated worlds by subtypes; the same representation
  is used here.  Equality of two inhabitants with the same underlying world
  consequently uses Coq's standard proof-irrelevance theorem.  All modal
  truth results themselves are inherited from bounded-morphism invariance.

  Foundation also installs a finiteness type-class instance for a generated
  subtype.  The local [frame] record has no finiteness field, so there is no
  corresponding proposition to prove in this file.
*)

From Stdlib Require Import Logic.Classical_Prop.
From Stdlib Require Import Logic.ProofIrrelevance.
From FoundationModal Require Import
  Syntax Kripke Correspondence Preservation FrameProperties.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Global and piecewise relation properties *)

Definition frame_convergent (F : frame) : Prop :=
  forall x y : World F, x <> y ->
    exists u : World F, Rel F x u /\ Rel F y u.

Definition frame_strongly_convergent (F : frame) : Prop :=
  forall x y : World F,
    exists u : World F, Rel F x u /\ Rel F y u.

Definition frame_connected (F : frame) : Prop :=
  forall x y : World F, Rel F x y \/ x = y \/ Rel F y x.

Definition frame_strongly_connected (F : frame) : Prop :=
  forall x y : World F, Rel F x y \/ Rel F y x.

Definition frame_piecewise_convergent (F : frame) : Prop :=
  forall x y z : World F,
    Rel F x y -> Rel F x z -> y <> z ->
    exists u : World F, Rel F y u /\ Rel F z u.

(** [frame_strongly_confluent] in [Correspondence] is Foundation's
    [IsPiecewiseStronglyConvergent]. *)
Definition frame_piecewise_strongly_convergent : frame -> Prop :=
  frame_strongly_confluent.

Definition frame_piecewise_connected (F : frame) : Prop :=
  forall x y z : World F,
    Rel F x y -> Rel F x z ->
    Rel F y z \/ y = z \/ Rel F z y.

Lemma strongly_convergent_convergent :
  forall F, frame_strongly_convergent F -> frame_convergent F.
Proof. firstorder. Qed.

Lemma strongly_connected_connected :
  forall F, frame_strongly_connected F -> frame_connected F.
Proof. firstorder. Qed.

Lemma frame_connected_distinct :
  forall F,
    frame_connected F ->
    forall x y : World F, x <> y -> Rel F x y \/ Rel F y x.
Proof.
  intros F Hconnected x y Hneq.
  destruct (Hconnected x y) as [Hxy | [Heq | Hyx]];
    auto; contradiction.
Qed.

Lemma piecewise_strongly_convergent_convergent :
  forall F,
    frame_piecewise_strongly_convergent F ->
    frame_piecewise_convergent F.
Proof. firstorder. Qed.

Lemma piecewise_strongly_connected_connected :
  forall F,
    frame_piecewise_strongly_connected F ->
    frame_piecewise_connected F.
Proof. firstorder. Qed.

Lemma piecewise_connected_distinct :
  forall F,
    frame_piecewise_connected F ->
    forall x y z : World F,
      Rel F x y -> Rel F x z -> y <> z ->
      Rel F y z \/ Rel F z y.
Proof.
  intros F Hpiece x y z Hxy Hxz Hneq.
  destruct (Hpiece x y z Hxy Hxz) as [Hyz | [Heq | Hzy]];
    auto; contradiction.
Qed.

Lemma piecewise_connected_strong_of_reflexive :
  forall F,
    frame_reflexive F ->
    frame_piecewise_connected F ->
    frame_piecewise_strongly_connected F.
Proof.
  intros F Hrefl Hpiece x y z Hxy Hxz.
  destruct (Hpiece x y z Hxy Hxz) as [Hyz | [-> | Hzy]].
  - now left.
  - left. apply Hrefl.
  - now right.
Qed.

Lemma piecewise_strongly_connected_strongly_convergent_of_reflexive :
  forall F,
    frame_reflexive F ->
    frame_piecewise_strongly_connected F ->
    frame_piecewise_strongly_convergent F.
Proof.
  intros F Hrefl Hpiece x y z Hxy Hxz.
  destruct (Hpiece x y z Hxy Hxz) as [Hyz | Hzy].
  - exists z; auto.
  - exists y; auto.
Qed.

(** * Roots and transitive roots *)

Definition frame_root (F : frame) (r : World F) : Prop :=
  forall x : World F, x <> r -> Rel F r x.

Arguments frame_root F r : clear implicits.

Definition frame_rooted (F : frame) : Prop :=
  exists r : World F, frame_root F r.

Definition frame_point_rooted (F : frame) : Prop :=
  exists r : World F,
    frame_root F r /\
    forall s : World F, frame_root F s -> s = r.

Definition frame_trans_root (F : frame) (r : World F) : Prop :=
  forall x : World F, x <> r ->
    relation_positive_closure (Rel F) r x.

Arguments frame_trans_root F r : clear implicits.

Definition frame_trans_rooted (F : frame) : Prop :=
  exists r : World F, frame_trans_root F r.

Lemma frame_root_access_or_eq :
  forall (F : frame) (r : World F),
    frame_root F r ->
    forall x, x = r \/ Rel F r x.
Proof.
  intros F r Hroot x.
  destruct (classic (x = r)) as [-> | Hneq]; auto.
Qed.

Lemma frame_root_access_of_reflexive :
  forall (F : frame) (r : World F),
    frame_reflexive F -> frame_root F r ->
    forall x, Rel F r x.
Proof.
  intros F r Hrefl Hroot x.
  destruct (frame_root_access_or_eq Hroot x) as [-> | H]; auto.
Qed.

Lemma frame_root_unique_of_irreflexive_transitive :
  forall (F : frame) (r s : World F),
    frame_irreflexive F -> frame_transitive F ->
    frame_root F r -> frame_root F s -> r = s.
Proof.
  intros F r s Hirrefl Htrans Hr Hs.
  destruct (classic (r = s)) as [Heq | Hneq]; [exact Heq |].
  exfalso. apply (Hirrefl r).
  eapply Htrans.
  - apply Hr. intro Hsr. apply Hneq. symmetry. exact Hsr.
  - apply Hs. exact Hneq.
Qed.

Theorem rooted_point_rooted_of_irreflexive_transitive :
  forall F,
    frame_irreflexive F -> frame_transitive F ->
    frame_rooted F -> frame_point_rooted F.
Proof.
  intros F Hirrefl Htrans [r Hr].
  exists r; split; [exact Hr |].
  intros s Hs.
  eapply frame_root_unique_of_irreflexive_transitive; eauto.
Qed.

Lemma trans_root_is_root_of_transitive :
  forall (F : frame) (r : World F),
    frame_transitive F ->
    frame_trans_root F r -> frame_root F r.
Proof.
  intros F r Htrans Hroot x Hneq.
  apply (proj1 (positive_closure_of_transitive_iff Htrans r x)).
  now apply Hroot.
Qed.

Theorem trans_rooted_rooted_of_transitive :
  forall F,
    frame_transitive F -> frame_trans_rooted F -> frame_rooted F.
Proof.
  intros F Htrans [r Hr]. exists r.
  now apply trans_root_is_root_of_transitive.
Qed.

(** A rooted frame remains rooted after taking its positive transitive
    closure. *)
Theorem transitive_closure_rooted :
  forall F, frame_rooted F -> frame_rooted (frame_trans_gen F).
Proof.
  intros F [r Hr]. exists r. intros x Hneq.
  apply positive_closure_base. now apply Hr.
Qed.

(** * Rooted local-to-global principles *)

Theorem convergent_of_rooted_reflexive_piecewise :
  forall F,
    frame_rooted F -> frame_reflexive F ->
    frame_piecewise_convergent F -> frame_convergent F.
Proof.
  intros F [r Hr] Hrefl Hpiece x y Hneq.
  eapply Hpiece; [apply frame_root_access_of_reflexive with (r := r) |
                  apply frame_root_access_of_reflexive with (r := r) |
                  exact Hneq]; eauto.
Qed.

Theorem strongly_convergent_of_rooted_reflexive_piecewise :
  forall F,
    frame_rooted F -> frame_reflexive F ->
    frame_piecewise_strongly_convergent F ->
    frame_strongly_convergent F.
Proof.
  intros F [r Hr] Hrefl Hpiece x y.
  eapply Hpiece; apply frame_root_access_of_reflexive with (r := r); eauto.
Qed.

Theorem connected_of_rooted_reflexive_piecewise :
  forall F,
    frame_rooted F -> frame_reflexive F ->
    frame_piecewise_connected F -> frame_connected F.
Proof.
  intros F [r Hr] Hrefl Hpiece x y.
  eapply Hpiece; apply frame_root_access_of_reflexive with (r := r); eauto.
Qed.

Theorem strongly_connected_of_rooted_reflexive_piecewise :
  forall F,
    frame_rooted F -> frame_reflexive F ->
    frame_piecewise_strongly_connected F ->
    frame_strongly_connected F.
Proof.
  intros F [r Hr] Hrefl Hpiece x y.
  eapply Hpiece; apply frame_root_access_of_reflexive with (r := r); eauto.
Qed.

(** * Direct point generation *)

Definition point_generated_member (F : frame) (r x : World F) : Prop :=
  x = r \/ Rel F r x.

Arguments point_generated_member F r x : clear implicits.

Definition point_generated_frame (F : frame) (r : World F) : frame :=
  {| World := { x : World F | point_generated_member F r x };
     Rel := fun x y => Rel F (proj1_sig x) (proj1_sig y) |}.

Arguments point_generated_frame F r : clear implicits.

Definition point_generated_root (F : frame) (r : World F)
    : World (point_generated_frame F r) :=
  exist _ r (or_introl eq_refl).

Arguments point_generated_root F r : clear implicits.

Lemma point_generated_sig_eq :
  forall (F : frame) (r x : World F)
         (hx hy : point_generated_member F r x),
    (exist _ x hx : World (point_generated_frame F r)) = exist _ x hy.
Proof.
  intros F r x hx hy.
  replace hy with hx by apply proof_irrelevance.
  reflexivity.
Qed.

Lemma point_generated_rooted :
  forall (F : frame) (r : World F),
    frame_root (point_generated_frame F r) (point_generated_root F r).
Proof.
  intros F r [x hx] Hneq. simpl.
  destruct hx as [-> | Hrx]; [|exact Hrx].
  exfalso. apply Hneq. apply point_generated_sig_eq.
Qed.

Theorem point_generated_frame_rooted :
  forall (F : frame) (r : World F),
    frame_rooted (point_generated_frame F r).
Proof.
  intros F r. exists (point_generated_root F r).
  apply point_generated_rooted.
Qed.

Lemma point_generated_member_successor :
  forall (F : frame) (r x y : World F),
    frame_transitive F ->
    point_generated_member F r x -> Rel F x y ->
    point_generated_member F r y.
Proof.
  intros F r x y Htrans [-> | Hrx] Hxy.
  - now right.
  - right. eapply Htrans; eauto.
Qed.

Lemma point_generated_reflexive :
  forall (F : frame) (r : World F),
    frame_reflexive F -> frame_reflexive (point_generated_frame F r).
Proof. intros F r Hrefl [x hx]; apply Hrefl. Qed.

Lemma point_generated_transitive :
  forall (F : frame) (r : World F),
    frame_transitive F -> frame_transitive (point_generated_frame F r).
Proof.
  intros F r Htrans [x hx] [y hy] [z hz]; simpl.
  apply Htrans.
Qed.

Lemma point_generated_antisymmetric :
  forall (F : frame) (r : World F),
    frame_antisymmetric F ->
    frame_antisymmetric (point_generated_frame F r).
Proof.
  intros F r Hanti [x hx] [y hy] Hxy Hyx; simpl in *.
  assert (x = y) as -> by (eapply Hanti; eauto).
  apply point_generated_sig_eq.
Qed.

Lemma point_generated_irreflexive :
  forall (F : frame) (r : World F),
    frame_irreflexive F ->
    frame_irreflexive (point_generated_frame F r).
Proof. intros F r Hirr [x hx]; apply Hirr. Qed.

Lemma point_generated_asymmetric :
  forall (F : frame) (r : World F),
    frame_asymmetric F ->
    frame_asymmetric (point_generated_frame F r).
Proof. intros F r Hasym [x hx] [y hy]; apply Hasym. Qed.

Lemma point_generated_preorder :
  forall (F : frame) (r : World F),
    frame_is_preorder F -> frame_is_preorder (point_generated_frame F r).
Proof.
  intros F r [Hrefl Htrans]; split.
  - now apply point_generated_reflexive.
  - now apply point_generated_transitive.
Qed.

Lemma point_generated_partial_order :
  forall (F : frame) (r : World F),
    frame_is_partial_order F ->
    frame_is_partial_order (point_generated_frame F r).
Proof.
  intros F r [Hrefl [Htrans Hanti]]; repeat split.
  - now apply point_generated_reflexive.
  - now apply point_generated_transitive.
  - now apply point_generated_antisymmetric.
Qed.

Theorem point_generated_point_rooted :
  forall (F : frame) (r : World F),
    frame_irreflexive F -> frame_transitive F ->
    frame_point_rooted (point_generated_frame F r).
Proof.
  intros F r Hirr Htrans.
  apply rooted_point_rooted_of_irreflexive_transitive.
  - now apply point_generated_irreflexive.
  - now apply point_generated_transitive.
  - apply point_generated_frame_rooted.
Qed.

Lemma point_generated_piecewise_convergent :
  forall (F : frame) (r : World F),
    frame_transitive F -> frame_piecewise_convergent F ->
    frame_piecewise_convergent (point_generated_frame F r).
Proof.
  intros F r Htrans Hpiece [x hx] [y hy] [z hz] Hxy Hxz Hneq.
  assert (y <> z) as Hyz.
  { intro Heq. apply Hneq. subst z. apply point_generated_sig_eq. }
  destruct (Hpiece x y z Hxy Hxz Hyz) as [u [Hyu Hzu]].
  assert (Hu : point_generated_member F r u).
  { eapply point_generated_member_successor; [exact Htrans | exact hy | exact Hyu]. }
  exists (exist _ u Hu); auto.
Qed.

Lemma point_generated_piecewise_strongly_convergent :
  forall (F : frame) (r : World F),
    frame_transitive F -> frame_piecewise_strongly_convergent F ->
    frame_piecewise_strongly_convergent (point_generated_frame F r).
Proof.
  intros F r Htrans Hpiece [x hx] [y hy] [z hz] Hxy Hxz.
  destruct (Hpiece x y z Hxy Hxz) as [u [Hyu Hzu]].
  assert (Hu : point_generated_member F r u).
  { eapply point_generated_member_successor; [exact Htrans | exact hy | exact Hyu]. }
  exists (exist _ u Hu); auto.
Qed.

Lemma point_generated_convergent :
  forall (F : frame) (r : World F),
    frame_reflexive F -> frame_transitive F ->
    frame_piecewise_convergent F ->
    frame_convergent (point_generated_frame F r).
Proof.
  intros F r Hrefl Htrans Hpiece.
  apply convergent_of_rooted_reflexive_piecewise.
  - exists (point_generated_root F r). apply point_generated_rooted.
  - now apply point_generated_reflexive.
  - now apply point_generated_piecewise_convergent.
Qed.

Lemma point_generated_strongly_convergent :
  forall (F : frame) (r : World F),
    frame_reflexive F -> frame_transitive F ->
    frame_piecewise_strongly_convergent F ->
    frame_strongly_convergent (point_generated_frame F r).
Proof.
  intros F r Hrefl Htrans Hpiece.
  apply strongly_convergent_of_rooted_reflexive_piecewise.
  - exists (point_generated_root F r). apply point_generated_rooted.
  - now apply point_generated_reflexive.
  - now apply point_generated_piecewise_strongly_convergent.
Qed.

Lemma point_generated_piecewise_connected :
  forall (F : frame) (r : World F),
    frame_piecewise_connected F ->
    frame_piecewise_connected (point_generated_frame F r).
Proof.
  intros F r Hpiece [x hx] [y hy] [z hz] Hxy Hxz.
  destruct (Hpiece x y z Hxy Hxz) as [Hyz | [Heq | Hzy]].
  - now left.
  - right; left. subst z. apply point_generated_sig_eq.
  - now right; right.
Qed.

Lemma point_generated_connected :
  forall (F : frame) (r : World F),
    frame_reflexive F -> frame_piecewise_connected F ->
    frame_connected (point_generated_frame F r).
Proof.
  intros F r Hrefl Hpiece.
  apply connected_of_rooted_reflexive_piecewise.
  - exists (point_generated_root F r). apply point_generated_rooted.
  - now apply point_generated_reflexive.
  - now apply point_generated_piecewise_connected.
Qed.

Lemma point_generated_piecewise_strongly_connected :
  forall (F : frame) (r : World F),
    frame_piecewise_strongly_connected F ->
    frame_piecewise_strongly_connected (point_generated_frame F r).
Proof.
  intros F r Hpiece [x hx] [y hy] [z hz] Hxy Hxz.
  exact (Hpiece x y z Hxy Hxz).
Qed.

Lemma point_generated_strongly_connected :
  forall (F : frame) (r : World F),
    frame_strongly_connected F ->
    frame_strongly_connected (point_generated_frame F r).
Proof.
  intros F r Htotal [x hx] [y hy]. exact (Htotal x y).
Qed.

Lemma point_generated_strongly_connected_of_piecewise :
  forall (F : frame) (r : World F),
    frame_reflexive F -> frame_piecewise_strongly_connected F ->
    frame_strongly_connected (point_generated_frame F r).
Proof.
  intros F r Hrefl Hpiece.
  apply strongly_connected_of_rooted_reflexive_piecewise.
  - exists (point_generated_root F r). apply point_generated_rooted.
  - now apply point_generated_reflexive.
  - now apply point_generated_piecewise_strongly_connected.
Qed.

(** The inclusion of a direct point-generated frame is a bounded morphism
    exactly when the original relation is transitive. *)
Definition point_generated_p_morphism
    (F : frame) (r : World F) (Htrans : frame_transitive F)
    : p_morphism (point_generated_frame F r) F.
Proof.
  refine {| pmap := fun x : World (point_generated_frame F r) =>
                       proj1_sig x |}.
  - intros [x hx] [y hy] Hxy. exact Hxy.
  - intros [x hx] y Hxy.
    assert (hy : point_generated_member F r y).
    { eapply point_generated_member_successor; eauto. }
    exists (exist _ y hy); split; reflexivity || exact Hxy.
Defined.

Arguments point_generated_p_morphism F r Htrans : clear implicits.

Lemma point_generated_p_morphism_injective :
  forall (F : frame) (r : World F) (Htrans : frame_transitive F),
    forall x y,
      pmap (point_generated_p_morphism F r Htrans) x =
      pmap (point_generated_p_morphism F r Htrans) y -> x = y.
Proof.
  intros F r Htrans [x hx] [y hy] Heq; simpl in Heq. subst y.
  apply point_generated_sig_eq.
Qed.

(** * Abstract generated subframes and generated valuations *)

Record generated_subframe (F1 F2 : frame) : Type := {
  generated_subframe_morphism : p_morphism F1 F2;
  generated_subframe_injective :
    forall x y,
      pmap generated_subframe_morphism x =
      pmap generated_subframe_morphism y -> x = y
}.

Arguments generated_subframe_morphism {F1 F2} _.

Definition point_generated_subframe
    (F : frame) (r : World F) (Htrans : frame_transitive F)
    : generated_subframe (point_generated_frame F r) F :=
  {| generated_subframe_morphism := point_generated_p_morphism F r Htrans;
     generated_subframe_injective :=
       @point_generated_p_morphism_injective F r Htrans |}.

(** A generated submodel is a generated subframe whose embedding preserves
    atomic truth.  This is the pair-of-a-frame-and-a-valuation counterpart of
    Foundation's [Model.GeneratedSub] record. *)
Record generated_submodel {AtomType : Type}
    (F1 : frame) (V1 : valuation AtomType F1)
    (F2 : frame) (V2 : valuation AtomType F2) : Type := {
  generated_submodel_frame : generated_subframe F1 F2;
  generated_submodel_atoms :
    forall (a : AtomType) (x : World F1),
      V1 a x <->
      V2 a (pmap (generated_subframe_morphism generated_submodel_frame) x)
}.

Arguments generated_submodel AtomType F1 V1 F2 V2 : clear implicits.
Arguments generated_submodel_frame
  {AtomType F1 V1 F2 V2} _.

Definition generated_submodel_bisimulation
    {AtomType : Type}
    {F1 : frame} {V1 : valuation AtomType F1}
    {F2 : frame} {V2 : valuation AtomType F2}
    (G : generated_submodel AtomType F1 V1 F2 V2)
    : @bisimulation AtomType F1 V1 F2 V2.
Proof.
  set (f := generated_subframe_morphism (generated_submodel_frame G)).
  refine
    {| bisimilar := fun x y => y = pmap f x |}.
  - intros x y a ->. apply generated_submodel_atoms.
  - intros x y x' -> Hxx'.
    exists (pmap f x'); split; [reflexivity |].
    now apply p_morphism_forth.
  - intros x y y' -> Hyy'.
    destruct (@p_morphism_back F1 F2 f x y' Hyy')
      as [x' [Hx' Hxx']].
    exists x'; split; [symmetry; exact Hx' | exact Hxx'].
Defined.

Theorem generated_submodel_truth :
  forall (AtomType : Type)
         (F1 : frame) (V1 : valuation AtomType F1)
         (F2 : frame) (V2 : valuation AtomType F2)
         (G : generated_submodel AtomType F1 V1 F2 V2)
         (x : World F1) (p : formula AtomType),
    satisfies F1 V1 x p <->
    satisfies F2 V2
      (pmap (generated_subframe_morphism (generated_submodel_frame G)) x) p.
Proof.
  intros AtomType F1 V1 F2 V2 G x p.
  eapply bisimulation_invariance
    with (Z := generated_submodel_bisimulation G).
  reflexivity.
Qed.

Definition point_generated_valuation {AtomType}
    (F : frame) (V : valuation AtomType F) (r : World F)
    : valuation AtomType (point_generated_frame F r) :=
  fun a x => V a (proj1_sig x).

Arguments point_generated_valuation {AtomType F} V r.

Definition point_generated_submodel {AtomType}
    (F : frame) (V : valuation AtomType F) (r : World F)
    (Htrans : frame_transitive F)
    : generated_submodel AtomType
        (point_generated_frame F r) (point_generated_valuation V r)
        F V.
Proof.
  refine
    {| generated_submodel_frame :=
         @point_generated_subframe F r Htrans |}.
  intros a [x hx]. reflexivity.
Defined.

Theorem point_generated_truth :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F)
         (r : World F) (Htrans : frame_transitive F)
         (x : World (point_generated_frame F r))
         (p : formula AtomType),
    satisfies (point_generated_frame F r)
      (point_generated_valuation V r) x p <->
    satisfies F V (proj1_sig x) p.
Proof.
  intros AtomType F V r Htrans x p.
  exact (p_morphism_truth (point_generated_p_morphism F r Htrans) V x p).
Qed.

Theorem point_generated_truth_at_root :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F)
         (r : World F) (Htrans : frame_transitive F)
         (p : formula AtomType),
    satisfies (point_generated_frame F r)
      (point_generated_valuation V r) (point_generated_root F r) p <->
    satisfies F V r p.
Proof.
  intros AtomType F V r Htrans p.
  exact (@point_generated_truth AtomType F V r Htrans
    (point_generated_root F r) p).
Qed.

Definition point_generated_bisimulation {AtomType}
    (F : frame) (V : valuation AtomType F) (r : World F)
    (Htrans : frame_transitive F)
    : @bisimulation AtomType (point_generated_frame F r)
        (point_generated_valuation V r) F V :=
  p_morphism_bisimulation (point_generated_p_morphism F r Htrans) V.

(** * Generation by positive reachability *)

Definition point_trans_generated_member
    (F : frame) (r x : World F) : Prop :=
  x = r \/ relation_positive_closure (Rel F) r x.

Arguments point_trans_generated_member F r x : clear implicits.

Definition point_trans_generated_frame (F : frame) (r : World F) : frame :=
  {| World := { x : World F | point_trans_generated_member F r x };
     Rel := fun x y => Rel F (proj1_sig x) (proj1_sig y) |}.

Arguments point_trans_generated_frame F r : clear implicits.

Definition point_trans_generated_root (F : frame) (r : World F)
    : World (point_trans_generated_frame F r) :=
  exist _ r (or_introl eq_refl).

Arguments point_trans_generated_root F r : clear implicits.

Lemma point_trans_generated_sig_eq :
  forall (F : frame) (r x : World F)
         (hx hy : point_trans_generated_member F r x),
    (exist _ x hx : World (point_trans_generated_frame F r)) =
    exist _ x hy.
Proof.
  intros F r x hx hy.
  replace hy with hx by apply proof_irrelevance.
  reflexivity.
Qed.

Lemma point_trans_generated_member_successor :
  forall (F : frame) (r x y : World F),
    point_trans_generated_member F r x -> Rel F x y ->
    point_trans_generated_member F r y.
Proof.
  intros F r x y [-> | Hrx] Hxy; right.
  - now apply positive_closure_base.
  - eapply positive_closure_transitive.
    + exact Hrx.
    + now apply positive_closure_base.
Qed.

Lemma point_trans_lift_iter :
  forall (F : frame) (r : World F) n (x y : World F)
         (hx : point_trans_generated_member F r x)
         (hy : point_trans_generated_member F r y),
    rel_iter (Rel F) n x y ->
    rel_iter (Rel (point_trans_generated_frame F r)) n
      (exist _ x hx) (exist _ y hy).
Proof.
  intros F r n; induction n as [|n IH]; intros x y hx hy Hxy.
  - simpl in *. subst y. apply point_trans_generated_sig_eq.
  - destruct Hxy as [z [Hxz Hzy]].
    assert (hz : point_trans_generated_member F r z).
    { exact (@point_trans_generated_member_successor F r x z hx Hxz). }
    exists (exist _ z hz); split; [exact Hxz |].
    now apply IH.
Qed.

Lemma point_trans_lift_positive :
  forall (F : frame) (r x y : World F)
         (hx : point_trans_generated_member F r x)
         (hy : point_trans_generated_member F r y),
    relation_positive_closure (Rel F) x y ->
    relation_positive_closure (Rel (point_trans_generated_frame F r))
      (exist _ x hx) (exist _ y hy).
Proof.
  intros F r x y hx hy [n [Hn Hxy]].
  exists n; split; [exact Hn |].
  now apply point_trans_lift_iter.
Qed.

Lemma point_trans_generated_trans_rooted :
  forall (F : frame) (r : World F),
    frame_trans_rooted (point_trans_generated_frame F r).
Proof.
  intros F r. exists (point_trans_generated_root F r).
  intros [x hx] Hneq.
  destruct hx as [-> | Hrx].
  - exfalso. apply Hneq. apply point_trans_generated_sig_eq.
  - apply point_trans_lift_positive. exact Hrx.
Qed.
