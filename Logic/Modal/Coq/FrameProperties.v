(**
  Elementary frame properties and relation closures.

  This module ports the semantic content of Foundation's
  [Modal/Kripke/Antisymmetric.lean], [Irreflexive.lean], [Closure.lean],
  [Asymmetric.lean], and [Terminated.lean].  Foundation delegates most of
  the closure algebra to Lean's relation library; here it is made explicit
  against [Kripke.rel_iter], so the results can be reused by the Coq modal
  development without an auxiliary relation representation.

  Two representation-only pieces of the Lean files deliberately have no
  theorem analogue here: coercions between a frame and a closure frame, and
  inherited [Finite]/[IsFinite] instances.  Coq's [frame] record carries no
  finiteness witness, and all three closure frames below have definitionally
  the same world type, so neither device is needed.  Foundation's
  [IsTerminated F t] means that every world other than [t] reaches [t]; it
  is not a synonym for converse well-foundedness.  We therefore prove their
  actual consequences and interaction, rather than asserting an invalid
  equivalence between the two notions.
*)

From Stdlib Require Import Arith.PeanoNat Lia.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Logic.Classical_Prop.
From Stdlib Require Import Relations.Relation_Definitions.
From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Wellfounded.Inclusion.
From Stdlib Require Import Wellfounded.Transitive_Closure.
From FoundationModal Require Import Kripke Correspondence Filtration Loeb.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Relation closures represented by finite paths *)

Definition relation_reflexive_closure {A : Type}
    (R : A -> A -> Prop) (x y : A) : Prop :=
  x = y \/ R x y.

Definition relation_positive_closure {A : Type}
    (R : A -> A -> Prop) (x y : A) : Prop :=
  exists n, 0 < n /\ rel_iter R n x y.

Definition relation_reflexive_transitive_closure {A : Type}
    (R : A -> A -> Prop) (x y : A) : Prop :=
  exists n, rel_iter R n x y.

Lemma rel_iter_monotone :
  forall (A : Type) (R S : A -> A -> Prop),
    (forall x y, R x y -> S x y) ->
    forall n x y, rel_iter R n x y -> rel_iter S n x y.
Proof.
  intros A R S Hincl n; induction n as [|n IH]; intros x y Hxy.
  - exact Hxy.
  - destruct Hxy as [z [Rxz Hzy]].
    exists z; split; [now apply Hincl | now apply IH].
Qed.

Lemma rel_iter_reverse_of_symmetric :
  forall (A : Type) (R : A -> A -> Prop),
    (forall x y, R x y -> R y x) ->
    forall n x y, rel_iter R n x y -> rel_iter R n y x.
Proof.
  intros A R Hsym n; induction n as [|n IH]; intros x y Hxy.
  - simpl in *. now subst y.
  - destruct Hxy as [z [Rxz Hzy]].
    eapply rel_iter_step_right.
    + exact (IH z y Hzy).
    + now apply Hsym.
Qed.

Lemma rel_iter_collapse_of_transitive :
  forall (A : Type) (R : A -> A -> Prop),
    (forall x y z, R x y -> R y z -> R x z) ->
    forall n x y, 0 < n -> rel_iter R n x y -> R x y.
Proof.
  intros A R Htrans n; destruct n as [|n]; [lia |].
  induction n as [|n IH]; intros x y _ Hxy.
  - exact (proj1 (rel_iter_one R x y) Hxy).
  - destruct Hxy as [z [Rxz Hzy]].
    eapply Htrans; [exact Rxz |].
    eapply IH; [lia | exact Hzy].
Qed.

Lemma reflexive_closure_base :
  forall (A : Type) (R : A -> A -> Prop) x y,
    R x y -> relation_reflexive_closure R x y.
Proof. intros; now right. Qed.

Lemma reflexive_closure_refl :
  forall (A : Type) (R : A -> A -> Prop) x,
    relation_reflexive_closure R x x.
Proof. intros; now left. Qed.

Lemma reflexive_closure_of_reflexive_iff :
  forall (A : Type) (R : A -> A -> Prop),
    (forall x, R x x) ->
    forall x y, relation_reflexive_closure R x y <-> R x y.
Proof.
  intros A R Hrefl x y; split.
  - intros [-> | Hxy]; [apply Hrefl | exact Hxy].
  - apply reflexive_closure_base.
Qed.

Lemma reflexive_closure_symmetric :
  forall (A : Type) (R : A -> A -> Prop),
    (forall x y, R x y -> R y x) ->
    forall x y,
      relation_reflexive_closure R x y ->
      relation_reflexive_closure R y x.
Proof.
  intros A R Hsym x y [-> | Hxy].
  - now left.
  - right. now apply Hsym.
Qed.

Lemma reflexive_closure_transitive :
  forall (A : Type) (R : A -> A -> Prop),
    (forall x y z, R x y -> R y z -> R x z) ->
    forall x y z,
      relation_reflexive_closure R x y ->
      relation_reflexive_closure R y z ->
      relation_reflexive_closure R x z.
Proof.
  intros A R Htrans x y z Hxy Hyz.
  destruct Hxy as [Hxy | Hxy]; destruct Hyz as [Hyz | Hyz].
  - subst y; subst z. now left.
  - subst y. now right.
  - subst z. now right.
  - right. eapply Htrans; eauto.
Qed.

Lemma positive_closure_base :
  forall (A : Type) (R : A -> A -> Prop) x y,
    R x y -> relation_positive_closure R x y.
Proof.
  intros A R x y Hxy. exists 1; split; [lia |].
  now apply rel_iter_one.
Qed.

Lemma positive_closure_iff_succ_iter :
  forall (A : Type) (R : A -> A -> Prop) x y,
    relation_positive_closure R x y <->
    exists n, rel_iter R (S n) x y.
Proof.
  intros A R x y; split.
  - intros [n [Hn Hxy]]. destruct n; [lia | now exists n].
  - intros [n Hxy]. exists (S n); split; [lia | exact Hxy].
Qed.

Lemma positive_closure_transitive :
  forall (A : Type) (R : A -> A -> Prop) x y z,
    relation_positive_closure R x y ->
    relation_positive_closure R y z ->
    relation_positive_closure R x z.
Proof.
  intros A R x y z [n [Hn Hxy]] [m [Hm Hyz]].
  exists (n + m); split; [lia |].
  apply (proj2 (rel_iter_plus R n m x z)).
  exists y; auto.
Qed.

Lemma positive_closure_symmetric :
  forall (A : Type) (R : A -> A -> Prop),
    (forall x y, R x y -> R y x) ->
    forall x y,
      relation_positive_closure R x y ->
      relation_positive_closure R y x.
Proof.
  intros A R Hsym x y [n [Hn Hxy]].
  exists n; split; [exact Hn |].
  now apply rel_iter_reverse_of_symmetric.
Qed.

Lemma positive_closure_of_transitive_iff :
  forall (A : Type) (R : A -> A -> Prop),
    (forall x y z, R x y -> R y z -> R x z) ->
    forall x y, relation_positive_closure R x y <-> R x y.
Proof.
  intros A R Htrans x y; split.
  - intros [n [Hn Hxy]].
    eapply rel_iter_collapse_of_transitive; eauto.
  - apply positive_closure_base.
Qed.

Lemma rtc_refl :
  forall (A : Type) (R : A -> A -> Prop) x,
    relation_reflexive_transitive_closure R x x.
Proof. intros; exists 0; reflexivity. Qed.

Lemma rtc_base :
  forall (A : Type) (R : A -> A -> Prop) x y,
    R x y -> relation_reflexive_transitive_closure R x y.
Proof.
  intros A R x y Hxy. exists 1. now apply rel_iter_one.
Qed.

Lemma rtc_positive :
  forall (A : Type) (R : A -> A -> Prop) x y,
    relation_positive_closure R x y ->
    relation_reflexive_transitive_closure R x y.
Proof. intros A R x y [n [_ Hxy]]; now exists n. Qed.

Lemma rtc_transitive :
  forall (A : Type) (R : A -> A -> Prop) x y z,
    relation_reflexive_transitive_closure R x y ->
    relation_reflexive_transitive_closure R y z ->
    relation_reflexive_transitive_closure R x z.
Proof.
  intros A R x y z [n Hxy] [m Hyz].
  exists (n + m).
  apply (proj2 (rel_iter_plus R n m x z)).
  exists y; auto.
Qed.

Lemma rtc_iff_eq_or_positive :
  forall (A : Type) (R : A -> A -> Prop) x y,
    relation_reflexive_transitive_closure R x y <->
    x = y \/ relation_positive_closure R x y.
Proof.
  intros A R x y; split.
  - intros [n Hxy]. destruct n as [|n].
    + left. exact Hxy.
    + right. exists (S n); split; [lia | exact Hxy].
  - intros [-> | [n [_ Hxy]]].
    + apply rtc_refl.
    + now exists n.
Qed.

Lemma rtc_of_reflexive_iff_positive :
  forall (A : Type) (R : A -> A -> Prop),
    (forall x, R x x) ->
    forall x y,
      relation_reflexive_transitive_closure R x y <->
      relation_positive_closure R x y.
Proof.
  intros A R Hrefl x y; split.
  - rewrite rtc_iff_eq_or_positive.
    intros [-> | Hxy]; [apply positive_closure_base, Hrefl | exact Hxy].
  - apply rtc_positive.
Qed.

Lemma rtc_of_transitive_iff_reflexive_closure :
  forall (A : Type) (R : A -> A -> Prop),
    (forall x y z, R x y -> R y z -> R x z) ->
    forall x y,
      relation_reflexive_transitive_closure R x y <->
      relation_reflexive_closure R x y.
Proof.
  intros A R Htrans x y.
  rewrite rtc_iff_eq_or_positive.
  unfold relation_reflexive_closure.
  now rewrite positive_closure_of_transitive_iff.
Qed.

Lemma rtc_symmetric :
  forall (A : Type) (R : A -> A -> Prop),
    (forall x y, R x y -> R y x) ->
    forall x y,
      relation_reflexive_transitive_closure R x y ->
      relation_reflexive_transitive_closure R y x.
Proof.
  intros A R Hsym x y [n Hxy].
  exists n. now apply rel_iter_reverse_of_symmetric.
Qed.

(** * Named frame properties and their exact relationships *)

Definition frame_irreflexive (F : frame) : Prop :=
  forall x : World F, ~ Rel F x x.

Definition frame_asymmetric (F : frame) : Prop :=
  forall x y : World F, Rel F x y -> ~ Rel F y x.

Definition frame_antisymmetric (F : frame) : Prop :=
  forall x y : World F, Rel F x y -> Rel F y x -> x = y.

Definition frame_is_strict_preorder (F : frame) : Prop :=
  frame_irreflexive F /\ frame_transitive F.

Definition frame_is_partial_order (F : frame) : Prop :=
  frame_reflexive F /\ frame_transitive F /\ frame_antisymmetric F.

Definition frame_is_preorder (F : frame) : Prop :=
  frame_reflexive F /\ frame_transitive F.

Definition frame_is_equivalence (F : frame) : Prop :=
  frame_reflexive F /\ frame_symmetric F /\ frame_transitive F.

Lemma asymmetric_irreflexive :
  forall F : frame, frame_asymmetric F -> frame_irreflexive F.
Proof.
  intros F Hasym x Rxx. exact (Hasym x x Rxx Rxx).
Qed.

Lemma asymmetric_antisymmetric :
  forall F : frame, frame_asymmetric F -> frame_antisymmetric F.
Proof.
  intros F Hasym x y Rxy Ryx. exfalso.
  exact (Hasym x y Rxy Ryx).
Qed.

Lemma irreflexive_antisymmetric_asymmetric :
  forall F : frame,
    frame_irreflexive F -> frame_antisymmetric F -> frame_asymmetric F.
Proof.
  intros F Hirrefl Hanti x y Rxy Ryx.
  pose proof (Hanti x y Rxy Ryx) as ->.
  exact (Hirrefl y Ryx).
Qed.

Theorem asymmetric_iff_irreflexive_and_antisymmetric :
  forall F : frame,
    frame_asymmetric F <->
    frame_irreflexive F /\ frame_antisymmetric F.
Proof.
  intro F; split.
  - intro H; split; [now apply asymmetric_irreflexive |
                     now apply asymmetric_antisymmetric].
  - intros [Hirrefl Hanti].
    now apply irreflexive_antisymmetric_asymmetric.
Qed.

Lemma irreflexive_transitive_asymmetric :
  forall F : frame,
    frame_irreflexive F -> frame_transitive F -> frame_asymmetric F.
Proof.
  intros F Hirrefl Htrans x y Rxy Ryx.
  apply (Hirrefl x). eapply Htrans; eauto.
Qed.

Theorem asymmetric_iff_irreflexive_of_transitive :
  forall F : frame,
    frame_transitive F ->
    (frame_asymmetric F <-> frame_irreflexive F).
Proof.
  intros F Htrans; split.
  - apply asymmetric_irreflexive.
  - intro Hirrefl. now apply irreflexive_transitive_asymmetric.
Qed.

(** * Closure frames *)

Definition frame_refl_gen (F : frame) : frame :=
  {| World := World F;
     Rel := relation_reflexive_closure (Rel F) |}.

Definition frame_trans_gen (F : frame) : frame :=
  {| World := World F;
     Rel := relation_positive_closure (Rel F) |}.

Definition frame_refl_trans_gen (F : frame) : frame :=
  {| World := World F;
     Rel := relation_reflexive_transitive_closure (Rel F) |}.

Lemma frame_refl_gen_reflexive :
  forall F, frame_reflexive (frame_refl_gen F).
Proof. intros F x; apply reflexive_closure_refl. Qed.

Lemma frame_refl_gen_symmetric :
  forall F,
    frame_symmetric F -> frame_symmetric (frame_refl_gen F).
Proof.
  intros F Hsym x y Hxy.
  exact (reflexive_closure_symmetric Hsym Hxy).
Qed.

Lemma frame_refl_gen_transitive :
  forall F,
    frame_transitive F -> frame_transitive (frame_refl_gen F).
Proof.
  intros F Htrans x y z Hxy Hyz.
  exact (reflexive_closure_transitive Htrans Hxy Hyz).
Qed.

Lemma frame_refl_gen_antisymmetric :
  forall F,
    frame_antisymmetric F -> frame_antisymmetric (frame_refl_gen F).
Proof.
  intros F Hanti x y Hxy Hyx.
  destruct Hxy as [-> | Rxy]; [reflexivity |].
  destruct Hyx as [-> | Ryx]; [reflexivity |].
  now apply (Hanti x y).
Qed.

Lemma frame_refl_gen_partial_order_of_strict_preorder :
  forall F,
    frame_is_strict_preorder F ->
    frame_is_partial_order (frame_refl_gen F).
Proof.
  intros F [Hirrefl Htrans].
  split; [apply frame_refl_gen_reflexive |].
  split; [now apply frame_refl_gen_transitive |].
  apply frame_refl_gen_antisymmetric.
  apply asymmetric_antisymmetric.
  now apply irreflexive_transitive_asymmetric.
Qed.

Lemma frame_trans_gen_transitive :
  forall F, frame_transitive (frame_trans_gen F).
Proof. intros F; exact (@positive_closure_transitive (World F) (Rel F)). Qed.

Lemma frame_trans_gen_reflexive :
  forall F,
    frame_reflexive F -> frame_reflexive (frame_trans_gen F).
Proof.
  intros F Hrefl x. apply positive_closure_base, Hrefl.
Qed.

Lemma frame_trans_gen_symmetric :
  forall F,
    frame_symmetric F -> frame_symmetric (frame_trans_gen F).
Proof.
  intros F Hsym x y Hxy.
  exact (positive_closure_symmetric Hsym Hxy).
Qed.

Lemma frame_trans_gen_preorder :
  forall F,
    frame_reflexive F -> frame_is_preorder (frame_trans_gen F).
Proof.
  intros F Hrefl; split.
  - now apply frame_trans_gen_reflexive.
  - apply frame_trans_gen_transitive.
Qed.

Lemma frame_trans_gen_equivalence :
  forall F,
    frame_reflexive F -> frame_symmetric F ->
    frame_is_equivalence (frame_trans_gen F).
Proof.
  intros F Hrefl Hsym; repeat split.
  - now apply frame_trans_gen_reflexive.
  - now apply frame_trans_gen_symmetric.
  - apply frame_trans_gen_transitive.
Qed.

Lemma frame_trans_gen_irreflexive_of_strict_preorder :
  forall F,
    frame_is_strict_preorder F -> frame_irreflexive (frame_trans_gen F).
Proof.
  intros F [Hirrefl Htrans] x Hxx.
  apply (Hirrefl x).
  apply (proj1 (positive_closure_of_transitive_iff Htrans x x)).
  exact Hxx.
Qed.

Lemma frame_trans_gen_relation_of_transitive_iff :
  forall F,
    frame_transitive F ->
    forall x y,
      Rel (frame_trans_gen F) x y <-> Rel F x y.
Proof. intros F Htrans; now apply positive_closure_of_transitive_iff. Qed.

Lemma frame_refl_trans_gen_preorder :
  forall F, frame_is_preorder (frame_refl_trans_gen F).
Proof.
  intro F; split.
  - intro x; apply rtc_refl.
  - exact (@rtc_transitive (World F) (Rel F)).
Qed.

Lemma frame_refl_trans_gen_symmetric :
  forall F,
    frame_symmetric F -> frame_symmetric (frame_refl_trans_gen F).
Proof.
  intros F Hsym x y Hxy. exact (rtc_symmetric Hsym Hxy).
Qed.

Lemma frame_refl_trans_gen_equivalence :
  forall F,
    frame_symmetric F -> frame_is_equivalence (frame_refl_trans_gen F).
Proof.
  intros F Hsym; split.
  - intro x. apply rtc_refl.
  - split.
    + now apply frame_refl_trans_gen_symmetric.
    + exact (@rtc_transitive (World F) (Rel F)).
Qed.

Lemma frame_refl_trans_gen_antisymmetric :
  forall F,
    frame_transitive F -> frame_antisymmetric F ->
    frame_antisymmetric (frame_refl_trans_gen F).
Proof.
  intros F Htrans Hanti x y Hxy Hyx.
  apply (proj1 (rtc_of_transitive_iff_reflexive_closure Htrans x y)) in Hxy.
  apply (proj1 (rtc_of_transitive_iff_reflexive_closure Htrans y x)) in Hyx.
  exact (@frame_refl_gen_antisymmetric F Hanti x y Hxy Hyx).
Qed.

(** * Termination at a distinguished target *)

Definition frame_terminated (F : frame) (t : World F) : Prop :=
  forall x, x <> t -> relation_positive_closure (Rel F) x t.

Definition frame_directly_terminated (F : frame) (t : World F) : Prop :=
  forall x, x <> t -> Rel F x t.

Definition frame_terminal (F : frame) (t : World F) : Prop :=
  forall y, ~ Rel F t y.

Arguments frame_terminated F t : clear implicits.
Arguments frame_directly_terminated F t : clear implicits.
Arguments frame_terminal F t : clear implicits.

Lemma terminated_of_directly_terminated :
  forall (F : frame) (t : World F),
    frame_directly_terminated F t -> frame_terminated F t.
Proof.
  intros F t Hdirect x Hxt.
  apply positive_closure_base. now apply Hdirect.
Qed.

(** This is Foundation's [direct_terminated_of_trans]. *)
Lemma directly_terminated_of_transitive :
  forall (F : frame) (t : World F),
    frame_transitive F ->
    frame_terminated F t -> frame_directly_terminated F t.
Proof.
  intros F t Htrans Hterm x Hxt.
  apply (proj1 (positive_closure_of_transitive_iff Htrans x t)).
  now apply Hterm.
Qed.

Theorem terminated_iff_directly_terminated_of_transitive :
  forall (F : frame) (t : World F),
    frame_transitive F ->
    (frame_terminated F t <-> frame_directly_terminated F t).
Proof.
  intros F t Htrans; split.
  - now apply directly_terminated_of_transitive.
  - apply terminated_of_directly_terminated.
Qed.

Lemma terminated_refl_gen_iff :
  forall (F : frame) (t : World F),
    frame_terminated (frame_refl_gen F) t <-> frame_terminated F t.
Proof.
  intros F t; split.
  - intros Hterm x Hxt.
    specialize (Hterm x Hxt).
    assert (Hrtc : relation_reflexive_transitive_closure (Rel F) x t).
    {
      destruct Hterm as [n [Hn Hpath]].
      apply (proj1 (positive_closure_of_transitive_iff
        (@rtc_transitive (World F) (Rel F)) x t)).
      exists n; split; [exact Hn |].
      eapply rel_iter_monotone; [|exact Hpath].
      intros u v [-> | Ruv].
      - apply rtc_refl.
      - now apply rtc_base.
    }
    apply (proj1 (rtc_iff_eq_or_positive (Rel F) x t)) in Hrtc.
    destruct Hrtc as [Hxt' | Hpos]; [contradiction | exact Hpos].
  - intros Hterm x Hxt.
    destruct (Hterm x Hxt) as [n [Hn Hpath]].
    exists n; split; [exact Hn |].
    eapply rel_iter_monotone; [|exact Hpath].
    intros u v Ruv. now right.
Qed.

Lemma terminated_trans_gen_iff :
  forall (F : frame) (t : World F),
    frame_terminated (frame_trans_gen F) t <-> frame_terminated F t.
Proof.
  intros F t; split.
  - intros Hterm x Hxt.
    apply (proj1 (positive_closure_of_transitive_iff
      (@positive_closure_transitive (World F) (Rel F)) x t)).
    now apply Hterm.
  - intros Hterm x Hxt.
    apply positive_closure_base. now apply Hterm.
Qed.

Lemma terminated_refl_trans_gen_iff :
  forall (F : frame) (t : World F),
    frame_terminated (frame_refl_trans_gen F) t <->
    frame_terminated F t.
Proof.
  intros F t; split.
  - intros Hterm x Hxt.
    specialize (Hterm x Hxt).
    apply (proj1 (positive_closure_of_transitive_iff
      (@rtc_transitive (World F) (Rel F)) x t)) in Hterm.
    apply (proj1 (rtc_iff_eq_or_positive (Rel F) x t)) in Hterm.
    destruct Hterm as [Hxt' | Hpos]; [contradiction | exact Hpos].
  - intros Hterm x Hxt.
    apply positive_closure_base, rtc_positive. now apply Hterm.
Qed.

(** * Converse well-foundedness *)

Definition relation_converse {A : Type} (R : A -> A -> Prop)
    (x y : A) : Prop := R y x.

Lemma converse_well_founded_irreflexive :
  forall F : frame,
    frame_converse_well_founded F -> frame_irreflexive F.
Proof.
  intros F Hcwf x.
  destruct (Hcwf (fun y => y = x)) as [m [Hm Hmax]].
  - now exists x.
  - subst m. exact (Hmax x eq_refl).
Qed.

(** Every finite transitive irreflexive frame is converse well-founded.
    This is the list-cover counterpart of Foundation's finite type-class
    instance.  The proof chooses a maximal member directly by induction on
    the cover; neither dependent choice nor an infinite-chain argument is
    needed. *)
Theorem finite_transitive_irreflexive_cwf :
  forall F : frame,
    finite_frame F -> frame_transitive F -> frame_irreflexive F ->
    frame_converse_well_founded F.
Proof.
  intros F [cover Hcover] Htrans Hirr X [x0 Hx0].
  assert (Hfinite_max : forall xs : list (World F),
      (exists x, In x xs /\ X x) ->
      exists m, In m xs /\ X m /\
        forall y, In y xs -> X y -> ~ Rel F m y).
  {
    intro xs; induction xs as [|a xs IH]; intros Hinh.
    - destruct Hinh as [x [Hin _]]. inversion Hin.
    - destruct (classic (exists x, In x xs /\ X x))
        as [Htail | Hno_tail].
      + destruct (IH Htail) as [m [Hmin [HmX Hmax]]].
        destruct (classic (X a /\ Rel F m a))
          as [[Ha Rma] | Hnot_ma].
        * exists a; split; [now left |].
          split; [exact Ha |].
          intros y Hyin HyX Ray.
          destruct Hyin as [Hya | Hyin].
          -- subst y. exact (Hirr a Ray).
          -- apply (Hmax y Hyin HyX).
             eapply Htrans; eauto.
        * exists m; split; [now right |].
          split; [exact HmX |].
          intros y Hyin HyX Rmy.
          destruct Hyin as [Hya | Hyin].
          -- subst y. apply Hnot_ma. now split.
          -- exact (Hmax y Hyin HyX Rmy).
      + destruct Hinh as [x [[Hax | Hxin] HxX]].
        * subst x. exists a; split; [now left |].
          split; [exact HxX |].
          intros y Hyin HyX Ray.
          destruct Hyin as [Hya | Hyin].
          -- subst y. exact (Hirr a Ray).
          -- exfalso. apply Hno_tail. now exists y.
        * exfalso. apply Hno_tail. now exists x.
  }
  destruct (Hfinite_max cover) as [m [_ [Hm Hmax]]].
  - exists x0; split; [apply Hcover | exact Hx0].
  - exists m; split; [exact Hm |].
    intros y Hy Rmy. exact (Hmax y (Hcover y) Hy Rmy).
Qed.

Lemma converse_well_founded_asymmetric :
  forall F : frame,
    frame_converse_well_founded F -> frame_asymmetric F.
Proof.
  intros F Hcwf x y Rxy Ryx.
  destruct (Hcwf (fun z => z = x \/ z = y)) as [m [Hm Hmax]].
  - exists x. now left.
  - destruct Hm as [-> | ->].
    + exact (Hmax y (or_intror eq_refl) Rxy).
    + exact (Hmax x (or_introl eq_refl) Ryx).
Qed.

Lemma converse_well_founded_antisymmetric :
  forall F : frame,
    frame_converse_well_founded F -> frame_antisymmetric F.
Proof.
  intros F Hcwf. apply asymmetric_antisymmetric.
  now apply converse_well_founded_asymmetric.
Qed.

Lemma converse_well_founded_subrelation :
  forall (F : frame) (S : World F -> World F -> Prop),
    (forall x y, S x y -> Rel F x y) ->
    frame_converse_well_founded F ->
    frame_converse_well_founded
      {| World := World F; Rel := S |}.
Proof.
  intros F S Hincl Hcwf X [x Hx].
  destruct (Hcwf X) as [m [Hm Hmax]]; [now exists x |].
  exists m; split; [exact Hm |].
  intros y Hy Rmy. apply (Hmax y Hy). now apply Hincl.
Qed.

(** The maximal-element definition used by [Loeb] is classically equivalent
    to ordinary well-foundedness of the converse accessibility relation. *)
Theorem converse_well_founded_iff_well_founded_converse :
  forall F : frame,
    frame_converse_well_founded F <->
    well_founded (relation_converse (Rel F)).
Proof.
  intro F; split.
  - intros Hcwf x.
    apply NNPP. intro Hnotacc.
    destruct (Hcwf (fun y => ~ Acc (relation_converse (Rel F)) y))
      as [m [Hbad Hmax]].
    + now exists x.
    + apply Hbad. constructor. intros y Hym.
      apply NNPP. intro Hbad_y.
      apply (Hmax y Hbad_y). exact Hym.
  - intros Hwf X [x Hx]. revert Hx.
    refine (@well_founded_ind (World F) (relation_converse (Rel F)) Hwf
      (fun u => X u ->
        exists m, X m /\ forall y, X y -> ~ Rel F m y) _ x).
    intros u IH Hu.
    destruct (classic (exists v, X v /\ Rel F u v))
      as [[v [Hv Ruv]] | Hnone].
    + apply (IH v Ruv Hv).
    + exists u; split; [exact Hu |].
      intros v Hv Ruv. apply Hnone. now exists v.
Qed.

Lemma positive_converse_in_clos_trans_converse :
  forall (A : Type) (R : A -> A -> Prop) x y,
    relation_positive_closure R y x ->
    clos_trans A (relation_converse R) x y.
Proof.
  intros A R x y Hpos.
  destruct (proj1 (@positive_closure_iff_succ_iter A R y x) Hpos)
    as [n Hpath]. clear Hpos. revert x y Hpath.
  induction n as [|n IH]; intros x y Hpath.
  - apply t_step. exact (proj1 (@rel_iter_one A R y x) Hpath).
  - destruct Hpath as [z [Ryz Hzx]].
    eapply t_trans.
    + apply IH. exact Hzx.
    + apply t_step. exact Ryz.
Qed.

Lemma converse_well_founded_positive_closure :
  forall F : frame,
    frame_converse_well_founded F ->
    frame_converse_well_founded (frame_trans_gen F).
Proof.
  intros F Hcwf.
  apply (proj2 (converse_well_founded_iff_well_founded_converse
    (frame_trans_gen F))).
  eapply wf_incl.
  - intros x y Hxy.
    exact (positive_converse_in_clos_trans_converse Hxy).
  - apply wf_clos_trans.
    apply (proj1 (converse_well_founded_iff_well_founded_converse F)).
    exact Hcwf.
Qed.

Theorem converse_well_founded_trans_gen_iff :
  forall F : frame,
    frame_converse_well_founded (frame_trans_gen F) <->
    frame_converse_well_founded F.
Proof.
  intro F; split.
  - intros Hcwf X HX.
    destruct (Hcwf X HX) as [m [Hm Hmax]].
    exists m; split; [exact Hm |].
    intros y Hy Rmy. apply (Hmax y Hy).
    now apply positive_closure_base.
  - apply converse_well_founded_positive_closure.
Qed.

Lemma converse_well_founded_refl_gen_impossible :
  forall (F : frame) (x : World F),
    ~ frame_converse_well_founded (frame_refl_gen F).
Proof.
  intros F x Hcwf.
  pose proof (@converse_well_founded_irreflexive
    (frame_refl_gen F) Hcwf) as Hirr.
  exact (Hirr x (reflexive_closure_refl (Rel F) x)).
Qed.

Lemma converse_well_founded_refl_trans_gen_impossible :
  forall (F : frame) (x : World F),
    ~ frame_converse_well_founded (frame_refl_trans_gen F).
Proof.
  intros F x Hcwf.
  pose proof (@converse_well_founded_irreflexive
    (frame_refl_trans_gen F) Hcwf) as Hirr.
  exact (Hirr x (rtc_refl (Rel F) x)).
Qed.

Theorem terminated_cwf_target_terminal :
  forall (F : frame) (t : World F),
    frame_terminated F t ->
    frame_converse_well_founded F ->
    frame_terminal F t.
Proof.
  intros F t Hterm Hcwf y Rty.
  destruct (classic (y = t)) as [-> | Hyt].
  - exact ((@converse_well_founded_irreflexive F Hcwf) t Rty).
  - pose proof (Hterm y Hyt) as Hyt_path.
    assert (Hcycle : relation_positive_closure (Rel F) t t).
    {
      eapply positive_closure_transitive.
      - exact (@positive_closure_base (World F) (Rel F) t y Rty).
      - exact Hyt_path.
    }
    pose proof (converse_well_founded_positive_closure Hcwf) as Hcwf_plus.
    exact ((@converse_well_founded_irreflexive
      (frame_trans_gen F) Hcwf_plus) t Hcycle).
Qed.
