(**
  Stable functions between coherence spaces.

  This module ports the active mathematical surface of Foundation's
  [Semantics/CoherenceSpace/StableFunction.lean].  Equality of points and
  stable maps is extensional, so the preservation and category laws do not
  require functional or propositional extensionality.
*)

From Stdlib Require Import RelationClasses Morphisms.
From FoundationModal Require Import CoherenceSpace.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Stable maps *)

Record stable_function {A B : Type}
    (CA : coherence_space A) (CB : coherence_space B) := {
  stable_apply : point CA -> point CB;

  stable_monotone' :
    forall p q, point_included p q ->
      point_included (stable_apply p) (stable_apply q);

  stable_colimit' :
    forall (s : point CA -> Prop)
      (Hdirected : directed_on point_included s) x,
      point_member (stable_apply (@point_colimit A CA s Hdirected)) x <->
      exists p, s p /\ point_member (stable_apply p) x;

  stable_pullback' :
    forall p q,
      is_clique CA
        (set_union (point_member p) (point_member q)) ->
      point_equiv
        (stable_apply (point_meet p q))
        (point_meet (stable_apply p) (stable_apply q))
}.

Arguments stable_apply {A B CA CB} _ _.
Arguments stable_monotone' {A B CA CB} _ _ _ _.
Arguments stable_colimit' {A B CA CB} _ _ _ _.
Arguments stable_pullback' {A B CA CB} _ _ _ _.

Definition stable_function_equiv {A B} {CA : coherence_space A}
    {CB : coherence_space B}
    (f g : stable_function CA CB) : Prop :=
  forall p, point_equiv (stable_apply f p) (stable_apply g p).

Lemma stable_function_equiv_refl :
  forall A B (CA : coherence_space A) (CB : coherence_space B)
      (f : stable_function CA CB),
    stable_function_equiv f f.
Proof. intros A B CA CB f p; apply point_equiv_refl. Qed.

Lemma stable_function_equiv_sym :
  forall A B (CA : coherence_space A) (CB : coherence_space B)
      (f g : stable_function CA CB),
    stable_function_equiv f g -> stable_function_equiv g f.
Proof.
  intros A B CA CB f g H p. apply point_equiv_sym. apply H.
Qed.

Lemma stable_function_equiv_trans :
  forall A B (CA : coherence_space A) (CB : coherence_space B)
      (f g h : stable_function CA CB),
    stable_function_equiv f g -> stable_function_equiv g h ->
    stable_function_equiv f h.
Proof.
  intros A B CA CB f g h Hfg Hgh p.
  eapply point_equiv_trans; [apply Hfg | apply Hgh].
Qed.

#[global] Instance stable_function_equiv_equivalence
    A B (CA : coherence_space A) (CB : coherence_space B) :
  Equivalence (@stable_function_equiv A B CA CB).
Proof.
  split.
  - intro f. apply stable_function_equiv_refl.
  - intros f g. apply stable_function_equiv_sym.
  - intros f g h. apply stable_function_equiv_trans.
Qed.

Lemma stable_monotone :
  forall A B (CA : coherence_space A) (CB : coherence_space B)
      (f : stable_function CA CB) p q,
    point_included p q ->
    point_included (stable_apply f p) (stable_apply f q).
Proof. intros; now apply stable_monotone'. Qed.

(** Extensionality on points is a consequence of monotonicity, since
    [point_equiv] is mutual inclusion.  Keeping it derived mirrors the source
    record, whose only order field is monotonicity. *)
Lemma stable_respects_equiv :
  forall A B (CA : coherence_space A) (CB : coherence_space B)
      (f : stable_function CA CB) p q,
    point_equiv p q ->
    point_equiv (stable_apply f p) (stable_apply f q).
Proof.
  intros A B CA CB f p q Heq.
  apply point_equiv_iff_mutual_inclusion in Heq.
  apply point_equiv_iff_mutual_inclusion.
  destruct Heq as [Hpq Hqp]; split; now apply stable_monotone.
Qed.

Lemma stable_colimit :
  forall A B (CA : coherence_space A) (CB : coherence_space B)
      (f : stable_function CA CB)
      (s : point CA -> Prop)
      (Hdirected : directed_on point_included s) x,
    point_member (stable_apply f (@point_colimit A CA s Hdirected)) x <->
    exists p, s p /\ point_member (stable_apply f p) x.
Proof. intros; apply stable_colimit'. Qed.

Lemma stable_pullback :
  forall A B (CA : coherence_space A) (CB : coherence_space B)
      (f : stable_function CA CB) p q,
    is_clique CA (set_union (point_member p) (point_member q)) ->
    point_equiv
      (stable_apply f (point_meet p q))
      (point_meet (stable_apply f p) (stable_apply f q)).
Proof. intros; now apply stable_pullback'. Qed.

(** Stable maps preserve compatibility of points.  Monotonicity gives the
    short proof: the union of two compatible points is itself a common upper
    bound, and both images lie inside its image. *)
Definition point_union_of_clique {A} {C : coherence_space A}
    (p q : point C)
    (Hclique : is_clique C
      (set_union (point_member p) (point_member q))) : point C :=
  {| point_member := set_union (point_member p) (point_member q);
     point_is_clique := Hclique |}.

Lemma point_left_included_union :
  forall A (C : coherence_space A) (p q : point C) Hclique,
    point_included p (@point_union_of_clique A C p q Hclique).
Proof. firstorder. Qed.

Lemma point_right_included_union :
  forall A (C : coherence_space A) (p q : point C) Hclique,
    point_included q (@point_union_of_clique A C p q Hclique).
Proof. firstorder. Qed.

Lemma stable_union_clique :
  forall A B (CA : coherence_space A) (CB : coherence_space B)
      (f : stable_function CA CB) p q,
    is_clique CA (set_union (point_member p) (point_member q)) ->
    is_clique CB
      (set_union
        (point_member (stable_apply f p))
        (point_member (stable_apply f q))).
Proof.
  intros A B CA CB f p q Hclique.
  pose (u := @point_union_of_clique A CA p q Hclique).
  pose proof (@stable_monotone A B CA CB f p u
    (@point_left_included_union A CA p q Hclique)) as Hpu.
  pose proof (@stable_monotone A B CA CB f q u
    (@point_right_included_union A CA p q Hclique)) as Hqu.
  intros x [Hxp | Hxq] y [Hyp | Hyq];
    apply (point_is_clique (stable_apply f u) x).
  - exact (Hpu x Hxp).
  - exact (Hpu y Hyp).
  - exact (Hpu x Hxp).
  - exact (Hqu y Hyq).
  - exact (Hqu x Hxq).
  - exact (Hpu y Hyp).
  - exact (Hqu x Hxq).
  - exact (Hqu y Hyq).
Qed.

Lemma stable_function_extensional :
  forall A B (CA : coherence_space A) (CB : coherence_space B)
      (f g : stable_function CA CB),
    (forall p, point_equiv (stable_apply f p) (stable_apply g p)) ->
    stable_function_equiv f g.
Proof. firstorder. Qed.

(** * Images and the source-form colimit equation *)

Definition stable_image {A B} {CA : coherence_space A}
    {CB : coherence_space B}
    (f : stable_function CA CB) (s : point CA -> Prop) :
    point CB -> Prop :=
  fun q => exists p, s p /\ point_equiv q (stable_apply f p).

Lemma stable_image_directed :
  forall A B (CA : coherence_space A) (CB : coherence_space B)
      (f : stable_function CA CB)
      (s : point CA -> Prop),
    directed_on point_included s ->
    directed_on point_included (stable_image f s).
Proof.
  intros A B CA CB f s Hdirected q [p [Hp Hqp]] r [t [Ht Hrt]].
  destruct (Hdirected p Hp t Ht) as [u [Hu [Hpu Htu]]].
  exists (stable_apply f u). split.
  - exists u. split; [exact Hu | apply point_equiv_refl].
  - split; intros x Hx.
    + exact (@stable_monotone A B CA CB f p u Hpu x
        ((proj1 (Hqp x)) Hx)).
    + exact (@stable_monotone A B CA CB f t u Htu x
        ((proj1 (Hrt x)) Hx)).
Qed.

Lemma stable_colimit_equiv :
  forall A B (CA : coherence_space A) (CB : coherence_space B)
      (f : stable_function CA CB)
      (s : point CA -> Prop)
      (Hdirected : directed_on point_included s),
    point_equiv
      (stable_apply f (@point_colimit A CA s Hdirected))
      (@point_colimit B CB (stable_image f s)
        (@stable_image_directed A B CA CB f s Hdirected)).
Proof.
  intros A B CA CB f s Hdirected x. split.
  - intro Hx. apply (proj1
      (@stable_colimit A B CA CB f s Hdirected x)) in Hx.
    destruct Hx as [p [Hp Hxp]].
    exists (stable_apply f p). split.
    + exists p. split; [exact Hp | apply point_equiv_refl].
    + exact Hxp.
  - intros [q [[p [Hp Hqp]] Hx]].
    apply (proj2 (@stable_colimit A B CA CB f s Hdirected x)).
    exists p. split; [exact Hp |].
    now apply (proj1 (Hqp x)).
Qed.

(** * Identity and composition *)

Definition stable_identity {A} (C : coherence_space A) :
    stable_function C C.
Proof.
  refine {| stable_apply := fun p => p |}.
  - intros p q Hpq. exact Hpq.
  - intros s Hdirected x. reflexivity.
  - intros p q Hclique. apply point_equiv_refl.
Defined.

Lemma stable_identity_apply :
  forall A (C : coherence_space A) (p : point C),
    point_equiv (stable_apply (stable_identity C) p) p.
Proof. intros; apply point_equiv_refl. Qed.

Definition stable_compose {A B D}
    {CA : coherence_space A} {CB : coherence_space B}
    {CD : coherence_space D}
    (g : stable_function CB CD) (f : stable_function CA CB) :
    stable_function CA CD.
Proof.
  refine {| stable_apply := fun p => stable_apply g (stable_apply f p) |}.
  - intros p q Hpq. apply stable_monotone, stable_monotone, Hpq.
  - intros s Hdirected x.
    pose (Hdimage :=
      @stable_image_directed A B CA CB f s Hdirected).
    pose proof (@stable_respects_equiv B D CB CD g
      (stable_apply f (@point_colimit A CA s Hdirected))
      (@point_colimit B CB (stable_image f s) Hdimage)
      (@stable_colimit_equiv A B CA CB f s Hdirected)) as Hrespect.
    transitivity
      (point_member
        (stable_apply g
          (@point_colimit B CB (stable_image f s) Hdimage)) x).
    + apply Hrespect.
    + transitivity
        (exists q, stable_image f s q /\
          point_member (stable_apply g q) x).
      * apply stable_colimit.
      * split.
        -- intros [q [[p [Hp Hqp]] Hx]].
           exists p. split; [exact Hp |].
           apply (proj1 ((stable_respects_equiv g Hqp) x)). exact Hx.
        -- intros [p [Hp Hx]]. exists (stable_apply f p). split.
           ++ exists p. split; [exact Hp | apply point_equiv_refl].
           ++ exact Hx.
  - intros p q Hclique.
    eapply point_equiv_trans.
    + apply stable_respects_equiv. now apply stable_pullback.
    + apply stable_pullback. now apply stable_union_clique.
Defined.

Lemma stable_compose_apply :
  forall A B D
      (CA : coherence_space A) (CB : coherence_space B)
      (CD : coherence_space D)
      (g : stable_function CB CD) (f : stable_function CA CB) p,
    point_equiv
      (stable_apply (stable_compose g f) p)
      (stable_apply g (stable_apply f p)).
Proof. intros; apply point_equiv_refl. Qed.

Lemma stable_identity_compose :
  forall A B (CA : coherence_space A) (CB : coherence_space B)
      (f : stable_function CA CB),
    stable_function_equiv (stable_compose (stable_identity CB) f) f.
Proof. intros A B CA CB f p; apply point_equiv_refl. Qed.

Lemma stable_compose_identity :
  forall A B (CA : coherence_space A) (CB : coherence_space B)
      (f : stable_function CA CB),
    stable_function_equiv (stable_compose f (stable_identity CA)) f.
Proof. intros A B CA CB f p; apply point_equiv_refl. Qed.

Lemma stable_compose_associative :
  forall A B D E
      (CA : coherence_space A) (CB : coherence_space B)
      (CD : coherence_space D) (CE : coherence_space E)
      (h : stable_function CD CE)
      (g : stable_function CB CD)
      (f : stable_function CA CB),
    stable_function_equiv
      (stable_compose h (stable_compose g f))
      (stable_compose (stable_compose h g) f).
Proof. intros A B D E CA CB CD CE h g f p; apply point_equiv_refl. Qed.
