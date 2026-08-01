(** Kripke models for relational first-order languages. *)

From Stdlib Require Import Lists.List Vectors.Fin.
From FoundationModal Require Import GenericForcingRelation.
From Foundation.Vorspiel.Order Require Import Dense.
From Foundation.Syntax.Predicate Require Import Language Relational.
From Foundation.FirstOrder.Basic.Semantics Require Import Semantics.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** Worlds are ordered explicitly.  Both domains and atomic relations persist
    toward smaller worlds, matching Foundation's use of the converse preorder
    as the intuitionistic accessibility relation. *)
Record ifo_kripke_model (L : language) (W C : Type)
    (O : preorder_data W) : Type := {
  ifo_kripke_domain : W -> C -> Prop;
  ifo_kripke_domain_nonempty :
    forall w, exists x, ifo_kripke_domain w x;
  ifo_kripke_domain_antimonotone :
    forall w v, preorder_le O v w -> forall x,
      ifo_kripke_domain w x -> ifo_kripke_domain v x;
  ifo_kripke_rel : forall w {k},
    language_rel L k -> (Fin.t k -> C) -> Prop;
  ifo_kripke_rel_monotone :
    forall w k (R : language_rel L k) t,
      ifo_kripke_rel w R t -> forall v,
        preorder_le O v w -> ifo_kripke_rel v R t
}.

Arguments ifo_kripke_model L W C O : clear implicits.

Arguments ifo_kripke_domain {L W C O} _ _ _.
Arguments ifo_kripke_domain_nonempty {L W C O} _ _.
Arguments ifo_kripke_domain_antimonotone {L W C O} _ _ _ _ _ _.
Arguments ifo_kripke_rel {L W C O} _ _ {k} _ _.
Arguments ifo_kripke_rel_monotone {L W C O} _ _ {k} _ _ _ _ _.

(** Pointwise fullness is the extensionality-free content of the source
    equation [Domain w = Set.univ]. *)
Definition ifo_kripke_constant_domain {L W C O}
    (K : ifo_kripke_model L W C O) : Prop :=
  forall w x, ifo_kripke_domain K w x.

Definition ifo_kripke_forcing_exists {L W C O}
    (K : ifo_kripke_model L W C O) : generic_forcing_exists W C :=
  {| generic_exists_forces := ifo_kripke_domain K |}.

Lemma ifo_kripke_domain_nonempty_forces : forall L W C O
    (K : ifo_kripke_model L W C O) w,
  exists x,
    generic_exists_forces (ifo_kripke_forcing_exists K) w x.
Proof. intros. apply ifo_kripke_domain_nonempty. Qed.

Lemma ifo_kripke_domain_persistent : forall L W C O
    (K : ifo_kripke_model L W C O) w x,
  ifo_kripke_domain K w x -> forall v,
    preorder_le O v w -> ifo_kripke_domain K v x.
Proof. intros. eapply ifo_kripke_domain_antimonotone; eauto. Qed.

Lemma ifo_kripke_constant_domain_forces : forall L W C O
    (K : ifo_kripke_model L W C O),
  ifo_kripke_constant_domain K -> forall w x,
    generic_exists_forces (ifo_kripke_forcing_exists K) w x.
Proof. intros L W C O K H w x. apply H. Qed.

(** * Filter colimits *)

Definition ifo_kripke_filter_carrier {L W C O}
    (K : ifo_kripke_model L W C O) (F : order_pfilter O) : Type :=
  { x : C &
    { p : W &
      (pfilter_member F p * ifo_kripke_domain K p x)%type } }.

Definition ifo_kripke_filter_val {L W C O K F}
    (x : @ifo_kripke_filter_carrier L W C O K F) : C :=
  projT1 x.

Definition ifo_kripke_filter_witness {L W C O K F}
    (x : @ifo_kripke_filter_carrier L W C O K F) : W :=
  projT1 (projT2 x).

Lemma ifo_kripke_filter_witness_member : forall L W C O K F
    (x : @ifo_kripke_filter_carrier L W C O K F),
  pfilter_member F (ifo_kripke_filter_witness x).
Proof. intros. exact (fst (projT2 (projT2 x))). Qed.

Lemma ifo_kripke_filter_witness_domain : forall L W C O K F
    (x : @ifo_kripke_filter_carrier L W C O K F),
  ifo_kripke_domain K (ifo_kripke_filter_witness x)
    (ifo_kripke_filter_val x).
Proof. intros. exact (snd (projT2 (projT2 x))). Qed.

Lemma ifo_kripke_filter_finite_colimit : forall L W C O
    (K : ifo_kripke_model L W C O) (F : order_pfilter O)
    I (cover : list I),
  (forall i, In i cover) ->
  forall p : I -> W, (forall i, pfilter_member F (p i)) ->
  exists q, pfilter_member F q /\
    forall i, preorder_le O q (p i).
Proof.
  intros L W C O K F I cover Hcover p Hp.
  destruct (@directed_finite_family_colimit W
    (fun x y => preorder_le O y x) (pfilter_member F)
    (fun x y z Hxy Hyz =>
      @preorder_trans W O z y x Hyz Hxy)
    (pfilter_nonempty F)
    (fun x y Hx Hy =>
      match @pfilter_directed W O F x y Hx Hy with
      | ex_intro _ z (conj Hz (conj Hzx Hzy)) =>
          ex_intro _ z (conj Hz (conj Hzx Hzy))
      end)
    I cover Hcover p Hp)
    as [q [Hq Hall]].
  now exists q.
Qed.

(** A duplicate-tolerant list theorem is the computational core of the
    source finite-family domain colimit and needs no finite-type instance. *)
Lemma ifo_kripke_filter_domain_list_colimit : forall L W C O
    (K : ifo_kripke_model L W C O) (F : order_pfilter O)
    (xs : list (ifo_kripke_filter_carrier K F)),
  exists q, pfilter_member F q /\
    forall x, In x xs ->
      ifo_kripke_domain K q (ifo_kripke_filter_val x).
Proof.
  intros L W C O K F xs. induction xs as [|x xs IH].
  - destruct (pfilter_nonempty F) as [q Hq].
    exists q. split; [exact Hq |]. intros y Hy. contradiction.
  - destruct IH as [q [Hq Hall]].
    destruct (@pfilter_directed W O F (ifo_kripke_filter_witness x) q
      (ifo_kripke_filter_witness_member x) Hq)
      as [r [Hr [Hrx Hrq]]].
    exists r. split; [exact Hr |].
    intros y [Hy | Hy].
    + subst y. exact (@ifo_kripke_domain_antimonotone
        L W C O K (ifo_kripke_filter_witness x) r Hrx
        (ifo_kripke_filter_val x)
        (ifo_kripke_filter_witness_domain x)).
    + exact (@ifo_kripke_domain_antimonotone
        L W C O K q r Hrq (ifo_kripke_filter_val y) (Hall y Hy)).
Qed.

Theorem ifo_kripke_filter_finite_family_domain : forall L W C O
    (K : ifo_kripke_model L W C O) (F : order_pfilter O)
    I (cover : list I),
  (forall i, In i cover) ->
  forall v : I -> ifo_kripke_filter_carrier K F,
  exists q, pfilter_member F q /\
    forall i, ifo_kripke_domain K q (ifo_kripke_filter_val (v i)).
Proof.
  intros L W C O K F I cover Hcover v.
  destruct (ifo_kripke_filter_domain_list_colimit
    (K := K) (F := F) (map v cover))
    as [q [Hq Hall]].
  exists q. split; [exact Hq |]. intro i. apply Hall.
  apply in_map. apply Hcover.
Qed.

Definition ifo_kripke_filter_structure {L W C O}
    (Hrel : language_relational L)
    (K : ifo_kripke_model L W C O) (F : order_pfilter O) :
    first_order_structure L (ifo_kripke_filter_carrier K F) :=
  {| structure_func := fun k f _ => False_rect _ (Hrel k f);
     structure_rel := fun k R v =>
       forall p, pfilter_member F p ->
         (forall i, ifo_kripke_domain K p
           (ifo_kripke_filter_val (v i))) ->
         ifo_kripke_rel K p R
           (fun i => ifo_kripke_filter_val (v i)) |}.

Lemma ifo_kripke_filter_structure_rel_iff : forall L W C O
    (Hrel : language_relational L)
    (K : ifo_kripke_model L W C O) (F : order_pfilter O)
    k (R : language_rel L k)
    (v : Fin.t k -> ifo_kripke_filter_carrier K F),
  structure_rel (ifo_kripke_filter_structure Hrel K F) R v <->
  forall p, pfilter_member F p ->
    (forall i, ifo_kripke_domain K p
      (ifo_kripke_filter_val (v i))) ->
    ifo_kripke_rel K p R (fun i => ifo_kripke_filter_val (v i)).
Proof. reflexivity. Qed.
