(** Classical weak forcing through the Gödel--Gentzen translation. *)

From Stdlib Require Import Logic.Classical_Prop Logic.FunctionalExtensionality
  Lists.List Vectors.Fin.
From FoundationModal Require Import GenericForcingRelation GenericSemantics.
From Foundation.Vorspiel.Order Require Import Dense.
From Foundation.Syntax.Predicate Require Import Language Relational Rew Term.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.NegationTranslation Require Import GoedelGentzen.
From Foundation.FirstOrder.Kripke Require Import Basic Intuitionistic.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition ifo_kripke_weakly_forces {L W C O}
    (Hrel : language_relational L)
    (K : ifo_kripke_model L W C O)
    {X n} (p : W) (bv : Fin.t n -> C) (fv : X -> C)
    (phi : semiformula L X n) : Prop :=
  ifo_kripke_forces Hrel K p bv fv
    (ifo_double_negation_translation phi).

Lemma ifo_preorder_exists_below : forall W (O : preorder_data W) p,
  exists q, preorder_le O q p.
Proof. intros. exists p. apply preorder_refl. Qed.

Lemma ifo_kripke_weakly_forces_rel : forall L W C O Hrel
    (K : ifo_kripke_model L W C O) (X : Type) (n : nat) (p : W)
    (bv : Fin.t n -> C) (fv : X -> C) k
    (R : language_rel L k) (t : Fin.t k -> semiterm L X n),
  ifo_kripke_weakly_forces Hrel K p bv fv (Semiformula_rel R t) <->
  forall q, preorder_le O q p ->
    exists r, preorder_le O r q /\
      ifo_kripke_rel K r R
        (fun i => semiterm_relational_val Hrel bv fv (t i)).
Proof.
  intros. unfold ifo_kripke_weakly_forces. simpl. split.
  - intros H q Hqp. apply NNPP. intro Hnone.
    apply (H q Hqp). intros r Hrq HR.
    apply Hnone. exists r. now split.
  - intros Hdense q Hqp Hneg.
    destruct (Hdense q Hqp) as [r [Hrq HR]].
    exact (Hneg r Hrq HR).
Qed.

Lemma ifo_kripke_weakly_forces_nrel : forall L W C O Hrel
    (K : ifo_kripke_model L W C O) (X : Type) (n : nat) (p : W)
    (bv : Fin.t n -> C) (fv : X -> C) k
    (R : language_rel L k) (t : Fin.t k -> semiterm L X n),
  ifo_kripke_weakly_forces Hrel K p bv fv (Semiformula_nrel R t) <->
  forall q, preorder_le O q p ->
    ~ ifo_kripke_rel K q R
        (fun i => semiterm_relational_val Hrel bv fv (t i)).
Proof. reflexivity. Qed.

Lemma ifo_kripke_weakly_forces_verum : forall L W C O Hrel
    (K : ifo_kripke_model L W C O) X n p bv fv,
  @ifo_kripke_weakly_forces L W C O Hrel K X n p bv fv
    (Semiformula_verum n).
Proof.
  intros. unfold ifo_kripke_weakly_forces.
  apply ifo_kripke_forces_verum.
Qed.

Lemma ifo_kripke_weakly_forces_falsum : forall L W C O Hrel
    (K : ifo_kripke_model L W C O) X n p bv fv,
  ~ @ifo_kripke_weakly_forces L W C O Hrel K X n p bv fv
      (Semiformula_falsum n).
Proof. intros L W C O Hrel K X n p bv fv H. exact H. Qed.

Lemma ifo_kripke_weakly_forces_and : forall L W C O Hrel
    (K : ifo_kripke_model L W C O) X n p bv fv
    (phi psi : semiformula L X n),
  ifo_kripke_weakly_forces Hrel K p bv fv
      (Semiformula_and phi psi) <->
  ifo_kripke_weakly_forces Hrel K p bv fv phi /\
  ifo_kripke_weakly_forces Hrel K p bv fv psi.
Proof. reflexivity. Qed.

Lemma ifo_kripke_weakly_forces_or : forall L W C O Hrel
    (K : ifo_kripke_model L W C O) X n p bv fv
    (phi psi : semiformula L X n),
  ifo_kripke_weakly_forces Hrel K p bv fv
      (Semiformula_or phi psi) <->
  forall q, preorder_le O q p ->
    exists r, preorder_le O r q /\
      (ifo_kripke_weakly_forces Hrel K r bv fv phi \/
       ifo_kripke_weakly_forces Hrel K r bv fv psi).
Proof.
  intros. unfold ifo_kripke_weakly_forces. simpl. split.
  - intros H q Hqp. apply NNPP. intro Hnone.
    apply (H q Hqp). split; intros r Hrq Hr.
    + apply Hnone. exists r. split; [exact Hrq | now left].
    + apply Hnone. exists r. split; [exact Hrq | now right].
  - intros Hdense q Hqp [Hnotphi Hnotpsi].
    destruct (Hdense q Hqp) as [r [Hrq [Hphi | Hpsi]]].
    + exact (Hnotphi r Hrq Hphi).
    + exact (Hnotpsi r Hrq Hpsi).
Qed.

Lemma ifo_kripke_weakly_forces_all : forall L W C O Hrel
    (K : ifo_kripke_model L W C O) X n p bv fv
    (phi : semiformula L X (S n)),
  ifo_kripke_weakly_forces Hrel K p bv fv
      (Semiformula_all phi) <->
  forall q, preorder_le O q p -> forall x,
    ifo_kripke_domain K q x ->
    ifo_kripke_weakly_forces Hrel K q (fin_cons x bv) fv phi.
Proof. reflexivity. Qed.

Lemma ifo_kripke_weakly_forces_exs : forall L W C O Hrel
    (K : ifo_kripke_model L W C O) X n p bv fv
    (phi : semiformula L X (S n)),
  ifo_kripke_weakly_forces Hrel K p bv fv
      (Semiformula_exists phi) <->
  forall q, preorder_le O q p ->
    exists r, preorder_le O r q /\
      exists x, ifo_kripke_domain K r x /\
        ifo_kripke_weakly_forces Hrel K r (fin_cons x bv) fv phi.
Proof.
  intros. unfold ifo_kripke_weakly_forces. simpl. split.
  - intros H q Hqp. apply NNPP. intro Hnone.
    apply (H q Hqp). intros r Hrq x Hx s Hsr Hbody.
    apply Hnone. exists s. split.
    + exact (@preorder_trans W O s r q Hsr Hrq).
    + exists x. split.
      * exact (@ifo_kripke_domain_antimonotone
          L W C O K r s Hsr x Hx).
      * exact Hbody.
  - intros Hdense q Hqp Hall.
    destruct (Hdense q Hqp) as [r [Hrq [x [Hx Hbody]]]].
    pose proof (Hall r Hrq x Hx) as Hneg.
    exact (Hneg r (preorder_refl O r) Hbody).
Qed.

Theorem ifo_kripke_weakly_forces_rewrite : forall L W C O Hrel
    (K : ifo_kripke_model L W C O) X n Y m
    (rw : rew L X n Y m) (phi : semiformula L X n)
    p (bv : Fin.t m -> C) (fv : Y -> C),
  ifo_kripke_weakly_forces Hrel K p bv fv
      (semiformula_rewrite rw phi) <->
  ifo_kripke_weakly_forces Hrel K p
    (fun i => semiterm_relational_val Hrel bv fv
      (rew_apply rw (Semiterm_bvar i)))
    (fun x => semiterm_relational_val Hrel bv fv
      (rew_apply rw (Semiterm_fvar x))) phi.
Proof.
  intros. unfold ifo_kripke_weakly_forces.
  rewrite <- ifo_rewrite_double_negation.
  apply ifo_kripke_forces_rewrite.
Qed.

Lemma ifo_kripke_weakly_forces_emb : forall L W C O Hrel
    (K : ifo_kripke_model L W C O) X Y n
    (empty : X -> False) p (bv : Fin.t n -> C) (fv : Y -> C)
    (phi : semiformula L X n),
  ifo_kripke_weakly_forces Hrel K p bv fv
      (semiformula_rewrite (rew_emb empty) phi) <->
  ifo_kripke_weakly_forces Hrel K p bv
    (fun x => False_rect C (empty x)) phi.
Proof.
  intros. rewrite ifo_kripke_weakly_forces_rewrite.
  assert ((fun i => semiterm_relational_val Hrel bv fv
      (rew_apply (rew_emb empty) (Semiterm_bvar i))) = bv) as ->.
  { apply functional_extensionality. intro i. reflexivity. }
  assert ((fun x => semiterm_relational_val Hrel bv fv
      (rew_apply (rew_emb empty) (Semiterm_fvar x))) =
    (fun x => False_rect C (empty x))) as ->.
  { apply functional_extensionality. intro x. destruct (empty x). }
  reflexivity.
Qed.

Lemma ifo_kripke_weakly_forces_monotone : forall L W C O Hrel
    (K : ifo_kripke_model L W C O) X n
    (phi : semiformula L X n) p bv fv,
  ifo_kripke_weakly_forces Hrel K p bv fv phi -> forall q,
    preorder_le O q p ->
    ifo_kripke_weakly_forces Hrel K q bv fv phi.
Proof.
  intros. eapply ifo_kripke_forces_monotone; eauto.
Qed.

Lemma ifo_kripke_weakly_forces_all_constant_domain : forall L W C O Hrel
    (K : ifo_kripke_model L W C O),
  ifo_kripke_constant_domain K -> forall X n p bv fv
    (phi : semiformula L X (S n)),
  ifo_kripke_weakly_forces Hrel K p bv fv
      (Semiformula_all phi) <->
  forall x,
    ifo_kripke_weakly_forces Hrel K p (fin_cons x bv) fv phi.
Proof.
  intros L W C O Hrel K Hconst X n p bv fv phi. split.
  - intros Hall x. exact (Hall p (preorder_refl O p) x (Hconst p x)).
  - intros Hall q Hqp x Hx.
    eapply ifo_kripke_weakly_forces_monotone;
      [exact (Hall x) | exact Hqp].
Qed.

Lemma ifo_kripke_weakly_forces_exs_constant_domain : forall L W C O Hrel
    (K : ifo_kripke_model L W C O),
  ifo_kripke_constant_domain K -> forall X n p bv fv
    (phi : semiformula L X (S n)),
  ifo_kripke_weakly_forces Hrel K p bv fv
      (Semiformula_exists phi) <->
  forall q, preorder_le O q p ->
    exists r, preorder_le O r q /\ exists x,
      ifo_kripke_weakly_forces Hrel K r (fin_cons x bv) fv phi.
Proof.
  intros L W C O Hrel K Hconst X n p bv fv phi.
  rewrite ifo_kripke_weakly_forces_exs. split.
  - intros H q Hqp. destruct (H q Hqp) as [r [Hrq [x [_ Hx]]]].
    exists r. split; [exact Hrq |]. exists x. exact Hx.
  - intros H q Hqp. destruct (H q Hqp) as [r [Hrq [x Hx]]].
    exists r. split; [exact Hrq |]. exists x. split.
    + apply Hconst.
    + exact Hx.
Qed.

(** Weak forcing is regular: dense forcing below a condition already forces
    at that condition.  The proof is structural and constructive once the
    exact atomic and positive-connective clauses are available. *)
Fixpoint ifo_kripke_weakly_forces_generic {L W C}
    {O : preorder_data W}
    (Hrel : language_relational L)
    (K : ifo_kripke_model L W C O)
    {X n} (phi : semiformula L X n) :
  forall p bv fv,
    (forall q, preorder_le O q p ->
      exists r, preorder_le O r q /\
        ifo_kripke_weakly_forces Hrel K r bv fv phi) ->
    ifo_kripke_weakly_forces Hrel K p bv fv phi.
Proof.
  destruct phi as [n0 | n0 | n0 k R t | n0 k R t |
    n0 phi psi | n0 phi psi | n0 phi | n0 phi];
    intros p bv fv Hdense.
  - apply ifo_kripke_weakly_forces_verum.
  - destruct (Hdense p (preorder_refl O p)) as [r [_ Hfalse]].
    exact (False_rect _ Hfalse).
  - apply (proj2 (@ifo_kripke_weakly_forces_rel
      L W C O Hrel K X n0 p bv fv k R t)).
    intros q Hqp.
    destruct (Hdense q Hqp) as [r [Hrq Hr]].
    pose proof (proj1 (@ifo_kripke_weakly_forces_rel
      L W C O Hrel K X n0 r bv fv k R t) Hr) as Hr'.
    destruct (Hr' r (preorder_refl O r)) as [s [Hsr Hs]].
    exists s. split; [|exact Hs].
    exact (@preorder_trans W O s r q Hsr Hrq).
  - apply (proj2 (@ifo_kripke_weakly_forces_nrel
      L W C O Hrel K X n0 p bv fv k R t)).
    intros q Hqp HR.
    destruct (Hdense q Hqp) as [r [Hrq Hr]].
    pose proof (proj1 (@ifo_kripke_weakly_forces_nrel
      L W C O Hrel K X n0 r bv fv k R t) Hr) as Hr'.
    apply (Hr' r (preorder_refl O r)).
    exact (@ifo_kripke_rel_monotone L W C O K q k R
      (fun i => semiterm_relational_val Hrel bv fv (t i))
      HR r Hrq).
  - split.
    + apply (@ifo_kripke_weakly_forces_generic
        L W C O Hrel K X n0 phi).
      intros q Hqp. destruct (Hdense q Hqp) as [r [Hrq [Hphi Hpsi]]].
      exists r. now repeat split.
    + apply (@ifo_kripke_weakly_forces_generic
        L W C O Hrel K X n0 psi).
      intros q Hqp. destruct (Hdense q Hqp) as [r [Hrq [Hphi Hpsi]]].
      exists r. now repeat split.
  - apply (proj2 (@ifo_kripke_weakly_forces_or
      L W C O Hrel K X n0 p bv fv phi psi)).
    intros q Hqp. destruct (Hdense q Hqp) as [r [Hrq Hr]].
    pose proof (proj1 (@ifo_kripke_weakly_forces_or
      L W C O Hrel K X n0 r bv fv phi psi) Hr) as Hr'.
    destruct (Hr' r (preorder_refl O r)) as [s [Hsr Hs]].
    exists s. split; [|exact Hs].
    exact (@preorder_trans W O s r q Hsr Hrq).
  - apply (proj2 (@ifo_kripke_weakly_forces_all
      L W C O Hrel K X n0 p bv fv phi)).
    intros q Hqp x Hx.
    apply (@ifo_kripke_weakly_forces_generic
      L W C O Hrel K X (S n0) phi).
    intros r Hrq.
    destruct (Hdense r (@preorder_trans W O r q p Hrq Hqp))
      as [s [Hsr Hs]].
    pose proof (proj1 (@ifo_kripke_weakly_forces_all
      L W C O Hrel K X n0 s bv fv phi) Hs) as Hs'.
    exists s. split; [exact Hsr |].
    apply (Hs' s (preorder_refl O s) x).
    exact (@ifo_kripke_domain_antimonotone
      L W C O K q s
      (@preorder_trans W O s r q Hsr Hrq) x Hx).
  - apply (proj2 (@ifo_kripke_weakly_forces_exs
      L W C O Hrel K X n0 p bv fv phi)).
    intros q Hqp. destruct (Hdense q Hqp) as [r [Hrq Hr]].
    pose proof (proj1 (@ifo_kripke_weakly_forces_exs
      L W C O Hrel K X n0 r bv fv phi) Hr) as Hr'.
    destruct (Hr' r (preorder_refl O r)) as [s [Hsr [x [Hx Hbody]]]].
    exists s. split.
    + exact (@preorder_trans W O s r q Hsr Hrq).
    + exists x. now split.
Defined.

Lemma ifo_kripke_weakly_forces_generic_iff : forall L W C O Hrel
    (K : ifo_kripke_model L W C O) X n
    (phi : semiformula L X n) p bv fv,
  ifo_kripke_weakly_forces Hrel K p bv fv phi <->
  forall q, preorder_le O q p ->
    exists r, preorder_le O r q /\
      ifo_kripke_weakly_forces Hrel K r bv fv phi.
Proof.
  intros. split.
  - intros H q Hqp. exists q. split; [apply preorder_refl |].
    eapply ifo_kripke_weakly_forces_monotone; eauto.
  - apply ifo_kripke_weakly_forces_generic.
Qed.

Lemma ifo_kripke_weakly_forces_generic_iff_not : forall L W C O Hrel
    (K : ifo_kripke_model L W C O) X n
    (phi : semiformula L X n) p bv fv,
  ~ ifo_kripke_weakly_forces Hrel K p bv fv phi <->
  exists q, preorder_le O q p /\ forall r,
    preorder_le O r q ->
    ~ ifo_kripke_weakly_forces Hrel K r bv fv phi.
Proof.
  intros. split.
  - intros Hnot. apply NNPP. intro Hnone. apply Hnot.
    apply ifo_kripke_weakly_forces_generic. intros q Hqp.
    apply NNPP. intro Hnor.
    apply Hnone. exists q. split; [exact Hqp |].
    intros r Hrq Hr. apply Hnor. exists r. now split.
  - intros [q [Hqp Hall]] Hp.
    apply (Hall q (preorder_refl O q)).
    eapply ifo_kripke_weakly_forces_monotone; eauto.
Qed.
