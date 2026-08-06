(** Classical weak forcing through the Gödel--Gentzen translation. *)

From Stdlib Require Import Logic.Classical_Prop Logic.FunctionalExtensionality
  Lists.List Vectors.Fin.
From FoundationModal Require Import GenericCalculus GenericForcingRelation
  GenericSemantics.
From Foundation.Vorspiel.Order Require Import Dense.
From Foundation.Syntax.Predicate Require Import Language Relational Rew Term.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Calculus.
From Foundation.FirstOrder.Intuitionistic Require Import Deduction.
From Foundation.FirstOrder.NegationTranslation Require Import GoedelGentzen.
From Foundation.FirstOrder.Kripke Require Import Basic Intuitionistic.

Import ListNotations.

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

(** Weak forcing commutes semantically with classical NNF negation.  The
    structural proof factors every density/refutation step through the two
    genericity characterizations above. *)
Fixpoint ifo_kripke_weakly_forces_neg {L W C}
    {O : preorder_data W}
    (Hrel : language_relational L)
    (K : ifo_kripke_model L W C O)
    {X n} (phi : semiformula L X n) :
  forall p bv fv,
  ifo_kripke_weakly_forces Hrel K p bv fv (semiformula_neg phi) <->
  forall q, preorder_le O q p ->
    ~ ifo_kripke_weakly_forces Hrel K q bv fv phi.
Proof.
  destruct phi as [n0 | n0 | n0 k R t | n0 k R t |
    n0 phi psi | n0 phi psi | n0 phi | n0 phi];
    intros p bv fv.
  - split.
    + intro Hfalse. exact (False_rect _ Hfalse).
    + intro Hall. exfalso. apply (Hall p (preorder_refl O p)).
      apply ifo_kripke_weakly_forces_verum.
  - split.
    + intros H q Hqp Hfalse. exact Hfalse.
    + intros. apply ifo_kripke_weakly_forces_verum.
  - split.
    + intros Hneg q Hqp Hweakrel.
      pose proof (proj1 (@ifo_kripke_weakly_forces_nrel
        L W C O Hrel K X n0 p bv fv k R t) Hneg) as Hneg'.
      pose proof (proj1 (@ifo_kripke_weakly_forces_rel
        L W C O Hrel K X n0 q bv fv k R t) Hweakrel) as Hrel'.
      destruct (Hrel' q (preorder_refl O q)) as [r [Hrq HR]].
      exact (Hneg' r (@preorder_trans W O r q p Hrq Hqp) HR).
    + intros Hall.
      apply (proj2 (@ifo_kripke_weakly_forces_nrel
        L W C O Hrel K X n0 p bv fv k R t)).
      intros q Hqp HR. apply (Hall q Hqp).
      apply (proj2 (@ifo_kripke_weakly_forces_rel
        L W C O Hrel K X n0 q bv fv k R t)).
      intros r Hrq. exists r. split; [apply preorder_refl |].
      exact (@ifo_kripke_rel_monotone L W C O K q k R
        (fun i => semiterm_relational_val Hrel bv fv (t i))
        HR r Hrq).
  - split.
    + intros Hweakrel q Hqp Hnrel.
      pose proof (proj1 (@ifo_kripke_weakly_forces_rel
        L W C O Hrel K X n0 p bv fv k R t) Hweakrel) as Hrel'.
      pose proof (proj1 (@ifo_kripke_weakly_forces_nrel
        L W C O Hrel K X n0 q bv fv k R t) Hnrel) as Hnrel'.
      destruct (Hrel' q Hqp) as [r [Hrq HR]].
      exact (Hnrel' r Hrq HR).
    + intros Hall.
      apply (proj2 (@ifo_kripke_weakly_forces_rel
        L W C O Hrel K X n0 p bv fv k R t)).
      intros q Hqp. apply NNPP. intro Hnone.
      apply (Hall q Hqp).
      apply (proj2 (@ifo_kripke_weakly_forces_nrel
        L W C O Hrel K X n0 q bv fv k R t)).
      intros r Hrq HR. apply Hnone. exists r. now split.
  - split.
    + intros Hneg q Hqp [Hphi Hpsi].
      pose proof (proj1 (@ifo_kripke_weakly_forces_or
        L W C O Hrel K X n0 p bv fv
        (semiformula_neg phi) (semiformula_neg psi)) Hneg) as Hneg'.
      destruct (Hneg' q Hqp) as [r [Hrq [Hnphi | Hnpsi]]].
      * pose proof (proj1 (@ifo_kripke_weakly_forces_neg
          L W C O Hrel K X n0 phi r bv fv) Hnphi) as Hnphi'.
        apply (Hnphi' r (preorder_refl O r)).
        eapply ifo_kripke_weakly_forces_monotone; eauto.
      * pose proof (proj1 (@ifo_kripke_weakly_forces_neg
          L W C O Hrel K X n0 psi r bv fv) Hnpsi) as Hnpsi'.
        apply (Hnpsi' r (preorder_refl O r)).
        eapply ifo_kripke_weakly_forces_monotone; eauto.
    + intros Hnotand.
      apply (proj2 (@ifo_kripke_weakly_forces_or
        L W C O Hrel K X n0 p bv fv
        (semiformula_neg phi) (semiformula_neg psi))).
      intros q Hqp. destruct (classic
        (ifo_kripke_weakly_forces Hrel K q bv fv phi)) as [Hphi | Hnphi].
      * assert (Hnpsi : ~ ifo_kripke_weakly_forces Hrel K q bv fv psi).
        { intro Hpsi. exact (Hnotand q Hqp (conj Hphi Hpsi)). }
        destruct (proj1 (@ifo_kripke_weakly_forces_generic_iff_not
          L W C O Hrel K X n0 psi q bv fv) Hnpsi)
          as [r [Hrq Hall]].
        exists r. split; [exact Hrq |]. right.
        exact (proj2 (@ifo_kripke_weakly_forces_neg
          L W C O Hrel K X n0 psi r bv fv) Hall).
      * destruct (proj1 (@ifo_kripke_weakly_forces_generic_iff_not
          L W C O Hrel K X n0 phi q bv fv) Hnphi)
          as [r [Hrq Hall]].
        exists r. split; [exact Hrq |]. left.
        exact (proj2 (@ifo_kripke_weakly_forces_neg
          L W C O Hrel K X n0 phi r bv fv) Hall).
  - split.
    + intros [Hnphi Hnpsi] q Hqp Hor.
      pose proof (proj1 (@ifo_kripke_weakly_forces_or
        L W C O Hrel K X n0 q bv fv phi psi) Hor) as Hor'.
      destruct (Hor' q (preorder_refl O q))
        as [r [Hrq [Hphi | Hpsi]]].
      * pose proof (proj1 (@ifo_kripke_weakly_forces_neg
          L W C O Hrel K X n0 phi p bv fv) Hnphi) as Hnphi'.
        exact (Hnphi' r
          (@preorder_trans W O r q p Hrq Hqp) Hphi).
      * pose proof (proj1 (@ifo_kripke_weakly_forces_neg
          L W C O Hrel K X n0 psi p bv fv) Hnpsi) as Hnpsi'.
        exact (Hnpsi' r
          (@preorder_trans W O r q p Hrq Hqp) Hpsi).
    + intros Hnotor. split.
      * apply (proj2 (@ifo_kripke_weakly_forces_neg
          L W C O Hrel K X n0 phi p bv fv)).
        intros q Hqp Hphi. apply (Hnotor q Hqp).
        apply (proj2 (@ifo_kripke_weakly_forces_or
          L W C O Hrel K X n0 q bv fv phi psi)).
        intros r Hrq. exists r. split; [apply preorder_refl |].
        left. eapply ifo_kripke_weakly_forces_monotone; eauto.
      * apply (proj2 (@ifo_kripke_weakly_forces_neg
          L W C O Hrel K X n0 psi p bv fv)).
        intros q Hqp Hpsi. apply (Hnotor q Hqp).
        apply (proj2 (@ifo_kripke_weakly_forces_or
          L W C O Hrel K X n0 q bv fv phi psi)).
        intros r Hrq. exists r. split; [apply preorder_refl |].
        right. eapply ifo_kripke_weakly_forces_monotone; eauto.
  - split.
    + intros Hex q Hqp Hall.
      pose proof (proj1 (@ifo_kripke_weakly_forces_exs
        L W C O Hrel K X n0 p bv fv (semiformula_neg phi)) Hex)
        as Hex'.
      destruct (Hex' q Hqp) as [r [Hrq [x [Hx Hnbody]]]].
      pose proof (proj1 (@ifo_kripke_weakly_forces_neg
        L W C O Hrel K X (S n0) phi r (fin_cons x bv) fv)
        Hnbody) as Hnbody'.
      pose proof (proj1 (@ifo_kripke_weakly_forces_all
        L W C O Hrel K X n0 q bv fv phi) Hall) as Hall'.
      apply (Hnbody' r (preorder_refl O r)).
      exact (Hall' r Hrq x Hx).
    + intros Hnotall.
      apply (proj2 (@ifo_kripke_weakly_forces_exs
        L W C O Hrel K X n0 p bv fv (semiformula_neg phi))).
      intros q Hqp. apply NNPP. intro Hnone.
      apply (Hnotall q Hqp).
      apply (proj2 (@ifo_kripke_weakly_forces_all
        L W C O Hrel K X n0 q bv fv phi)).
      intros r Hrq x Hx. apply NNPP. intro Hnbody.
      destruct (proj1 (@ifo_kripke_weakly_forces_generic_iff_not
        L W C O Hrel K X (S n0) phi r (fin_cons x bv) fv) Hnbody)
        as [s [Hsr Hall]].
      apply Hnone. exists s. split.
      * exact (@preorder_trans W O s r q Hsr Hrq).
      * exists x. split.
        { exact (@ifo_kripke_domain_antimonotone
            L W C O K r s Hsr x Hx). }
        { exact (proj2 (@ifo_kripke_weakly_forces_neg
            L W C O Hrel K X (S n0) phi s (fin_cons x bv) fv)
            Hall). }
  - split.
    + intros Hallneg q Hqp Hex.
      pose proof (proj1 (@ifo_kripke_weakly_forces_all
        L W C O Hrel K X n0 p bv fv (semiformula_neg phi)) Hallneg)
        as Hallneg'.
      pose proof (proj1 (@ifo_kripke_weakly_forces_exs
        L W C O Hrel K X n0 q bv fv phi) Hex) as Hex'.
      destruct (Hex' q (preorder_refl O q))
        as [r [Hrq [x [Hx Hbody]]]].
      pose proof (Hallneg' r
        (@preorder_trans W O r q p Hrq Hqp) x Hx) as Hnbody.
      pose proof (proj1 (@ifo_kripke_weakly_forces_neg
        L W C O Hrel K X (S n0) phi r (fin_cons x bv) fv)
        Hnbody) as Hnbody'.
      exact (Hnbody' r (preorder_refl O r) Hbody).
    + intros Hnotex.
      apply (proj2 (@ifo_kripke_weakly_forces_all
        L W C O Hrel K X n0 p bv fv (semiformula_neg phi))).
      intros q Hqp x Hx.
      apply (proj2 (@ifo_kripke_weakly_forces_neg
        L W C O Hrel K X (S n0) phi q (fin_cons x bv) fv)).
      intros r Hrq Hbody. apply (Hnotex r
        (@preorder_trans W O r q p Hrq Hqp)).
      apply (proj2 (@ifo_kripke_weakly_forces_exs
        L W C O Hrel K X n0 r bv fv phi)).
      intros s Hsr. exists s. split; [apply preorder_refl |].
      exists x. split.
      * exact (@ifo_kripke_domain_antimonotone L W C O K q s
          (@preorder_trans W O s r q Hsr Hrq) x Hx).
      * eapply ifo_kripke_weakly_forces_monotone; eauto.
Defined.

Lemma ifo_kripke_weakly_forces_generic_iff_not_forces_neg :
  forall L W C O Hrel (K : ifo_kripke_model L W C O) X n
    (phi : semiformula L X n) p bv fv,
  ~ ifo_kripke_weakly_forces Hrel K p bv fv phi <->
  exists q, preorder_le O q p /\
    ifo_kripke_weakly_forces Hrel K q bv fv (semiformula_neg phi).
Proof.
  intros. split.
  - intro Hnot.
    destruct (proj1 (@ifo_kripke_weakly_forces_generic_iff_not
      L W C O Hrel K X n phi p bv fv) Hnot)
      as [q [Hqp Hall]].
    exists q. split; [exact Hqp |].
    exact (proj2 (@ifo_kripke_weakly_forces_neg
      L W C O Hrel K X n phi q bv fv) Hall).
  - intros [q [Hqp Hneg]] Hphi.
    pose proof (proj1 (@ifo_kripke_weakly_forces_neg
      L W C O Hrel K X n phi q bv fv) Hneg) as Hneg'.
    apply (Hneg' q (preorder_refl O q)).
    eapply ifo_kripke_weakly_forces_monotone; eauto.
Qed.

Lemma ifo_kripke_weakly_forces_imp : forall L W C O Hrel
    (K : ifo_kripke_model L W C O) X n p bv fv
    (phi psi : semiformula L X n),
  ifo_kripke_weakly_forces Hrel K p bv fv
      (semiformula_imp phi psi) <->
  forall q, preorder_le O q p ->
    ifo_kripke_weakly_forces Hrel K q bv fv phi ->
    ifo_kripke_weakly_forces Hrel K q bv fv psi.
Proof.
  intros. unfold semiformula_imp. split.
  - intros Himp q Hqp Hphi.
    apply (@ifo_kripke_weakly_forces_generic
      L W C O Hrel K X n psi q bv fv).
    intros r Hrq.
    pose proof (proj1 (@ifo_kripke_weakly_forces_or
      L W C O Hrel K X n p bv fv (semiformula_neg phi) psi)
      Himp) as Himp'.
    destruct (Himp' r (@preorder_trans W O r q p Hrq Hqp))
      as [s [Hsr [Hneg | Hpsi]]].
    + pose proof (proj1 (@ifo_kripke_weakly_forces_neg
        L W C O Hrel K X n phi s bv fv) Hneg) as Hneg'.
      exfalso. apply (Hneg' s (preorder_refl O s)).
      eapply ifo_kripke_weakly_forces_monotone; [exact Hphi |].
      exact (@preorder_trans W O s r q Hsr Hrq).
    + exists s. now split.
  - intros Himp.
    apply (proj2 (@ifo_kripke_weakly_forces_or
      L W C O Hrel K X n p bv fv (semiformula_neg phi) psi)).
    intros q Hqp.
    destruct (classic
      (ifo_kripke_weakly_forces Hrel K q bv fv phi)) as [Hphi | Hnphi].
    + exists q. split; [apply preorder_refl |].
      right. exact (Himp q Hqp Hphi).
    + destruct (proj1
        (@ifo_kripke_weakly_forces_generic_iff_not_forces_neg
          L W C O Hrel K X n phi q bv fv) Hnphi)
        as [r [Hrq Hneg]].
      exists r. split; [exact Hrq |]. now left.
Qed.

Lemma ifo_kripke_weakly_forces_iff : forall L W C O Hrel
    (K : ifo_kripke_model L W C O) X n p bv fv
    (phi psi : semiformula L X n),
  ifo_kripke_weakly_forces Hrel K p bv fv
      (semiformula_iff phi psi) <->
  forall q, preorder_le O q p ->
    (ifo_kripke_weakly_forces Hrel K q bv fv phi <->
     ifo_kripke_weakly_forces Hrel K q bv fv psi).
Proof.
  intros. unfold semiformula_iff.
  rewrite ifo_kripke_weakly_forces_and,
    ifo_kripke_weakly_forces_imp,
    ifo_kripke_weakly_forces_imp.
  split.
  - intros [Hforward Hbackward] q Hqp. split.
    + apply (Hforward q Hqp).
    + apply (Hbackward q Hqp).
  - intro Hall. split; intros q Hqp.
    + apply (proj1 (Hall q Hqp)).
    + apply (proj2 (Hall q Hqp)).
Qed.

Definition ifo_kripke_sentence_weakly_forces {L W C O}
    (Hrel : language_relational L)
    (K : ifo_kripke_model L W C O)
    (p : W) (phi : sentence L) : Prop :=
  ifo_kripke_weakly_forces Hrel K p ifo_empty_bound_env
    ifo_empty_free_env phi.

Definition ifo_kripke_sentence_weak_forcing_relation {L W C O}
    (Hrel : language_relational L)
    (K : ifo_kripke_model L W C O) :
    generic_weak_forcing_relation W (sentence L) :=
  @Build_generic_semantics W (sentence L)
    (ifo_kripke_sentence_weakly_forces Hrel K).

Lemma ifo_kripke_sentence_weakly_forces_iff_forces :
  forall L W C O Hrel (K : ifo_kripke_model L W C O) p
    (phi : sentence L),
  ifo_kripke_sentence_weakly_forces Hrel K p phi <->
  ifo_kripke_sentence_forces Hrel K p
    (ifo_double_negation_translation phi).
Proof. reflexivity. Qed.

Lemma ifo_kripke_sentence_weakly_forces_monotone :
  forall L W C O Hrel (K : ifo_kripke_model L W C O) p phi,
  ifo_kripke_sentence_weakly_forces Hrel K p phi -> forall q,
    preorder_le O q p ->
    ifo_kripke_sentence_weakly_forces Hrel K q phi.
Proof. intros. eapply ifo_kripke_weakly_forces_monotone; eauto. Qed.

Lemma ifo_kripke_sentence_weakly_forces_generic :
  forall L W C O Hrel (K : ifo_kripke_model L W C O) p phi,
  (forall q, preorder_le O q p -> exists r,
    preorder_le O r q /\
      ifo_kripke_sentence_weakly_forces Hrel K r phi) ->
  ifo_kripke_sentence_weakly_forces Hrel K p phi.
Proof. intros. eapply ifo_kripke_weakly_forces_generic; eauto. Qed.

Definition ifo_kripke_sentence_classical_kripke {L W C O}
    (Hrel : language_relational L)
    (K : ifo_kripke_model L W C O) :
  generic_classical_kripke (semiformula_connectives L Empty_set 0)
    (ifo_kripke_sentence_weak_forcing_relation Hrel K)
    (fun p q => preorder_le O q p).
Proof.
  constructor.
  - constructor.
    + constructor. intro p. apply ifo_kripke_weakly_forces_verum.
    + constructor. intro p. apply ifo_kripke_weakly_forces_falsum.
    + constructor. intros p phi psi. apply ifo_kripke_weakly_forces_and.
  - intros p phi psi. apply ifo_kripke_weakly_forces_or.
  - constructor. intros p phi. apply ifo_kripke_weakly_forces_neg.
  - constructor. intros p phi psi. apply ifo_kripke_weakly_forces_imp.
  - constructor. intros p phi Hp q Hqp.
    change (ifo_kripke_sentence_weakly_forces Hrel K p phi) in Hp.
    change (ifo_kripke_sentence_weakly_forces Hrel K q phi).
    exact (@ifo_kripke_sentence_weakly_forces_monotone
      L W C O Hrel K p phi Hp q Hqp).
  - intros p phi Hdense.
    change (ifo_kripke_sentence_weakly_forces Hrel K p phi).
    apply (@ifo_kripke_sentence_weakly_forces_generic
      L W C O Hrel K p phi).
    exact Hdense.
Defined.

(** Classical LK soundness follows by composing the Gödel--Gentzen proof
    translation with intuitionistic Kripke soundness. *)
Theorem ifo_kripke_weakly_forces_lk_sound : forall L W C O Hrel
    (K : ifo_kripke_model L W C O) (D : language_decidable_eq L)
    (phi : proposition L),
  first_order_lk_provable phi -> forall p (fv : nat -> C),
    (forall i, ifo_kripke_domain K p (fv i)) ->
    ifo_kripke_weakly_forces Hrel K p ifo_empty_bound_env fv phi.
Proof.
  intros L W C O Hrel K D phi Hphi p fv Hfv.
  destruct (@ifo_goedel_gentzen_provable
    L D (ifo_hilbert_intuitionistic L) phi Hphi) as [d].
  unfold ifo_kripke_weakly_forces.
  exact (@ifo_kripke_intuitionistic_sound
    L W C O Hrel K (ifo_double_negation_translation phi) d p fv Hfv).
Qed.

Theorem ifo_kripke_sentence_weakly_forces_lk_sound :
  forall L W C O Hrel (K : ifo_kripke_model L W C O)
    (D : language_decidable_eq L) (sigma : sentence L),
  first_order_lk_provable (first_order_sentence_embed sigma) ->
  forall p, ifo_kripke_sentence_weakly_forces Hrel K p sigma.
Proof.
  intros L W C O Hrel K D sigma Hsigma p.
  destruct (ifo_kripke_domain_nonempty K p) as [x Hx].
  pose proof (@ifo_kripke_weakly_forces_lk_sound
    L W C O Hrel K D (first_order_sentence_embed sigma) Hsigma p
    (fun _ : nat => x) (fun _ => Hx)) as Hsound.
  unfold first_order_sentence_embed in Hsound.
  apply (proj1 (@ifo_kripke_weakly_forces_emb
    L W C O Hrel K Empty_set nat 0 ifo_empty_elim p
    ifo_empty_bound_env (fun _ : nat => x) sigma)) in Hsound.
  assert ((fun y : Empty_set => False_rect C (ifo_empty_elim y)) =
    @ifo_empty_free_env C) as Hempty.
  { apply functional_extensionality. intro y. destruct y. }
  exact (eq_rect _ (fun e =>
    ifo_kripke_weakly_forces Hrel K p ifo_empty_bound_env e sigma)
    Hsound _ Hempty).
Qed.

(** * Positive derivations used by the canonical completeness preorder *)

Inductive first_order_positive_derivation_from {L}
    (Xi : first_order_sequent L) : first_order_sequent L -> Type :=
| FOPDOr : forall (phi psi : proposition L) Gamma,
    first_order_positive_derivation_from Xi (phi :: psi :: Gamma) ->
    first_order_positive_derivation_from Xi
      (Semiformula_or phi psi :: Gamma)
| FOPDExs : forall (phi : semiproposition L 1)
    (t : syntactic_term L) Gamma,
    first_order_positive_derivation_from Xi
      (semiformula_substitute (fun _ : Fin.t 1 => t) phi :: Gamma) ->
    first_order_positive_derivation_from Xi
      (Semiformula_exists phi :: Gamma)
| FOPDWeak : forall Delta Gamma,
    first_order_positive_derivation_from Xi Delta ->
    generic_list_subset Delta Gamma ->
    first_order_positive_derivation_from Xi Gamma
| FOPDId : first_order_positive_derivation_from Xi Xi.

Arguments FOPDOr {L Xi phi psi Gamma} _.
Arguments FOPDExs {L Xi phi t Gamma} _.
Arguments FOPDWeak {L Xi Delta Gamma} _ _.
Arguments FOPDId {L Xi}.

Definition first_order_positive_derivation_of_subset {L Xi Gamma}
    (Hsub : generic_list_subset Xi Gamma) :
    @first_order_positive_derivation_from L Xi Gamma :=
  FOPDWeak FOPDId Hsub.

Fixpoint first_order_positive_derivation_trans {L Xi Gamma Delta}
    (b : @first_order_positive_derivation_from L Xi Gamma)
    (d : @first_order_positive_derivation_from L Gamma Delta) :
    @first_order_positive_derivation_from L Xi Delta.
Proof.
  destruct d as [phi psi Theta d | phi t Theta d |
    Theta Lambda d Hsub |].
  - exact (FOPDOr (@first_order_positive_derivation_trans
      L Xi Gamma (phi :: psi :: Theta) b d)).
  - exact (FOPDExs (@first_order_positive_derivation_trans
      L Xi Gamma
      (semiformula_substitute (fun _ : Fin.t 1 => t) phi :: Theta)
      b d)).
  - exact (FOPDWeak (@first_order_positive_derivation_trans
      L Xi Gamma Theta b d) Hsub).
  - exact b.
Defined.

Fixpoint first_order_positive_derivation_cons {L Xi Gamma}
    (a : proposition L)
    (d : @first_order_positive_derivation_from L Xi Gamma) :
    @first_order_positive_derivation_from L (a :: Xi) (a :: Gamma).
Proof.
  destruct d as [phi psi Theta d | phi t Theta d |
    Theta Lambda d Hsub |].
  - pose (dcons := @first_order_positive_derivation_cons
      L Xi (phi :: psi :: Theta) a d).
    assert (Hprem : generic_list_subset
      (a :: phi :: psi :: Theta) (phi :: psi :: a :: Theta)).
    { intros x [Hx | [Hx | [Hx | Hx]]].
      - subst x. right. right. now left.
      - subst x. now left.
      - subst x. right. now left.
      - right. right. now right. }
    pose (dor := FOPDOr (FOPDWeak dcons Hprem)).
    apply (FOPDWeak dor). intros x [Hx | [Hx | Hx]].
    + subst x. right. now left.
    + subst x. now left.
    + right. now right.
  - pose (dcons := @first_order_positive_derivation_cons
      L Xi
      (semiformula_substitute (fun _ : Fin.t 1 => t) phi :: Theta) a d).
    set (instance := semiformula_substitute
      (fun _ : Fin.t 1 => t) phi).
    assert (Hprem : generic_list_subset
      (a :: instance :: Theta) (instance :: a :: Theta)).
    { intros x [Hx | [Hx | Hx]].
      - subst x. right. now left.
      - subst x. now left.
      - right. now right. }
    pose (dexs := @FOPDExs L (a :: Xi) phi t (a :: Theta)
      (FOPDWeak dcons Hprem)).
    apply (FOPDWeak dexs). intros x [Hx | [Hx | Hx]].
    + subst x. right. now left.
    + subst x. now left.
    + right. now right.
  - apply (FOPDWeak (@first_order_positive_derivation_cons
      L Xi Theta a d)).
    intros x [Hx | Hx].
    + subst x. now left.
    + right. exact (Hsub x Hx).
  - exact FOPDId.
Defined.

Fixpoint first_order_positive_derivation_append {L Xi Gamma}
    (Delta : first_order_sequent L)
    (d : @first_order_positive_derivation_from L Xi Gamma) :
    @first_order_positive_derivation_from L (Delta ++ Xi) (Delta ++ Gamma) :=
  match Delta with
  | [] => d
  | a :: rest =>
      first_order_positive_derivation_cons a
        (first_order_positive_derivation_append rest d)
  end.

Fixpoint first_order_positive_derivation_add {L Gamma Delta Xi Theta}
    (b : @first_order_positive_derivation_from L Gamma Delta)
    (d : @first_order_positive_derivation_from L Xi Theta) :
    @first_order_positive_derivation_from L (Gamma ++ Xi) (Delta ++ Theta).
Proof.
  destruct b as [phi psi Lambda b | phi t Lambda b |
    Lambda Omega b Hsub |].
  - exact (FOPDOr (@first_order_positive_derivation_add
      L Gamma (phi :: psi :: Lambda) Xi Theta b d)).
  - exact (FOPDExs (@first_order_positive_derivation_add
      L Gamma
      (semiformula_substitute (fun _ : Fin.t 1 => t) phi :: Lambda)
      Xi Theta b d)).
  - apply (FOPDWeak (@first_order_positive_derivation_add
      L Gamma Lambda Xi Theta b d)).
    intros x Hx.
    apply (proj1 (@generic_list_member_app_iff _ x Lambda Theta)) in Hx.
    apply (proj2 (@generic_list_member_app_iff _ x Omega Theta)).
    destruct Hx as [Hx | Hx].
    + left. exact (Hsub x Hx).
    + now right.
  - exact (first_order_positive_derivation_append Gamma d).
Defined.

Fixpoint first_order_positive_derivation_graft {L Xi Gamma}
    (b : first_order_derivation L Xi)
    (d : @first_order_positive_derivation_from L Xi Gamma) :
    first_order_derivation L Gamma.
Proof.
  destruct d as [phi psi Theta d | phi t Theta d |
    Theta Lambda d Hsub |].
  - exact (FODOr (@first_order_positive_derivation_graft
      L Xi (phi :: psi :: Theta) b d)).
  - exact (FODExists (@first_order_positive_derivation_graft
      L Xi
      (semiformula_substitute (fun _ : Fin.t 1 => t) phi :: Theta)
      b d)).
  - exact (FODContraction
      (@first_order_positive_derivation_graft L Xi Theta b d) Hsub).
  - exact b.
Defined.

Definition first_order_consistent_sequent (L : language) : Type :=
  { Gamma : first_order_sequent L |
    first_order_derivation L (map semiformula_neg Gamma) -> False }.

Definition first_order_consistent_sequent_order (L : language) :
    preorder_data (first_order_consistent_sequent L).
Proof.
  refine {| preorder_le := fun Gamma Delta =>
      inhabited (@first_order_positive_derivation_from L
        (map semiformula_neg (proj1_sig Delta))
        (map semiformula_neg (proj1_sig Gamma))) |}.
  - intro Gamma. constructor. exact FOPDId.
  - intros Gamma Delta Xi [bDelta] [bXi]. constructor.
    exact (first_order_positive_derivation_trans bXi bDelta).
Defined.
