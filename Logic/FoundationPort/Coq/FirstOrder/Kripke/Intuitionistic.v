(** Intuitionistic first-order Kripke forcing. *)

From Stdlib Require Import Logic.FunctionalExtensionality Lists.List
  Program.Equality Vectors.Fin.
From FoundationModal Require Import GenericForcingRelation GenericSemantics
  PropositionalEntailmentMinimal.
From Foundation.Vorspiel.Order Require Import Dense.
From Foundation.Syntax.Predicate Require Import Language Term Relational Rew.
From Foundation.FirstOrder.Intuitionistic Require Import Formula Rew Deduction.
From Foundation.FirstOrder.Kripke Require Import Basic.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Fixpoint ifo_kripke_forces_aux {L W C O}
    (Hrel : language_relational L)
    (K : ifo_kripke_model L W C O)
    {X n} (phi : ifo_semiformula L X n) :
    forall (w : W), (Fin.t n -> C) -> (X -> C) -> Prop :=
  match phi in ifo_semiformula _ _ n0 return
      forall (w : W), (Fin.t n0 -> C) -> (X -> C) -> Prop with
  | IFOFalsum => fun _ _ _ => False
  | IFORel R t => fun w bv fv =>
      ifo_kripke_rel K w R
        (fun i => semiterm_relational_val Hrel bv fv (t i))
  | IFOAnd psi chi => fun w bv fv =>
      ifo_kripke_forces_aux Hrel K psi w bv fv /\
      ifo_kripke_forces_aux Hrel K chi w bv fv
  | IFOOr psi chi => fun w bv fv =>
      ifo_kripke_forces_aux Hrel K psi w bv fv \/
      ifo_kripke_forces_aux Hrel K chi w bv fv
  | IFOImp psi chi => fun w bv fv =>
      forall v, preorder_le O v w ->
        ifo_kripke_forces_aux Hrel K psi v bv fv ->
        ifo_kripke_forces_aux Hrel K chi v bv fv
  | IFOAll psi => fun w bv fv =>
      forall v, preorder_le O v w -> forall x,
        ifo_kripke_domain K v x ->
        ifo_kripke_forces_aux Hrel K psi v (fin_cons x bv) fv
  | IFOExs psi => fun w bv fv =>
      exists x, ifo_kripke_domain K w x /\
        ifo_kripke_forces_aux Hrel K psi w (fin_cons x bv) fv
  end.

Definition ifo_kripke_forces {L W C O}
    (Hrel : language_relational L)
    (K : ifo_kripke_model L W C O)
    {X n} (w : W) (bv : Fin.t n -> C) (fv : X -> C)
    (phi : ifo_semiformula L X n) : Prop :=
  ifo_kripke_forces_aux Hrel K phi w bv fv.

Lemma ifo_kripke_forces_falsum : forall L W C O Hrel K X n w bv fv,
  ~ @ifo_kripke_forces L W C O Hrel K X n w bv fv IFOFalsum.
Proof. intros L W C O Hrel K X n w bv fv H. exact H. Qed.

Lemma ifo_kripke_forces_rel : forall L W C O Hrel K X n w bv fv
    k (R : language_rel L k) t,
  @ifo_kripke_forces L W C O Hrel K X n w bv fv (IFORel R t) <->
  ifo_kripke_rel K w R
    (fun i => semiterm_relational_val Hrel bv fv (t i)).
Proof. reflexivity. Qed.

Lemma ifo_kripke_forces_and : forall L W C (O : preorder_data W)
    (Hrel : language_relational L) (K : ifo_kripke_model L W C O)
    X n w bv fv
    (phi psi : ifo_semiformula L X n),
  ifo_kripke_forces Hrel K w bv fv (IFOAnd phi psi) <->
  ifo_kripke_forces Hrel K w bv fv phi /\
  ifo_kripke_forces Hrel K w bv fv psi.
Proof. reflexivity. Qed.

Lemma ifo_kripke_forces_or : forall L W C (O : preorder_data W)
    (Hrel : language_relational L) (K : ifo_kripke_model L W C O)
    X n w bv fv
    (phi psi : ifo_semiformula L X n),
  ifo_kripke_forces Hrel K w bv fv (IFOOr phi psi) <->
  ifo_kripke_forces Hrel K w bv fv phi \/
  ifo_kripke_forces Hrel K w bv fv psi.
Proof. reflexivity. Qed.

Lemma ifo_kripke_forces_imp : forall L W C (O : preorder_data W)
    (Hrel : language_relational L) (K : ifo_kripke_model L W C O)
    X n w bv fv
    (phi psi : ifo_semiformula L X n),
  ifo_kripke_forces Hrel K w bv fv (IFOImp phi psi) <->
  forall v, preorder_le O v w ->
    ifo_kripke_forces Hrel K v bv fv phi ->
    ifo_kripke_forces Hrel K v bv fv psi.
Proof. reflexivity. Qed.

Lemma ifo_kripke_forces_neg : forall L W C (O : preorder_data W)
    (Hrel : language_relational L) (K : ifo_kripke_model L W C O)
    X n w bv fv
    (phi : ifo_semiformula L X n),
  ifo_kripke_forces Hrel K w bv fv (ifo_neg phi) <->
  forall v, preorder_le O v w ->
    ~ ifo_kripke_forces Hrel K v bv fv phi.
Proof. reflexivity. Qed.

Lemma ifo_kripke_forces_verum : forall L W C (O : preorder_data W)
    (Hrel : language_relational L) (K : ifo_kripke_model L W C O)
    X n w bv fv,
  @ifo_kripke_forces L W C O Hrel K X n w bv fv ifo_verum.
Proof. intros L W C O Hrel K X n w bv fv v Hvw Hfalse. exact Hfalse. Qed.

Lemma ifo_kripke_forces_all : forall L W C (O : preorder_data W)
    (Hrel : language_relational L) (K : ifo_kripke_model L W C O)
    X n w bv fv
    (phi : ifo_semiformula L X (S n)),
  ifo_kripke_forces Hrel K w bv fv (IFOAll phi) <->
  forall v, preorder_le O v w -> forall x,
    ifo_kripke_domain K v x ->
    ifo_kripke_forces Hrel K v (fin_cons x bv) fv phi.
Proof. reflexivity. Qed.

Lemma ifo_kripke_forces_exs : forall L W C (O : preorder_data W)
    (Hrel : language_relational L) (K : ifo_kripke_model L W C O)
    X n w bv fv
    (phi : ifo_semiformula L X (S n)),
  ifo_kripke_forces Hrel K w bv fv (IFOExs phi) <->
  exists x, ifo_kripke_domain K w x /\
    ifo_kripke_forces Hrel K w (fin_cons x bv) fv phi.
Proof. reflexivity. Qed.

Lemma ifo_kripke_forces_iff : forall L W C (O : preorder_data W)
    (Hrel : language_relational L) (K : ifo_kripke_model L W C O)
    X n w bv fv (phi psi : ifo_semiformula L X n),
  ifo_kripke_forces Hrel K w bv fv
    (IFOAnd (IFOImp phi psi) (IFOImp psi phi)) <->
  forall v, preorder_le O v w ->
    (ifo_kripke_forces Hrel K v bv fv phi <->
     ifo_kripke_forces Hrel K v bv fv psi).
Proof.
  intros. split.
  - intros [Hforward Hbackward] v Hvw. split.
    + apply (Hforward v Hvw).
    + apply (Hbackward v Hvw).
  - intro Hall. split; intros v Hvw.
    + apply (proj1 (Hall v Hvw)).
    + apply (proj2 (Hall v Hvw)).
Qed.

Fixpoint ifo_kripke_list_conj {L X n}
    (Gamma : list (ifo_semiformula L X n)) : ifo_semiformula L X n :=
  match Gamma with
  | [] => ifo_verum
  | phi :: [] => phi
  | phi :: rest => IFOAnd phi (ifo_kripke_list_conj rest)
  end.

Fixpoint ifo_kripke_list_disj {L X n}
    (Gamma : list (ifo_semiformula L X n)) : ifo_semiformula L X n :=
  match Gamma with
  | [] => IFOFalsum
  | phi :: [] => phi
  | phi :: rest => IFOOr phi (ifo_kripke_list_disj rest)
  end.

Lemma ifo_kripke_forces_list_conj : forall L W C O Hrel
    (K : ifo_kripke_model L W C O) X n w bv fv
    (Gamma : list (ifo_semiformula L X n)),
  ifo_kripke_forces Hrel K w bv fv (ifo_kripke_list_conj Gamma) <->
  forall phi, In phi Gamma -> ifo_kripke_forces Hrel K w bv fv phi.
Proof.
  intros L W C O Hrel K X n w bv fv Gamma.
  induction Gamma as [|phi Gamma IH].
  - simpl. split; [intros _ psi H; contradiction |].
    intros _. exact
      (@ifo_kripke_forces_verum L W C O Hrel K X n w bv fv).
  - destruct Gamma as [|psi Gamma].
    + simpl. split.
      * intros H chi [Hchi | Hchi]; [now subst chi | contradiction].
      * intros H. apply H. now left.
    + change
        ((ifo_kripke_forces Hrel K w bv fv phi /\
          ifo_kripke_forces Hrel K w bv fv
            (ifo_kripke_list_conj (psi :: Gamma))) <->
         forall chi, In chi (phi :: psi :: Gamma) ->
           ifo_kripke_forces Hrel K w bv fv chi).
      rewrite IH. split.
      * intros [Hphi Htail] chi [Hchi | Hchi].
        { now subst chi. }
        { now apply Htail. }
      * intro Hall. split.
        { apply Hall. now left. }
        { intros chi Hchi. apply Hall. now right. }
Qed.

Lemma ifo_kripke_forces_list_disj : forall L W C O Hrel
    (K : ifo_kripke_model L W C O) X n w bv fv
    (Gamma : list (ifo_semiformula L X n)),
  ifo_kripke_forces Hrel K w bv fv (ifo_kripke_list_disj Gamma) <->
  exists phi, In phi Gamma /\ ifo_kripke_forces Hrel K w bv fv phi.
Proof.
  intros L W C O Hrel K X n w bv fv Gamma.
  induction Gamma as [|phi Gamma IH].
  - simpl. split; [contradiction | intros [psi [H _]]; contradiction].
  - destruct Gamma as [|psi Gamma].
    + simpl. split.
      * intro H. exists phi. split; [now left | exact H].
      * intros [chi [[Hchi | Hchi] H]]; [now subst chi | contradiction].
    + change
        ((ifo_kripke_forces Hrel K w bv fv phi \/
          ifo_kripke_forces Hrel K w bv fv
            (ifo_kripke_list_disj (psi :: Gamma))) <->
         exists chi, In chi (phi :: psi :: Gamma) /\
           ifo_kripke_forces Hrel K w bv fv chi).
      rewrite IH. split.
      * intros [Hphi | [chi [Hchi Hforce]]].
        { exists phi. split; [now left | exact Hphi]. }
        { exists chi. split; [now right | exact Hforce]. }
      * intros [chi [[Hchi | Hchi] Hforce]].
        { left. now subst chi. }
        { right. exists chi. now split. }
Qed.

Lemma ifo_relational_val_rew_q_bound : forall L C Hrel X n Y m
    (rw : rew L X n Y m) (x : C)
    (bv : Fin.t m -> C) (fv : Y -> C),
  (fun i => semiterm_relational_val Hrel (fin_cons x bv) fv
      (rew_apply (rew_q rw) (Semiterm_bvar i))) =
  fin_cons x
    (fun i => semiterm_relational_val Hrel bv fv
      (rew_apply rw (Semiterm_bvar i))).
Proof.
  intros. apply functional_extensionality. intro i.
  refine (@Fin.caseS' _ i (fun j =>
    semiterm_relational_val Hrel (fin_cons x bv) fv
      (rew_apply (rew_q rw) (Semiterm_bvar j)) =
    fin_cons x
      (fun u => semiterm_relational_val Hrel bv fv
        (rew_apply rw (Semiterm_bvar u))) j) _ _).
  - rewrite rew_q_bvar_zero. reflexivity.
  - intro j. rewrite rew_q_bvar_succ.
    apply semiterm_relational_val_bshift.
Qed.

Lemma ifo_relational_val_rew_q_free : forall L C Hrel X n Y m
    (rw : rew L X n Y m) (x : C)
    (bv : Fin.t m -> C) (fv : Y -> C) y,
  semiterm_relational_val Hrel (fin_cons x bv) fv
    (rew_apply (rew_q rw) (Semiterm_fvar y)) =
  semiterm_relational_val Hrel bv fv
    (rew_apply rw (Semiterm_fvar y)).
Proof.
  intros. rewrite rew_q_fvar.
  apply semiterm_relational_val_bshift.
Qed.

Lemma ifo_relational_val_rew_q_frees : forall L C Hrel X n Y m
    (rw : rew L X n Y m) (x : C)
    (bv : Fin.t m -> C) (fv : Y -> C),
  (fun y => semiterm_relational_val Hrel (fin_cons x bv) fv
    (rew_apply (rew_q rw) (Semiterm_fvar y))) =
  (fun y => semiterm_relational_val Hrel bv fv
    (rew_apply rw (Semiterm_fvar y))).
Proof.
  intros. apply functional_extensionality. intro y.
  apply ifo_relational_val_rew_q_free.
Qed.

Theorem ifo_kripke_forces_rewrite : forall L W C O Hrel
    (K : ifo_kripke_model L W C O) X n Y m
    (rw : rew L X n Y m) (phi : ifo_semiformula L X n)
    w (bv : Fin.t m -> C) (fv : Y -> C),
  ifo_kripke_forces Hrel K w bv fv (ifo_rewrite rw phi) <->
  ifo_kripke_forces Hrel K w
    (fun i => semiterm_relational_val Hrel bv fv
      (rew_apply rw (Semiterm_bvar i)))
    (fun x => semiterm_relational_val Hrel bv fv
      (rew_apply rw (Semiterm_fvar x))) phi.
Proof.
  intros L W C O Hrel K X n Y m rw phi.
  revert Y m rw.
  induction phi as [n0 | n0 k R args |
    n0 phi1 IHphi1 phi2 IHphi2 |
    n0 phi1 IHphi1 phi2 IHphi2 |
    n0 phi1 IHphi1 phi2 IHphi2 |
    n0 phi IHphi | n0 phi IHphi];
    intros Y m rw w bv fv; simpl.
  - reflexivity.
  - assert ((fun i => semiterm_relational_val Hrel bv fv
        (rew_apply rw (args i))) =
      (fun i => semiterm_relational_val Hrel
        (fun j => semiterm_relational_val Hrel bv fv
          (rew_apply rw (Semiterm_bvar j)))
        (fun x => semiterm_relational_val Hrel bv fv
          (rew_apply rw (Semiterm_fvar x))) (args i))) as ->.
    { apply functional_extensionality. intro i.
      apply semiterm_relational_val_rew. }
    reflexivity.
  - now rewrite (IHphi1 Y m rw), (IHphi2 Y m rw).
  - now rewrite (IHphi1 Y m rw), (IHphi2 Y m rw).
  - split; intros Hall v Hvw Hv.
    + apply (proj1 (IHphi2 Y m rw v bv fv)).
      apply Hall; [exact Hvw |].
      apply (proj2 (IHphi1 Y m rw v bv fv)). exact Hv.
    + apply (proj2 (IHphi2 Y m rw v bv fv)).
      apply Hall; [exact Hvw |].
      apply (proj1 (IHphi1 Y m rw v bv fv)). exact Hv.
  - split; intros Hall v Hvw x Hx.
    + pose proof (Hall v Hvw x Hx) as Hbody.
      apply (proj1 (IHphi Y (S m) (rew_q rw) v (fin_cons x bv) fv))
        in Hbody.
      rewrite (ifo_relational_val_rew_q_bound Hrel rw x bv fv),
        (ifo_relational_val_rew_q_frees Hrel rw x bv fv) in Hbody.
      exact Hbody.
    + rewrite (IHphi Y (S m) (rew_q rw) v (fin_cons x bv) fv).
      rewrite (ifo_relational_val_rew_q_bound Hrel rw x bv fv),
        (ifo_relational_val_rew_q_frees Hrel rw x bv fv).
      exact (Hall v Hvw x Hx).
  - split.
    + intros [x [Hx Hbody]]. exists x. split; [exact Hx |].
      apply (proj1 (IHphi Y (S m) (rew_q rw) w (fin_cons x bv) fv))
        in Hbody.
      rewrite (ifo_relational_val_rew_q_bound Hrel rw x bv fv),
        (ifo_relational_val_rew_q_frees Hrel rw x bv fv) in Hbody.
      exact Hbody.
    + intros [x [Hx Hbody]]. exists x. split; [exact Hx |].
      apply (proj2 (IHphi Y (S m) (rew_q rw) w (fin_cons x bv) fv)).
      rewrite (ifo_relational_val_rew_q_bound Hrel rw x bv fv),
        (ifo_relational_val_rew_q_frees Hrel rw x bv fv).
      exact Hbody.
Qed.

(** Add a distinguished value at free-variable index zero. *)
Definition ifo_nat_env_cons {C} (x : C) (fv : nat -> C) (i : nat) : C :=
  match i with
  | 0 => x
  | S j => fv j
  end.

(** Append a value at the final bound-variable index. *)
Definition ifo_fin_env_snoc {C n} (bv : Fin.t n -> C) (x : C)
    (i : Fin.t (n + 1)) : C :=
  @Fin.case_L_R' n 1 (fun _ => C) i bv (fun _ => x).

Lemma ifo_fin_env_snoc_left : forall C n (bv : Fin.t n -> C) x
    (i : Fin.t n),
  ifo_fin_env_snoc bv x (Fin.L 1 i) = bv i.
Proof.
  intros. unfold ifo_fin_env_snoc. now rewrite Fin.case_L_R'_L.
Qed.

Lemma ifo_fin_env_snoc_last : forall C n (bv : Fin.t n -> C) x,
  ifo_fin_env_snoc bv x (Fin.R n Fin.F1) = x.
Proof.
  intros. unfold ifo_fin_env_snoc. now rewrite Fin.case_L_R'_R.
Qed.

Lemma ifo_relational_val_rew_free_bound : forall L C Hrel n
    (bv : Fin.t n -> C) (fv : nat -> C) x,
  (fun i => semiterm_relational_val Hrel bv (ifo_nat_env_cons x fv)
    (rew_apply rew_free (@Semiterm_bvar L nat (n + 1) i))) =
  ifo_fin_env_snoc bv x.
Proof.
  intros. apply functional_extensionality. intro i.
  refine (@Fin.case_L_R' n 1 (fun j =>
    semiterm_relational_val Hrel bv (ifo_nat_env_cons x fv)
      (rew_apply rew_free (@Semiterm_bvar L nat (n + 1) j)) =
    ifo_fin_env_snoc bv x j) i _ _).
  - intro j. rewrite rew_free_bvar_old, ifo_fin_env_snoc_left.
    reflexivity.
  - intro j. assert (Hj : j = Fin.F1) by apply fin_one_eq_f1.
    subst j. rewrite rew_free_bvar_last, ifo_fin_env_snoc_last.
    reflexivity.
Qed.

Lemma ifo_relational_val_rew_free_free : forall L C Hrel n
    (bv : Fin.t n -> C) (fv : nat -> C) x,
  (fun i => semiterm_relational_val Hrel bv (ifo_nat_env_cons x fv)
    (rew_apply rew_free (@Semiterm_fvar L nat (n + 1) i))) = fv.
Proof.
  intros. apply functional_extensionality. intro i.
  rewrite rew_free_fvar. reflexivity.
Qed.

(** Freeing a final bound variable commutes with forcing.  This generalized
    arity form subsumes the proposition-level law needed by generalization. *)
Lemma ifo_kripke_forces_free : forall L W C O Hrel
    (K : ifo_kripke_model L W C O) n w
    (bv : Fin.t n -> C) (fv : nat -> C) x
    (phi : ifo_semiproposition L (n + 1)),
  ifo_kripke_forces Hrel K w bv (ifo_nat_env_cons x fv)
      (ifo_free phi) <->
  ifo_kripke_forces Hrel K w (ifo_fin_env_snoc bv x) fv phi.
Proof.
  intros. unfold ifo_free. rewrite ifo_kripke_forces_rewrite.
  rewrite ifo_relational_val_rew_free_bound,
    ifo_relational_val_rew_free_free. reflexivity.
Qed.

Lemma ifo_kripke_forces_substitute : forall L W C O Hrel
    (K : ifo_kripke_model L W C O) X n m w
    (bv : Fin.t m -> C) (fv : X -> C)
    (terms : Fin.t n -> semiterm L X m)
    (phi : ifo_semiformula L X n),
  ifo_kripke_forces Hrel K w bv fv (ifo_substitute terms phi) <->
  ifo_kripke_forces Hrel K w
    (fun i => semiterm_relational_val Hrel bv fv (terms i)) fv phi.
Proof.
  intros. unfold ifo_substitute. rewrite ifo_kripke_forces_rewrite.
  assert ((fun i => semiterm_relational_val Hrel bv fv
      (rew_apply (rew_subst terms) (Semiterm_bvar i))) =
    (fun i => semiterm_relational_val Hrel bv fv (terms i))) as ->.
  { apply functional_extensionality. intro i. now rewrite rew_subst_bvar. }
  assert ((fun x => semiterm_relational_val Hrel bv fv
      (rew_apply (rew_subst terms) (Semiterm_fvar x))) = fv) as ->.
  { apply functional_extensionality. intro x. now rewrite rew_subst_fvar. }
  reflexivity.
Qed.

Lemma ifo_kripke_forces_emb : forall L W C O Hrel
    (K : ifo_kripke_model L W C O) X Y n
    (empty : X -> False) w (bv : Fin.t n -> C) (fv : Y -> C)
    (phi : ifo_semiformula L X n),
  ifo_kripke_forces Hrel K w bv fv (ifo_emb empty phi) <->
  ifo_kripke_forces Hrel K w bv
    (fun x => False_rect C (empty x)) phi.
Proof.
  intros. unfold ifo_emb. rewrite ifo_kripke_forces_rewrite.
  assert ((fun i => semiterm_relational_val Hrel bv fv
      (rew_apply (rew_emb empty) (Semiterm_bvar i))) = bv) as ->.
  { apply functional_extensionality. intro i. reflexivity. }
  assert ((fun x => semiterm_relational_val Hrel bv fv
      (rew_apply (rew_emb empty) (Semiterm_fvar x))) =
    (fun x => False_rect C (empty x))) as ->.
  { apply functional_extensionality. intro x. destruct (empty x). }
  reflexivity.
Qed.

Lemma ifo_kripke_forces_bshift : forall L W C O Hrel
    (K : ifo_kripke_model L W C O) X n w x
    (bv : Fin.t n -> C) (fv : X -> C)
    (phi : ifo_semiformula L X n),
  ifo_kripke_forces Hrel K w (fin_cons x bv) fv
      (ifo_bshift phi) <->
  ifo_kripke_forces Hrel K w bv fv phi.
Proof.
  intros. unfold ifo_bshift. rewrite ifo_kripke_forces_rewrite.
  assert ((fun i => semiterm_relational_val Hrel (fin_cons x bv) fv
      (rew_apply rew_bshift (Semiterm_bvar i))) = bv) as ->.
  { apply functional_extensionality. intro i.
    apply semiterm_relational_val_bshift. }
  assert ((fun y => semiterm_relational_val Hrel (fin_cons x bv) fv
      (rew_apply rew_bshift (Semiterm_fvar y))) = fv) as ->.
  { apply functional_extensionality. intro y.
    apply semiterm_relational_val_bshift. }
  reflexivity.
Qed.

Definition ifo_empty_bound_env {C} : Fin.t 0 -> C :=
  fun i => Fin.case0 (fun _ => C) i.

Lemma ifo_fin_env_snoc_empty : forall C
    (bv : Fin.t 0 -> C) x,
  ifo_fin_env_snoc bv x = fin_cons x bv.
Proof.
  intros. apply functional_extensionality. intro i.
  assert (Hi : i = Fin.F1) by apply fin_one_eq_f1.
  subst i. rewrite ifo_fin_env_snoc_last. reflexivity.
Qed.

Lemma ifo_fin_one_constant_eq_cons : forall C x (bv : Fin.t 0 -> C),
  (fun _ : Fin.t 1 => x) = fin_cons x bv.
Proof.
  intros. apply functional_extensionality. intro i.
  assert (Hi : i = Fin.F1) by apply fin_one_eq_f1.
  now subst i.
Qed.

Theorem ifo_kripke_forces_monotone : forall L W C O Hrel
    (K : ifo_kripke_model L W C O) X n
    (phi : ifo_semiformula L X n) w bv fv,
  ifo_kripke_forces Hrel K w bv fv phi -> forall v,
    preorder_le O v w -> ifo_kripke_forces Hrel K v bv fv phi.
Proof.
  intros L W C O Hrel K X n phi. induction phi;
    intros w bv fv Hforce v Hvw; simpl in *.
  - exact Hforce.
  - eapply ifo_kripke_rel_monotone; eauto.
  - destruct Hforce as [Hleft Hright]. split.
    + exact (IHphi1 w bv fv Hleft v Hvw).
    + exact (IHphi2 w bv fv Hright v Hvw).
  - destruct Hforce as [Hforce | Hforce].
    + left. eapply IHphi1; eauto.
    + right. eapply IHphi2; eauto.
  - intros u Huv Hu. apply (Hforce u).
    + exact (@preorder_trans W O u v w Huv Hvw).
    + exact Hu.
  - intros u Huv x Hx. apply (Hforce u).
    + exact (@preorder_trans W O u v w Huv Hvw).
    + exact Hx.
  - destruct Hforce as [x [Hx Hbody]]. exists x. split.
    + exact (@ifo_kripke_domain_antimonotone
        L W C O K w v Hvw x Hx).
    + eapply IHphi; eauto.
Qed.

Lemma ifo_kripke_triple_negation_elim : forall L W C O Hrel
    (K : ifo_kripke_model L W C O) X n
    (phi : ifo_semiformula L X n) w bv fv,
  (forall v, preorder_le O v w ->
    exists x, preorder_le O x v /\
      forall y, preorder_le O y x ->
        ~ ifo_kripke_forces Hrel K y bv fv phi) <->
  (forall v, preorder_le O v w ->
    ~ ifo_kripke_forces Hrel K v bv fv phi).
Proof.
  intros. split.
  - intros Hdense v Hvw Hv.
    destruct (Hdense v Hvw) as [x [Hxv Hall]].
    apply (Hall x (preorder_refl O x)).
    eapply ifo_kripke_forces_monotone; eauto.
  - intros Hall v Hvw. exists v. split; [apply preorder_refl |].
    intros x Hxv. apply Hall.
    exact (@preorder_trans W O x v w Hxv Hvw).
Qed.

Lemma ifo_kripke_forces_all_constant_domain : forall L W C O Hrel
    (K : ifo_kripke_model L W C O),
  ifo_kripke_constant_domain K -> forall X n w bv fv
    (phi : ifo_semiformula L X (S n)),
  ifo_kripke_forces Hrel K w bv fv (IFOAll phi) <->
  forall x, ifo_kripke_forces Hrel K w (fin_cons x bv) fv phi.
Proof.
  intros L W C O Hrel K Hconst X n w bv fv phi. split.
  - intros Hall x. exact (Hall w (preorder_refl O w) x (Hconst w x)).
  - intros Hall v Hvw x Hx.
    eapply ifo_kripke_forces_monotone; [exact (Hall x) | exact Hvw].
Qed.

Lemma ifo_kripke_forces_exs_constant_domain : forall L W C O Hrel
    (K : ifo_kripke_model L W C O),
  ifo_kripke_constant_domain K -> forall X n w bv fv
    (phi : ifo_semiformula L X (S n)),
  ifo_kripke_forces Hrel K w bv fv (IFOExs phi) <->
  exists x, ifo_kripke_forces Hrel K w (fin_cons x bv) fv phi.
Proof.
  intros L W C O Hrel K Hconst X n w bv fv phi. split.
  - intros [x [_ Hx]]. now exists x.
  - intros [x Hx]. exists x. split; [apply Hconst | exact Hx].
Qed.

(** Every intuitionistic Hilbert theorem is forced at every world whenever
    the valuation denotes elements of that world's domain.  The proof is
    constructive and works for arbitrary explicit preorders. *)
Fixpoint ifo_kripke_intuitionistic_sound {L W C}
    {O : preorder_data W}
    (Hrel : language_relational L)
    (K : ifo_kripke_model L W C O)
    {phi : ifo_proposition L}
    (d : @ifo_hilbert_proof L (ifo_hilbert_intuitionistic L) phi) :
  forall w (fv : nat -> C),
    (forall i, ifo_kripke_domain K w (fv i)) ->
    ifo_kripke_forces Hrel K w ifo_empty_bound_env fv phi.
Proof.
  destruct d as [phi Hax | phi psi dimp dphi | phi dbody |
    | phi psi | phi psi chi | phi psi | phi psi | phi psi |
    phi psi | phi psi | phi psi chi | phi t | phi psi | t phi |
    phi psi].
  - change (ifo_intuitionistic_axiom phi) in Hax.
    dependent destruction Hax. intros w fv Hfv.
    intros v Hvw Hfalse. change False in Hfalse. contradiction.
  - intros w fv Hfv.
    pose proof (@ifo_kripke_intuitionistic_sound
      L W C O Hrel K (IFOImp phi psi) dimp w fv Hfv)
      as Himp.
    apply (Himp w (preorder_refl O w)).
    exact (@ifo_kripke_intuitionistic_sound
      L W C O Hrel K phi dphi w fv Hfv).
  - intros w fv Hfv v Hvw x Hx.
    pose proof (@ifo_kripke_intuitionistic_sound
      L W C O Hrel K (@ifo_free L 0 phi) dbody v
      (ifo_nat_env_cons x fv)) as Hbody.
    assert (Henv : forall i,
      ifo_kripke_domain K v (ifo_nat_env_cons x fv i)).
    { intros [|i].
      - exact Hx.
      - exact (@ifo_kripke_domain_antimonotone
          L W C O K w v Hvw (fv i) (Hfv i)). }
    specialize (Hbody Henv).
    apply (proj1 (@ifo_kripke_forces_free
      L W C O Hrel K 0 v ifo_empty_bound_env fv x phi)) in Hbody.
    rewrite ifo_fin_env_snoc_empty in Hbody. exact Hbody.
  - intros. apply ifo_kripke_forces_verum.
  - intros w fv Hfv v Hvw Hphi u Huv Hpsi.
    eapply ifo_kripke_forces_monotone; [exact Hphi | exact Huv].
  - intros w fv Hfv v Hvw Hfirst u Huv Hsecond z Hzu Hphi.
    pose proof (Hsecond z Hzu Hphi) as Hpsi.
    pose proof (Hfirst z
      (@preorder_trans W O z u v Hzu Huv) Hphi) as Hpsi_chi.
    exact (Hpsi_chi z (preorder_refl O z) Hpsi).
  - intros w fv Hfv v Hvw [Hphi Hpsi]. exact Hphi.
  - intros w fv Hfv v Hvw [Hphi Hpsi]. exact Hpsi.
  - intros w fv Hfv v Hvw Hphi u Huv Hpsi. split.
    + eapply ifo_kripke_forces_monotone; [exact Hphi | exact Huv].
    + exact Hpsi.
  - intros w fv Hfv v Hvw Hphi. now left.
  - intros w fv Hfv v Hvw Hpsi. now right.
  - intros w fv Hfv v Hvw Hphi_chi u Huv Hpsi_chi z Hzu Hor.
    destruct Hor as [Hphi | Hpsi].
    + exact (Hphi_chi z
        (@preorder_trans W O z u v Hzu Huv) Hphi).
    + exact (Hpsi_chi z Hzu Hpsi).
  - intros w fv Hfv.
    destruct (term_fvar_relational Hrel t) as [i ->].
    intros v Hvw Hall.
    apply (proj2 (@ifo_kripke_forces_substitute
      L W C O Hrel K nat 1 0 v ifo_empty_bound_env fv
      (fun _ : Fin.t 1 => Semiterm_fvar i) phi)).
    change (ifo_kripke_forces Hrel K v
      (fun _ : Fin.t 1 => fv i) fv phi).
    rewrite (@ifo_fin_one_constant_eq_cons C (fv i)
      (@ifo_empty_bound_env C)).
    apply (Hall v (preorder_refl O v) (fv i)).
    exact (@ifo_kripke_domain_antimonotone
      L W C O K w v Hvw (fv i) (Hfv i)).
  - intros w fv Hfv v Hvw Hall u Huv Hphi z Hzu x Hx.
    pose proof (Hall z
      (@preorder_trans W O z u v Hzu Huv) x Hx) as Himp.
    apply (Himp z (preorder_refl O z)).
    apply (proj2 (@ifo_kripke_forces_bshift
      L W C O Hrel K nat 0 z x ifo_empty_bound_env fv phi)).
    eapply ifo_kripke_forces_monotone; [exact Hphi | exact Hzu].
  - intros w fv Hfv.
    destruct (term_fvar_relational Hrel t) as [i ->].
    intros v Hvw Hbody.
    exists (fv i). split.
    + exact (@ifo_kripke_domain_antimonotone
        L W C O K w v Hvw (fv i) (Hfv i)).
    + apply (proj1 (@ifo_kripke_forces_substitute
        L W C O Hrel K nat 1 0 v ifo_empty_bound_env fv
        (fun _ : Fin.t 1 => Semiterm_fvar i) phi))
        in Hbody.
      change (ifo_kripke_forces Hrel K v
        (fun _ : Fin.t 1 => fv i) fv phi) in Hbody.
      rewrite (@ifo_fin_one_constant_eq_cons C (fv i)
        (@ifo_empty_bound_env C)) in Hbody.
      exact Hbody.
  - intros w fv Hfv v Hvw Hall u Huv Hex.
    destruct Hex as [x [Hx Hbody]].
    pose proof (Hall u Huv x Hx) as Himp.
    pose proof (Himp u (preorder_refl O u) Hbody) as Hshift.
    apply (proj1 (@ifo_kripke_forces_bshift
      L W C O Hrel K nat 0 u x ifo_empty_bound_env fv psi)).
    exact Hshift.
Defined.

Definition ifo_empty_free_env {C} : Empty_set -> C :=
  fun x => match x with end.

Definition ifo_kripke_sentence_forces {L W C O}
    (Hrel : language_relational L)
    (K : ifo_kripke_model L W C O)
    (w : W) (phi : ifo_sentence L) : Prop :=
  ifo_kripke_forces Hrel K w ifo_empty_bound_env
    ifo_empty_free_env phi.

Definition ifo_kripke_sentence_forcing_relation {L W C O}
    (Hrel : language_relational L)
    (K : ifo_kripke_model L W C O) :
    generic_forcing_relation W (ifo_sentence L) :=
  @Build_generic_semantics W (ifo_sentence L)
    (ifo_kripke_sentence_forces Hrel K).

Lemma ifo_kripke_sentence_forces_monotone : forall L W C O Hrel
    (K : ifo_kripke_model L W C O) w phi,
  ifo_kripke_sentence_forces Hrel K w phi -> forall v,
    preorder_le O v w -> ifo_kripke_sentence_forces Hrel K v phi.
Proof.
  intros. eapply ifo_kripke_forces_monotone; eauto.
Qed.

(** Sentence forcing supplies the generic intuitionistic Kripke interface.
    Its accessibility relation is the converse of the explicit preorder,
    exactly as in the source model. *)
Definition ifo_kripke_sentence_int_kripke {L W C O}
    (Hrel : language_relational L)
    (K : ifo_kripke_model L W C O) :
  generic_int_kripke (ifo_connectives L Empty_set 0)
    (ifo_kripke_sentence_forcing_relation Hrel K)
    (fun w v => preorder_le O v w).
Proof.
  constructor.
  - constructor.
    + constructor. intro w. apply ifo_kripke_forces_verum.
    + constructor. intros w phi psi. apply ifo_kripke_forces_and.
    + constructor. intros w phi psi. apply ifo_kripke_forces_or.
  - constructor. intros w phi Hphi v Hvw.
    change (ifo_kripke_sentence_forces Hrel K w phi) in Hphi.
    change (ifo_kripke_sentence_forces Hrel K v phi).
    exact (@ifo_kripke_sentence_forces_monotone
      L W C O Hrel K w phi Hphi v Hvw).
  - constructor. intros w phi psi. apply ifo_kripke_forces_imp.
  - constructor. intro w. apply ifo_kripke_forces_falsum.
  - constructor. intros w phi. apply ifo_kripke_forces_neg.
Defined.

(** A general semantic induction for proof-relevant contexts.  This stronger
    lemma avoids converting arbitrary theory contexts to finite lists. *)
Lemma ifo_kripke_type_context_sound : forall L W C O Hrel
    (K : ifo_kripke_model L W C O)
    (T : ifo_proposition L -> Type) phi,
  generic_type_context_derivation (ifo_hilbert_entailment L)
    (ifo_hilbert_intuitionistic L) (ifo_connectives L nat 0) T phi ->
  forall w (fv : nat -> C),
    (forall i, ifo_kripke_domain K w (fv i)) ->
    (forall p, T p ->
      ifo_kripke_forces Hrel K w ifo_empty_bound_env fv p) ->
    ifo_kripke_forces Hrel K w ifo_empty_bound_env fv phi.
Proof.
  intros L W C O Hrel K T phi d.
  induction d as [p hp | p b | p q dpq IHimp dp IHphi];
    intros w fv Hfv HT.
  - exact (HT p hp).
  - exact (@ifo_kripke_intuitionistic_sound
      L W C O Hrel K p b w fv Hfv).
  - pose proof (IHimp w fv Hfv HT) as Himp.
    exact (Himp w (preorder_refl O w) (IHphi w fv Hfv HT)).
Qed.

Definition ifo_kripke_world_forces_theory {L W C O}
    (Hrel : language_relational L)
    (K : ifo_kripke_model L W C O)
    (w : W) (T : ifo_theory L) : Prop :=
  forall phi, ifo_theory_axiom T phi ->
    ifo_kripke_sentence_forces Hrel K w phi.

Definition ifo_kripke_globally_forces_theory {L W C O}
    (Hrel : language_relational L)
    (K : ifo_kripke_model L W C O)
    (T : ifo_theory L) : Prop :=
  forall w, ifo_kripke_world_forces_theory Hrel K w T.

(** Theory soundness is world-local: assumptions need only be forced at the
    world where the conclusion is requested.  Global soundness follows as an
    immediate specialization. *)
Theorem ifo_kripke_intuitionistic_theory_sound_at : forall L W C O Hrel
    (K : ifo_kripke_model L W C O) (T : ifo_theory L) phi,
  @ifo_theory_proof L (ifo_hilbert_intuitionistic L) T phi ->
  forall w,
    ifo_kripke_world_forces_theory Hrel K w T ->
    ifo_kripke_sentence_forces Hrel K w phi.
Proof.
  intros L W C O Hrel K T phi d w HT.
  destruct (ifo_kripke_domain_nonempty K w) as [x Hx].
  pose proof (@ifo_kripke_type_context_sound
    L W C O Hrel K (ifo_theory_formula_context T)
    (ifo_sentence_embed phi) d w (fun _ : nat => x)) as Hsound.
  assert (Hdomain : forall i : nat,
    ifo_kripke_domain K w ((fun _ : nat => x) i)).
  { intros. exact Hx. }
  specialize (Hsound Hdomain).
  assert (Hcontext : forall p, ifo_theory_formula_context T p ->
    ifo_kripke_forces Hrel K w ifo_empty_bound_env
      (fun _ : nat => x) p).
  { intros p [psi [Hpsi <-]].
    apply (proj2 (@ifo_kripke_forces_emb
      L W C O Hrel K Empty_set nat 0 ifo_empty_elim w
      ifo_empty_bound_env (fun _ : nat => x) psi)).
    assert ((fun y : Empty_set => False_rect C (ifo_empty_elim y)) =
      @ifo_empty_free_env C) as ->.
    { apply functional_extensionality. intro y. destruct y. }
    exact (HT psi Hpsi). }
  specialize (Hsound Hcontext).
  apply (proj1 (@ifo_kripke_forces_emb
    L W C O Hrel K Empty_set nat 0 ifo_empty_elim w
    ifo_empty_bound_env (fun _ : nat => x) phi)) in Hsound.
  assert ((fun y : Empty_set => False_rect C (ifo_empty_elim y)) =
    @ifo_empty_free_env C) as Hempty.
  { apply functional_extensionality. intro y. destruct y. }
  now rewrite Hempty in Hsound.
Qed.

Theorem ifo_kripke_intuitionistic_theory_sound : forall L W C O Hrel
    (K : ifo_kripke_model L W C O) (T : ifo_theory L) phi,
  @ifo_theory_proof L (ifo_hilbert_intuitionistic L) T phi ->
  ifo_kripke_globally_forces_theory Hrel K T ->
  forall w, ifo_kripke_sentence_forces Hrel K w phi.
Proof.
  intros L W C O Hrel K T phi d HT w.
  exact (@ifo_kripke_intuitionistic_theory_sound_at
    L W C O Hrel K T phi d w (HT w)).
Qed.
