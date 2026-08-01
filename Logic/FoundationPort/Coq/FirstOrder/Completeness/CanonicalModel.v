(** The consistent-sequent canonical model for classical first-order logic. *)

From Stdlib Require Import Lists.List Logic.ClassicalChoice Logic.Classical_Prop
  Logic.FunctionalExtensionality Vectors.Fin.
From FoundationModal Require Import GenericForcingRelation GenericSemantics.
From Foundation.Vorspiel.Order Require Import Dense.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Intuitionistic Require Import Formula Rew.
From Foundation.FirstOrder.NegationTranslation Require Import GoedelGentzen.
From Foundation.FirstOrder.Basic Require Import Calculus CutFree Soundness.
From Foundation.FirstOrder.Kripke Require Import WeakForcing.
From Foundation.FirstOrder Require Import Hauptsatz.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Lemma first_order_inhabited_forall_choice : forall (A : Type)
    (B : A -> Type),
  (forall x, inhabited (B x)) -> inhabited (forall x, B x).
Proof.
  intros A B H.
  assert (Hex : forall x : A,
      exists y : { z : A & B z }, projT1 y = x).
  { intro x. destruct (H x) as [Hx].
    exists (existT B x Hx). reflexivity. }
  destruct (@ClassicalChoice.choice A { z : A & B z }
    (fun x y => projT1 y = x) Hex) as [f Hf].
  constructor. intro x.
  destruct (f x) as [z Hz] eqn:Ef. cbn in Hf.
  specialize (Hf x). rewrite Ef in Hf. cbn in Hf. now subst z.
Qed.

Definition first_order_canonical_world (L : language) : Type :=
  first_order_consistent_sequent L.

Definition first_order_canonical_world_order (L : language) :
    preorder_data (first_order_canonical_world L) :=
  first_order_consistent_sequent_order L.

Definition first_order_canonical_world_nil {L} :
    first_order_canonical_world L.
Proof.
  exists []. cbn. apply first_order_derivation_nil_empty.
Defined.

Definition first_order_canonical_world_of_unprovable {L}
    (phi : proposition L)
    (H : ~ first_order_lk_provable (semiformula_neg phi)) :
    first_order_canonical_world L.
Proof.
  exists [phi]. intro d. apply H.
  apply (proj2 (first_order_lk_provable_iff
    (semiformula_neg phi))).
  exact (inhabits d).
Defined.

Definition first_order_canonical_is_forced {L}
    (p : first_order_canonical_world L) (phi : ifo_proposition L) : Prop :=
  inhabited (first_order_canonical_forces (proj1_sig p) phi).

Definition first_order_canonical_forcing_relation (L : language) :
    generic_forcing_relation (first_order_canonical_world L)
      (ifo_proposition L) :=
  {| generic_models := first_order_canonical_is_forced |}.

Definition first_order_canonical_is_weakly_forced {L}
    (p : first_order_canonical_world L) (phi : proposition L) : Prop :=
  first_order_canonical_is_forced p
    (ifo_double_negation_translation phi).

Definition first_order_canonical_weak_forcing_relation (L : language) :
    generic_forcing_relation (first_order_canonical_world L)
      (proposition L) :=
  {| generic_models := first_order_canonical_is_weakly_forced |}.

Lemma first_order_canonical_is_forced_rel : forall L
    (D : language_decidable_eq L) (p : first_order_canonical_world L)
    k (R : language_rel L k) (v : Fin.t k -> syntactic_term L),
  first_order_canonical_is_forced p (IFORel R v) <->
  inhabited (first_order_derivation L
    (Semiformula_rel R v :: map semiformula_neg (proj1_sig p))).
Proof.
  intros L D [Gamma Hconsistent] k R v. split.
  - intros [[b Hb]].
    assert (Hv :
      (fun i => rew_apply
        (rew_bind first_order_empty_bound_env
          first_order_identity_free_env) (v i)) = v).
    { apply functional_extensionality. intro i.
      apply first_order_rew_apply_bind_identity. }
    constructor. exact (first_order_derivation_cast b
      (f_equal (fun args =>
        Semiformula_rel R args :: map semiformula_neg Gamma) Hv)).
  - intros [d].
    destruct (first_order_hauptsatz D d) as [b Hb].
    assert (Hv :
      (fun i => rew_apply
        (rew_bind first_order_empty_bound_env
          first_order_identity_free_env) (v i)) = v).
    { apply functional_extensionality. intro i.
      apply first_order_rew_apply_bind_identity. }
    constructor. exists (first_order_derivation_cast b
      (f_equal (fun args =>
        Semiformula_rel R args :: map semiformula_neg Gamma) (eq_sym Hv))).
    apply (proj2 (first_order_is_cut_free_cast_iff b _)). exact Hb.
Qed.

Lemma first_order_canonical_is_forced_all : forall L
    (p : first_order_canonical_world L) (phi : ifo_semiproposition L 1),
  first_order_canonical_is_forced p (IFOAll phi) <->
  forall t : syntactic_term L,
    first_order_canonical_is_forced p
      (ifo_substitute (fun _ : Fin.t 1 => t) phi).
Proof.
  intros L [Gamma Hconsistent] phi. split.
  - intros [H] t. constructor.
    apply (first_order_type_biequivalence_backward
      (@first_order_canonical_forces_substitute_one L Gamma phi t)).
    exact (H t).
  - intros H. apply first_order_inhabited_forall_choice.
    intro t. destruct (H t) as [Ht]. constructor.
    exact (first_order_type_biequivalence_forward
      (@first_order_canonical_forces_substitute_one L Gamma phi t) Ht).
Qed.

Lemma first_order_canonical_is_forced_and : forall L
    (p : first_order_canonical_world L) (phi psi : ifo_proposition L),
  first_order_canonical_is_forced p (IFOAnd phi psi) <->
  first_order_canonical_is_forced p phi /\
  first_order_canonical_is_forced p psi.
Proof.
  intros L p phi psi. split.
  - intros [[Hphi Hpsi]]. now split; constructor.
  - intros [[Hphi] [Hpsi]]. constructor. now split.
Qed.

Lemma first_order_canonical_is_forced_or : forall L
    (p : first_order_canonical_world L) (phi psi : ifo_proposition L),
  first_order_canonical_is_forced p (IFOOr phi psi) <->
  first_order_canonical_is_forced p phi \/
  first_order_canonical_is_forced p psi.
Proof.
  intros L p phi psi. split.
  - intros [[Hphi | Hpsi]].
    + left. now constructor.
    + right. now constructor.
  - intros [[Hphi] | [Hpsi]]; constructor.
    + now left.
    + now right.
Qed.

Lemma first_order_canonical_is_forced_not_falsum : forall L
    (p : first_order_canonical_world L),
  ~ first_order_canonical_is_forced p IFOFalsum.
Proof.
  intros L [Gamma Hconsistent] [[b Hb]]. exact (Hconsistent b).
Qed.

Lemma first_order_canonical_is_forced_exists : forall L
    (p : first_order_canonical_world L) (phi : ifo_semiproposition L 1),
  first_order_canonical_is_forced p (IFOExs phi) <->
  exists t : syntactic_term L,
    first_order_canonical_is_forced p
      (ifo_substitute (fun _ : Fin.t 1 => t) phi).
Proof.
  intros L [Gamma Hconsistent] phi. split.
  - intros [[t Ht]]. exists t. constructor.
    exact (first_order_type_biequivalence_backward
      (@first_order_canonical_forces_substitute_one L Gamma phi t) Ht).
  - intros [t [Ht]]. constructor. exists t.
    exact (first_order_type_biequivalence_forward
      (@first_order_canonical_forces_substitute_one L Gamma phi t) Ht).
Qed.

Lemma first_order_canonical_is_forced_monotone : forall L
    (p q : first_order_canonical_world L),
  preorder_le (first_order_canonical_world_order L) q p ->
  forall phi : ifo_proposition L,
    first_order_canonical_is_forced p phi ->
    first_order_canonical_is_forced q phi.
Proof.
  intros L [Gamma HGamma] [Delta HDelta] [s] phi [Hphi].
  constructor. exact (first_order_canonical_forces_monotone
    {| first_order_stronger_derivation := s |} Hphi).
Qed.
