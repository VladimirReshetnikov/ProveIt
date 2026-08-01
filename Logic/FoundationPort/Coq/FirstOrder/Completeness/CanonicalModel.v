(** The consistent-sequent canonical model for classical first-order logic. *)

From Stdlib Require Import Lists.List Logic.ClassicalChoice Logic.Classical_Prop
  Logic.FunctionalExtensionality Vectors.Fin.
From FoundationModal Require Import GenericForcingRelation GenericSemantics.
From Foundation.Vorspiel.Order Require Import Dense.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Intuitionistic Require Import Formula Rew Deduction.
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

Lemma first_order_canonical_world_le_nil : forall L
    (p : first_order_canonical_world L),
  preorder_le (first_order_canonical_world_order L)
    p first_order_canonical_world_nil.
Proof.
  intros L [Gamma HGamma]. constructor.
  apply first_order_positive_derivation_of_subset.
  intros phi Hphi. inversion Hphi.
Qed.

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

Lemma first_order_canonical_is_weakly_forced_iff_is_forced : forall L
    (p : first_order_canonical_world L) (phi : proposition L),
  first_order_canonical_is_weakly_forced p phi <->
  first_order_canonical_is_forced p
    (ifo_double_negation_translation phi).
Proof. reflexivity. Qed.

(** Equality transport for weak forcing.  Quantifier constructions frequently
    expose formulas through two extensionally identical rewrite expressions;
    keeping the transport at this layer prevents every client from unfolding
    the double-negation translation. *)
Lemma first_order_canonical_is_weakly_forced_cast : forall L
    (p : first_order_canonical_world L) (phi psi : proposition L),
  phi = psi ->
  first_order_canonical_is_weakly_forced p phi ->
  first_order_canonical_is_weakly_forced p psi.
Proof. intros L p phi psi -> Hphi; exact Hphi. Qed.

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

Lemma first_order_canonical_is_forced_imp : forall L
    (D : language_decidable_eq L)
    (p : first_order_canonical_world L) (phi psi : ifo_proposition L),
  first_order_canonical_is_forced p (IFOImp phi psi) <->
  forall q : first_order_canonical_world L,
    preorder_le (first_order_canonical_world_order L) q p ->
    first_order_canonical_is_forced q phi ->
    first_order_canonical_is_forced q psi.
Proof.
  intros L D [Gamma HGamma] phi psi. split.
  - intros [Himp] [Delta HDelta] [s] [Hphi]. constructor.
    exact (Himp Delta {| first_order_stronger_derivation := s |} Hphi).
  - intros H.
    apply first_order_inhabited_forall_choice. intro Delta.
    apply first_order_inhabited_forall_choice. intro sDeltaGamma.
    apply first_order_inhabited_forall_choice. intro Hphi.
    destruct (classic
      (first_order_derivation L (map semiformula_neg Delta) -> False))
      as [HDelta | HDelta].
    + exact (H (exist _ Delta HDelta)
        (inhabits (first_order_stronger_derivation sDeltaGamma))
        (inhabits Hphi)).
    + assert (Hd : inhabited
        (first_order_derivation L (map semiformula_neg Delta))).
      { apply NNPP. intro Hnot.
        apply HDelta. intro d. apply Hnot. exact (inhabits d). }
      destruct Hd as [d].
      destruct (first_order_hauptsatz D d) as [b Hb].
      constructor.
      exact (first_order_canonical_forces_explosion (existT _ b Hb)).
Qed.

Lemma first_order_canonical_is_forced_neg : forall L
    (D : language_decidable_eq L)
    (p : first_order_canonical_world L) (phi : ifo_proposition L),
  first_order_canonical_is_forced p (ifo_neg phi) <->
  forall q : first_order_canonical_world L,
    preorder_le (first_order_canonical_world_order L) q p ->
    ~ first_order_canonical_is_forced q phi.
Proof.
  intros L D p phi. unfold ifo_neg.
  rewrite (@first_order_canonical_is_forced_imp
    L D p phi IFOFalsum). split.
  - intros H q Hqp Hphi.
    exact (first_order_canonical_is_forced_not_falsum
      (H q Hqp Hphi)).
  - intros H q Hqp Hphi. exfalso. exact (H q Hqp Hphi).
Qed.

Theorem first_order_canonical_minimal_sound_global : forall L
    (phi : ifo_proposition L)
    (d : @ifo_hilbert_proof L (ifo_hilbert_minimal L) phi),
  forall p : first_order_canonical_world L,
    first_order_canonical_is_forced p phi.
Proof.
  intros L phi d [Gamma HGamma]. constructor.
  exact (first_order_canonical_minimal_sound d Gamma).
Qed.

Definition first_order_canonical_int_kripke {L}
    (D : language_decidable_eq L) :
  generic_int_kripke (ifo_connectives L nat 0)
    (first_order_canonical_forcing_relation L)
    (fun p q => preorder_le (first_order_canonical_world_order L) q p).
Proof.
  constructor.
  - constructor.
    + constructor. intro p. unfold first_order_canonical_forcing_relation.
      cbn [generic_forces generic_models generic_top ifo_connectives].
      constructor. intros q sqp Hbot. exact Hbot.
    + constructor. intros p phi psi.
      apply first_order_canonical_is_forced_and.
    + constructor. intros p phi psi.
      apply first_order_canonical_is_forced_or.
  - constructor. intros p phi Hphi q Hqp.
    exact (first_order_canonical_is_forced_monotone Hqp Hphi).
  - constructor. intros p phi psi.
    exact (first_order_canonical_is_forced_imp D p phi psi).
  - constructor. apply first_order_canonical_is_forced_not_falsum.
  - constructor. intros p phi.
    exact (first_order_canonical_is_forced_neg D p phi).
Defined.

(** Transporting an inhabited forcing witness is the proposition-level
    counterpart of [first_order_canonical_forces_cast].  Keeping this helper
    separate avoids repeating dependent equality elimination in the
    quantifier clauses below. *)
Lemma first_order_canonical_is_forced_cast : forall L
    (p : first_order_canonical_world L) (phi psi : ifo_proposition L),
  phi = psi ->
  first_order_canonical_is_forced p phi ->
  first_order_canonical_is_forced p psi.
Proof.
  intros L [Gamma HGamma] phi psi -> Hphi. exact Hphi.
Qed.

Lemma first_order_canonical_weak_neg_translation : forall L
    (p : first_order_canonical_world L) (phi : proposition L),
  first_order_canonical_is_weakly_forced p (semiformula_neg phi) <->
  first_order_canonical_is_forced p
    (ifo_neg (ifo_double_negation_translation phi)).
Proof.
  intros L [Gamma HGamma] phi. unfold first_order_canonical_is_weakly_forced,
    first_order_canonical_is_forced.
  pose (Hequiv := first_order_canonical_minimal_sound
    (@ifo_hilbert_neg_double_negation L (ifo_hilbert_minimal L) phi)
    Gamma).
  split; intros [Hphi]; constructor.
  - exact (@first_order_canonical_modus_ponens L Gamma
      (ifo_double_negation_translation (semiformula_neg phi))
      (ifo_neg (ifo_double_negation_translation phi))
      (snd Hequiv) Hphi).
  - exact (@first_order_canonical_modus_ponens L Gamma
      (ifo_neg (ifo_double_negation_translation phi))
      (ifo_double_negation_translation (semiformula_neg phi))
      (fst Hequiv) Hphi).
Qed.

Lemma first_order_canonical_is_weakly_forced_verum : forall L
    (p : first_order_canonical_world L),
  first_order_canonical_is_weakly_forced p
    (@Semiformula_verum L nat 0).
Proof.
  intros L [Gamma HGamma]. constructor.
  intros Delta HDelta Hbot. exact Hbot.
Qed.

Lemma first_order_canonical_is_weakly_forced_falsum : forall L
    (p : first_order_canonical_world L),
  ~ first_order_canonical_is_weakly_forced p
    (@Semiformula_falsum L nat 0).
Proof.
  intros L p. exact (@first_order_canonical_is_forced_not_falsum L p).
Qed.

Lemma first_order_canonical_is_weakly_forced_not : forall L
    (D : language_decidable_eq L)
    (p : first_order_canonical_world L) (phi : proposition L),
  first_order_canonical_is_weakly_forced p (semiformula_neg phi) <->
  forall q : first_order_canonical_world L,
    preorder_le (first_order_canonical_world_order L) q p ->
    ~ first_order_canonical_is_weakly_forced q phi.
Proof.
  intros L D p phi. split.
  - intro Hneg.
    apply (proj1 (@first_order_canonical_is_forced_neg L D p
      (ifo_double_negation_translation phi))).
    exact (proj1 (@first_order_canonical_weak_neg_translation L p phi)
      Hneg).
  - intro Hall.
    apply (proj2 (@first_order_canonical_weak_neg_translation L p phi)).
    apply (proj2 (@first_order_canonical_is_forced_neg L D p
      (ifo_double_negation_translation phi))).
    exact Hall.
Qed.

Lemma first_order_canonical_is_weakly_forced_and : forall L
    (p : first_order_canonical_world L) (phi psi : proposition L),
  first_order_canonical_is_weakly_forced p (Semiformula_and phi psi) <->
  first_order_canonical_is_weakly_forced p phi /\
  first_order_canonical_is_weakly_forced p psi.
Proof.
  intros L p phi psi. unfold first_order_canonical_is_weakly_forced.
  apply first_order_canonical_is_forced_and.
Qed.

Lemma first_order_canonical_is_weakly_forced_all : forall L
    (p : first_order_canonical_world L) (phi : semiproposition L 1),
  first_order_canonical_is_weakly_forced p (Semiformula_all phi) <->
  forall t : syntactic_term L,
    first_order_canonical_is_weakly_forced p
      (semiformula_substitute (fun _ : Fin.t 1 => t) phi).
Proof.
  intros L p phi. unfold first_order_canonical_is_weakly_forced.
  change (first_order_canonical_is_forced p
      (IFOAll (ifo_double_negation_translation phi)) <->
    forall t : syntactic_term L,
      first_order_canonical_is_forced p
        (ifo_double_negation_translation
          (semiformula_substitute (fun _ : Fin.t 1 => t) phi))).
  rewrite first_order_canonical_is_forced_all. split.
  - intros Hall t. eapply first_order_canonical_is_forced_cast.
    + apply ifo_substitute_double_negation.
    + exact (Hall t).
  - intros Hall t. eapply first_order_canonical_is_forced_cast.
    + symmetry. apply ifo_substitute_double_negation.
    + exact (Hall t).
Qed.

Lemma first_order_canonical_is_weakly_forced_monotone : forall L
    (p q : first_order_canonical_world L) (phi : proposition L),
  preorder_le (first_order_canonical_world_order L) q p ->
  first_order_canonical_is_weakly_forced p phi ->
  first_order_canonical_is_weakly_forced q phi.
Proof.
  intros L p q phi Hqp Hphi.
  exact (first_order_canonical_is_forced_monotone Hqp Hphi).
Qed.

Lemma first_order_canonical_is_weakly_forced_generic : forall L
    (D : language_decidable_eq L)
    (p : first_order_canonical_world L) (phi : proposition L),
  first_order_canonical_is_weakly_forced p phi <->
  forall q : first_order_canonical_world L,
    preorder_le (first_order_canonical_world_order L) q p ->
    exists r : first_order_canonical_world L,
      preorder_le (first_order_canonical_world_order L) r q /\
      first_order_canonical_is_weakly_forced r phi.
Proof.
  intros L D p phi. split.
  - intros Hphi q Hqp. exists q. split.
    + apply preorder_refl.
    + exact (first_order_canonical_is_weakly_forced_monotone Hqp Hphi).
  - intros Hdense.
    assert (Hnn : first_order_canonical_is_weakly_forced p
        (semiformula_neg (semiformula_neg phi))).
    { apply (proj2 (first_order_canonical_is_weakly_forced_not
        D p (semiformula_neg phi))).
      intros q Hqp Hneg.
      destruct (Hdense q Hqp) as [r [Hrq Hrphi]].
      exact ((proj1 (first_order_canonical_is_weakly_forced_not
        D q phi) Hneg) r Hrq Hrphi). }
    unfold first_order_canonical_is_weakly_forced in Hnn |- *.
    now rewrite semiformula_neg_involutive in Hnn.
Qed.

Lemma first_order_canonical_is_weakly_forced_or : forall L
    (D : language_decidable_eq L)
    (p : first_order_canonical_world L) (phi psi : proposition L),
  first_order_canonical_is_weakly_forced p (Semiformula_or phi psi) <->
  forall q : first_order_canonical_world L,
    preorder_le (first_order_canonical_world_order L) q p ->
    exists r : first_order_canonical_world L,
      preorder_le (first_order_canonical_world_order L) r q /\
      (first_order_canonical_is_weakly_forced r phi \/
       first_order_canonical_is_weakly_forced r psi).
Proof.
  intros L D p phi psi.
  unfold first_order_canonical_is_weakly_forced.
  change (first_order_canonical_is_forced p
      (ifo_neg (IFOAnd
        (ifo_neg (ifo_double_negation_translation phi))
        (ifo_neg (ifo_double_negation_translation psi)))) <->
    forall q : first_order_canonical_world L,
      preorder_le (first_order_canonical_world_order L) q p ->
      exists r : first_order_canonical_world L,
        preorder_le (first_order_canonical_world_order L) r q /\
        (first_order_canonical_is_forced r
           (ifo_double_negation_translation phi) \/
         first_order_canonical_is_forced r
           (ifo_double_negation_translation psi))).
  split.
  - intros Hor q Hqp.
    pose (Hnotand := proj1 (@first_order_canonical_is_forced_neg
      L D p
      (IFOAnd
        (ifo_neg (ifo_double_negation_translation phi))
        (ifo_neg (ifo_double_negation_translation psi)))) Hor).
    destruct (classic (exists r : first_order_canonical_world L,
        preorder_le (first_order_canonical_world_order L) r q /\
        first_order_canonical_is_forced r
          (ifo_double_negation_translation phi)))
      as [Hphi | Hphi].
    + destruct Hphi as [r [Hrq Hrphi]].
      exists r. split; [exact Hrq |]. left. exact Hrphi.
    + assert (Hnegphi : first_order_canonical_is_forced q
          (ifo_neg (ifo_double_negation_translation phi))).
      { apply (proj2 (@first_order_canonical_is_forced_neg L D q
          (ifo_double_negation_translation phi))).
        intros r Hrq Hrphi. apply Hphi. exists r. now split. }
      assert (Hnotnegpsi : ~ first_order_canonical_is_forced q
          (ifo_neg (ifo_double_negation_translation psi))).
      { intro Hnegpsi. apply (Hnotand q Hqp).
        apply (proj2 (@first_order_canonical_is_forced_and L q
          (ifo_neg (ifo_double_negation_translation phi))
          (ifo_neg (ifo_double_negation_translation psi)))).
        now split. }
      apply NNPP. intro Hpsi.
      apply Hnotnegpsi.
      apply (proj2 (@first_order_canonical_is_forced_neg L D q
        (ifo_double_negation_translation psi))).
      intros r Hrq Hrpsi. apply Hpsi. exists r.
      split; [exact Hrq |]. right. exact Hrpsi.
  - intros Hdense.
    apply (proj2 (@first_order_canonical_is_forced_neg L D p
      (IFOAnd
        (ifo_neg (ifo_double_negation_translation phi))
        (ifo_neg (ifo_double_negation_translation psi))))).
    intros q Hqp Hand.
    destruct (proj1 (@first_order_canonical_is_forced_and L q
      (ifo_neg (ifo_double_negation_translation phi))
      (ifo_neg (ifo_double_negation_translation psi))) Hand)
      as [Hnegphi Hnegpsi].
    destruct (Hdense q Hqp) as [r [Hrq [Hrphi | Hrpsi]]].
    + exact ((proj1 (@first_order_canonical_is_forced_neg L D q
        (ifo_double_negation_translation phi)) Hnegphi) r Hrq Hrphi).
    + exact ((proj1 (@first_order_canonical_is_forced_neg L D q
        (ifo_double_negation_translation psi)) Hnegpsi) r Hrq Hrpsi).
Qed.

Lemma first_order_canonical_is_weakly_forced_exists : forall L
    (D : language_decidable_eq L)
    (p : first_order_canonical_world L) (phi : semiproposition L 1),
  first_order_canonical_is_weakly_forced p (Semiformula_exists phi) <->
  forall q : first_order_canonical_world L,
    preorder_le (first_order_canonical_world_order L) q p ->
    exists r : first_order_canonical_world L,
      preorder_le (first_order_canonical_world_order L) r q /\
      exists t : syntactic_term L,
        first_order_canonical_is_weakly_forced r
          (semiformula_substitute (fun _ : Fin.t 1 => t) phi).
Proof.
  intros L D p phi.
  unfold first_order_canonical_is_weakly_forced.
  change (first_order_canonical_is_forced p
      (ifo_neg (IFOAll
        (ifo_neg (ifo_double_negation_translation phi)))) <->
    forall q : first_order_canonical_world L,
      preorder_le (first_order_canonical_world_order L) q p ->
      exists r : first_order_canonical_world L,
        preorder_le (first_order_canonical_world_order L) r q /\
        exists t : syntactic_term L,
          first_order_canonical_is_forced r
            (ifo_double_negation_translation
              (semiformula_substitute (fun _ : Fin.t 1 => t) phi))).
  split.
  - intros Hex q Hqp.
    pose (Hnotall := proj1 (@first_order_canonical_is_forced_neg
      L D p (IFOAll
        (ifo_neg (ifo_double_negation_translation phi)))) Hex).
    apply NNPP. intro Hnone.
    apply (Hnotall q Hqp).
    apply (proj2 (@first_order_canonical_is_forced_all L q
      (ifo_neg (ifo_double_negation_translation phi)))).
    intro t.
    change (first_order_canonical_is_forced q
      (ifo_neg (ifo_substitute (fun _ : Fin.t 1 => t)
        (ifo_double_negation_translation phi)))).
    apply (proj2 (@first_order_canonical_is_forced_neg L D q
      (ifo_substitute (fun _ : Fin.t 1 => t)
        (ifo_double_negation_translation phi)))).
    intros r Hrq Hrbody. apply Hnone. exists r. split; [exact Hrq |].
    exists t. eapply first_order_canonical_is_forced_cast.
    + apply ifo_substitute_double_negation.
    + exact Hrbody.
  - intros Hdense.
    apply (proj2 (@first_order_canonical_is_forced_neg L D p
      (IFOAll (ifo_neg (ifo_double_negation_translation phi))))).
    intros q Hqp Hallneg.
    destruct (Hdense q Hqp) as [r [Hrq [t Hrbody]]].
    pose (Hneg := proj1 (@first_order_canonical_is_forced_all L q
      (ifo_neg (ifo_double_negation_translation phi))) Hallneg t).
    assert (Hneg' : first_order_canonical_is_forced q
        (ifo_neg (ifo_substitute (fun _ : Fin.t 1 => t)
          (ifo_double_negation_translation phi)))).
    { eapply first_order_canonical_is_forced_cast.
      - apply ifo_rewrite_neg.
      - exact Hneg. }
    apply ((proj1 (@first_order_canonical_is_forced_neg L D q
      (ifo_substitute (fun _ : Fin.t 1 => t)
        (ifo_double_negation_translation phi))) Hneg') r Hrq).
    eapply first_order_canonical_is_forced_cast.
    + symmetry. apply ifo_substitute_double_negation.
    + exact Hrbody.
Qed.

(** Failure of a weakly forced formula can be made persistent at a stronger
    world.  This is the reusable density/refutation step behind implication
    and is stated independently of either connective. *)
Lemma first_order_canonical_weak_neg_extension : forall L
    (D : language_decidable_eq L)
    (p : first_order_canonical_world L) (phi : proposition L),
  ~ first_order_canonical_is_weakly_forced p phi ->
  exists q : first_order_canonical_world L,
    preorder_le (first_order_canonical_world_order L) q p /\
    first_order_canonical_is_weakly_forced q (semiformula_neg phi).
Proof.
  intros L D p phi Hnot. apply NNPP. intro Hnone.
  apply Hnot.
  apply (proj2 (first_order_canonical_is_weakly_forced_generic D p phi)).
  intros q Hqp. apply NNPP. intro Hnonephi.
  apply Hnone. exists q. split; [exact Hqp |].
  apply (proj2 (first_order_canonical_is_weakly_forced_not D q phi)).
  intros r Hrq Hrphi. apply Hnonephi. exists r. now split.
Qed.

Lemma first_order_canonical_is_weakly_forced_imp : forall L
    (D : language_decidable_eq L)
    (p : first_order_canonical_world L) (phi psi : proposition L),
  first_order_canonical_is_weakly_forced p (semiformula_imp phi psi) <->
  forall q : first_order_canonical_world L,
    preorder_le (first_order_canonical_world_order L) q p ->
    first_order_canonical_is_weakly_forced q phi ->
    first_order_canonical_is_weakly_forced q psi.
Proof.
  intros L D p phi psi. unfold semiformula_imp. split.
  - intros Himp q Hqp Hphi.
    apply (proj2 (first_order_canonical_is_weakly_forced_generic D q psi)).
    intros r Hrq.
    destruct (proj1 (first_order_canonical_is_weakly_forced_or
      D p (semiformula_neg phi) psi) Himp r
      (@preorder_trans _ (first_order_canonical_world_order L)
        r q p Hrq Hqp)) as [s [Hsr [Hneg | Hpsi]]].
    + exfalso.
      apply ((proj1 (first_order_canonical_is_weakly_forced_not
        D s phi) Hneg) s (preorder_refl _ s)).
      exact (first_order_canonical_is_weakly_forced_monotone
        (@preorder_trans _ (first_order_canonical_world_order L)
          s r q Hsr Hrq) Hphi).
    + exists s. now split.
  - intros Himp.
    apply (proj2 (first_order_canonical_is_weakly_forced_or
      D p (semiformula_neg phi) psi)).
    intros q Hqp.
    destruct (classic
      (first_order_canonical_is_weakly_forced q phi)) as [Hphi | Hphi].
    + exists q. split; [apply preorder_refl |].
      right. exact (Himp q Hqp Hphi).
    + destruct (@first_order_canonical_weak_neg_extension L D q phi Hphi)
        as [r [Hrq Hrneg]].
      exists r. split; [exact Hrq |]. now left.
Qed.

Definition first_order_canonical_classical_kripke {L}
    (D : language_decidable_eq L) :
  generic_classical_kripke (semiformula_connectives L nat 0)
    (first_order_canonical_weak_forcing_relation L)
    (fun p q => preorder_le (first_order_canonical_world_order L) q p).
Proof.
  constructor.
  - constructor.
    + constructor. apply first_order_canonical_is_weakly_forced_verum.
    + constructor. apply first_order_canonical_is_weakly_forced_falsum.
    + constructor. intros p phi psi.
      apply first_order_canonical_is_weakly_forced_and.
  - intros p phi psi.
    apply first_order_canonical_is_weakly_forced_or. exact D.
  - constructor. intros p phi.
    apply first_order_canonical_is_weakly_forced_not. exact D.
  - constructor. intros p phi psi.
    apply first_order_canonical_is_weakly_forced_imp. exact D.
  - constructor. intros p phi Hphi q Hqp.
    exact (first_order_canonical_is_weakly_forced_monotone Hqp Hphi).
  - intros p phi Hdense.
    exact (proj2 (first_order_canonical_is_weakly_forced_generic D p phi)
      Hdense).
Defined.

Theorem first_order_canonical_weak_completeness : forall L
    (D : language_decidable_eq L) (phi : proposition L),
  (forall p : first_order_canonical_world L,
    first_order_canonical_is_weakly_forced p phi) <->
  first_order_lk_provable phi.
Proof.
  intros L D phi. split.
  - intro Hall. apply NNPP. intro Hnot.
    assert (Hnn : ~ first_order_lk_provable
        (semiformula_neg (semiformula_neg phi))).
    { intro Hprov. apply Hnot.
      exact (first_order_lk_provable_cast Hprov
        (semiformula_neg_involutive phi)). }
    pose (p := @first_order_canonical_world_of_unprovable
      L (semiformula_neg phi) Hnn).
    destruct (Hall p) as [Hphi].
    pose (Hneg := first_order_canonical_reflection (semiformula_neg phi)).
    pose (Hequiv := first_order_canonical_minimal_sound
      (@ifo_hilbert_neg_double_negation L (ifo_hilbert_minimal L) phi)
      [semiformula_neg phi]).
    pose (Hnotphi :=
      @first_order_canonical_modus_ponens L [semiformula_neg phi]
        (ifo_double_negation_translation (semiformula_neg phi))
        (ifo_neg (ifo_double_negation_translation phi))
        (snd Hequiv) Hneg).
    change (first_order_canonical_forces [semiformula_neg phi]
      (ifo_double_negation_translation phi)) in Hphi.
    pose (Hbot :=
      @first_order_canonical_modus_ponens L [semiformula_neg phi]
        (ifo_double_negation_translation phi) IFOFalsum
        Hnotphi Hphi).
    destruct Hbot as [b Hb]. exact ((proj2_sig p) b).
  - intros Hprov [Gamma HGamma].
    destruct (@ifo_goedel_gentzen_provable L D
      (ifo_hilbert_minimal L) phi Hprov) as [d].
    constructor. exact (first_order_canonical_minimal_sound d Gamma).
Qed.

Lemma first_order_canonical_weak_reflection : forall L
    (phi : proposition L)
    (H : ~ first_order_lk_provable (semiformula_neg phi)),
  first_order_canonical_is_weakly_forced
    (@first_order_canonical_world_of_unprovable L phi H) phi.
Proof.
  intros L phi H. constructor.
  apply first_order_canonical_reflection.
Qed.
