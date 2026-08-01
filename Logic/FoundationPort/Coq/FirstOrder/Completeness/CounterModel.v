(** Generic filters and the syntactic countermodel for classical first-order
    logic.

    This ports the core of
    [Foundation/FirstOrder/Completeness/CounterModel.lean].  The construction
    is split into explicit dense requirements, their countable enumeration,
    generic forcing, and the term model. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Logic.ClassicalChoice
  Logic.ClassicalDescription Logic.ClassicalEpsilon Logic.Classical_Prop
  Logic.FunctionalExtensionality Vectors.Fin.
From FoundationModal Require Import GenericAdjunctiveSet GenericEntailment GenericLogicSymbol
  GenericSemantics PropositionalEntailmentAxioms PropositionalEntailmentMinimal
  PropositionalEntailmentClassical.
From Foundation.Vorspiel.Order Require Import Dense.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Calculus Calculus2 Coding Soundness.
From Foundation.FirstOrder.Basic.Semantics Require Import Semantics ModelTheory Elementary.
From Foundation.FirstOrder Require Import Hauptsatz.
From Foundation.FirstOrder Require Import Ultraproduct.
From Foundation.FirstOrder.Completeness Require Import
  CanonicalModel CountableSublanguage.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition first_order_lk_provable_em {L} (phi : proposition L) :
  first_order_lk_provable
    (Semiformula_or phi (semiformula_neg phi)).
Proof.
  apply (proj2 (first_order_lk_provable_iff _)).
  constructor. exact (FODOr (first_order_derivation_eta phi)).
Defined.

Section GenericRequirements.

Universe u.
Context {L : language@{Set u}} (D : language_decidable_eq L)
  (EL : language_encodable L).

Local Definition canonical_order := first_order_canonical_world_order L.

Definition first_order_decidable_points (phi : proposition L) :
    dense_set canonical_order.
Proof.
  refine {| dense_member := fun p =>
      first_order_canonical_is_weakly_forced p phi \/
      first_order_canonical_is_weakly_forced p (semiformula_neg phi) |}.
  intro p.
  pose proof (proj2 (@first_order_canonical_weak_completeness L D
      (Semiformula_or phi (semiformula_neg phi)))
    (first_order_lk_provable_em phi)) as Hem.
  destruct (proj1 (@first_order_canonical_is_weakly_forced_or L
      D p phi (semiformula_neg phi)) (Hem p) p (preorder_refl _ p))
    as [q [Hqp Hq]].
  now exists q.
Defined.

Lemma first_order_decidable_points_member : forall phi p,
  dense_member (first_order_decidable_points phi) p <->
  first_order_canonical_is_weakly_forced p phi \/
  first_order_canonical_is_weakly_forced p (semiformula_neg phi).
Proof. reflexivity. Qed.

Definition first_order_henkin_points (phi : semiproposition L 1) :
    dense_set canonical_order.
Proof.
  refine {| dense_member := fun p => forall q,
      preorder_le canonical_order q p ->
      first_order_canonical_is_weakly_forced q
        (Semiformula_exists phi) ->
      exists t : syntactic_term L,
        first_order_canonical_is_weakly_forced q
          (semiformula_substitute (fun _ : Fin.t 1 => t) phi) |}.
  intro p.
  pose proof (proj2 (@first_order_canonical_weak_completeness L D
      (Semiformula_or (Semiformula_exists phi)
        (semiformula_neg (Semiformula_exists phi))))
    (first_order_lk_provable_em (Semiformula_exists phi))) as Hem.
  destruct (proj1 (@first_order_canonical_is_weakly_forced_or L D p
      (Semiformula_exists phi)
      (semiformula_neg (Semiformula_exists phi))) (Hem p) p
      (preorder_refl _ p)) as [q [Hqp [Hex | Hnex]]].
  - destruct (proj1 (@first_order_canonical_is_weakly_forced_exists L
        D q phi) Hex q (preorder_refl _ q))
      as [r [Hrq [t Ht]]].
    exists r. split.
    + exact (@preorder_trans _ canonical_order r q p Hrq Hqp).
    + intros s Hsr _. exists t.
      exact (first_order_canonical_is_weakly_forced_monotone Hsr Ht).
  - exists q. split; [exact Hqp |].
    intros r Hrq Hrex.
    destruct (proj1 (@first_order_canonical_is_weakly_forced_exists L
        D r phi) Hrex r (preorder_refl _ r))
      as [s [Hsr [t Ht]]].
    exfalso.
    assert (Hnall : first_order_canonical_is_weakly_forced q
        (Semiformula_all (semiformula_neg phi))).
    { exact Hnex. }
    pose proof (proj1 (first_order_canonical_is_weakly_forced_all
        q (semiformula_neg phi)) Hnall t) as Hnsub.
    assert (Hnsub' : first_order_canonical_is_weakly_forced q
        (semiformula_neg
          (semiformula_substitute (fun _ : Fin.t 1 => t) phi))).
    { eapply first_order_canonical_is_weakly_forced_cast.
      - unfold semiformula_substitute. apply semiformula_rewrite_neg.
      - exact Hnsub. }
    pose proof (first_order_canonical_is_weakly_forced_monotone
      (@preorder_trans _ canonical_order s r q Hsr Hrq) Hnsub') as Hsn.
    exact ((proj1 (first_order_canonical_is_weakly_forced_not D s _)
      Hsn) s (preorder_refl _ s) Ht).
Defined.

Lemma first_order_henkin_points_member : forall phi p,
  dense_member (first_order_henkin_points phi) p <->
  forall q, preorder_le canonical_order q p ->
    first_order_canonical_is_weakly_forced q
      (Semiformula_exists phi) ->
    exists t : syntactic_term L,
      first_order_canonical_is_weakly_forced q
        (semiformula_substitute (fun _ : Fin.t 1 => t) phi).
Proof. reflexivity. Qed.

Definition first_order_dense_requirements
    (d : dense_set canonical_order) : Prop :=
  (exists phi : proposition L, forall p,
      dense_member d p <->
      dense_member (first_order_decidable_points phi) p) \/
  (exists phi : semiproposition L 1, forall p,
      dense_member d p <->
      dense_member (first_order_henkin_points phi) p).

Definition nat_encoding : encoding nat :=
  {| encode := fun n => n;
     decode := fun n => Some n;
     decode_encode := fun _ => eq_refl |}.

Definition encoding_enumerate {A} (default : A) (E : encoding A)
    (n : nat) : A :=
  match decode E n with Some x => x | None => default end.

Lemma encoding_enumerate_encode : forall A (default : A)
    (E : encoding A) x,
  encoding_enumerate default E (encode E x) = x.
Proof. intros. unfold encoding_enumerate. now rewrite decode_encode. Qed.

Local Definition proposition_encoding : encoding (proposition L) :=
  semiformula_encoding 0 EL nat_encoding.

Local Definition semiproposition_one_encoding :
    encoding (semiproposition L 1) :=
  semiformula_encoding 1 EL nat_encoding.

Definition first_order_dense_requirement_enum (n : nat) :
    dense_set canonical_order :=
  if Nat.even n then
    first_order_decidable_points
      (encoding_enumerate (@Semiformula_verum L nat 0)
        proposition_encoding
        (Nat.div2 n))
  else
    first_order_henkin_points
      (encoding_enumerate (@Semiformula_verum L nat 1)
        semiproposition_one_encoding
        (Nat.div2 n)).

Lemma first_order_dense_requirement_enum_member : forall n,
  first_order_dense_requirements
    (first_order_dense_requirement_enum n).
Proof.
  intro n. unfold first_order_dense_requirement_enum.
  destruct (Nat.even n).
  - left. eexists. intro p. reflexivity.
  - right. eexists. intro p. reflexivity.
Qed.

Theorem first_order_dense_requirements_countable :
  dense_family_countable first_order_dense_requirements.
Proof.
  right. exists first_order_dense_requirement_enum. split.
  - apply first_order_dense_requirement_enum_member.
  - intros d [[phi Hd] | [phi Hd]].
    + exists (2 * encode proposition_encoding phi). intro p.
      rewrite Hd. unfold first_order_dense_requirement_enum.
      assert (Heven : Nat.even (2 * encode proposition_encoding phi) = true).
      { rewrite Nat.even_mul. reflexivity. }
      rewrite Heven, Nat.div2_double, encoding_enumerate_encode.
      reflexivity.
    + exists (S (2 * encode semiproposition_one_encoding phi)). intro p.
      rewrite Hd. unfold first_order_dense_requirement_enum.
      assert (Heven :
          Nat.even (S (2 * encode semiproposition_one_encoding phi)) = false).
      { rewrite Nat.even_succ, Nat.odd_mul. reflexivity. }
      rewrite Heven, Nat.div2_succ_double, encoding_enumerate_encode.
      reflexivity.
Qed.

Theorem first_order_exists_generic_pfilter : forall p,
  exists G : order_pfilter canonical_order,
    pfilter_generic G first_order_dense_requirements /\
    pfilter_member G p.
Proof.
  apply (exists_generic_pfilter_of_countable
    first_order_dense_requirements_countable).
Qed.

End GenericRequirements.

Section GenericForcing.

Universe u.
Context {L : language@{Set u}} (D : language_decidable_eq L)
  (EL : language_encodable L).

Local Definition generic_canonical_order :=
  first_order_canonical_world_order L.

Definition first_order_generic_pfilter
    (p : first_order_canonical_world L) :
    order_pfilter generic_canonical_order :=
  proj1_sig (constructive_indefinite_description
    (fun G =>
      pfilter_generic G (first_order_dense_requirements D) /\
      pfilter_member G p)
    (first_order_exists_generic_pfilter D EL p)).

Lemma first_order_generic_pfilter_generic : forall p,
  pfilter_generic (first_order_generic_pfilter p)
    (first_order_dense_requirements D).
Proof.
  intro p. unfold first_order_generic_pfilter.
  exact (proj1 (proj2_sig (constructive_indefinite_description
    (fun G =>
      pfilter_generic G (first_order_dense_requirements D) /\
      pfilter_member G p)
    (first_order_exists_generic_pfilter D EL p)))).
Qed.

Lemma first_order_generic_pfilter_contains : forall p,
  pfilter_member (first_order_generic_pfilter p) p.
Proof.
  intro p. unfold first_order_generic_pfilter.
  exact (proj2 (proj2_sig (constructive_indefinite_description
    (fun G =>
      pfilter_generic G (first_order_dense_requirements D) /\
      pfilter_member G p)
    (first_order_exists_generic_pfilter D EL p)))).
Qed.

Definition first_order_generic_forces
    (p : first_order_canonical_world L) (phi : proposition L) : Prop :=
  exists q, pfilter_member (first_order_generic_pfilter p) q /\
    first_order_canonical_is_weakly_forced q phi.

Lemma first_order_generic_forces_cast : forall p phi psi,
  phi = psi ->
  first_order_generic_forces p phi ->
  first_order_generic_forces p psi.
Proof. intros p phi psi -> H; exact H. Qed.

Lemma first_order_generic_forces_em : forall p phi,
  first_order_generic_forces p phi \/
  first_order_generic_forces p (semiformula_neg phi).
Proof.
  intros p phi.
  assert (Hreq : first_order_dense_requirements D
      (first_order_decidable_points D phi)).
  { left. exists phi. intro r. reflexivity. }
  destruct (first_order_generic_pfilter_generic p Hreq)
    as [q [HqG Hq]].
  destruct Hq as [Hphi | Hneg].
  - left. now exists q.
  - right. now exists q.
Qed.

Lemma first_order_generic_forces_neg : forall p phi,
  first_order_generic_forces p (semiformula_neg phi) <->
  ~ first_order_generic_forces p phi.
Proof.
  intros p phi. split.
  - intros [q0 [Hq0G Hq0]] [q1 [Hq1G Hq1]].
    destruct (@pfilter_directed _ _ (first_order_generic_pfilter p)
        q0 q1 Hq0G Hq1G) as [r [HrG [Hr0 Hr1]]].
    pose proof (first_order_canonical_is_weakly_forced_monotone
      Hr1 Hq1) as Hrphi.
    exact ((proj1 (@first_order_canonical_is_weakly_forced_not L
      D q0 phi) Hq0) r Hr0 Hrphi).
  - intro Hnot.
    destruct (first_order_generic_forces_em p phi) as [Hphi | Hneg].
    + exfalso. exact (Hnot Hphi).
    + exact Hneg.
Qed.

Lemma first_order_generic_forces_verum : forall p,
  first_order_generic_forces p (@Semiformula_verum L nat 0).
Proof.
  intro p. exists p. split.
  - apply first_order_generic_pfilter_contains.
  - apply first_order_canonical_is_weakly_forced_verum.
Qed.

Lemma first_order_generic_forces_not_falsum : forall p,
  ~ first_order_generic_forces p (@Semiformula_falsum L nat 0).
Proof.
  intros p [q [_ Hq]].
  exact (first_order_canonical_is_weakly_forced_falsum Hq).
Qed.

Lemma first_order_generic_forces_nrel : forall p k
    (R : language_rel L k) (v : Fin.t k -> syntactic_term L),
  first_order_generic_forces p (Semiformula_nrel R v) <->
  ~ first_order_generic_forces p (Semiformula_rel R v).
Proof.
  intros. change (first_order_generic_forces p
    (semiformula_neg (Semiformula_rel R v)) <->
    ~ first_order_generic_forces p (Semiformula_rel R v)).
  apply first_order_generic_forces_neg.
Qed.

Lemma first_order_generic_forces_henkin : forall p
    (phi : semiproposition L 1),
  first_order_generic_forces p (Semiformula_exists phi) ->
  exists t : syntactic_term L,
    first_order_generic_forces p
      (semiformula_substitute (fun _ : Fin.t 1 => t) phi).
Proof.
  intros p phi.
  assert (Hreq : first_order_dense_requirements D
      (first_order_henkin_points D phi)).
  { right. exists phi. intro r. reflexivity. }
  destruct (first_order_generic_pfilter_generic p Hreq)
    as [q [HqG Hq]].
  intros [r [HrG Hr]].
  destruct (@pfilter_directed _ _ (first_order_generic_pfilter p)
      q r HqG HrG) as [z [HzG [Hzq Hzr]]].
  destruct (Hq z Hzq
    (first_order_canonical_is_weakly_forced_monotone Hzr Hr))
    as [t Ht].
  exists t, z. now split.
Qed.

Lemma first_order_generic_forces_exists : forall p
    (phi : semiproposition L 1),
  first_order_generic_forces p (Semiformula_exists phi) <->
  exists t : syntactic_term L,
    first_order_generic_forces p
      (semiformula_substitute (fun _ : Fin.t 1 => t) phi).
Proof.
  intros p phi. split.
  - apply first_order_generic_forces_henkin.
  - intros [t [q [HqG Hq]]]. exists q. split; [exact HqG |].
    apply (proj2 (@first_order_canonical_is_weakly_forced_exists L
      D q phi)).
    intros r Hrq. exists r. split; [apply preorder_refl |].
    exists t. exact (first_order_canonical_is_weakly_forced_monotone
      Hrq Hq).
Qed.

Lemma first_order_generic_forces_all : forall p
    (phi : semiproposition L 1),
  first_order_generic_forces p (Semiformula_all phi) <->
  forall t : syntactic_term L,
    first_order_generic_forces p
      (semiformula_substitute (fun _ : Fin.t 1 => t) phi).
Proof.
  intros p phi. split.
  - intro Hall.
    assert (Heq : semiformula_neg
        (Semiformula_exists (semiformula_neg phi)) =
        Semiformula_all phi).
    { cbn. f_equal. apply semiformula_neg_involutive. }
    assert (Hall' : first_order_generic_forces p
        (semiformula_neg
          (Semiformula_exists (semiformula_neg phi)))).
    { eapply first_order_generic_forces_cast.
      - symmetry. exact Heq.
      - exact Hall. }
    assert (Hnotex : ~ first_order_generic_forces p
        (Semiformula_exists (semiformula_neg phi))).
    { apply (proj1 (first_order_generic_forces_neg p
        (Semiformula_exists (semiformula_neg phi)))). exact Hall'. }
    intro t.
    destruct (first_order_generic_forces_em p
        (semiformula_substitute (fun _ : Fin.t 1 => t) phi))
      as [Ht | Hnt]; [exact Ht |].
    apply False_rect. apply Hnotex.
    apply (proj2 (first_order_generic_forces_exists p
      (semiformula_neg phi))).
    exists t. eapply first_order_generic_forces_cast.
    + unfold semiformula_substitute. symmetry.
      apply semiformula_rewrite_neg.
    + exact Hnt.
  - intro Hall.
    assert (Heq : semiformula_neg
        (Semiformula_exists (semiformula_neg phi)) =
        Semiformula_all phi).
    { cbn. f_equal. apply semiformula_neg_involutive. }
    assert (Hnegex : first_order_generic_forces p
        (semiformula_neg
          (Semiformula_exists (semiformula_neg phi)))).
    { apply (proj2 (first_order_generic_forces_neg p
        (Semiformula_exists (semiformula_neg phi)))).
      intros Hex.
      destruct (proj1 (first_order_generic_forces_exists p
        (semiformula_neg phi)) Hex) as [t Hnt].
      assert (Hnt' : first_order_generic_forces p
          (semiformula_neg
            (semiformula_substitute (fun _ : Fin.t 1 => t) phi))).
      { eapply first_order_generic_forces_cast.
        - unfold semiformula_substitute. apply semiformula_rewrite_neg.
        - exact Hnt. }
      exact ((proj1 (first_order_generic_forces_neg p _) Hnt') (Hall t)). }
    eapply first_order_generic_forces_cast.
    + exact Heq.
    + exact Hnegex.
Qed.

Lemma first_order_generic_forces_and : forall p phi psi,
  first_order_generic_forces p (Semiformula_and phi psi) <->
  first_order_generic_forces p phi /\
  first_order_generic_forces p psi.
Proof.
  intros p phi psi. split.
  - intros [q [HqG Hq]].
    destruct (proj1 (first_order_canonical_is_weakly_forced_and
      q phi psi) Hq) as [Hphi Hpsi].
    split; exists q; now split.
  - intros [[q1 [Hq1G Hq1]] [q2 [Hq2G Hq2]]].
    destruct (@pfilter_directed _ _ (first_order_generic_pfilter p)
        q1 q2 Hq1G Hq2G) as [r [HrG [Hr1 Hr2]]].
    exists r. split; [exact HrG |].
    apply (proj2 (first_order_canonical_is_weakly_forced_and r phi psi)).
    split.
    + exact (first_order_canonical_is_weakly_forced_monotone Hr1 Hq1).
    + exact (first_order_canonical_is_weakly_forced_monotone Hr2 Hq2).
Qed.

Lemma first_order_generic_forces_or : forall p phi psi,
  first_order_generic_forces p (Semiformula_or phi psi) <->
  first_order_generic_forces p phi \/
  first_order_generic_forces p psi.
Proof.
  intros p phi psi. split.
  - intros [q [HqG Hq]].
    destruct (classic (first_order_generic_forces p phi)) as [Hphi | Hphi].
    + now left.
    + right. apply NNPP. intro Hpsi.
      pose proof (proj2 (first_order_generic_forces_neg p phi) Hphi)
        as Hnphi.
      pose proof (proj2 (first_order_generic_forces_neg p psi) Hpsi)
        as Hnpsi.
      destruct Hnphi as [q1 [Hq1G Hq1]].
      destruct Hnpsi as [q2 [Hq2G Hq2]].
      destruct (@pfilter_directed _ _ (first_order_generic_pfilter p)
          q q1 HqG Hq1G) as [r [HrG [Hrq Hr1]]].
      destruct (@pfilter_directed _ _ (first_order_generic_pfilter p)
          r q2 HrG Hq2G) as [s [HsG [Hsr Hs2]]].
      destruct (proj1 (@first_order_canonical_is_weakly_forced_or L
          D q phi psi) Hq s
        (@preorder_trans _ generic_canonical_order s r q Hsr Hrq))
        as [z [Hzs [Hzphi | Hzpsi]]].
      * pose proof (first_order_canonical_is_weakly_forced_monotone
          (@preorder_trans _ generic_canonical_order z s r Hzs Hsr)
          (first_order_canonical_is_weakly_forced_monotone Hr1 Hq1))
          as Hzneg.
        exact ((proj1 (first_order_canonical_is_weakly_forced_not
          D z phi) Hzneg) z (preorder_refl _ z) Hzphi).
      * pose proof (first_order_canonical_is_weakly_forced_monotone
          (@preorder_trans _ generic_canonical_order z s q2 Hzs Hs2) Hq2)
          as Hzneg.
        exact ((proj1 (first_order_canonical_is_weakly_forced_not
          D z psi) Hzneg) z (preorder_refl _ z) Hzpsi).
  - intros [Hphi | Hpsi].
    + destruct Hphi as [q [HqG Hq]]. exists q. split; [exact HqG |].
      apply (proj2 (@first_order_canonical_is_weakly_forced_or L
        D q phi psi)).
      intros r Hrq. exists r. split; [apply preorder_refl |].
      left. exact (first_order_canonical_is_weakly_forced_monotone Hrq Hq).
    + destruct Hpsi as [q [HqG Hq]]. exists q. split; [exact HqG |].
      apply (proj2 (@first_order_canonical_is_weakly_forced_or L
        D q phi psi)).
      intros r Hrq. exists r. split; [apply preorder_refl |].
      right. exact (first_order_canonical_is_weakly_forced_monotone Hrq Hq).
Qed.

End GenericForcing.

Section TermModel.

Universe u.
Context {L : language@{Set u}} (D : language_decidable_eq L)
  (EL : language_encodable L).

Definition first_order_generic_term_structure
    (p : first_order_canonical_world L) :
    first_order_structure L (syntactic_term L) :=
  {| structure_func := fun _ f v => Semiterm_func f v;
     structure_rel := fun _ R v =>
       first_order_generic_forces D EL p (Semiformula_rel R v) |}.

Lemma first_order_generic_term_structure_func : forall p k
    (f : language_func L k) (v : Fin.t k -> syntactic_term L),
  structure_func (first_order_generic_term_structure p) f v =
  Semiterm_func f v.
Proof. reflexivity. Qed.

Lemma first_order_generic_term_structure_rel : forall p k
    (R : language_rel L k) (v : Fin.t k -> syntactic_term L),
  structure_rel (first_order_generic_term_structure p) R v <->
  first_order_generic_forces D EL p (Semiformula_rel R v).
Proof. reflexivity. Qed.

Lemma first_order_generic_term_val : forall p X n
    (t : semiterm L X n) (fv : X -> syntactic_term L)
    (bv : Fin.t n -> syntactic_term L),
  semiterm_val (first_order_generic_term_structure p) bv fv t =
  rew_apply (rew_bind bv fv) t.
Proof.
  intros p X n t; induction t as [i | x | k f v IH];
    intros fv bv; simpl; try reflexivity.
  f_equal. apply functional_extensionality. intro i. apply IH.
Qed.

(** Instantiating the lifted rewrite under one binder is the same rewrite as
    extending the bound-variable environment.  This is useful independently
    of forcing and isolates the only de Bruijn calculation in the truth
    lemma. *)
Lemma rew_substitute_q_bind : forall X n (bv : Fin.t n -> syntactic_term L)
    (fv : X -> syntactic_term L) (t : syntactic_term L),
  rew_equiv
    (rew_comp (rew_subst (fun _ : Fin.t 1 => t))
      (rew_q (rew_bind bv fv)))
    (rew_bind (fin_env_cons t bv) fv).
Proof.
  intros X n bv fv t. apply rew_equiv_of_variables.
  - intro i. refine (@Fin.caseS' n i (fun j =>
      rew_apply
        (rew_comp (rew_subst (fun _ : Fin.t 1 => t))
          (rew_q (rew_bind bv fv))) (Semiterm_bvar j) =
      rew_apply (rew_bind (fin_env_cons t bv) fv)
        (Semiterm_bvar j)) _ _).
    + reflexivity.
    + intro j. cbn. apply rew_subst_bshift_zero.
  - intro x. cbn. apply rew_subst_bshift_zero.
Qed.

Lemma semiformula_substitute_q_bind : forall X n
    (phi : semiformula L X (S n))
    (bv : Fin.t n -> syntactic_term L)
    (fv : X -> syntactic_term L) (t : syntactic_term L),
  semiformula_substitute (fun _ : Fin.t 1 => t)
      (semiformula_rewrite (rew_q (rew_bind bv fv)) phi) =
  semiformula_rewrite (rew_bind (fin_env_cons t bv) fv) phi.
Proof.
  intros. unfold semiformula_substitute.
  rewrite <- semiformula_rewrite_comp.
  apply semiformula_rewrite_ext, rew_substitute_q_bind.
Qed.

Theorem first_order_generic_forcing_lemma : forall p X n
    (phi : semiformula L X n) (fv : X -> syntactic_term L)
    (bv : Fin.t n -> syntactic_term L),
  semiformula_eval (first_order_generic_term_structure p) bv fv phi <->
  first_order_generic_forces D EL p
    (semiformula_rewrite (rew_bind bv fv) phi).
Proof.
  intros p X n phi; induction phi as
    [n | n | n k R v | n k R v |
     n phi IHphi psi IHpsi | n phi IHphi psi IHpsi |
     n phi IHphi | n phi IHphi]; intros fv bv; simpl.
  - split; intro; [apply first_order_generic_forces_verum | exact I].
  - split.
    + contradiction.
    + intro H. exfalso. exact (first_order_generic_forces_not_falsum H).
  - assert (Hv :
        (fun i => semiterm_val (first_order_generic_term_structure p)
          bv fv (v i)) =
        (fun i => rew_apply (rew_bind bv fv) (v i))).
    { apply functional_extensionality. intro i.
      apply first_order_generic_term_val. }
    rewrite Hv. reflexivity.
  - assert (Hv :
        (fun i => semiterm_val (first_order_generic_term_structure p)
          bv fv (v i)) =
        (fun i => rew_apply (rew_bind bv fv) (v i))).
    { apply functional_extensionality. intro i.
      apply first_order_generic_term_val. }
    rewrite Hv. symmetry. apply first_order_generic_forces_nrel.
  - rewrite IHphi, IHpsi, first_order_generic_forces_and.
    reflexivity.
  - rewrite IHphi, IHpsi, first_order_generic_forces_or.
    reflexivity.
  - rewrite first_order_generic_forces_all. split; intros H t.
    + specialize (H t).
      apply (proj1 (IHphi fv (fin_env_cons t bv))) in H.
      eapply first_order_generic_forces_cast.
      * symmetry. apply semiformula_substitute_q_bind.
      * exact H.
    + apply (proj2 (IHphi fv (fin_env_cons t bv))).
      eapply first_order_generic_forces_cast.
      * apply semiformula_substitute_q_bind.
      * exact (H t).
  - rewrite first_order_generic_forces_exists. split.
    + intros [t Ht]. exists t.
      apply (proj1 (IHphi fv (fin_env_cons t bv))) in Ht.
      eapply first_order_generic_forces_cast.
      * symmetry. apply semiformula_substitute_q_bind.
      * exact Ht.
    + intros [t Ht]. exists t.
      apply (proj2 (IHphi fv (fin_env_cons t bv))).
      eapply first_order_generic_forces_cast.
      * apply semiformula_substitute_q_bind.
      * exact Ht.
Qed.

Lemma semiformula_rewrite_bind_identity : forall
    (bv : Fin.t 0 -> syntactic_term L) (phi : proposition L),
  semiformula_rewrite
    (rew_bind bv first_order_identity_free_env)
    phi = phi.
Proof.
  intros bv phi.
  assert (Hb : bv = first_order_empty_bound_env).
  { apply functional_extensionality. intro i. inversion i. }
  subst bv. transitivity (semiformula_rewrite rew_id phi).
  - apply semiformula_rewrite_ext. intro t.
    apply first_order_rew_apply_bind_identity.
  - apply semiformula_rewrite_id.
Qed.

Theorem first_order_generic_reflection : forall (phi : proposition L)
    (H : ~ first_order_lk_provable (semiformula_neg phi)),
  formula_eval
    (first_order_generic_term_structure
      (first_order_canonical_world_of_unprovable (phi := phi) H))
    first_order_identity_free_env phi.
Proof.
  intros phi H.
  unfold formula_eval.
  apply (proj2 (first_order_generic_forcing_lemma
    (first_order_canonical_world_of_unprovable (phi := phi) H)
    phi first_order_identity_free_env
    (fun i : Fin.t 0 => match i with end))).
  rewrite semiformula_rewrite_bind_identity.
  exists (first_order_canonical_world_of_unprovable (phi := phi) H). split.
  - apply first_order_generic_pfilter_contains.
  - apply first_order_canonical_weak_reflection.
Qed.

End TermModel.

(** Classical equality is used only to number the finitely many symbols that
    occur in the input sentence.  The constructed sublanguage itself has
    computational finite equality and encodings. *)
Definition classical_language_decidable_eq (L : language) :
    language_decidable_eq L :=
  @Build_language_decidable_eq L
    (fun _ x y => excluded_middle_informative (x = y))
    (fun _ x y => excluded_middle_informative (x = y)).

Theorem first_order_satisfiable_of_irrefutable : forall L
    (sigma : sentence L),
  ~ first_order_lk_provable
      (semiformula_neg (first_order_sentence_embed sigma)) ->
  first_order_satisfiable (fun tau => tau = sigma).
Proof.
  intros L sigma Hsigma.
  pose (D := classical_language_decidable_eq L).
  pose (rho := first_order_sentence_embed sigma).
  pose (K := semiformula_predicate_sublanguage rho).
  pose (pi := (semiformula_to_predicate_sublanguage rho : proposition K)).
  pose (h := (@language_sublanguage_unsub L
    (fun k f => In f (semiformula_function_symbols rho k))
    (fun k r => In r (semiformula_relation_symbols rho k)) :
      language_hom K L)).
  assert (Hmap : semiformula_language_map h pi = rho).
  { apply semiformula_language_map_to_predicate_sublanguage. }
  assert (Hpi : ~ first_order_lk_provable
      (semiformula_neg pi)).
  { intro Hprov. apply Hsigma.
    pose proof (first_order_lk_provable_language_map h Hprov) as Hmapped.
    assert (Heq : semiformula_language_map h (semiformula_neg pi) =
        semiformula_neg rho).
    { etransitivity.
      - apply semiformula_language_map_neg.
      - exact (f_equal semiformula_neg Hmap). }
    exact (first_order_lk_provable_cast Hmapped Heq). }
  pose (DK := @language_sublanguage_decidable_eq L
    (fun k f => In f (semiformula_function_symbols rho k))
    (fun k r => In r (semiformula_relation_symbols rho k)) D).
  pose (EK := semiformula_predicate_sublanguage_encodable D rho).
  pose (p := first_order_canonical_world_of_unprovable (phi := pi) Hpi).
  pose (SK := @first_order_generic_term_structure K DK EK p).
  assert (Hpi_model : formula_eval SK first_order_identity_free_env pi).
  { exact (@first_order_generic_reflection K DK EK pi Hpi). }
  pose (mK := first_order_model_of_structure
    (inhabits (@Semiterm_fvar K nat 0 0)) SK).
  pose (mL := first_order_model_extend h mK).
  exists mL. constructor. intros tau Htau. subst tau.
  apply (proj1 (first_order_sentence_embed_eval
    (first_order_model_structure mL) first_order_identity_free_env sigma)).
  assert (Hmapped : formula_eval (first_order_model_structure mL)
      first_order_identity_free_env (semiformula_language_map h pi)).
  { unfold formula_eval in Hpi_model |- *.
    apply (proj2 (@semiformula_eval_language_map_extend K L
      (syntactic_term K) (inhabits (@Semiterm_fvar K nat 0 0))
      h language_sublanguage_unsub_injective SK
      nat 0 pi
      (fun i : Fin.t 0 => match i with end)
      first_order_identity_free_env)).
    exact Hpi_model. }
  unfold rho in Hmap. now rewrite Hmap in Hmapped.
Qed.

(** * Theory-level completeness *)

Lemma first_order_model_realize_list_conj2 : forall L
    (m : first_order_model L) (Gamma : list (sentence L)),
  first_order_model_realize m
      (generic_list_conj2 (sentence_connectives L) Gamma) <->
  forall sigma, In sigma Gamma -> first_order_model_realize m sigma.
Proof.
  intros L m Gamma.
  exact (@generic_models_list_conj2
    (first_order_model L) (sentence L) (sentence_connectives L)
    (first_order_semantics L) (first_order_semantics_top L)
    (first_order_semantics_and L) m Gamma).
Qed.

Lemma first_order_raw_list_member_in : forall A (x : A) xs,
  generic_raw_list_member x xs -> In x xs.
Proof.
  intros A x xs H. induction H.
  - now left.
  - now right.
Qed.

Definition first_order_theory_explosion (L : language) :
    generic_deductive_explosion
      (first_order_theory_entailment L)
      (generic_bottom (sentence_connectives L)) :=
  @generic_deductive_explosion_of_classical
    (theory L) (sentence L)
    (first_order_theory_entailment L) (sentence_connectives L)
    (@first_order_theory_classical L).

(** Completeness I: compactness reduces consistency to a single finite
    conjunction, whose singleton countermodel is supplied by the generic term
    model above. *)
Theorem first_order_satisfiable_of_consistent : forall L (T : theory L),
  generic_consistent (first_order_theory_entailment L) T ->
  first_order_satisfiable T.
Proof.
  intros L T Hconsistent.
  apply (proj2 (first_order_compactness T)).
  intros Gamma Hsubset.
  pose (sigma := generic_list_conj2 (sentence_connectives L) Gamma).
  assert (Hsigma : first_order_theory_provable T sigma).
  { constructor. apply (generic_minimal_list_conj2_intro_raw
      (generic_minimal_of_classical (first_order_theory_classical T))).
    intros tau Htau.
    apply (generic_axiomatized_by_axiom_raw
      (first_order_theory_axiomatized L)).
    apply Hsubset. now apply first_order_raw_list_member_in. }
  assert (Hirrefutable : ~ first_order_lk_provable
      (semiformula_neg (first_order_sentence_embed sigma))).
  { intro Hneg_lk.
    assert (Hneg : first_order_theory_provable T (semiformula_neg sigma)).
    { apply first_order_theory_of_lk_provable.
      change (first_order_lk_provable
        (first_order_sentence_embed (semiformula_neg sigma))).
      eapply first_order_lk_provable_cast; [exact Hneg_lk |].
      symmetry. apply first_order_sentence_embed_neg. }
    destruct Hsigma as [dsigma]. destruct Hneg as [dneg].
    apply (@generic_consistent_not_bottom
      (theory L) (sentence L) (first_order_theory_entailment L)
      (generic_bottom (sentence_connectives L))
      (first_order_theory_explosion L) T Hconsistent).
    constructor. exact (generic_minimal_neg_mdp_raw
      (generic_minimal_of_classical (first_order_theory_classical T))
      sigma dneg dsigma). }
  destruct (@first_order_satisfiable_of_irrefutable L sigma Hirrefutable)
    as [m Hm].
  exists m. apply (proj2 (first_order_models_theory_iff m _)).
  intros tau Htau.
  apply (proj1 (first_order_model_realize_list_conj2 m Gamma)).
  exact (first_order_models_of_member Hm eq_refl).
  exact Htau.
Qed.

Theorem first_order_satisfiable_iff_consistent : forall L (T : theory L),
  first_order_satisfiable T <->
  generic_consistent (first_order_theory_entailment L) T.
Proof.
  intros L T. split.
  - apply first_order_theory_consistent_of_satisfiable.
  - apply first_order_satisfiable_of_consistent.
Qed.

(** Completeness II: if a consequence were unprovable, adjoining its
    negation would remain consistent and hence have a model. *)
Theorem first_order_theory_proof_complete : forall L
    (T : theory L) (sigma : sentence L),
  first_order_consequence T sigma ->
  first_order_theory_provable T sigma.
Proof.
  intros L T sigma Hconsequence. apply NNPP. intro Hunprovable.
  pose (Tneg := generic_adjunctive_adjoin
    (generic_predicate_adjunctive_set (sentence L))
    (semiformula_neg sigma) T).
  assert (Hconsistent :
    generic_consistent (first_order_theory_entailment L) Tneg).
  { apply (proj1 (@generic_classical_unprovable_iff_consistent_adjoin
      (theory L) (sentence L) (first_order_theory_entailment L)
      (sentence_connectives L)
      (generic_predicate_adjunctive_set (sentence L))
      (first_order_theory_axiomatized L)
      (first_order_theory_deduction L) T sigma
      (first_order_theory_classical T)
      (generic_intuitionistic_of_classical
        (first_order_theory_classical Tneg)))).
    exact Hunprovable. }
  destruct (first_order_satisfiable_of_consistent Hconsistent) as [m Hm].
  assert (HT : first_order_models_theory m T).
  { eapply first_order_models_of_subset; [exact Hm |].
    intros tau Htau. unfold Tneg. now right. }
  assert (Hneg : first_order_model_realize m (semiformula_neg sigma)).
  { apply (first_order_models_of_member Hm).
    unfold Tneg. now left. }
  unfold first_order_model_realize, sentence_realize, formula_eval in Hneg.
  apply (proj1 (semiformula_eval_neg
    (first_order_model_structure m)
    (fun i : Fin.t 0 => match i with end)
    (fun x : Empty_set => match x with end) sigma)) in Hneg.
  exact (Hneg (Hconsequence m HT)).
Qed.

Theorem first_order_theory_proof_complete_iff : forall L
    (T : theory L) (sigma : sentence L),
  first_order_consequence T sigma <->
  first_order_theory_provable T sigma.
Proof.
  intros L T sigma. split.
  - apply first_order_theory_proof_complete.
  - apply first_order_theory_proof_sound.
Qed.

(** A reusable form of completeness restricted to a semantic class.  The
    source specializes [C] to structures interpreting equality literally and
    obtains [normalize] from its quotient-model construction.  Stating the
    reduction separately exposes the precise model-theoretic ingredient and
    applies equally to any elementary normalization. *)
Theorem first_order_theory_proof_complete_on_model_class : forall L
    (T : theory L) (sigma : sentence L)
    (C : first_order_model L -> Prop),
  (forall m, first_order_models_theory m T ->
    exists n,
      C n /\
      first_order_elementary_equiv m n /\
      first_order_models_theory n T) ->
  (forall m, C m -> first_order_models_theory m T ->
    first_order_model_realize m sigma) ->
  first_order_theory_provable T sigma.
Proof.
  intros L T sigma C normalize Hrestricted.
  apply first_order_theory_proof_complete.
  intros m Hm.
  destruct (normalize m Hm) as [n [HC [Hequiv Hn]]].
  apply (proj2 (first_order_elementary_equiv_realize Hequiv sigma)).
  exact (Hrestricted n HC Hn).
Qed.
