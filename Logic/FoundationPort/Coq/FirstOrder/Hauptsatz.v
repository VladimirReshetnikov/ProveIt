(** Canonical forcing infrastructure for first-order cut elimination. *)

From Stdlib Require Import Logic.FunctionalExtensionality Lists.List Vectors.Fin.
From FoundationModal Require Import GenericCalculus.
From Foundation.Syntax.Predicate Require Import Language Term Relational Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Intuitionistic Require Import Formula Rew.
From Foundation.FirstOrder.Basic Require Import Calculus CutFree.
From Foundation.FirstOrder.Kripke Require Import WeakForcing.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** Positive rules cannot introduce cuts.  This is stated independently of
    the initial sequent and therefore applies to every later canonical-model
    use of the shared positive-derivation algebra. *)
Fixpoint first_order_positive_derivation_graft_cut_free {L Xi Gamma}
    (b : first_order_derivation L Xi)
    (d : @first_order_positive_derivation_from L Xi Gamma)
    (Hb : first_order_is_cut_free b) :
    first_order_is_cut_free (first_order_positive_derivation_graft b d).
Proof.
  destruct d as [phi psi Delta d | phi t Delta d |
    Delta Theta d Hsub |].
  - apply FOCFOr.
    exact (@first_order_positive_derivation_graft_cut_free
      L Xi (phi :: psi :: Delta) b d Hb).
  - apply FOCFExists.
    exact (@first_order_positive_derivation_graft_cut_free
      L Xi
      (semiformula_substitute (fun _ : Fin.t 1 => t) phi :: Delta)
      b d Hb).
  - apply (FOCFContraction Hsub).
    exact (@first_order_positive_derivation_graft_cut_free
      L Xi Delta b d Hb).
  - exact Hb.
Defined.

(** [q] is stronger than [p] when the negated assumptions of [p] can be
    transformed into those of [q] using only positive LK rules.  Keeping the
    witness in [Type] is stronger than the source's propositionally truncated
    order instance and makes subsequent constructions executable. *)
Record first_order_stronger_than {L}
    (q p : first_order_sequent L) : Type := {
  first_order_stronger_derivation :
    @first_order_positive_derivation_from L
      (map semiformula_neg p) (map semiformula_neg q)
}.

Arguments first_order_stronger_derivation {L q p} _.

Definition first_order_stronger_than_refl {L}
    (p : first_order_sequent L) : first_order_stronger_than p p :=
  {| first_order_stronger_derivation := FOPDId |}.

Definition first_order_stronger_than_trans {L r q p}
    (srq : @first_order_stronger_than L r q)
    (sqp : @first_order_stronger_than L q p) :
    @first_order_stronger_than L r p :=
  {| first_order_stronger_derivation :=
       first_order_positive_derivation_trans
         (first_order_stronger_derivation sqp)
         (first_order_stronger_derivation srq) |}.

Definition first_order_stronger_than_of_subset {L q p}
    (Hsub : generic_list_subset p q) :
    @first_order_stronger_than L q p :=
  {| first_order_stronger_derivation :=
       first_order_positive_derivation_of_subset
         (@generic_list_map_subset _ _ semiformula_neg p q Hsub) |}.

Definition first_order_sequent_meet {L}
    (p q : first_order_sequent L) : first_order_sequent L := p ++ q.

Definition first_order_stronger_than_meet_left {L}
    (p q : first_order_sequent L) :
    first_order_stronger_than (first_order_sequent_meet p q) p.
Proof.
  apply first_order_stronger_than_of_subset.
  intros phi Hphi.
  apply (proj2 (generic_list_member_app_iff phi p q)). now left.
Defined.

Definition first_order_stronger_than_meet_right {L}
    (p q : first_order_sequent L) :
    first_order_stronger_than (first_order_sequent_meet p q) q.
Proof.
  apply first_order_stronger_than_of_subset.
  intros phi Hphi.
  apply (proj2 (generic_list_member_app_iff phi p q)). now right.
Defined.

Definition first_order_stronger_than_and {L}
    (p : first_order_sequent L) (phi psi : proposition L) :
    first_order_stronger_than
      (Semiformula_and phi psi :: p) (phi :: psi :: p).
Proof.
  constructor. cbn. exact (FOPDOr FOPDId).
Defined.

Definition first_order_stronger_than_and_left {L}
    (p : first_order_sequent L) (phi psi : proposition L) :
    first_order_stronger_than (Semiformula_and phi psi :: p) (phi :: p).
Proof.
  eapply first_order_stronger_than_trans.
  - exact (first_order_stronger_than_and p phi psi).
  - apply first_order_stronger_than_of_subset.
    intros a [Ha | Ha].
    + subst a. now left.
    + right. now right.
Defined.

Definition first_order_stronger_than_and_right {L}
    (p : first_order_sequent L) (phi psi : proposition L) :
    first_order_stronger_than (Semiformula_and phi psi :: p) (psi :: p).
Proof.
  eapply first_order_stronger_than_trans.
  - exact (first_order_stronger_than_and p phi psi).
  - apply first_order_stronger_than_of_subset.
    intros a [Ha | Ha].
    + subst a. right. now left.
    + right. now right.
Defined.

Definition first_order_stronger_than_all {L}
    (p : first_order_sequent L) (phi : semiproposition L 1)
    (t : syntactic_term L) :
    first_order_stronger_than (Semiformula_all phi :: p)
      (semiformula_substitute (fun _ : Fin.t 1 => t) phi :: p).
Proof.
  constructor.
  change (first_order_positive_derivation_from
    (semiformula_neg
       (semiformula_substitute (fun _ : Fin.t 1 => t) phi) ::
     map semiformula_neg p)
    (Semiformula_exists (semiformula_neg phi) ::
     map semiformula_neg p)).
  unfold semiformula_substitute.
  rewrite <- semiformula_rewrite_neg.
  exact (FOPDExs FOPDId).
Defined.

Definition first_order_stronger_than_meet {L r p q}
    (srp : @first_order_stronger_than L r p)
    (srq : @first_order_stronger_than L r q) :
    first_order_stronger_than r (first_order_sequent_meet p q).
Proof.
  constructor. unfold first_order_sequent_meet. rewrite map_app.
  apply (FOPDWeak (first_order_positive_derivation_add
    (first_order_stronger_derivation srp)
    (first_order_stronger_derivation srq))).
  intros a Ha.
  apply (proj1 (generic_list_member_app_iff a
    (map semiformula_neg r) (map semiformula_neg r))) in Ha.
  now destruct Ha.
Defined.

Definition first_order_stronger_than_meet_with_right {L q p}
    (sqp : @first_order_stronger_than L q p) :
    first_order_stronger_than q (first_order_sequent_meet p q) :=
  first_order_stronger_than_meet sqp (first_order_stronger_than_refl q).

(** The canonical forcing relation is generalized from propositions to
    arbitrary semiformulas equipped with syntactic valuations.  Quantifiers
    then recurse structurally on their bodies; the source proposition-level
    relation is the empty-bound, identity-free-valuation specialization. *)
Fixpoint first_order_canonical_forces_aux {L X n}
    (p : first_order_sequent L) (phi : ifo_semiformula L X n) :
    (Fin.t n -> syntactic_term L) -> (X -> syntactic_term L) -> Type :=
  match phi in ifo_semiformula _ _ n0 return
      (Fin.t n0 -> syntactic_term L) -> (X -> syntactic_term L) -> Type with
  | IFOFalsum => fun _ _ =>
      { b : first_order_derivation L (map semiformula_neg p) &
        first_order_is_cut_free b }
  | IFORel R v => fun bv fv =>
      { b : first_order_derivation L
          (Semiformula_rel R
            (fun i => rew_apply (rew_bind bv fv) (v i)) ::
           map semiformula_neg p) &
        first_order_is_cut_free b }
  | IFOAnd psi chi => fun bv fv =>
      (first_order_canonical_forces_aux p psi bv fv *
       first_order_canonical_forces_aux p chi bv fv)%type
  | IFOOr psi chi => fun bv fv =>
      (first_order_canonical_forces_aux p psi bv fv +
       first_order_canonical_forces_aux p chi bv fv)%type
  | IFOImp psi chi => fun bv fv =>
      forall q, first_order_stronger_than q p ->
        first_order_canonical_forces_aux q psi bv fv ->
        first_order_canonical_forces_aux q chi bv fv
  | IFOAll psi => fun bv fv =>
      forall t : syntactic_term L,
        first_order_canonical_forces_aux p psi (fin_cons t bv) fv
  | IFOExs psi => fun bv fv =>
      { t : syntactic_term L &
        first_order_canonical_forces_aux p psi (fin_cons t bv) fv }
  end.

Definition first_order_empty_bound_env {L} :
    Fin.t 0 -> syntactic_term L := fun i => Fin.case0 (fun _ => _) i.

Definition first_order_identity_free_env {L} :
    nat -> syntactic_term L := fun x => Semiterm_fvar x.

Definition first_order_canonical_forces {L}
    (p : first_order_sequent L) (phi : ifo_proposition L) : Type :=
  first_order_canonical_forces_aux p phi
    first_order_empty_bound_env first_order_identity_free_env.

Definition first_order_canonical_forces_all {L}
    (phi : ifo_proposition L) : Type :=
  forall p, first_order_canonical_forces p phi.

Record first_order_type_biequivalence (A B : Type) : Type := {
  first_order_type_biequivalence_forward : A -> B;
  first_order_type_biequivalence_backward : B -> A
}.

Arguments first_order_type_biequivalence_forward {A B} _ _.
Arguments first_order_type_biequivalence_backward {A B} _ _.

Lemma first_order_rew_apply_bind_comp : forall L X n Y m
    (rw : rew L X n Y m) (bv : Fin.t m -> syntactic_term L)
    (fv : Y -> syntactic_term L) (t : semiterm L X n),
  rew_apply (rew_bind bv fv) (rew_apply rw t) =
  rew_apply
    (rew_bind
      (fun i => rew_apply (rew_bind bv fv)
        (rew_apply rw (Semiterm_bvar i)))
      (fun x => rew_apply (rew_bind bv fv)
        (rew_apply rw (Semiterm_fvar x)))) t.
Proof.
  intros L X n Y m rw bv fv t.
  induction t as [i | x | k f v IH]; simpl; try reflexivity.
  rewrite rew_apply_func. cbn [rew_apply rew_bind rew_bind_aux]. f_equal.
  apply functional_extensionality. exact IH.
Qed.

Lemma first_order_rew_apply_bind_bshift : forall L X n
    (bv : Fin.t n -> syntactic_term L) (fv : X -> syntactic_term L)
    (x : syntactic_term L) (t : semiterm L X n),
  rew_apply (rew_bind (fin_cons x bv) fv)
    (rew_apply rew_bshift t) = rew_apply (rew_bind bv fv) t.
Proof.
  intros L X n bv fv x t.
  induction t as [i | y | k f v IH]; simpl; try reflexivity.
  f_equal.
  apply functional_extensionality. exact IH.
Qed.

Lemma first_order_rew_q_bind_bound : forall L X n Y m
    (rw : rew L X n Y m) (x : syntactic_term L)
    (bv : Fin.t m -> syntactic_term L) (fv : Y -> syntactic_term L),
  (fun i => rew_apply (rew_bind (fin_cons x bv) fv)
      (rew_apply (rew_q rw) (Semiterm_bvar i))) =
  fin_cons x
    (fun i => rew_apply (rew_bind bv fv)
      (rew_apply rw (Semiterm_bvar i))).
Proof.
  intros. apply functional_extensionality. intro i.
  refine (@Fin.caseS' _ i (fun j =>
    rew_apply (rew_bind (fin_cons x bv) fv)
      (rew_apply (rew_q rw) (Semiterm_bvar j)) =
    fin_cons x
      (fun u => rew_apply (rew_bind bv fv)
        (rew_apply rw (Semiterm_bvar u))) j) _ _).
  - rewrite rew_q_bvar_zero. reflexivity.
  - intro j. rewrite rew_q_bvar_succ.
    apply first_order_rew_apply_bind_bshift.
Qed.

Lemma first_order_rew_q_bind_free : forall L X n Y m
    (rw : rew L X n Y m) (x : syntactic_term L)
    (bv : Fin.t m -> syntactic_term L) (fv : Y -> syntactic_term L),
  (fun y => rew_apply (rew_bind (fin_cons x bv) fv)
      (rew_apply (rew_q rw) (Semiterm_fvar y))) =
  (fun y => rew_apply (rew_bind bv fv)
      (rew_apply rw (Semiterm_fvar y))).
Proof.
  intros. apply functional_extensionality. intro y.
  rewrite rew_q_fvar. apply first_order_rew_apply_bind_bshift.
Qed.

(** Canonical forcing commutes with every capture-avoiding rewrite.  A pair
    of maps is sufficient downstream and avoids imposing proof-irrelevant
    inverse laws on the Type-valued derivation witnesses. *)
Fixpoint first_order_canonical_forces_rewrite {L X n}
    (phi : ifo_semiformula L X n) : forall Y m
    (rw : rew L X n Y m) p
    (bv : Fin.t m -> syntactic_term L) (fv : Y -> syntactic_term L),
  first_order_type_biequivalence
    (first_order_canonical_forces_aux p (ifo_rewrite rw phi) bv fv)
    (first_order_canonical_forces_aux p phi
      (fun i => rew_apply (rew_bind bv fv)
        (rew_apply rw (Semiterm_bvar i)))
      (fun x => rew_apply (rew_bind bv fv)
        (rew_apply rw (Semiterm_fvar x)))).
Proof.
  destruct phi as [n0 | n0 k R v | n0 psi chi |
    n0 psi chi | n0 psi chi | n0 psi | n0 psi];
    intros Y m rw p bv fv; simpl.
  - split; exact (fun H => H).
  - assert (Hargs :
      (fun i => rew_apply (rew_bind bv fv) (rew_apply rw (v i))) =
      (fun i => rew_apply
        (rew_bind
          (fun j => rew_apply (rew_bind bv fv)
            (rew_apply rw (Semiterm_bvar j)))
          (fun x => rew_apply (rew_bind bv fv)
            (rew_apply rw (Semiterm_fvar x)))) (v i))).
    { apply functional_extensionality. intro i.
      apply first_order_rew_apply_bind_comp. }
    split; intros [b Hb].
    + exists (first_order_derivation_cast b
        (f_equal (fun args =>
          Semiformula_rel R args :: map semiformula_neg p) Hargs)).
      apply (proj2 (first_order_is_cut_free_cast_iff b _)).
      exact Hb.
    + exists (first_order_derivation_cast b
        (eq_sym (f_equal (fun args =>
          Semiformula_rel R args :: map semiformula_neg p) Hargs))).
      apply (proj2 (first_order_is_cut_free_cast_iff b _)).
      exact Hb.
  - pose (Epsi := @first_order_canonical_forces_rewrite
      L X n0 psi Y m rw p bv fv).
    pose (Echi := @first_order_canonical_forces_rewrite
      L X n0 chi Y m rw p bv fv).
    split; intros [Hpsi Hchi]; split.
    + exact (first_order_type_biequivalence_forward Epsi Hpsi).
    + exact (first_order_type_biequivalence_forward Echi Hchi).
    + exact (first_order_type_biequivalence_backward Epsi Hpsi).
    + exact (first_order_type_biequivalence_backward Echi Hchi).
  - pose (Epsi := @first_order_canonical_forces_rewrite
      L X n0 psi Y m rw p bv fv).
    pose (Echi := @first_order_canonical_forces_rewrite
      L X n0 chi Y m rw p bv fv).
    split; intros H.
    + destruct H as [Hpsi | Hchi].
      * left. exact (first_order_type_biequivalence_forward Epsi Hpsi).
      * right. exact (first_order_type_biequivalence_forward Echi Hchi).
    + destruct H as [Hpsi | Hchi].
      * left. exact (first_order_type_biequivalence_backward Epsi Hpsi).
      * right. exact (first_order_type_biequivalence_backward Echi Hchi).
  - split; intros H q sqp Hpsi.
    + pose (Epsi := @first_order_canonical_forces_rewrite
        L X n0 psi Y m rw q bv fv).
      pose (Echi := @first_order_canonical_forces_rewrite
        L X n0 chi Y m rw q bv fv).
      apply (first_order_type_biequivalence_forward Echi).
      apply H; [exact sqp |].
      exact (first_order_type_biequivalence_backward Epsi Hpsi).
    + pose (Epsi := @first_order_canonical_forces_rewrite
        L X n0 psi Y m rw q bv fv).
      pose (Echi := @first_order_canonical_forces_rewrite
        L X n0 chi Y m rw q bv fv).
      apply (first_order_type_biequivalence_backward Echi).
      apply H; [exact sqp |].
      exact (first_order_type_biequivalence_forward Epsi Hpsi).
  - split; intros H t.
    + pose (E := @first_order_canonical_forces_rewrite
        L X (S n0) psi Y (S m) (rew_q rw) p (fin_cons t bv) fv).
      pose (Hb := first_order_type_biequivalence_forward E (H t)).
      rewrite (first_order_rew_q_bind_bound rw t bv fv),
        (first_order_rew_q_bind_free rw t bv fv) in Hb.
      exact Hb.
    + pose (E := @first_order_canonical_forces_rewrite
        L X (S n0) psi Y (S m) (rew_q rw) p (fin_cons t bv) fv).
      apply (first_order_type_biequivalence_backward E).
      rewrite (first_order_rew_q_bind_bound rw t bv fv),
        (first_order_rew_q_bind_free rw t bv fv).
      exact (H t).
  - split; intros [t Ht]; exists t.
    + pose (E := @first_order_canonical_forces_rewrite
        L X (S n0) psi Y (S m) (rew_q rw) p (fin_cons t bv) fv).
      pose (Hb := first_order_type_biequivalence_forward E Ht).
      rewrite (first_order_rew_q_bind_bound rw t bv fv),
        (first_order_rew_q_bind_free rw t bv fv) in Hb.
      exact Hb.
    + pose (E := @first_order_canonical_forces_rewrite
        L X (S n0) psi Y (S m) (rew_q rw) p (fin_cons t bv) fv).
      apply (first_order_type_biequivalence_backward E).
      rewrite (first_order_rew_q_bind_bound rw t bv fv),
        (first_order_rew_q_bind_free rw t bv fv).
      exact Ht.
Defined.

Lemma first_order_rew_apply_bind_identity : forall L
    (t : syntactic_term L),
  rew_apply (rew_bind first_order_empty_bound_env
    first_order_identity_free_env) t = t.
Proof.
  intros L t. induction t as [i | x | k f v IH].
  - exact (Fin.case0 (fun i =>
      rew_apply (rew_bind first_order_empty_bound_env
        first_order_identity_free_env) (Semiterm_bvar i) =
      Semiterm_bvar i) i).
  - reflexivity.
  - simpl. f_equal. apply functional_extensionality. exact IH.
Qed.

Definition first_order_canonical_forces_substitute {L X n m p}
    (terms : Fin.t n -> semiterm L X m)
    (phi : ifo_semiformula L X n)
    (bv : Fin.t m -> syntactic_term L) (fv : X -> syntactic_term L) :
  first_order_type_biequivalence
    (first_order_canonical_forces_aux p (ifo_substitute terms phi) bv fv)
    (first_order_canonical_forces_aux p phi
      (fun i => rew_apply (rew_bind bv fv) (terms i)) fv).
Proof.
  unfold ifo_substitute.
  pose (E := @first_order_canonical_forces_rewrite
    L X n phi X m (rew_subst terms) p bv fv).
  assert (Hb :
    (fun i => rew_apply (rew_bind bv fv)
      (rew_apply (rew_subst terms) (Semiterm_bvar i))) =
    (fun i => rew_apply (rew_bind bv fv) (terms i))).
  { apply functional_extensionality. intro i. now rewrite rew_subst_bvar. }
  assert (Hf :
    (fun x => rew_apply (rew_bind bv fv)
      (rew_apply (rew_subst terms) (Semiterm_fvar x))) = fv).
  { apply functional_extensionality. intro x. now rewrite rew_subst_fvar. }
  now rewrite Hb, Hf in E.
Defined.

Definition first_order_canonical_forces_substitute_one {L p}
    (phi : ifo_semiproposition L 1) (t : syntactic_term L) :
  first_order_type_biequivalence
    (first_order_canonical_forces p
      (ifo_substitute (fun _ : Fin.t 1 => t) phi))
    (first_order_canonical_forces_aux p phi
      (fin_cons t first_order_empty_bound_env)
      first_order_identity_free_env).
Proof.
  pose (E := @first_order_canonical_forces_substitute
    L nat 1 0 p (fun _ : Fin.t 1 => t) phi
    first_order_empty_bound_env first_order_identity_free_env).
  assert (Hb :
    (fun _ : Fin.t 1 =>
      rew_apply (rew_bind first_order_empty_bound_env
        first_order_identity_free_env) t) =
    fin_cons t first_order_empty_bound_env).
  { apply functional_extensionality. intro i.
    rewrite first_order_rew_apply_bind_identity.
    refine (@Fin.caseS' 0 i (fun j => t =
      fin_cons t first_order_empty_bound_env j) eq_refl _).
    intro j. exact (Fin.case0 (fun j =>
      t = fin_cons t first_order_empty_bound_env (Fin.FS j)) j). }
  destruct Hb. exact E.
Defined.

Definition first_order_canonical_forces_bshift {L X n p}
    (phi : ifo_semiformula L X n)
    (bv : Fin.t n -> syntactic_term L) (fv : X -> syntactic_term L)
    (t : syntactic_term L) :
  first_order_type_biequivalence
    (first_order_canonical_forces_aux p (ifo_bshift phi)
      (fin_cons t bv) fv)
    (first_order_canonical_forces_aux p phi bv fv).
Proof.
  unfold ifo_bshift.
  pose (E := @first_order_canonical_forces_rewrite
    L X n phi X (S n) rew_bshift p (fin_cons t bv) fv).
  assert (Hb :
    (fun i => rew_apply (rew_bind (fin_cons t bv) fv)
      (rew_apply rew_bshift (Semiterm_bvar i))) = bv).
  { apply functional_extensionality. intro i.
    apply first_order_rew_apply_bind_bshift. }
  assert (Hf :
    (fun x => rew_apply (rew_bind (fin_cons t bv) fv)
      (rew_apply rew_bshift (Semiterm_fvar x))) = fv).
  { apply functional_extensionality. intro x.
    apply first_order_rew_apply_bind_bshift. }
  now rewrite Hb, Hf in E.
Defined.

Definition first_order_nat_env_cons {L}
    (t : syntactic_term L) (f : nat -> syntactic_term L) (x : nat) :
    syntactic_term L :=
  match x with 0 => t | S y => f y end.

Lemma ifo_rewrite_free_identity_cons : forall L
    (phi : ifo_semiproposition L 1) (t : syntactic_term L),
  ifo_rewrite
    (rew_rewrite (first_order_nat_env_cons t
      first_order_identity_free_env)) (@ifo_free L 0 phi) =
  ifo_substitute (fun _ : Fin.t 1 => t) phi.
Proof.
  intros L phi t. unfold ifo_free, ifo_substitute.
  rewrite <- ifo_rewrite_comp.
  apply ifo_rewrite_ext, rew_equiv_of_variables.
  - intro i. assert (Hi : i = Fin.F1) by apply fin_one_eq_f1.
    now subst i.
  - intro x. reflexivity.
Qed.

Fixpoint first_order_canonical_forces_monotone_aux {L X n}
    (phi : ifo_semiformula L X n) :
    forall p q (bv : Fin.t n -> syntactic_term L)
      (fv : X -> syntactic_term L),
      first_order_stronger_than q p ->
      first_order_canonical_forces_aux p phi bv fv ->
      first_order_canonical_forces_aux q phi bv fv.
Proof.
  destruct phi as [n0 | n0 k R v | n0 psi chi |
    n0 psi chi | n0 psi chi | n0 psi | n0 psi].
  - intros p q bv fv s [b Hb].
    exists (first_order_positive_derivation_graft b
      (first_order_stronger_derivation s)).
    exact (first_order_positive_derivation_graft_cut_free
      (first_order_stronger_derivation s) Hb).
  - intros p q bv fv s [b Hb].
    exists (first_order_positive_derivation_graft b
      (first_order_positive_derivation_cons
        (Semiformula_rel R
          (fun i => rew_apply (rew_bind bv fv) (v i)))
        (first_order_stronger_derivation s))).
    exact (first_order_positive_derivation_graft_cut_free
      (first_order_positive_derivation_cons
        (Semiformula_rel R
          (fun i => rew_apply (rew_bind bv fv) (v i)))
        (first_order_stronger_derivation s)) Hb).
  - intros p q bv fv s [Hpsi Hchi].
    split.
    + exact (@first_order_canonical_forces_monotone_aux
        L X n0 psi p q bv fv s Hpsi).
    + exact (@first_order_canonical_forces_monotone_aux
        L X n0 chi p q bv fv s Hchi).
  - intros p q bv fv s H.
    destruct H as [Hpsi | Hchi].
    + left. exact (@first_order_canonical_forces_monotone_aux
        L X n0 psi p q bv fv s Hpsi).
    + right. exact (@first_order_canonical_forces_monotone_aux
        L X n0 chi p q bv fv s Hchi).
  - intros p q bv fv s H r srq Hpsi.
    exact (H r (first_order_stronger_than_trans srq s) Hpsi).
  - intros p q bv fv s H t.
    exact (@first_order_canonical_forces_monotone_aux
      L X (S n0) psi p q (fin_cons t bv) fv s (H t)).
  - intros p q bv fv s [t Ht].
    exists t. exact (@first_order_canonical_forces_monotone_aux
      L X (S n0) psi p q (fin_cons t bv) fv s Ht).
Defined.

Definition first_order_canonical_forces_monotone {L p q phi}
    (s : @first_order_stronger_than L q p)
    (H : first_order_canonical_forces p phi) :
    first_order_canonical_forces q phi :=
  @first_order_canonical_forces_monotone_aux
    L nat 0 phi p q first_order_empty_bound_env
      first_order_identity_free_env s H.

Definition first_order_canonical_imply_of_aux {L X n p phi psi}
    (bv : Fin.t n -> syntactic_term L) (fv : X -> syntactic_term L)
    (H : forall q,
      first_order_canonical_forces_aux q phi bv fv ->
      first_order_canonical_forces_aux
        (first_order_sequent_meet p q) psi bv fv) :
    first_order_canonical_forces_aux p (IFOImp phi psi) bv fv.
Proof.
  intros q sqp Hphi.
  exact (@first_order_canonical_forces_monotone_aux
    L X n psi (first_order_sequent_meet p q) q bv fv
    (first_order_stronger_than_meet_with_right sqp) (H q Hphi)).
Defined.

Definition first_order_canonical_imply_of {L p phi psi}
    (H : forall q,
      first_order_canonical_forces q phi ->
      first_order_canonical_forces
        (first_order_sequent_meet p q) psi) :
    first_order_canonical_forces p (IFOImp phi psi) :=
  @first_order_canonical_imply_of_aux L nat 0 p phi psi
    first_order_empty_bound_env first_order_identity_free_env H.

Fixpoint first_order_canonical_forces_explosion_aux {L X n}
    (phi : ifo_semiformula L X n) :
    forall p (bv : Fin.t n -> syntactic_term L)
      (fv : X -> syntactic_term L),
      first_order_canonical_forces_aux p IFOFalsum bv fv ->
      first_order_canonical_forces_aux p phi bv fv.
Proof.
  destruct phi as [n0 | n0 k R v | n0 psi chi |
    n0 psi chi | n0 psi chi | n0 psi | n0 psi].
  - intros p bv fv H. exact H.
  - intros p bv fv [b Hb].
    exists (@FODContraction L (map semiformula_neg p)
      (Semiformula_rel R
        (fun i => rew_apply (rew_bind bv fv) (v i)) ::
       map semiformula_neg p)
      b (fun a Ha => or_intror Ha)).
    now apply FOCFContraction.
  - intros p bv fv H. split.
    + exact (@first_order_canonical_forces_explosion_aux
        L X n0 psi p bv fv H).
    + exact (@first_order_canonical_forces_explosion_aux
        L X n0 chi p bv fv H).
  - intros p bv fv H. left.
    exact (@first_order_canonical_forces_explosion_aux
      L X n0 psi p bv fv H).
  - intros p bv fv H q sqp Hpsi.
    pose (Hq := @first_order_canonical_forces_monotone_aux
      L X n0 IFOFalsum p q bv fv sqp H).
    exact (@first_order_canonical_forces_explosion_aux
      L X n0 chi q bv fv Hq).
  - intros p bv fv H t.
    exact (@first_order_canonical_forces_explosion_aux
      L X (S n0) psi p (fin_cons t bv) fv H).
  - intros p bv fv H.
    exists (Semiterm_fvar 0).
    exact (@first_order_canonical_forces_explosion_aux
      L X (S n0) psi p (fin_cons (Semiterm_fvar 0) bv) fv H).
Defined.

Definition first_order_canonical_forces_explosion {L p phi}
    (H : first_order_canonical_forces p IFOFalsum) :
    first_order_canonical_forces p phi :=
  @first_order_canonical_forces_explosion_aux
    L nat 0 phi p first_order_empty_bound_env
      first_order_identity_free_env H.

Definition first_order_canonical_efq {L} (phi : ifo_proposition L) :
    first_order_canonical_forces_all (IFOImp IFOFalsum phi) :=
  fun p q sqp Hbot => first_order_canonical_forces_explosion Hbot.

Definition first_order_canonical_modus_ponens {L : language}
    {p : first_order_sequent L} {phi psi : ifo_proposition L}
    (Himp : first_order_canonical_forces p (IFOImp phi psi))
    (Hphi : first_order_canonical_forces p phi) :
    first_order_canonical_forces p psi :=
  Himp p (first_order_stronger_than_refl p) Hphi.
