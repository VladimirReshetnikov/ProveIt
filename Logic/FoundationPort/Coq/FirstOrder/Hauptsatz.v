(** Canonical forcing infrastructure for first-order cut elimination. *)

From Stdlib Require Import Lists.List Vectors.Fin.
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
