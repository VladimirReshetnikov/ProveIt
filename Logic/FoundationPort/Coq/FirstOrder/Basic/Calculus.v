(**
  A one-sided classical sequent calculus for first-order NNF formulas.

  This begins the port of [Foundation/FirstOrder/Basic/Calculus.lean].  The
  primitive derivation stays in [Type], preserving proof data, and uses the
  duplicate-insensitive generic list inclusion shared by the audited
  one-sided calculus infrastructure.
*)

From Stdlib Require Import Arith.PeanoNat Lists.List Vectors.Fin.
From FoundationModal Require Import GenericAdjunctiveSet GenericCalculus.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition first_order_sequent (L : language) : Type := list (proposition L).

Definition first_order_sequent_shift {L}
    (Gamma : first_order_sequent L) : first_order_sequent L :=
  map semiformula_shift Gamma.

Definition first_order_sequent_language_map {L M}
    (h : language_hom L M) (Gamma : first_order_sequent L) :
    first_order_sequent M :=
  map (semiformula_language_map h) Gamma.

Lemma first_order_sequent_language_map_shift :
  forall L M (h : language_hom L M) (Gamma : first_order_sequent L),
    first_order_sequent_language_map h (first_order_sequent_shift Gamma) =
    first_order_sequent_shift (first_order_sequent_language_map h Gamma).
Proof.
  intros L M h Gamma. induction Gamma as [|p Gamma IH]; simpl.
  - reflexivity.
  - now rewrite semiformula_language_map_shift, IH.
Qed.

(** Primitive LK rules.  Contraction includes exchange and weakening because
    [generic_list_subset] is pointwise list inclusion. *)
Inductive first_order_derivation (L : language) :
    first_order_sequent L -> Type :=
| FODIdentity : forall k (r : language_rel L k)
    (v : Fin.t k -> syntactic_term L),
    @first_order_derivation L
      [Semiformula_rel r v; Semiformula_nrel r v]
| FODCut : forall (p : proposition L) Gamma Delta,
    @first_order_derivation L (p :: Gamma) ->
    @first_order_derivation L (semiformula_neg p :: Delta) ->
    @first_order_derivation L (Gamma ++ Delta)
| FODContraction : forall Gamma Delta,
    @first_order_derivation L Gamma ->
    generic_list_subset Gamma Delta ->
    @first_order_derivation L Delta
| FODVerum : @first_order_derivation L [Semiformula_verum 0]
| FODOr : forall (p q : proposition L) Gamma,
    @first_order_derivation L (p :: q :: Gamma) ->
    @first_order_derivation L (Semiformula_or p q :: Gamma)
  | FODAnd : forall (p q : proposition L) Gamma,
    @first_order_derivation L (p :: Gamma) ->
    @first_order_derivation L (q :: Gamma) ->
    @first_order_derivation L (Semiformula_and p q :: Gamma)
| FODAll : forall (p : semiproposition L 1) Gamma,
    @first_order_derivation L
      (@semiformula_free L 0 p :: first_order_sequent_shift Gamma) ->
    @first_order_derivation L (Semiformula_all p :: Gamma)
| FODExists : forall (p : semiproposition L 1)
    (t : syntactic_term L) Gamma,
    @first_order_derivation L
      (semiformula_substitute (fun _ : Fin.t 1 => t) p :: Gamma) ->
    @first_order_derivation L (Semiformula_exists p :: Gamma).

Arguments first_order_derivation L Gamma : clear implicits.
Arguments FODIdentity {L k} _ _.
Arguments FODCut {L p Gamma Delta} _ _.
Arguments FODContraction {L Gamma Delta} _ _.
Arguments FODVerum {L}.
Arguments FODOr {L p q Gamma} _.
Arguments FODAnd {L p q Gamma} _ _.
Arguments FODAll {L p Gamma} _.
Arguments FODExists {L p t Gamma} _.

Fixpoint first_order_derivation_height {L Gamma}
    (d : first_order_derivation L Gamma) : nat :=
  match d with
  | FODIdentity _ _ => 0
  | FODCut dp dn =>
      S (Nat.max (first_order_derivation_height dp)
                 (first_order_derivation_height dn))
  | FODContraction d _ => S (first_order_derivation_height d)
  | FODVerum => 0
  | FODOr d => S (first_order_derivation_height d)
  | FODAnd dp dq =>
      S (Nat.max (first_order_derivation_height dp)
                 (first_order_derivation_height dq))
  | FODAll d => S (first_order_derivation_height d)
  | FODExists d => S (first_order_derivation_height d)
  end.

Definition first_order_derivation_cast {L Gamma Delta}
    (d : first_order_derivation L Gamma) (e : Gamma = Delta) :
    first_order_derivation L Delta :=
  generic_lk_cast (first_order_derivation L) d e.

Lemma first_order_derivation_height_cast :
  forall L Gamma Delta (d : first_order_derivation L Gamma)
         (e : Gamma = Delta),
    first_order_derivation_height (first_order_derivation_cast d e) =
    first_order_derivation_height d.
Proof. intros L Gamma Delta d e; destruct e; reflexivity. Qed.

Definition first_order_derivation_contra {L Gamma Delta}
    (d : first_order_derivation L Gamma)
    (H : generic_list_subset Gamma Delta) :
    first_order_derivation L Delta :=
  FODContraction d H.

Definition first_order_derivation_top {L Gamma}
    (Htop : generic_list_member (Semiformula_verum 0) Gamma) :
    first_order_derivation L Gamma.
Proof.
  apply (FODContraction FODVerum).
  intros p [Hp | Hp].
  - now subst p.
  - contradiction.
Defined.

Definition first_order_derivation_atomic_identity {L k}
    (r : language_rel L k) (v : Fin.t k -> syntactic_term L)
    (Gamma : first_order_sequent L)
    (Hpos : generic_list_member (Semiformula_rel r v) Gamma)
    (Hneg : generic_list_member (Semiformula_nrel r v) Gamma) :
    first_order_derivation L Gamma.
Proof.
  apply (FODContraction (FODIdentity r v)).
  intros p [Hp | [Hp | Hp]].
  - now subst p.
  - now subst p.
  - contradiction.
Defined.

Definition first_order_derivation_rotate {L p Gamma}
    (d : first_order_derivation L (p :: Gamma)) :
    first_order_derivation L (Gamma ++ [p]) :=
  FODContraction d (@generic_list_subset_rotate _ p Gamma).

Definition first_order_derivation_tensor {L p q Gamma Delta}
    (dp : first_order_derivation L (p :: Gamma))
    (dq : first_order_derivation L (q :: Delta)) :
    first_order_derivation L
      (Semiformula_and p q :: Gamma ++ Delta) :=
  FODAnd
    (FODContraction dp
      (@generic_list_subset_cons_append_right _ p Gamma Delta))
    (FODContraction dq
      (@generic_list_subset_cons_append_left _ q Gamma Delta)).

(** Every derivation is functorial in the underlying first-order language. *)
Fixpoint first_order_derivation_language_map {L M Gamma}
    (h : language_hom L M) (d : first_order_derivation L Gamma) {struct d} :
    first_order_derivation M (first_order_sequent_language_map h Gamma).
Proof.
  destruct d as [k r v | p Gamma Delta dp dn | Gamma Delta d Hsub |
    | p q Gamma d | p q Gamma dp dq | p Gamma d | p t Gamma d].
  - exact (FODIdentity (hom_rel h r)
      (fun i => semiterm_language_map h (v i))).
  - pose (dp' := @first_order_derivation_language_map L M _ h dp).
    pose (dn' := @first_order_derivation_language_map L M _ h dn).
    refine (first_order_derivation_cast
      (FODCut dp'
        (first_order_derivation_cast dn' _)) _).
    + simpl. now rewrite semiformula_language_map_neg.
    + unfold first_order_sequent_language_map. simpl.
      now rewrite List.map_app.
  - apply (FODContraction (@first_order_derivation_language_map L M _ h d)).
    now apply generic_list_map_subset.
  - exact FODVerum.
  - exact (FODOr (@first_order_derivation_language_map L M _ h d)).
  - exact (FODAnd (@first_order_derivation_language_map L M _ h dp)
                  (@first_order_derivation_language_map L M _ h dq)).
  - apply FODAll.
    refine (first_order_derivation_cast
      (@first_order_derivation_language_map L M _ h d) _).
    simpl. rewrite semiformula_language_map_free.
    now rewrite first_order_sequent_language_map_shift.
  - apply (FODExists (t := semiterm_language_map h t)).
    refine (first_order_derivation_cast
      (@first_order_derivation_language_map L M _ h d) _).
    simpl. now rewrite semiformula_language_map_substitute.
Defined.

Lemma first_order_derivation_height_identity :
  forall L k (r : language_rel L k) v,
    first_order_derivation_height (FODIdentity r v) = 0.
Proof. reflexivity. Qed.

Lemma first_order_derivation_height_cut :
  forall L p Gamma Delta
         (dp : first_order_derivation L (p :: Gamma))
         (dn : first_order_derivation L (semiformula_neg p :: Delta)),
    first_order_derivation_height (FODCut dp dn) =
    S (Nat.max (first_order_derivation_height dp)
               (first_order_derivation_height dn)).
Proof. reflexivity. Qed.

Lemma first_order_derivation_height_contraction :
  forall L Gamma Delta (d : first_order_derivation L Gamma) H,
    first_order_derivation_height (@FODContraction L Gamma Delta d H) =
    S (first_order_derivation_height d).
Proof. reflexivity. Qed.

Lemma first_order_derivation_height_or :
  forall L p q Gamma (d : first_order_derivation L (p :: q :: Gamma)),
    first_order_derivation_height (FODOr d) =
    S (first_order_derivation_height d).
Proof. reflexivity. Qed.

Lemma first_order_derivation_height_and :
  forall L p q Gamma
         (dp : first_order_derivation L (p :: Gamma))
         (dq : first_order_derivation L (q :: Gamma)),
    first_order_derivation_height (FODAnd dp dq) =
    S (Nat.max (first_order_derivation_height dp)
               (first_order_derivation_height dq)).
Proof. reflexivity. Qed.

Lemma first_order_derivation_height_all :
  forall L (p : semiproposition L 1) Gamma
         (d : first_order_derivation L
           (@semiformula_free L 0 p :: first_order_sequent_shift Gamma)),
    first_order_derivation_height (FODAll d) =
    S (first_order_derivation_height d).
Proof. reflexivity. Qed.

Lemma first_order_derivation_height_exists :
  forall L (p : semiproposition L 1) t Gamma
         (d : first_order_derivation L
           (semiformula_substitute (fun _ : Fin.t 1 => t) p :: Gamma)),
    first_order_derivation_height (FODExists d) =
    S (first_order_derivation_height d).
Proof. reflexivity. Qed.
