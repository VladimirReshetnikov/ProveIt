(** Cut-freeness for first-order LK derivation trees. *)

From Stdlib Require Import Lists.List Vectors.Fin Program.Equality.
From Foundation.Syntax.Predicate Require Import Language Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Calculus.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Inductive first_order_is_cut_free {L} :
    forall Gamma, first_order_derivation L Gamma -> Prop :=
| FOCFIdentity : forall k (r : language_rel L k) v,
    first_order_is_cut_free (FODIdentity r v)
| FOCFVerum : first_order_is_cut_free FODVerum
| FOCFOr : forall p q Gamma
    (d : first_order_derivation L (p :: q :: Gamma)),
    first_order_is_cut_free d ->
    first_order_is_cut_free (FODOr d)
| FOCFAnd : forall p q Gamma
    (dp : first_order_derivation L (p :: Gamma))
    (dq : first_order_derivation L (q :: Gamma)),
    first_order_is_cut_free dp ->
    first_order_is_cut_free dq ->
    first_order_is_cut_free (FODAnd dp dq)
| FOCFAll : forall (p : semiproposition L 1) Gamma
    (d : first_order_derivation L
      (@semiformula_free L 0 p :: first_order_sequent_shift Gamma)),
    first_order_is_cut_free d ->
    first_order_is_cut_free (FODAll d)
| FOCFExists : forall (p : semiproposition L 1) t Gamma
    (d : first_order_derivation L
      (semiformula_substitute (fun _ : Fin.t 1 => t) p :: Gamma)),
    first_order_is_cut_free d ->
    first_order_is_cut_free (FODExists d)
| FOCFContraction : forall Gamma Delta
    (d : first_order_derivation L Gamma) H,
    first_order_is_cut_free d ->
    first_order_is_cut_free (@FODContraction L Gamma Delta d H).

Arguments first_order_is_cut_free {L Gamma} _.
Arguments FOCFIdentity {L k} _ _.
Arguments FOCFVerum {L}.
Arguments FOCFOr {L p q Gamma d} _.
Arguments FOCFAnd {L p q Gamma dp dq} _ _.
Arguments FOCFAll {L p Gamma d} _.
Arguments FOCFExists {L p t Gamma d} _.
Arguments FOCFContraction {L Gamma Delta d} H _.

Lemma first_order_is_cut_free_or_iff :
  forall L p q Gamma (d : first_order_derivation L (p :: q :: Gamma)),
    first_order_is_cut_free (FODOr d) <-> first_order_is_cut_free d.
Proof.
  split.
  - intro H; dependent destruction H; assumption.
  - apply FOCFOr.
Qed.

Lemma first_order_is_cut_free_and_iff :
  forall L p q Gamma
         (dp : first_order_derivation L (p :: Gamma))
         (dq : first_order_derivation L (q :: Gamma)),
    first_order_is_cut_free (FODAnd dp dq) <->
    first_order_is_cut_free dp /\ first_order_is_cut_free dq.
Proof.
  split.
  - intro H; dependent destruction H; now split.
  - intros [Hp Hq]. now constructor.
Qed.

Lemma first_order_is_cut_free_all_iff :
  forall L (p : semiproposition L 1) Gamma
         (d : first_order_derivation L
           (@semiformula_free L 0 p :: first_order_sequent_shift Gamma)),
    first_order_is_cut_free (FODAll d) <-> first_order_is_cut_free d.
Proof.
  split.
  - intro H; dependent destruction H; assumption.
  - apply FOCFAll.
Qed.

Lemma first_order_is_cut_free_exists_iff :
  forall L (p : semiproposition L 1) t Gamma
         (d : first_order_derivation L
           (semiformula_substitute (fun _ : Fin.t 1 => t) p :: Gamma)),
    first_order_is_cut_free (FODExists d) <-> first_order_is_cut_free d.
Proof.
  split.
  - intro H; dependent destruction H; assumption.
  - apply FOCFExists.
Qed.

Lemma first_order_is_cut_free_contraction_iff :
  forall L Gamma Delta (d : first_order_derivation L Gamma) H,
    first_order_is_cut_free (@FODContraction L Gamma Delta d H) <->
    first_order_is_cut_free d.
Proof.
  split.
  - intro Hcf; dependent destruction Hcf; assumption.
  - apply FOCFContraction.
Qed.

Lemma first_order_is_cut_free_cast_iff :
  forall L Gamma Delta (d : first_order_derivation L Gamma)
         (e : Gamma = Delta),
    first_order_is_cut_free (first_order_derivation_cast d e) <->
    first_order_is_cut_free d.
Proof. intros L Gamma Delta d e; destruct e; reflexivity. Qed.

Definition first_order_derivation_root_is_cut {L Gamma}
    (d : first_order_derivation L Gamma) : bool :=
  match d with
  | FODCut _ _ => true
  | _ => false
  end.

Lemma first_order_is_cut_free_root_is_not_cut :
  forall L Gamma (d : first_order_derivation L Gamma),
    first_order_is_cut_free d ->
    first_order_derivation_root_is_cut d = false.
Proof. intros L Gamma d H; destruct H; reflexivity. Qed.

Lemma first_order_is_cut_free_not_cut :
  forall L p Gamma Delta
         (dp : first_order_derivation L (p :: Gamma))
         (dn : first_order_derivation L (semiformula_neg p :: Delta)),
    ~ first_order_is_cut_free (FODCut dp dn).
Proof.
  intros L p Gamma Delta dp dn H.
  pose proof (first_order_is_cut_free_root_is_not_cut H) as Hroot.
  discriminate Hroot.
Qed.

Lemma first_order_is_cut_free_language_map_iff :
  forall L M Gamma (h : language_hom L M)
         (d : first_order_derivation L Gamma),
    first_order_is_cut_free (first_order_derivation_language_map h d) <->
    first_order_is_cut_free d.
Proof.
  intros L M Gamma h d. induction d; cbn.
  - split; intro; constructor.
  - split; intro Hcf.
    + exfalso. rewrite first_order_is_cut_free_cast_iff in Hcf.
      exact (first_order_is_cut_free_not_cut Hcf).
    + exfalso. exact (first_order_is_cut_free_not_cut Hcf).
  - repeat rewrite first_order_is_cut_free_contraction_iff. exact IHd.
  - split; intro; constructor.
  - repeat rewrite first_order_is_cut_free_or_iff. exact IHd.
  - repeat rewrite first_order_is_cut_free_and_iff.
    now rewrite IHd1, IHd2.
  - repeat rewrite first_order_is_cut_free_all_iff.
    rewrite first_order_is_cut_free_cast_iff. exact IHd.
  - repeat rewrite first_order_is_cut_free_exists_iff.
    rewrite first_order_is_cut_free_cast_iff. exact IHd.
Qed.
