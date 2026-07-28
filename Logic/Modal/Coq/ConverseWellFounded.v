(**
  Generic converse-well-founded relations and their finite heights.

  This module independently ports the complete seventeen-declaration
  mathematical surface of the pinned Foundation module
  [Vorspiel/Rel/CWF.lean].  Foundation uses two finiteness interfaces:
  proposition-valued [Finite] for existence theorems and data-carrying
  [Fintype] for the noncomputable height.  Their Rocq counterparts below are
  [relation_finite], an existential list cover in [Prop], and
  [finite_enumeration], an explicit list cover in [Type].  Duplicate entries
  are harmless because height uses a maximum.

  [converse_well_founded R] is ordinary well-foundedness of the flipped
  relation, exactly as upstream.  The finite height is defined with
  [Wellfounded.Fix]; classical decidability is used only to retain from the
  cover those elements which are immediate successors.  Thus no decidable
  equality or decidable relation is added to the public interface.
*)

From Stdlib Require Import Arith.PeanoNat Lia.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Logic.ClassicalDescription.
From Stdlib Require Import Logic.Classical_Prop.
From Stdlib Require Import Relations.Relation_Definitions.
From Stdlib Require Import Wellfounded.Wellfounded.
From FoundationModal Require Import
  Filtration FrameProperties RelationProperties.

Import ListNotations.
Import FrameProperties RelationProperties.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Finiteness and relation interfaces *)

Definition relation_finite (A : Type) : Prop :=
  exists cover : list A, forall x : A, In x cover.

Record finite_enumeration (A : Type) : Type := {
  finite_enum : list A;
  finite_enum_complete : forall x : A, In x finite_enum
}.

Arguments finite_enum {A} _.
Arguments finite_enum_complete {A} _ _.

Definition finite_enumeration_is_finite {A : Type}
    (E : finite_enumeration A) : relation_finite A :=
  ex_intro _ (finite_enum E) (finite_enum_complete E).

(** Source declaration 1/17: [ConverseWellFounded]. *)
Definition converse_well_founded {A : Type}
    (R : A -> A -> Prop) : Prop :=
  well_founded (relation_converse R).

(** Source declaration 2/17: [IsConverseWellFounded].  The record is kept
    only as the source-facing class wrapper; ordinary theorems use the
    underlying predicate directly. *)
Record is_converse_well_founded {A : Type}
    (R : A -> A -> Prop) : Prop := {
  relation_cwf : converse_well_founded R
}.

Definition relation_has_maximal_elements {A : Type}
    (R : A -> A -> Prop) : Prop :=
  forall X : A -> Prop,
    (exists x, X x) ->
    exists m, X m /\ forall y, X y -> ~ R m y.

(** Source declaration 3/17: [ConverseWellFounded.iff_has_max]. *)
Theorem converse_well_founded_iff_has_max :
  forall (A : Type) (R : A -> A -> Prop),
    converse_well_founded R <-> relation_has_maximal_elements R.
Proof.
  intros A R; split.
  - intros Hwf X [x Hx]. revert Hx.
    refine (@well_founded_ind A (relation_converse R) Hwf
      (fun u => X u ->
        exists m, X m /\ forall y, X y -> ~ R m y) _ x).
    intros u IH Hu.
    destruct (classic (exists v, X v /\ R u v))
      as [[v [Hv Ruv]] | Hnone].
    + apply (IH v Ruv Hv).
    + exists u; split; [exact Hu |].
      intros v Hv Ruv. apply Hnone. now exists v.
  - intros Hmax x.
    apply NNPP. intro Hnotacc.
    destruct (Hmax (fun y => ~ Acc (relation_converse R) y))
      as [m [Hbad Hmaximal]].
    + now exists x.
    + apply Hbad. constructor. intros y Hym.
      apply NNPP. intro Hbad_y.
      apply (Hmaximal y Hbad_y). exact Hym.
Qed.

(** Source declaration 4/17: [ConverseWellFounded.has_max]. *)
Lemma converse_well_founded_has_max :
  forall (A : Type) (R : A -> A -> Prop),
    converse_well_founded R -> relation_has_maximal_elements R.
Proof.
  intros A R Hwf.
  now apply (proj1 (@converse_well_founded_iff_has_max A R)).
Qed.

(** Source declaration 5/17:
    [Finite.converseWellFounded_of_trans_of_irrefl]. *)
Theorem finite_converse_well_founded_of_transitive_irreflexive :
  forall (A : Type) (R : A -> A -> Prop),
    relation_finite A -> transitive A R -> relation_irreflexive R ->
    converse_well_founded R.
Proof.
  intros A R [cover Hcover] Htrans Hirr.
  apply (proj2 (@converse_well_founded_iff_has_max A R)).
  intros X [x0 Hx0].
  assert (Hfinite_max : forall xs : list A,
      (exists x, In x xs /\ X x) ->
      exists m, In m xs /\ X m /\
        forall y, In y xs -> X y -> ~ R m y).
  {
    intro xs; induction xs as [|a xs IH]; intros Hinh.
    - destruct Hinh as [x [Hin _]]. inversion Hin.
    - destruct (classic (exists x, In x xs /\ X x))
        as [Htail | Hno_tail].
      + destruct (IH Htail) as [m [Hmin [HmX Hmax]]].
        destruct (classic (X a /\ R m a))
          as [[Ha Rma] | Hnot_ma].
        * exists a; split; [now left |].
          split; [exact Ha |].
          intros y Hyin HyX Ray.
          destruct Hyin as [Hya | Hyin].
          -- subst y. exact (Hirr a Ray).
          -- apply (Hmax y Hyin HyX).
             eapply Htrans; eauto.
        * exists m; split; [now right |].
          split; [exact HmX |].
          intros y Hyin HyX Rmy.
          destruct Hyin as [Hya | Hyin].
          -- subst y. apply Hnot_ma. now split.
          -- exact (Hmax y Hyin HyX Rmy).
      + destruct Hinh as [x [[Hax | Hxin] HxX]].
        * subst x. exists a; split; [now left |].
          split; [exact HxX |].
          intros y Hyin HyX Ray.
          destruct Hyin as [Hya | Hyin].
          -- subst y. exact (Hirr a Ray).
          -- exfalso. apply Hno_tail. now exists y.
        * exfalso. apply Hno_tail. now exists x.
  }
  destruct (Hfinite_max cover) as [m [_ [Hm Hmax]]].
  - exists x0; split; [apply Hcover | exact Hx0].
  - exists m; split; [exact Hm |].
    intros y Hy Rmy. exact (Hmax y (Hcover y) Hy Rmy).
Qed.

(** Source declaration 6/17: the corresponding finite/transitive/
    irreflexive [IsConverseWellFounded] instance. *)
Definition finite_transitive_irreflexive_is_converse_well_founded
    (A : Type) (R : A -> A -> Prop)
    (Hfinite : relation_finite A) (Htrans : transitive A R)
    (Hirr : relation_irreflexive R)
    : is_converse_well_founded R :=
  {| relation_cwf :=
       finite_converse_well_founded_of_transitive_irreflexive
         Hfinite Htrans Hirr |}.

(** * A finite maximum and the well-founded height *)

Definition relation_successor_enumeration {A : Type}
    (E : finite_enumeration A) (R : A -> A -> Prop) (x : A)
    : list {y : A | R x y} :=
  @sig_filter A (fun y => R x y)
    (fun y => excluded_middle_informative (R x y)) (finite_enum E).

Arguments relation_successor_enumeration {A} E R x.

Definition cwf_height_step {A : Type}
    (E : finite_enumeration A) (R : A -> A -> Prop) (x : A)
    (rec : forall y, relation_converse R y x -> nat) : nat :=
  list_max
    (map (fun y => S (rec (proj1_sig y) (proj2_sig y)))
      (relation_successor_enumeration E R x)).

Arguments cwf_height_step {A} E R x rec.

(** Source declaration 7/17: [cwfHeight]. *)
Definition cwf_height {A : Type}
    (E : finite_enumeration A) (R : A -> A -> Prop)
    (Hwf : converse_well_founded R) : A -> nat :=
  @Fix A (relation_converse R) Hwf (fun _ => nat)
    (@cwf_height_step A E R).

Arguments cwf_height {A} E R Hwf x.

Lemma cwf_height_step_ext :
  forall (A : Type) (E : finite_enumeration A)
         (R : A -> A -> Prop) x
         (f g : forall y, relation_converse R y x -> nat),
    (forall y p, f y p = g y p) ->
    cwf_height_step E R x f = cwf_height_step E R x g.
Proof.
  intros A E R x f g Hfg. unfold cwf_height_step.
  f_equal. apply map_ext. intros [y Hy]; simpl.
  now rewrite (Hfg y Hy).
Qed.

(** Source declaration 8/17: [cwfHeight_eq]. *)
Lemma cwf_height_eq :
  forall (A : Type) (E : finite_enumeration A)
         (R : A -> A -> Prop) (Hwf : converse_well_founded R) a,
    cwf_height E R Hwf a =
    list_max
      (map (fun b => S (cwf_height E R Hwf (proj1_sig b)))
        (relation_successor_enumeration E R a)).
Proof.
  intros A E R Hwf a. unfold cwf_height.
  apply (@Fix_eq A (relation_converse R) Hwf
    (fun _ => nat) (cwf_height_step E R)).
  intros x f g Hfg. now apply cwf_height_step_ext.
Qed.

Lemma in_list_max_le :
  forall n xs, In n xs -> n <= list_max xs.
Proof.
  intros n xs; induction xs as [|a xs IH]; simpl; intros Hin.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [now apply IH | apply Nat.le_max_r].
Qed.

Lemma list_max_le_of_members :
  forall xs n,
    (forall k, In k xs -> k <= n) -> list_max xs <= n.
Proof.
  intros xs n Hall. apply (proj2 (list_max_le xs n)).
  apply Forall_forall. exact Hall.
Qed.

Lemma list_max_attained_if_nonzero :
  forall xs, list_max xs <> 0 ->
    exists n, In n xs /\ list_max xs = n.
Proof.
  intro xs; induction xs as [|a xs IH]; simpl; intro Hnz.
  - contradiction.
  - destruct (Nat.max_dec a (list_max xs)) as [Hleft | Hright].
    + exists a; split; [now left | exact Hleft].
    + assert (Htail : list_max xs <> 0).
      { intro Hz. apply Hnz. now rewrite Hright, Hz. }
      destruct (IH Htail) as [n [Hin Hmax]].
      exists n; split; [now right |]. now rewrite Hright, Hmax.
Qed.

Lemma relation_successor_enumeration_complete :
  forall (A : Type) (E : finite_enumeration A)
         (R : A -> A -> Prop) x y (Hxy : R x y),
    exists Hy : R x y,
      In (exist (fun z => R x z) y Hy)
        (relation_successor_enumeration E R x).
Proof.
  intros A E R x y Hxy. unfold relation_successor_enumeration.
  remember (finite_enum E) as xs eqn:Hxs.
  assert (Hin : In y xs).
  { rewrite Hxs. apply finite_enum_complete. }
  clear Hxs E. induction xs as [|a xs IH]; simpl in Hin |- *.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + destruct (excluded_middle_informative (R x y)) as [Hy | Hnot].
      * exists Hy. now left.
      * contradiction.
    + destruct (excluded_middle_informative (R x a)) as [Ha | Hnot].
      * destruct (IH Hin) as [Hy Hmem]. exists Hy. now right.
      * now apply IH.
Qed.

(** Source declaration 9/17: [cwfHeight_gt_of]. *)
Lemma cwf_height_gt_of :
  forall (A : Type) (E : finite_enumeration A)
         (R : A -> A -> Prop) (Hwf : converse_well_founded R) a b,
    R a b -> cwf_height E R Hwf b < cwf_height E R Hwf a.
Proof.
  intros A E R Hwf a b Hab.
  rewrite (@cwf_height_eq A E R Hwf a).
  assert (Hin : In (S (cwf_height E R Hwf b))
      (map (fun z => S (cwf_height E R Hwf (proj1_sig z)))
        (relation_successor_enumeration E R a))).
  { destruct (relation_successor_enumeration_complete E Hab)
      as [Hb Hmem].
    apply in_map_iff.
    exists (exist (fun z => R a z) b Hb); split; [reflexivity | exact Hmem]. }
  pose proof (in_list_max_le Hin). lia.
Qed.

(** Source declaration 10/17: [cwfHeight_eq_zero_iff]. *)
Lemma cwf_height_eq_zero_iff :
  forall (A : Type) (E : finite_enumeration A)
         (R : A -> A -> Prop) (Hwf : converse_well_founded R) a,
    cwf_height E R Hwf a = 0 <-> forall b, ~ R a b.
Proof.
  intros A E R Hwf a; split.
  - intros Hz b Hab.
    pose proof (@cwf_height_gt_of A E R Hwf a b Hab). lia.
  - intros Hterminal. rewrite cwf_height_eq.
    destruct (relation_successor_enumeration E R a) as [|b bs].
    + reflexivity.
    + exfalso. exact (Hterminal (proj1_sig b) (proj2_sig b)).
Qed.

(** Source declaration 11/17: [cwfHeight_le]. *)
Lemma cwf_height_le :
  forall (A : Type) (E : finite_enumeration A)
         (R : A -> A -> Prop) (Hwf : converse_well_founded R) a n,
    (forall b, R a b -> cwf_height E R Hwf b < n) ->
    cwf_height E R Hwf a <= n.
Proof.
  intros A E R Hwf a n Hbound. rewrite cwf_height_eq.
  apply list_max_le_of_members. intros k Hk.
  apply in_map_iff in Hk.
  destruct Hk as [[b Hb] [<- _]]; simpl.
  specialize (Hbound b Hb). lia.
Qed.

(** Source declaration 12/17: [lt_cwfHeight]. *)
Lemma lt_cwf_height :
  forall (A : Type) (E : finite_enumeration A)
         (R : A -> A -> Prop) (Hwf : converse_well_founded R)
         a b n,
    R a b -> n <= cwf_height E R Hwf b ->
    n < cwf_height E R Hwf a.
Proof.
  intros A E R Hwf a b n Hab Hn.
  pose proof (@cwf_height_gt_of A E R Hwf a b Hab). lia.
Qed.

(** Source declaration 13/17: [cwfHeight_eq_of_lt_of_le]. *)
Lemma cwf_height_eq_of_lt_of_le :
  forall (A : Type) (E : finite_enumeration A)
         (R : A -> A -> Prop) (Hwf : converse_well_founded R) a n,
    (forall b, R a b -> cwf_height E R Hwf b < n) ->
    (exists b, R a b /\ n <= cwf_height E R Hwf b + 1) ->
    cwf_height E R Hwf a = n.
Proof.
  intros A E R Hwf a n Hupper [b [Hab Hlower]].
  apply Nat.le_antisymm.
  - now apply cwf_height_le.
  - pose proof (@cwf_height_gt_of A E R Hwf a b Hab). lia.
Qed.

(** Source declaration 14/17: [cwfHeight_eq_succ]. *)
Lemma cwf_height_eq_succ :
  forall (A : Type) (E : finite_enumeration A)
         (R : A -> A -> Prop) (Hwf : converse_well_founded R) a,
    cwf_height E R Hwf a <> 0 ->
    exists b, R a b /\
      cwf_height E R Hwf a = cwf_height E R Hwf b + 1.
Proof.
  intros A E R Hwf a Hnonzero.
  pose proof (@cwf_height_eq A E R Hwf a) as Heq.
  set (values :=
    map (fun b => S (cwf_height E R Hwf (proj1_sig b)))
      (relation_successor_enumeration E R a)) in *.
  assert (Hmax_nonzero : list_max values <> 0).
  { intro Hz. apply Hnonzero. now rewrite Heq, Hz. }
  destruct (list_max_attained_if_nonzero Hmax_nonzero)
    as [k [Hkin Hmax]].
  unfold values in Hkin.
  apply in_map_iff in Hkin.
  destruct Hkin as [[b Hb] [Hk _]]; simpl in Hk. subst k.
  exists b; split; [exact Hb |].
  rewrite Heq, Hmax. lia.
Qed.

(** Source declaration 15/17: [cwfHeight_eq_succ_cwfHeight]. *)
Lemma cwf_height_eq_succ_cwf_height :
  forall (A : Type) (E : finite_enumeration A)
         (R : A -> A -> Prop) (Hwf : converse_well_founded R) a b,
    R a b ->
    (forall c, R a c -> R b c \/ b = c) ->
    cwf_height E R Hwf a = cwf_height E R Hwf b + 1.
Proof.
  intros A E R Hwf a b Hab Hsuccessors.
  apply cwf_height_eq_of_lt_of_le.
  - intros c Hac. destruct (Hsuccessors c Hac) as [Hbc | ->].
    + pose proof (@cwf_height_gt_of A E R Hwf b c Hbc). lia.
    + lia.
  - exists b; split; [exact Hab | lia].
Qed.

(** Source declaration 16/17: [cwfHeight_lt]. *)
Lemma cwf_height_lt :
  forall (A : Type) (E : finite_enumeration A)
         (R : A -> A -> Prop) (Hwf : converse_well_founded R),
    transitive A R ->
    forall a n, n < cwf_height E R Hwf a ->
      exists b, R a b /\ cwf_height E R Hwf b = n.
Proof.
  intros A E R Hwf Htrans a.
  refine (@well_founded_ind A (relation_converse R) Hwf
    (fun x => forall n, n < cwf_height E R Hwf x ->
      exists b, R x b /\ cwf_height E R Hwf b = n) _ a).
  intros x IH n Hn.
  assert (Hpositive : cwf_height E R Hwf x <> 0) by lia.
  destruct (@cwf_height_eq_succ A E R Hwf x Hpositive)
    as [b [Hxb Heq]].
  destruct (Nat.eq_dec n (cwf_height E R Hwf b)) as [-> | Hneq].
  - exists b; auto.
  - assert (Hlt : n < cwf_height E R Hwf b) by lia.
    destruct (IH b Hxb n Hlt) as [c [Hbc Hrank]].
    exists c; split; [eapply Htrans; eauto | exact Hrank].
Qed.

(** A small source-facing equivalence record, replacing Lean's [Equiv]. *)
Record type_equiv (A B : Type) : Type := {
  equiv_to : A -> B;
  equiv_from : B -> A;
  equiv_to_from : forall y, equiv_to (equiv_from y) = y;
  equiv_from_to : forall x, equiv_from (equiv_to x) = x
}.

Arguments equiv_to {A B} _ _.
Arguments equiv_from {A B} _ _.
Arguments equiv_to_from {A B} _ _.
Arguments equiv_from_to {A B} _ _.

(** Source declaration 17/17: [cwfHeight_congr]. *)
Lemma cwf_height_congr :
  forall (A B : Type)
         (EA : finite_enumeration A) (EB : finite_enumeration B)
         (R : A -> A -> Prop) (S : B -> B -> Prop)
         (HwfR : converse_well_founded R)
         (HwfS : converse_well_founded S)
         (f : type_equiv A B),
    (forall a b, R a b <-> S (equiv_to f a) (equiv_to f b)) ->
    forall a,
      cwf_height EA R HwfR a =
      cwf_height EB S HwfS (equiv_to f a).
Proof.
  intros A B EA EB R S HwfR HwfS f Hrel a.
  refine (@well_founded_ind A (relation_converse R) HwfR
    (fun x => cwf_height EA R HwfR x =
      cwf_height EB S HwfS (equiv_to f x)) _ a).
  intros x IH. apply Nat.le_antisymm.
  - apply cwf_height_le. intros y Hxy.
    rewrite (IH y Hxy).
    now apply cwf_height_gt_of, (proj1 (Hrel x y)).
  - apply cwf_height_le. intros y Hfy.
    set (z := equiv_from f y).
    assert (Hto : equiv_to f z = y).
    { unfold z. apply equiv_to_from. }
    assert (Hxz : R x z).
    { apply (proj2 (Hrel x z)). now rewrite Hto. }
    rewrite <- Hto, <- (IH z Hxz).
    now apply cwf_height_gt_of.
Qed.
