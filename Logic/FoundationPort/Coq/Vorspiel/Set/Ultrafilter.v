(** Ultrafilters on predicate sets.

    The interface records exactly the Boolean-prime filter laws used by
    first-order ultraproducts.  Keeping existence separate lets Łoś's theorem
    depend only on the algebraic laws, while maximal-extension constructions
    can be audited independently. *)

From Stdlib Require Import Logic.Classical_Prop Logic.ProofIrrelevance
  Lists.List.
From Foundation.Vorspiel.Set Require Import Basic.
From Foundation.Vorspiel.Order Require Import Zorn.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Import ListNotations.

Definition set_intersection {A} (s t : pred_set A) : pred_set A :=
  fun x => s x /\ t x.

Definition set_union {A} (s t : pred_set A) : pred_set A :=
  fun x => s x \/ t x.

Definition set_complement {A} (s : pred_set A) : pred_set A :=
  fun x => ~ s x.

Definition set_universal {A} : pred_set A := fun _ => True.
Definition set_void {A} : pred_set A := fun _ => False.

Record set_ultrafilter (A : Type) : Type := {
  ultrafilter_member : pred_set A -> Prop;
  ultrafilter_universal_mem : ultrafilter_member set_universal;
  ultrafilter_void_not_mem : ~ ultrafilter_member set_void;
  ultrafilter_mem_of_superset : forall s t,
    set_subset s t -> ultrafilter_member s -> ultrafilter_member t;
  ultrafilter_intersection_mem_iff : forall s t,
    ultrafilter_member (set_intersection s t) <->
    ultrafilter_member s /\ ultrafilter_member t;
  ultrafilter_union_mem_iff : forall s t,
    ultrafilter_member (set_union s t) <->
    ultrafilter_member s \/ ultrafilter_member t;
  ultrafilter_complement_mem_iff : forall s,
    ultrafilter_member (set_complement s) <->
    ~ ultrafilter_member s
}.

Arguments ultrafilter_member {A} _ _.

(** A proper filter is kept separate from an ultrafilter.  This makes the
    maximal-extension theorem useful independently of Boolean primeness. *)
Record set_filter (A : Type) : Type := {
  filter_member : pred_set (pred_set A);
  filter_universal_mem : filter_member set_universal;
  filter_void_not_mem : ~ filter_member set_void;
  filter_mem_of_superset : forall s t,
    set_subset s t -> filter_member s -> filter_member t;
  filter_intersection_mem : forall s t,
    filter_member s -> filter_member t ->
    filter_member (set_intersection s t)
}.

Arguments filter_member {A} _ _.

Definition filter_included {A} (F G : set_filter A) : Prop :=
  forall s, filter_member F s -> filter_member G s.

Lemma set_filter_ext : forall A (F G : set_filter A),
  (forall s, filter_member F s <-> filter_member G s) -> F = G.
Proof.
  intros A [Fm Fun Fvoid Fup Finter] [Gm Gun Gvoid Gup Ginter] Heq.
  cbn in Heq. cbn.
  assert (Fm = Gm) by now apply pred_set_extensionality.
  subst Gm. f_equal; apply proof_irrelevance.
Qed.

Lemma filter_included_order : forall A,
  partial_order_laws (@filter_included A).
Proof.
  intro A. constructor.
  - intros F s Hs. exact Hs.
  - intros F G H HFG HGH s Hs. now apply HGH, HFG.
  - intros F G HFG HGF. apply set_filter_ext. intro s. split;
      [apply HFG | apply HGF].
Qed.

Section FilterExtension.

  Context {A : Type} (seed : set_filter A).

  Record set_filter_extension : Type := {
    extension_filter : set_filter A;
    extension_includes_seed : filter_included seed extension_filter
  }.

  Definition filter_extension_included
      (F G : set_filter_extension) : Prop :=
    filter_included (extension_filter F) (extension_filter G).

  Lemma set_filter_extension_ext : forall F G,
    filter_extension_included F G ->
    filter_extension_included G F -> F = G.
  Proof.
    intros [F HF] [G HG] HFG HGF. cbn in *.
    assert (F = G).
    { apply set_filter_ext. intro s. split; [apply HFG | apply HGF]. }
    subst G. f_equal. apply proof_irrelevance.
  Qed.

  Lemma filter_extension_included_order :
    partial_order_laws filter_extension_included.
  Proof.
    constructor.
    - intros F s Hs. exact Hs.
    - intros F G H HFG HGH s Hs. now apply HGH, HFG.
    - intros F G. apply set_filter_extension_ext.
  Qed.

  Definition filter_chain_union_member
      (C : pred_set set_filter_extension) : pred_set (pred_set A) :=
    fun s => filter_member seed s \/
      exists F, C F /\ filter_member (extension_filter F) s.

  Lemma filter_chain_union_is_filter : forall C,
    order_chain filter_extension_included C ->
    set_filter A.
  Proof.
    intros C HC.
    refine {| filter_member := filter_chain_union_member C |}.
    - left. apply filter_universal_mem.
    - intros [Hvoid | [F [_ Hvoid]]].
      + exact (filter_void_not_mem Hvoid).
      + exact (filter_void_not_mem Hvoid).
    - intros s t Hst [Hs | [F [HCF HFs]]].
      + left. eapply filter_mem_of_superset; [exact Hst | exact Hs].
      + right. exists F. split; [exact HCF |].
        eapply filter_mem_of_superset; [exact Hst | exact HFs].
    - intros s t [Hs | [F [HCF HFs]]] [Ht | [G [HCG HGt]]].
      + left. now apply filter_intersection_mem.
      + right. exists G. split; [exact HCG |].
        apply filter_intersection_mem.
        * apply extension_includes_seed. exact Hs.
        * exact HGt.
      + right. exists F. split; [exact HCF |].
        apply filter_intersection_mem.
        * exact HFs.
        * apply extension_includes_seed. exact Ht.
      + destruct (HC F G HCF HCG) as [HFG | HGF].
        * right. exists G. split; [exact HCG |].
          apply filter_intersection_mem; [now apply HFG | exact HGt].
        * right. exists F. split; [exact HCF |].
          apply filter_intersection_mem; [exact HFs | now apply HGF].
  Defined.

  Definition filter_chain_union_extension C
      (HC : order_chain filter_extension_included C) :
      set_filter_extension :=
    {| extension_filter := filter_chain_union_is_filter HC;
       extension_includes_seed := fun s Hs => or_introl Hs |}.

  Lemma filter_extension_chain_upper_bound : forall C,
    order_chain filter_extension_included C ->
    exists F, order_upper_bound filter_extension_included C F.
  Proof.
    intros C HC. exists (@filter_chain_union_extension C HC).
    intros F HCF s HFs. right. exists F. now split.
  Qed.

  Theorem set_filter_maximal_extension :
    exists U : set_filter A,
      filter_included seed U /\
      forall F, filter_included U F -> U = F.
  Proof.
    destruct (zorn_maximal_element filter_extension_included_order
      filter_extension_chain_upper_bound) as [U HU].
    exists (extension_filter U). split.
    - apply extension_includes_seed.
    - intros F HUF.
      pose (Fext := {| extension_filter := F;
        extension_includes_seed := fun s Hs =>
          @HUF s (@extension_includes_seed U s Hs) |}).
      assert (U = Fext).
      { apply HU. exact HUF. }
      now apply (f_equal extension_filter) in H.
  Qed.

End FilterExtension.

(** The filter generated by adjoining one set. *)
Definition filter_adjoin_member {A} (F : set_filter A)
    (s : pred_set A) : pred_set (pred_set A) :=
  fun t => exists u, filter_member F u /\
    set_subset (set_intersection u s) t.

Lemma filter_adjoin_is_filter : forall A (F : set_filter A) s,
  ~ filter_member F (set_complement s) -> set_filter A.
Proof.
  intros A F s Hnotcomp.
  refine {| filter_member := filter_adjoin_member F s |}.
  - exists set_universal. split; [apply filter_universal_mem |].
    intros x _. constructor.
  - intros [u [Hu Hempty]]. apply Hnotcomp.
    eapply filter_mem_of_superset; [|exact Hu].
    intros x Hux Hsx. exfalso. apply (Hempty x). now split.
  - intros t v Htv [u [Hu Hut]]. exists u. split; [exact Hu |].
    intros x Hx. now apply Htv, Hut.
  - intros t v [u [Hu Hut]] [w [Hw Hwv]].
    exists (set_intersection u w). split.
    + now apply filter_intersection_mem.
    + intros x [[Hux Hwx] Hsx]. split.
      * apply Hut. now split.
      * apply Hwv. now split.
Defined.

Lemma filter_included_adjoin : forall A (F : set_filter A) s Hproper,
  filter_included F (@filter_adjoin_is_filter A F s Hproper).
Proof.
  intros A F s Hproper t Ht. exists t. split; [exact Ht |].
  intros x [Htx _]. exact Htx.
Qed.

Lemma filter_adjoin_contains : forall A (F : set_filter A) s Hproper,
  filter_member (@filter_adjoin_is_filter A F s Hproper) s.
Proof.
  intros A F s Hproper. exists set_universal. split.
  - apply filter_universal_mem.
  - intros x [_ Hsx]. exact Hsx.
Qed.

Lemma maximal_filter_decides : forall A (F : set_filter A),
  (forall G, filter_included F G -> F = G) ->
  forall s, filter_member F s \/ filter_member F (set_complement s).
Proof.
  intros A F Hmax s. destruct (classic (filter_member F s)) as [Hs | Hs].
  - now left.
  - right. apply NNPP. intro Hnotcomp.
    pose (G := @filter_adjoin_is_filter A F s Hnotcomp).
    assert (Heq : F = G).
    { apply Hmax. unfold G. apply filter_included_adjoin. }
    apply Hs. rewrite Heq. unfold G. apply filter_adjoin_contains.
Qed.

Definition ultrafilter_as_filter {A} (U : set_ultrafilter A) :
    set_filter A :=
  {| filter_member := ultrafilter_member U;
     filter_universal_mem := @ultrafilter_universal_mem A U;
     filter_void_not_mem := @ultrafilter_void_not_mem A U;
     filter_mem_of_superset := @ultrafilter_mem_of_superset A U;
     filter_intersection_mem := fun s t Hs Ht =>
       proj2 (@ultrafilter_intersection_mem_iff A U s t) (conj Hs Ht) |}.

Theorem set_ultrafilter_extension : forall A (F : set_filter A),
  exists U : set_ultrafilter A, filter_included F (ultrafilter_as_filter U).
Proof.
  intros A F.
  destruct (set_filter_maximal_extension F) as [M [HFM Hmax]].
  assert (Hdec : forall s,
    filter_member M s \/ filter_member M (set_complement s)).
  { exact (maximal_filter_decides Hmax). }
  assert (Hinteriff : forall s t,
    filter_member M (set_intersection s t) <->
    filter_member M s /\ filter_member M t).
  { intros s t. split.
    - intro H. split.
      + eapply filter_mem_of_superset; [|exact H]. intros x [Hx _]. exact Hx.
      + eapply filter_mem_of_superset; [|exact H]. intros x [_ Hx]. exact Hx.
    - intros [Hs Ht]. now apply filter_intersection_mem. }
  assert (Hcompiff : forall s,
    filter_member M (set_complement s) <-> ~ filter_member M s).
  { intro s. split.
    - intros Hcs Hs. apply (@filter_void_not_mem A M).
      eapply (@filter_mem_of_superset A M
        (set_intersection s (set_complement s)) set_void).
      + intros x [Hx Hnx]. contradiction.
      + now apply filter_intersection_mem.
    - intro Hs. destruct (Hdec s); [contradiction | assumption]. }
  assert (Hunioniff : forall s t,
    filter_member M (set_union s t) <->
    filter_member M s \/ filter_member M t).
  { intros s t. split.
    - intro Hunion.
      destruct (classic (filter_member M s)) as [Hs | Hs]; [now left |].
      destruct (classic (filter_member M t)) as [Ht | Ht]; [now right |].
      exfalso. apply (@filter_void_not_mem A M).
      pose proof (proj2 (Hcompiff s) Hs) as Hcs.
      pose proof (proj2 (Hcompiff t) Ht) as Hct.
      pose proof (filter_intersection_mem Hcs Hct) as Hboth.
      pose proof (filter_intersection_mem Hunion Hboth) as Hbad.
      eapply filter_mem_of_superset; [|exact Hbad].
      intros x [[Hsx | Htx] [Hns Hnt]]; contradiction.
    - intros [Hs | Ht].
      + eapply (@filter_mem_of_superset A M s (set_union s t)).
        * intros x Hx. now left.
        * exact Hs.
      + eapply (@filter_mem_of_superset A M t (set_union s t)).
        * intros x Hx. now right.
        * exact Ht. }
  pose (U := {| ultrafilter_member := filter_member M;
    ultrafilter_universal_mem := @filter_universal_mem A M;
    ultrafilter_void_not_mem := @filter_void_not_mem A M;
    ultrafilter_mem_of_superset := @filter_mem_of_superset A M;
    ultrafilter_intersection_mem_iff := Hinteriff;
    ultrafilter_union_mem_iff := Hunioniff;
    ultrafilter_complement_mem_iff := Hcompiff |}).
  exists U. exact HFM.
Qed.

(** A finite-intersection-property interface stated without a finite-set
    container or decidable equality.  Lists are sufficient because duplicate
    generators do not affect intersections. *)
Fixpoint set_list_intersection {A} (xs : list (pred_set A)) : pred_set A :=
  match xs with
  | [] => set_universal
  | s :: xs => set_intersection s (set_list_intersection xs)
  end.

Lemma set_list_intersection_member_iff : forall A
    (xs : list (pred_set A)) x,
  set_list_intersection xs x <-> forall s, In s xs -> s x.
Proof.
  intros A xs; induction xs as [|s xs IH]; intro x.
  - cbn. split; [intros _ t Ht; contradiction | intros _; constructor].
  - change (s x /\ set_list_intersection xs x <->
      forall t, s = t \/ In t xs -> t x).
    rewrite (IH x). split.
    + intros [Hs Hall] t [<- | Ht]; [exact Hs | now apply Hall].
    + intro Hall. split.
      * apply Hall. now left.
      * intros t Ht. apply Hall. now right.
Qed.

Definition set_family_finite_intersection_property {A}
    (family : pred_set (pred_set A)) : Prop :=
  forall xs : list (pred_set A),
    (forall s, In s xs -> family s) ->
    exists x, set_list_intersection xs x.

Definition family_generated_filter_member {A}
    (family : pred_set (pred_set A)) : pred_set (pred_set A) :=
  fun t => exists xs : list (pred_set A),
    (forall s, In s xs -> family s) /\
    set_subset (set_list_intersection xs) t.

Lemma family_generated_filter : forall A (family : pred_set (pred_set A)),
  set_family_finite_intersection_property family -> set_filter A.
Proof.
  intros A family Hfinite.
  refine {| filter_member := family_generated_filter_member family |}.
  - exists []. split.
    + intros s Hs. contradiction.
    + intros x _. constructor.
  - intros [xs [Hfamily Hempty]].
    destruct (Hfinite xs Hfamily) as [x Hx]. exact (Hempty x Hx).
  - intros s t Hst [xs [Hfamily Hxs]]. exists xs. split;
      [exact Hfamily |].
    intros x Hx. now apply Hst, Hxs.
  - intros s t [xs [HxsFamily Hxs]] [ys [HysFamily Hys]].
    exists (xs ++ ys). split.
    + intros u Hu. apply in_app_iff in Hu. destruct Hu;
        [now apply HxsFamily | now apply HysFamily].
    + intros x Hx.
      pose proof (proj1 (@set_list_intersection_member_iff
        A (xs ++ ys) x) Hx) as Hall.
      split.
      * apply Hxs. apply (proj2 (@set_list_intersection_member_iff A xs x)).
        intros u Hu. apply Hall, in_app_iff. now left.
      * apply Hys. apply (proj2 (@set_list_intersection_member_iff A ys x)).
        intros u Hu. apply Hall, in_app_iff. now right.
Defined.

Lemma family_generated_filter_contains : forall A
    (family : pred_set (pred_set A)) Hfinite s,
  family s ->
  filter_member (@family_generated_filter A family Hfinite) s.
Proof.
  intros A family Hfinite s Hs. exists [s]. split.
  - intros t [<- | Hnone]; [exact Hs | contradiction].
  - intros x [Hsx _]. exact Hsx.
Qed.

Theorem ultrafilter_of_finite_intersection_property : forall A
    (family : pred_set (pred_set A)),
  set_family_finite_intersection_property family ->
  exists U : set_ultrafilter A,
    forall s, family s -> ultrafilter_member U s.
Proof.
  intros A family Hfinite.
  destruct (set_ultrafilter_extension
    (@family_generated_filter A family Hfinite)) as [U HU].
  exists U. intros s Hs.
  exact (@HU s (family_generated_filter_contains Hfinite Hs)).
Qed.

Lemma ultrafilter_member_equiv : forall A (U : set_ultrafilter A) s t,
  set_equiv s t ->
  (ultrafilter_member U s <-> ultrafilter_member U t).
Proof.
  intros A U s t Heq. split; intro H.
  - eapply ultrafilter_mem_of_superset; [|exact H].
    intros x Hx. exact (proj1 (Heq x) Hx).
  - eapply ultrafilter_mem_of_superset; [|exact H].
    intros x Hx. exact (proj2 (Heq x) Hx).
Qed.

Lemma ultrafilter_intersection_mem : forall A (U : set_ultrafilter A) s t,
  ultrafilter_member U s -> ultrafilter_member U t ->
  ultrafilter_member U (set_intersection s t).
Proof.
  intros A U s t Hs Ht.
  apply (proj2 (ultrafilter_intersection_mem_iff U s t)). now split.
Qed.

Lemma ultrafilter_member_intersection_left : forall A
    (U : set_ultrafilter A) s t,
  ultrafilter_member U (set_intersection s t) ->
  ultrafilter_member U s.
Proof.
  intros A U s t H. exact (proj1
    (proj1 (ultrafilter_intersection_mem_iff U s t) H)).
Qed.

Lemma ultrafilter_member_intersection_right : forall A
    (U : set_ultrafilter A) s t,
  ultrafilter_member U (set_intersection s t) ->
  ultrafilter_member U t.
Proof.
  intros A U s t H. exact (proj2
    (proj1 (ultrafilter_intersection_mem_iff U s t) H)).
Qed.

Lemma ultrafilter_member_decides : forall A (U : set_ultrafilter A) s,
  ultrafilter_member U s \/
  ultrafilter_member U (set_complement s).
Proof.
  intros A U s. destruct (classic (ultrafilter_member U s)) as [Hs | Hs].
  - now left.
  - right. now apply (proj2 (ultrafilter_complement_mem_iff U s)).
Qed.
