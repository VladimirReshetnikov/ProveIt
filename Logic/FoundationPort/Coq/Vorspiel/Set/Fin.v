(** Predicate sets over the first three finite ordinals. *)

From Foundation.Vorspiel.Fin Require Import Basic.
From Foundation.Vorspiel.Set Require Import Basic Cofinite.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition set_empty {A} : pred_set A := fun _ => False.
Definition set_full {A} : pred_set A := fun _ => True.
Definition set_singleton {A} (a : A) : pred_set A := fun x => x = a.
Definition set_pair {A} (a b : A) : pred_set A :=
  fun x => x = a \/ x = b.
Definition set_triple {A} (a b c : A) : pred_set A :=
  fun x => x = a \/ x = b \/ x = c.

Definition set_powerset {A} (u : pred_set A) : pred_set (pred_set A) :=
  fun s => set_subset s u.

Definition fin1_zero : Fin.t 1 := Fin.F1.
Definition fin2_zero : Fin.t 2 := Fin.F1.
Definition fin2_one : Fin.t 2 := Fin.FS Fin.F1.
Definition fin3_zero : Fin.t 3 := Fin.F1.
Definition fin3_one : Fin.t 3 := Fin.FS Fin.F1.
Definition fin3_two : Fin.t 3 := Fin.FS (Fin.FS Fin.F1).

Lemma fin1_elim : forall (P : Fin.t 1 -> Prop),
  P fin1_zero -> forall i, P i.
Proof.
  intros P H i. refine (@Fin.caseS' 0 i P H _).
  intros j. inversion j.
Qed.

Lemma fin2_elim : forall (P : Fin.t 2 -> Prop),
  P fin2_zero -> P fin2_one -> forall i, P i.
Proof.
  intros P Hzero Hone i.
  refine (@Fin.caseS' 1 i P Hzero _). intro j.
  refine (@Fin.caseS' 0 j (fun k => P (Fin.FS k)) Hone _).
  intros k. inversion k.
Qed.

Lemma fin3_elim : forall (P : Fin.t 3 -> Prop),
  P fin3_zero -> P fin3_one -> P fin3_two -> forall i, P i.
Proof.
  intros P Hzero Hone Htwo i.
  refine (@Fin.caseS' 2 i P Hzero _). intro j.
  refine (@Fin.caseS' 1 j (fun k => P (Fin.FS k)) Hone _). intro k.
  refine (@Fin.caseS' 0 k (fun l => P (Fin.FS (Fin.FS l))) Htwo _).
  intros l. inversion l.
Qed.

Lemma fin1_full_equiv_singleton :
  set_equiv (@set_full (Fin.t 1)) (set_singleton fin1_zero).
Proof.
  intro i. refine (@fin1_elim (fun i =>
    set_full i <-> set_singleton fin1_zero i) _ i).
  split; [intros; reflexivity | intros; exact I].
Qed.

Theorem fin1_set_cases : forall s : pred_set (Fin.t 1),
  s fin1_zero \/ ~ s fin1_zero ->
  set_equiv s (set_singleton fin1_zero) \/ set_equiv s set_empty.
Proof.
  intros s [Hzero | Hzero].
  - left. intro i. refine (@fin1_elim (fun i =>
      s i <-> set_singleton fin1_zero i) _ i).
    split; [intros; reflexivity |].
    intros _. exact Hzero.
  - right. intro i. refine (@fin1_elim
      (fun i => s i <-> set_empty i) _ i). split.
    + intro H. contradiction.
    + intro H. contradiction.
Qed.

Theorem fin1_powerset_iff : forall s : pred_set (Fin.t 1),
  s fin1_zero \/ ~ s fin1_zero ->
  set_powerset set_full s <->
  set_equiv s (set_singleton fin1_zero) \/ set_equiv s set_empty.
Proof.
  intros s Hdec. split.
  - intros _. now apply fin1_set_cases.
  - intros _ x Hx. exact I.
Qed.

Lemma fin2_full_equiv_pair :
  set_equiv (@set_full (Fin.t 2)) (set_pair fin2_zero fin2_one).
Proof.
  intro i. refine (@fin2_elim (fun i =>
    set_full i <-> set_pair fin2_zero fin2_one i) _ _ i).
  - split; [intros; now left | intros; exact I].
  - split; [intros; now right | intros; exact I].
Qed.

Theorem fin2_singleton_not_full : forall x : Fin.t 2,
  ~ set_equiv (set_singleton x) set_full.
Proof.
  intro x. refine (@Fin.caseS' 1 x
    (fun y => ~ set_equiv (set_singleton y) set_full) _ _).
  - intro H. destruct (H fin2_one) as [_ Hfrom].
    discriminate (Hfrom I).
  - intro j. refine (@Fin.caseS' 0 j
      (fun k => ~ set_equiv (set_singleton (Fin.FS k)) set_full) _ _).
    + intro H. destruct (H fin2_zero) as [_ Hfrom].
      discriminate (Hfrom I).
    + intros k. inversion k.
Qed.

Theorem fin2_set_cases : forall s : pred_set (Fin.t 2),
  (s fin2_zero \/ ~ s fin2_zero) ->
  (s fin2_one \/ ~ s fin2_one) ->
  set_equiv s (set_pair fin2_zero fin2_one) \/
  set_equiv s (set_singleton fin2_zero) \/
  set_equiv s (set_singleton fin2_one) \/
  set_equiv s set_empty.
Proof.
  intros s Hzero Hone. destruct Hzero as [Hzero | Hzero];
    destruct Hone as [Hone | Hone].
  - left. intro i. refine (@fin2_elim (fun i =>
      s i <-> set_pair fin2_zero fin2_one i) _ _ i).
    + split; [intros; now left | intros; exact Hzero].
    + split; [intros; now right | intros; exact Hone].
  - right; left. intro i. refine (@fin2_elim (fun i =>
      s i <-> set_singleton fin2_zero i) _ _ i).
    + split; [intros; reflexivity | intros; exact Hzero].
    + split; [intro H; contradiction | intro H; discriminate].
  - right; right; left. intro i. refine (@fin2_elim (fun i =>
      s i <-> set_singleton fin2_one i) _ _ i).
    + split; [intro H; contradiction | intro H; discriminate].
    + split; [intros; reflexivity | intros; exact Hone].
  - right; right; right. intro i. refine (@fin2_elim (fun i =>
      s i <-> set_empty i) _ _ i).
    + split; intro H; contradiction.
    + split; intro H; contradiction.
Qed.

Theorem fin2_powerset_iff : forall s : pred_set (Fin.t 2),
  (s fin2_zero \/ ~ s fin2_zero) ->
  (s fin2_one \/ ~ s fin2_one) ->
  set_powerset set_full s <->
  set_equiv s (set_pair fin2_zero fin2_one) \/
  set_equiv s (set_singleton fin2_zero) \/
  set_equiv s (set_singleton fin2_one) \/
  set_equiv s set_empty.
Proof.
  intros s Hzero Hone. split.
  - intros _. now apply fin2_set_cases.
  - intros _ x Hx. exact I.
Qed.

Lemma fin2_complement_one_equiv_zero :
  set_equiv (set_complement (set_singleton fin2_one))
    (set_singleton fin2_zero).
Proof.
  intro i. refine (@fin2_elim (fun i =>
    set_complement (set_singleton fin2_one) i <->
    set_singleton fin2_zero i) _ _ i).
  - split; [intros; reflexivity | intros _ Heq; discriminate].
  - split.
    + intro H. exfalso. apply H. reflexivity.
    + intro H. discriminate.
Qed.

Lemma fin2_complement_zero_equiv_one :
  set_equiv (set_complement (set_singleton fin2_zero))
    (set_singleton fin2_one).
Proof.
  intro i. refine (@fin2_elim (fun i =>
    set_complement (set_singleton fin2_zero) i <->
    set_singleton fin2_one i) _ _ i).
  - split.
    + intro H. exfalso. apply H. reflexivity.
    + intro H. discriminate.
  - split; [intros; reflexivity | intros _ Heq; discriminate].
Qed.

Lemma fin3_full_equiv_triple :
  set_equiv (@set_full (Fin.t 3))
    (set_triple fin3_zero fin3_one fin3_two).
Proof.
  intro i. refine (@fin3_elim (fun i =>
    set_full i <-> set_triple fin3_zero fin3_one fin3_two i) _ _ _ i).
  - split; [intros; now left | intros; exact I].
  - split; [intros; right; now left | intros; exact I].
  - split; [intros; right; now right | intros; exact I].
Qed.
