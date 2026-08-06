(**
  Primitive recursion certified by HFS computation sequences.

  Foundation packages a zero clause and a successor clause as formulas,
  proves that finite HFS sequences satisfying those clauses are coherent,
  and defines the represented function through their final entries.  The
  standard-model mathematical content is independent of formula syntax.  We
  therefore factor it over an arbitrary parameter type [P], strictly
  generalizing the source's fixed finite vector of parameters.

  The actual trace is still encoded by [HFS.Seq]: a finite set of arithmetic
  index-value pairs.  Existing verified primitive recursion supplies the
  executable result, while the theorems below prove that every valid trace
  computes exactly that result and that the existential trace graph is
  functional.
*)

From Stdlib Require Import Arith.PeanoNat Lia Lists.List NArith.NArith.
From Foundation.Vorspiel Require Import Arithmetic.
From Foundation.FirstOrder.Arithmetic.HFS Require Import Basic Seq.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.

Record hfs_pr_construction (P : Type) : Type := {
  hfs_pr_zero : P -> hfs_code;
  hfs_pr_step : P -> nat -> hfs_code -> hfs_code
}.

Arguments hfs_pr_zero {P} _ _.
Arguments hfs_pr_step {P} _ _ _ _.

Fixpoint hfs_pr_result {P} (c : hfs_pr_construction P)
    (parameters : P) (n : nat) : hfs_code :=
  match n with
  | 0 => hfs_pr_zero c parameters
  | S k => hfs_pr_step c parameters k (hfs_pr_result c parameters k)
  end.

Lemma hfs_pr_result_zero : forall P (c : hfs_pr_construction P) p,
  hfs_pr_result c p 0 = hfs_pr_zero c p.
Proof. reflexivity. Qed.

Lemma hfs_pr_result_succ : forall P (c : hfs_pr_construction P) p n,
  hfs_pr_result c p (S n) =
  hfs_pr_step c p n (hfs_pr_result c p n).
Proof. reflexivity. Qed.

(** The trace through stage [n], including both stages [0] and [n]. *)
Fixpoint hfs_pr_trace {P} (c : hfs_pr_construction P)
    (parameters : P) (n : nat) : hfs_sequence :=
  match n with
  | 0 => hfs_sequence_singleton (hfs_pr_zero c parameters)
  | S k =>
      hfs_sequence_cons (hfs_pr_trace c parameters k)
        (hfs_pr_step c parameters k (hfs_pr_result c parameters k))
  end.

Lemma hfs_pr_trace_zero : forall P (c : hfs_pr_construction P) p,
  hfs_pr_trace c p 0 = hfs_sequence_singleton (hfs_pr_zero c p).
Proof. reflexivity. Qed.

Lemma hfs_pr_trace_succ : forall P (c : hfs_pr_construction P) p n,
  hfs_pr_trace c p (S n) =
  hfs_sequence_cons (hfs_pr_trace c p n)
    (hfs_pr_step c p n (hfs_pr_result c p n)).
Proof. reflexivity. Qed.

Theorem hfs_pr_trace_length : forall P (c : hfs_pr_construction P) p n,
  hfs_sequence_length (hfs_pr_trace c p n) = S n.
Proof.
  intros P c p n. induction n as [|n IH]; [reflexivity|].
  simpl. rewrite hfs_sequence_cons_length, IH. reflexivity.
Qed.

Theorem hfs_pr_trace_nth : forall P (c : hfs_pr_construction P) p n i,
  i <= n ->
  hfs_sequence_nth (hfs_pr_trace c p n) i =
  Some (hfs_pr_result c p i).
Proof.
  intros P c p n. induction n as [|n IH]; intros i Hi.
  - assert (i = 0) by lia. subst. reflexivity.
  - destruct (Nat.eq_dec i (S n)) as [-> | Hneq].
    + rewrite hfs_pr_trace_succ.
      pose proof (hfs_sequence_cons_nth_last
        (hfs_pr_trace c p n)
        (hfs_pr_step c p n (hfs_pr_result c p n))) as Hlast.
      rewrite hfs_pr_trace_length in Hlast. rewrite Hlast.
      now rewrite hfs_pr_result_succ.
    + assert (Hin : i <= n) by lia.
      rewrite hfs_pr_trace_succ, hfs_sequence_cons_nth_old.
      * now apply IH.
      * rewrite hfs_pr_trace_length. lia.
Qed.

Corollary hfs_pr_trace_last : forall P (c : hfs_pr_construction P) p n,
  hfs_sequence_nth (hfs_pr_trace c p n) n =
  Some (hfs_pr_result c p n).
Proof. intros. now apply hfs_pr_trace_nth. Qed.

Corollary hfs_pr_trace_mem : forall P (c : hfs_pr_construction P) p n i,
  i <= n ->
  hfs_mem
    (hfs_index_pair (N.of_nat i) (hfs_pr_result c p i))
    (hfs_sequence_code (hfs_pr_trace c p n)).
Proof.
  intros P c p n i Hi. unfold hfs_sequence_code.
  rewrite hfs_mem_sequence_index_iff. now apply hfs_pr_trace_nth.
Qed.

(** A computation sequence has a base entry and obeys the step equation at
    every adjacent pair that lies in its domain.  Nonemptiness is explicit,
    making the zero entry meaningful without any default convention. *)
Definition hfs_pr_computation {P} (c : hfs_pr_construction P)
    (parameters : P) (s : hfs_sequence) : Prop :=
  0 < hfs_sequence_length s /\
  hfs_sequence_nth s 0 = Some (hfs_pr_zero c parameters) /\
  forall i z,
    hfs_sequence_nth s i = Some z ->
    S i < hfs_sequence_length s ->
    hfs_sequence_nth s (S i) =
      Some (hfs_pr_step c parameters i z).

Lemma hfs_pr_computation_nonempty : forall P
    (c : hfs_pr_construction P) p s,
  hfs_pr_computation c p s -> 0 < hfs_sequence_length s.
Proof. firstorder. Qed.

Lemma hfs_pr_computation_zero : forall P
    (c : hfs_pr_construction P) p s,
  hfs_pr_computation c p s ->
  hfs_sequence_nth s 0 = Some (hfs_pr_zero c p).
Proof. firstorder. Qed.

Lemma hfs_pr_computation_step : forall P
    (c : hfs_pr_construction P) p s,
  hfs_pr_computation c p s ->
  forall i z,
    hfs_sequence_nth s i = Some z ->
    S i < hfs_sequence_length s ->
    hfs_sequence_nth s (S i) = Some (hfs_pr_step c p i z).
Proof. firstorder. Qed.

Theorem hfs_pr_trace_computation : forall P
    (c : hfs_pr_construction P) p n,
  hfs_pr_computation c p (hfs_pr_trace c p n).
Proof.
  intros P c p n. split.
  - rewrite hfs_pr_trace_length. lia.
  - split.
    + rewrite hfs_pr_trace_nth by lia. now rewrite hfs_pr_result_zero.
    + intros i z Hnth Hnext.
      rewrite hfs_pr_trace_length in Hnext.
      assert (Hi : i <= n) by lia.
      pose proof (@hfs_pr_trace_nth P c p n i Hi) as Hcanonical.
      rewrite Hnth in Hcanonical. inversion Hcanonical; subst z.
      rewrite hfs_pr_trace_nth by lia. now rewrite hfs_pr_result_succ.
Qed.

(** Every entry of every valid computation is forced by primitive recursion.
    This single induction factors all pairwise trace-uniqueness arguments. *)
Theorem hfs_pr_computation_value : forall P
    (c : hfs_pr_construction P) p s,
  hfs_pr_computation c p s ->
  forall i z,
    hfs_sequence_nth s i = Some z ->
    z = hfs_pr_result c p i.
Proof.
  intros P c p s Hcomp i. induction i as [|i IH]; intro z; intro Hnth.
  - pose proof (hfs_pr_computation_zero Hcomp) as Hzero.
    rewrite Hnth in Hzero. inversion Hzero. now rewrite hfs_pr_result_zero.
  - assert (Hbound : S i < hfs_sequence_length s).
    { apply (proj1 (@nth_error_Some hfs_code
        (hfs_sequence_values s) (S i))).
      unfold hfs_sequence_nth in Hnth. now rewrite Hnth. }
    assert (Hprevious_some :
        nth_error (hfs_sequence_values s) i <> None).
    { apply (proj2 (@nth_error_Some hfs_code
        (hfs_sequence_values s) i)).
      unfold hfs_sequence_length in Hbound. lia. }
    destruct (hfs_sequence_nth s i) as [previous |] eqn:Hprevious.
    2: { unfold hfs_sequence_nth in Hprevious_some.
         contradiction. }
    pose proof (hfs_pr_computation_step Hcomp Hprevious Hbound) as Hstep.
    rewrite Hnth in Hstep. inversion Hstep; subst z.
    specialize (IH previous eq_refl). subst previous.
    now rewrite hfs_pr_result_succ.
Qed.

Corollary hfs_pr_computations_agree : forall P
    (c : hfs_pr_construction P) p s t,
  hfs_pr_computation c p s ->
  hfs_pr_computation c p t ->
  forall i x y,
    hfs_sequence_nth s i = Some x ->
    hfs_sequence_nth t i = Some y -> x = y.
Proof.
  intros P c p s t Hs Ht i x y Hx Hy.
  rewrite (hfs_pr_computation_value Hs Hx),
    (hfs_pr_computation_value Ht Hy). reflexivity.
Qed.

Theorem hfs_pr_computation_eq_trace : forall P
    (c : hfs_pr_construction P) p s n,
  hfs_pr_computation c p s ->
  hfs_sequence_length s = S n ->
  s = hfs_pr_trace c p n.
Proof.
  intros P c p s n Hcomp Hlength.
  apply hfs_sequence_extensionality. intro i.
  destruct (hfs_sequence_nth s i) as [x |] eqn:Hs.
  - assert (Hi : i <= n).
    { assert (Hilen : i < length (hfs_sequence_values s)).
      { apply (proj1 (@nth_error_Some hfs_code
          (hfs_sequence_values s) i)).
        unfold hfs_sequence_nth in Hs. rewrite Hs. discriminate. }
      unfold hfs_sequence_length in Hlength. lia. }
    pose proof (hfs_pr_computation_value Hcomp Hs) as Hx.
    rewrite hfs_pr_trace_nth by exact Hi. now subst x.
  - assert (Hout : S n <= i).
    { apply (proj1 (@nth_error_None hfs_code
        (hfs_sequence_values s) i)) in Hs.
      unfold hfs_sequence_length in Hlength. lia. }
    assert (Ht : hfs_sequence_nth (hfs_pr_trace c p n) i = None).
    { apply (proj2 (@nth_error_None hfs_code
        (hfs_sequence_values (hfs_pr_trace c p n)) i)).
      change (hfs_sequence_length (hfs_pr_trace c p n) <= i).
      rewrite hfs_pr_trace_length. exact Hout. }
    change (None = hfs_sequence_nth (hfs_pr_trace c p n) i).
    now symmetry.
Qed.

(** The raw existential graph used by Foundation's [resultDef]. *)
Definition hfs_pr_result_graph {P} (c : hfs_pr_construction P)
    (parameters : P) (n : nat) (z : hfs_code) : Prop :=
  exists s,
    hfs_pr_computation c parameters s /\
    n < hfs_sequence_length s /\
    hfs_sequence_nth s n = Some z.

Theorem hfs_pr_result_graph_iff : forall P
    (c : hfs_pr_construction P) p n z,
  hfs_pr_result_graph c p n z <-> z = hfs_pr_result c p n.
Proof.
  intros P c p n z. split.
  - intros [s [Hcomp [_ Hnth]]].
    now apply (hfs_pr_computation_value Hcomp Hnth).
  - intro Hz. subst z. exists (hfs_pr_trace c p n). split.
    + apply hfs_pr_trace_computation.
    + split.
      * rewrite hfs_pr_trace_length. lia.
      * apply hfs_pr_trace_last.
Qed.

Corollary hfs_pr_result_graph_functional : forall P
    (c : hfs_pr_construction P) p n x y,
  hfs_pr_result_graph c p n x ->
  hfs_pr_result_graph c p n y -> x = y.
Proof.
  intros P c p n x y Hx Hy.
  apply hfs_pr_result_graph_iff in Hx, Hy. now rewrite Hx, Hy.
Qed.

Corollary hfs_pr_result_graph_exists_unique : forall P
    (c : hfs_pr_construction P) p n,
  exists! z, hfs_pr_result_graph c p n z.
Proof.
  intros P c p n. exists (hfs_pr_result c p n). split.
  - apply hfs_pr_result_graph_iff. reflexivity.
  - intros z Hz. now apply hfs_pr_result_graph_iff in Hz.
Qed.
