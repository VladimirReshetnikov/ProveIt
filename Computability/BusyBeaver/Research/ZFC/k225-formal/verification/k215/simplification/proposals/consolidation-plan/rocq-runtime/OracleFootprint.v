(** Finite oracle-footprint transport, independent of K215 implementation details.

    This is a proposed reusable proof boundary, not a replacement K215 endpoint.
    A query answer can itself be [None], so absent machine rows are observations.
    The result type can contain symbolic configurations, failure, branch tags and
    the positive-progress flag; equality preserves the complete result.

    Original contribution prepared for the ProveIt K215 proof-simplification
    report, 2026-10-22. This file depends only on the standard library. *)
From Coq Require Import List Bool.
Import ListNotations.
Set Implicit Arguments.

Section OracleFootprint.
Variables (Query Answer Result : Type).

(** A terminating, possibly adaptive computation whose only external reads are
    answers from a transition table. Internal arithmetic and control flow may
    be incorporated in the continuations. *)
Inductive query_tree : Type :=
| Done : Result -> query_tree
| Ask : Query -> (Answer -> query_tree) -> query_tree.

Fixpoint value (table : Query -> Answer) (p : query_tree) : Result :=
  match p with
  | Done x => x
  | Ask q k => value table (k (table q))
  end.

Fixpoint reads (table : Query -> Answer) (p : query_tree) : list Query :=
  match p with
  | Done _ => []
  | Ask q k => q :: reads table (k (table q))
  end.

Definition agrees_on (table other : Query -> Answer) (qs : list Query) : Prop :=
  forall q, In q qs -> table q = other q.

(** Exact transport from one observed footprint. It is not necessary to know
    the target trace in advance; equality of the queried answers forces it. *)
Theorem footprint_transport (p : query_tree) :
  forall table other,
  agrees_on table other (reads table p) ->
  value other p = value table p /\ reads other p = reads table p.
Proof.
  induction p as [x|q k IH]; intros table other H.
  - split; reflexivity.
  - assert (E : table q = other q) by (apply H; simpl; now left).
    assert (T : agrees_on table other (reads table (k (table q)))).
    { intros r Hr. apply H. simpl. now right. }
    destruct (IH (table q) table other T) as [Hv Hr].
    simpl. rewrite <- E. split; [exact Hv|now rewrite Hr].
Qed.

Corollary footprint_preserves_spec (p : query_tree) table other
    (Spec : Result -> Prop) :
  agrees_on table other (reads table p) ->
  Spec (value table p) -> Spec (value other p).
Proof.
  intros H HS. rewrite (proj1 (@footprint_transport p table other H)). exact HS.
Qed.

(** A larger statically certified support can cover every symbolic input.
    This is the form needed for the universally quantified register lemmas. *)
Corollary static_support_transport (p : query_tree) table other support :
  (forall q, In q (reads table p) -> In q support) ->
  agrees_on table other support ->
  value other p = value table p /\ reads other p = reads table p.
Proof.
  intros Hin Heq. apply footprint_transport. intros q Hq. apply Heq, Hin, Hq.
Qed.

Variable answer_eqb : Answer -> Answer -> bool.
Hypothesis answer_eqb_sound : forall x y, answer_eqb x y = true -> x = y.

Definition check_support (table other : Query -> Answer) (qs : list Query) : bool :=
  forallb (fun q => answer_eqb (table q) (other q)) qs.

Theorem check_support_sound table other qs :
  check_support table other qs = true -> agrees_on table other qs.
Proof.
  unfold check_support, agrees_on. rewrite forallb_forall.
  intros H q Hq. apply answer_eqb_sound, H, Hq.
Qed.

Corollary checked_footprint_transport (p : query_tree) table other :
  check_support table other (reads table p) = true ->
  value other p = value table p /\ reads other p = reads table p.
Proof. intros H. apply footprint_transport, check_support_sound, H. Qed.
End OracleFootprint.

(** An explicit outcome wrapper records failure, successful symbolic execution,
    and the positive-progress Boolean without any projection that can lose it.
    This corollary preserves all three. An oracle contract still must be proved
    for the target table before using its generic executor soundness theorem. *)
Section Outcomes.
Variables (Q A C : Type).
Definition symbolic_result := option (C * bool).

Theorem exact_outcome_transport
    (p : query_tree Q A symbolic_result) (table other : Q -> A) :
  agrees_on table other (reads table p) ->
  forall out, value table p = out -> value other p = out.
Proof.
  intros H out E. rewrite (proj1 (@footprint_transport Q A symbolic_result p table other H)). exact E.
Qed.
End Outcomes.

Print Assumptions footprint_transport.
Print Assumptions checked_footprint_transport.
Print Assumptions exact_outcome_transport.
