(** NEW RESEARCH DRAFT. Not compiled or kernel-checked in this environment.
    This is only the representation-independent coverage lemma. It is not
    the missing generalized Bisim230 soundness theorem or K215 endpoint.
    Original review helper, 2026-10-21. *)
From Coq Require Import Bool PArith Arith.

Module PositiveTrieCoverage.
Section Generic.
Variable A : Type.

Inductive trie : Type :=
| Empty
| Branch (value : A) (left right : trie).

Fixpoint lookup (T : trie) (p : positive) : option A :=
  match T with
  | Empty => None
  | Branch x l r =>
      match p with
      | xH => Some x
      | xO q => lookup l q
      | xI q => lookup r q
      end
  end.

Fixpoint all (f : A -> bool) (T : trie) : bool :=
  match T with
  | Empty => true
  | Branch x l r => f x && all f l && all f r
  end.

Theorem lookup_checked (f : A -> bool) T :
  all f T = true -> forall p x, lookup T p = Some x -> f x = true.
Proof.
  induction T as [|a l IHl r IHr]; cbn.
  - intros _ p x H. discriminate.
  - intro H. apply andb_true_iff in H as [H Hr].
    apply andb_true_iff in H as [Ha Hl].
    intros p x E. destruct p as [p|p|]; cbn in E.
    + exact (IHr Hr p x E).
    + exact (IHl Hl p x E).
    + injection E as E. subst x. exact Ha.
Qed.

Fixpoint digits (p : positive) : nat :=
  match p with xH => 1 | xO q | xI q => S (digits q) end.
Fixpoint probes (T : trie) (p : positive) : nat :=
  match T with
  | Empty => 0
  | Branch _ l r =>
      match p with xH => 1 | xO q => S (probes l q) | xI q => S (probes r q) end
  end.
Theorem probes_le_digits T : forall p, probes T p <= digits p.
Proof.
  induction T as [|a l IHl r IHr]; intros p.
  - cbn. apply Nat.le_0_l.
  - destruct p as [p|p|]; cbn.
    + apply le_n_S. apply IHr.
    + apply le_n_S. apply IHl.
    + apply le_n.
Qed.
End Generic.
End PositiveTrieCoverage.

(* No printed assumptions are represented as executed audit evidence. *)
