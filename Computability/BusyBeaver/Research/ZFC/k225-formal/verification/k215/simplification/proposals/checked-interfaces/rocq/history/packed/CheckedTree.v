(** A direct checked-tree adapter. Subtree cut values are unconstrained.
    A successful lookup always returns a leaf checked by allTree. *)
From Coq Require Import List Bool Arith NArith.
From K230 Require Import RM.
From K230P Require Import Bisim230.
Require Import LookupNormalized.
Import ListNotations.

Inductive CTree (A : Type) : Type :=
| CEmpty
| CLeaf (x : A)
| CNode (cut : N) (left right : CTree A).

Arguments CEmpty {A}.
Arguments CLeaf {A} x.
Arguments CNode {A} cut left right.

Fixpoint lookup {A} (T : CTree A) (j : N) : option A :=
  match T with
  | CEmpty => None
  | CLeaf x => if N.eqb j 0 then Some x else None
  | CNode cut l r =>
      if N.ltb j cut then lookup l j else lookup r (j-cut)%N
  end.

Fixpoint allTree {A} (f : A -> bool) (T : CTree A) : bool :=
  match T with
  | CEmpty => true
  | CLeaf x => f x
  | CNode _ l r => allTree f l && allTree f r
  end.

Lemma lookup_allTree {A} (f : A -> bool) T : allTree f T = true ->
  forall j x, lookup T j = Some x -> f x = true.
Proof.
  induction T as [|e|cut l IHl r IHr]; cbn; intros H j x E.
  - discriminate.
  - destruct (N.eqb j 0); [injection E as <-; exact H|discriminate].
  - apply andb_prop in H as [Hl Hr].
    destruct (N.ltb j cut).
    + exact (IHl Hl j x E).
    + exact (IHr Hr (j-cut)%N x E).
Qed.

Definition getTree {A} (decode : A -> entry) (T : CTree A) (j : N)
    : option (list bool * list bool) :=
  match lookup T j with
  | Some x => let '(a,b,_,_) := decode x in Some (a,b)
  | None => None
  end.

Definition check {A} (decode : A -> entry) (t1 t2 : tree) (T : CTree A) : bool :=
  LCheck.branch_ok t1 t2 (getTree decode T) [] [] 0 &&
  allTree (fun x => LCheck.entry_ok t1 t2 (getTree decode T) (decode x)) T.

Lemma allTree_validated {A} (decode : A -> entry) t1 t2 T :
  allTree (fun x => LCheck.entry_ok t1 t2 (getTree decode T) (decode x)) T = true ->
  LCheck.validated t1 t2 (getTree decode T).
Proof.
  intros H j a b E. unfold getTree in E.
  destruct (lookup T j) as [x|] eqn:El; [|discriminate].
  destruct (decode x) as [[[a' b'] k] l] eqn:Ed.
  injection E as Ea Eb. subst a b. exists k, l.
  pose proof (lookup_allTree _ T H j x El) as Hx.
  cbn in Hx. rewrite Ed in Hx. exact Hx.
Qed.

Theorem check_halts_iff {A} p1 p2 (decode : A -> entry) T :
  check decode (ptree p1) (ptree p2) T = true ->
  forall R, rm_halts p1 ([],R) <-> rm_halts p2 ([],R).
Proof.
  unfold check. intros H. apply andb_prop in H as [Hroot Hall].
  exact (LCheck.initial_halts_iff p1 p2 (getTree decode T)
    (allTree_validated decode _ _ _ Hall) Hroot).
Qed.

(** Untrusted data construction. Its output is accepted solely by check.
    No correctness theorem for this function is a source-proof prerequisite. *)
Fixpoint buildTree {A} (fuel : nat) (xs : list A) : CTree A :=
  match fuel, xs with
  | _, [] => CEmpty
  | _, [x] => CLeaf x
  | 0, _ => CEmpty
  | S f, _ =>
      let k := length xs / 2 in
      CNode (N.of_nat k) (buildTree f (firstn k xs)) (buildTree f (skipn k xs))
  end.

Print Assumptions lookup_allTree.
Print Assumptions check_halts_iff.
