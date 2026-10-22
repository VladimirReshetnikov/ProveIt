(** Proposed standalone interface prototype. NOT compiler-checked here.
    No axioms, admitted obligations, native computation or downloaded scripts. *)
From Coq Require Import List Bool Arith.
Import ListNotations.

Inductive index (A : Type) : Type :=
| empty : index A
| leaf : A -> index A
| branch : nat -> index A -> index A -> index A.
Arguments empty {A}.
Arguments leaf {A} _.
Arguments branch {A} _ _ _.

Fixpoint lookup {A} (T : index A) (j : nat) : option A :=
  match T with
  | empty => None
  | leaf x => Some x
  | branch cut l r => if j <? cut then lookup l j else lookup r (j-cut)
  end.
Fixpoint all {A} (f : A -> bool) (T : index A) : bool :=
  match T with
  | empty => true
  | leaf x => f x
  | branch _ l r => all f l && all f r
  end.

Theorem lookup_all {A} (T : index A) (f : A -> bool) :
  forall j x, lookup T j = Some x -> all f T = true -> f x = true.
Proof.
  induction T as [|y|cut l IHl r IHr]; intros j x H E.
  - discriminate H.
  - simpl in H,E. injection H as H. subst x. exact E.
  - simpl in H,E. apply andb_true_iff in E as [El Er].
    destruct (j <? cut); [eapply IHl | eapply IHr]; eauto.
Qed.

(** This malformed cut does not preserve flatten/list indexing. Nevertheless,
    every successful lookup returns an entry checked by all. *)
Definition wrong_cut : index nat := branch 0 (leaf 11) (leaf 22).
Example routes_right : lookup wrong_cut 0 = Some 22.
Proof. reflexivity. Qed.
Example not_flatten_lookup : nth_error [11;22] 0 <> lookup wrong_cut 0.
Proof. discriminate. Qed.
Example checked_despite_wrong_cut :
  all (fun n => (n =? 11) || (n =? 22)) wrong_cut = true.
Proof. reflexivity. Qed.

Print Assumptions lookup_all.
