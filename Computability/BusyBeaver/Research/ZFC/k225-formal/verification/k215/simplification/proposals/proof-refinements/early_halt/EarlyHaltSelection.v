(** Early-halting selection from a finite stack prefix.
    This is an abstract command theorem, not a new K215 endpoint.
    The only stack hypothesis is the exact push/pop inverse law. *)
From Coq Require Import List Arith Lia.
Import ListNotations.

Section Selector.
  Context {A S : Type}.
  Variable push : A -> S -> S.
  Variable pop : S -> A * S.
  Hypothesis pop_push : forall x s, pop (push x s) = (x, s).
  Variable alarm : A -> bool.
  Variable zero : A.

  Record state := State { top : A; stack : S; cache : A }.
  Inductive cmd := NIP | DROP.

  Definition step (c : cmd) (s : state) : option state :=
    match c with
    | NIP => if alarm (cache s) then None
             else let '(x, w) := pop (stack s) in Some (State (top s) w x)
    | DROP => Some (State (cache s) (push (top s) (stack s)) (cache s))
    end.

  Fixpoint run (cs : list cmd) (s : state) : option state :=
    match cs with
    | [] => Some s
    | c :: rest => match step c s with
                   | None => None
                   | Some t => run rest t
                   end
    end.

  Fixpoint pack (xs : list A) (tail : S) : S :=
    match xs with [] => tail | x :: rest => push x (pack rest tail) end.

  Definition Allows (r : option state) (s : state) : Prop :=
    r = None \/ r = Some s.

  Lemma run_append (p q : list cmd) (s : state) :
    run (p ++ q) s =
      match run p s with None => None | Some t => run q t end.
  Proof.
    revert s; induction p as [|c p IH]; intro s; simpl; [reflexivity|].
    destruct (step c s); [apply IH|reflexivity].
  Qed.

  Lemma pack_append (xs ys : list A) (tail : S) :
    pack (xs ++ ys) tail = pack xs (pack ys tail).
  Proof. induction xs; simpl; [reflexivity|now rewrite IHxs]. Qed.

  (** Reading a nonempty prefix either triggers the alarm or returns
      the last explicit head. No head-non-alarm premise is needed. *)
  Theorem drain_prefix (xs : list A) (x t h : A) (tail : S) :
    Allows (run (repeat NIP (length xs + 1))
                (State t (pack (xs ++ [x]) tail) h))
           (State t tail x).
  Proof.
    revert t h; induction xs as [|a xs IH]; intros t h.
    - cbn [Nat.add length app pack repeat run step top stack cache Allows].
      destruct (alarm h); [now left|].
      rewrite pop_push; cbn; now right.
    - cbn [Nat.add length app pack repeat run step top stack cache Allows].
      destruct (alarm h); [now left|].
      rewrite pop_push; cbn.
      apply IH.
  Qed.

  (** An explicit zero is retained below the selected head. The remaining
      arbitrary tail is never inspected on a nonhalting execution. *)
  Definition selector (before after : list A) : list cmd :=
    repeat NIP (length before + 1) ++
      DROP :: repeat NIP (length after + 2).

  Theorem select_with_zero (before after : list A) (x g h : A) (tail : S) :
    Allows
      (run (selector before after)
        (State g (pack (before ++ x :: after ++ [zero]) tail) h))
      (State x tail zero).
  Proof.
    unfold selector.
    replace (before ++ x :: after ++ [zero])
      with ((before ++ [x]) ++ (after ++ [zero])) by
        (rewrite <- app_assoc; reflexivity).
    rewrite pack_append, run_append.
    destruct (drain_prefix before x g h (pack (after ++ [zero]) tail))
      as [H|H]; rewrite H; [now left|].
    cbn [run step top stack cache].
    replace (length after + 2) with (length (g :: after) + 1) by (simpl; lia).
    change (Allows
      (run (repeat NIP (length (g :: after) + 1))
        (State x (pack ((g :: after) ++ [zero]) tail) x))
      (State x tail zero)).
    apply drain_prefix.
  Qed.
End Selector.

Print Assumptions drain_prefix.
Print Assumptions select_with_zero.
