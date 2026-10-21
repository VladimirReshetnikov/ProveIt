(** Numeric four-register adapter for the exact NIP/DROP command shapes.
    Pair/unpair are quantified, so instantiation uses the repository's
    existing unP_P theorem. This file does not reprove the whole endpoint. *)
From Coq Require Import List Arith Lia.
Require Import EarlyHaltSelection.
Import ListNotations.

Section Native.
  Variable P : nat -> nat -> nat.
  Variable unP : nat -> nat * nat.
  Hypothesis unP_P : forall x w, unP (P x w) = (x, w).

  Definition tup := (nat * nat * nat * nat)%type.
  Definition xstep (k : cmd) (q : tup) : option tup :=
    let '(t, w, d, h) := q in
    match k with
    | NIP => if Nat.eqb h 1 then None
             else Some (t, snd (unP w), d, fst (unP w))
    | DROP => Some (h, P t w, d, h)
    end.
  Fixpoint exec (L : list cmd) (q : tup) : option tup :=
    match L with
    | [] => Some q
    | k :: rest => match xstep k q with
                   | Some q' => exec rest q' | None => None end
    end.
  Definition embed (d : nat) (s : @state nat nat) : tup :=
    (top s, stack s, d, cache s).

  Lemma step_embed (k : cmd) (d : nat) (s : @state nat nat) :
    xstep k (embed d s) =
    option_map (embed d) (step P unP (fun h => Nat.eqb h 1) k s).
  Proof.
    destruct s as [t w h]; destruct k; cbn [xstep embed step top stack cache].
    - destruct (Nat.eqb h 1); [reflexivity|].
      destruct (unP w); reflexivity.
    - reflexivity.
  Qed.

  Lemma exec_embed (L : list cmd) (d : nat) (s : @state nat nat) :
    exec L (embed d s) =
    option_map (embed d) (run P unP (fun h => Nat.eqb h 1) L s).
  Proof.
    revert s; induction L as [|k rest IH]; intro s; [reflexivity|].
    cbn [exec run]; rewrite step_embed.
    destruct (step P unP (fun h => Nat.eqb h 1) k s);
      [apply IH|reflexivity].
  Qed.

  Theorem native_select (before after : list nat) (x g d h tail : nat) :
    exec (selector before after)
      (g, pack P (before ++ x :: after ++ [0]) tail, d, h) = None \/
    exec (selector before after)
      (g, pack P (before ++ x :: after ++ [0]) tail, d, h) = Some (x, tail, d, 0).
  Proof.
    change (exec (selector before after)
      (embed d (State g (pack P (before ++ x :: after ++ [0]) tail) h)) = None \/
      exec (selector before after)
      (embed d (State g (pack P (before ++ x :: after ++ [0]) tail) h))
        = Some (embed d (State x tail 0))).
    rewrite !exec_embed.
    destruct (select_with_zero P unP unP_P (fun h => Nat.eqb h 1) 0
      before after x g h tail) as [H|H]; rewrite H; [now left|now right].
  Qed.
  Corollary native_select_nth (rows : list nat) (j x g d h tail : nat)
      (Hx : nth_error rows j = Some x) :
    exec (repeat NIP (j + 1) ++ DROP :: repeat NIP (length rows + 1 - j))
      (g, pack P (rows ++ [0]) tail, d, h) = None \/
    exec (repeat NIP (j + 1) ++ DROP :: repeat NIP (length rows + 1 - j))
      (g, pack P (rows ++ [0]) tail, d, h) = Some (x, tail, d, 0).
  Proof.
    destruct (nth_error_split rows j Hx) as [before [after [E Hj]]].
    subst rows; rewrite <- app_assoc; cbn [app].
    replace (length (before ++ x :: after) + 1 - j)
      with (length after + 2) by (rewrite app_length; cbn [length]; lia).
    rewrite <- Hj.
    apply native_select.
  Qed.
End Native.

Print Assumptions native_select.
Print Assumptions native_select_nth.
