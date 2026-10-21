(** k225-formal/rocqperm/EnumPerm.v (SHA256 7906b2ab14f05fcfed2fd3911ce0525e47961af69c03ceca02b0897f92e337e3) under namespace K215F. *)
(** * EnumPerm: the abstract proof enumerator of the 215 (Source 159's command-permuted
    commands on Source 149's dominated AX).

    Persistent registers at a command boundary are Enum222's: pl = prooflist, np = nextproof,
    tw = topwff, ws = wffstack, d = param1 (the counter), h = param2 (the cached formula).
    The counter field is read by the commands that use it, and the small commands are permuted:
      0       NIP          : if h = 1 then HALT else h := pop
      1       DROP         : push tw; tw := h
      2       MP    x      : d += x; if wim tw d = h then tw := d and push 0, else tw := 0; h := 0
      3 + c   AX    y x    : U := d; A := d + x; b := h + y; push tw, wal U h, rho8 .. rho1 at
                             (A, b, c) with rho8's fourth argument U;
                             tw := (if c = A or c = b then 0 else bundle222 A b c); d := 0; h := 0
    The first command of a candidate is read from the candidate number itself; later commands are
    read from prooflist - 1. *)
From Coq Require Import Arith Lia Bool.
From K230L Require Import Codes230.
From K215F Require Import Codes222.

Record state : Type := mkState { pl : nat; np : nat; tw : nat; ws : nat; d : nat; h : nat }.

Definition s0 : state := mkState 0 0 0 0 0 0.

(** the stack after AX: [tw] pushed first, then GEN of the cache at [u], then rho8 .. rho1 *)
Definition ax_stack (a h b c u t w : nat) : nat :=
  P (rho1 a b) (P (rho2 a b c) (P (rho3 a b c) (P (rho4 a b c) (P (rho5 a b c)
    (P (rho6 a c) (P (growG a b c) (P (rho8 a b c u) (P (wal u h) (P t w))))))))).

Definition gate (a b c : nat) : nat := if Nat.eqb c a || Nat.eqb c b then 0 else bundle222 a b c.

Definition enum_step (s : state) : option state :=
  let '(pl1, np1) := if Nat.eqb (pl s) 0 then (np s, S (np s)) else (pred (pl s), np s) in
  let '(ac, pl2) := unP pl1 in
  match ac with
  | 0 => if Nat.eqb (h s) 1 then None
         else let '(h1, w1) := unP (ws s) in Some (mkState pl2 np1 (tw s) w1 (d s) h1)
  | 1 => Some (mkState pl2 np1 (h s) (P (tw s) (ws s)) (d s) (h s))
  | 2 => let '(x, pl3) := unP pl2 in
         Some (if Nat.eqb (wim (tw s) (d s + x)) (h s)
               then mkState pl3 np1 (d s + x) (P 0 (ws s)) (d s + x) 0
               else mkState pl3 np1 0 (ws s) (d s + x) 0)
  | S (S (S c)) =>
      let '(y, pl3) := unP pl2 in
      let '(x, pl4) := unP pl3 in
      let b := h s + y in
      Some (mkState pl4 np1 (gate (d s + x) b c) (ax_stack (d s + x) (h s) b c (d s) (tw s) (ws s)) 0 0)
  end.

(** [run n s]: n steps from s, [None] if a step halts on the way *)
Fixpoint run (n : nat) (s : state) : option state :=
  match n with
  | 0 => Some s
  | S n => match enum_step s with Some s' => run n s' | None => None end
  end.

Definition enum_halts : Prop := exists n s, run n s0 = Some s /\ enum_step s = None.
