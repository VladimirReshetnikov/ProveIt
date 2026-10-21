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
    One step decodes the next command ([decode]) and runs it on the working registers
    ([xstep]). The first command of a candidate is read from the candidate number itself; later
    commands are read from prooflist - 1. *)
From Coq Require Import Arith Lia Bool.
From K230L Require Import Codes230.
From NS Require Import Codes222.

Record state : Type := mkState { pl : nat; np : nat; tw : nat; ws : nat; d : nat; h : nat }.

(** the stack after AX: [tw] pushed first, then GEN of the cache at [u], then rho8 .. rho1 *)
Definition ax_stack (a h b c u t w : nat) : nat :=
  P (rho1 a b) (P (rho2 a b c) (P (rho3 a b c) (P (rho4 a b c) (P (rho5 a b c)
    (P (rho6 a c) (P (growG a b c) (P (rho8 a b c u) (P (wal u h) (P t w))))))))).

Definition gate (a b c : nat) : nat := if Nat.eqb c a || Nat.eqb c b then 0 else bundle222 a b c.

(** ** Commands on the working registers (current, stack, counter, cache) *)
Inductive cmd : Type := CNIP | CDROP | CMP (x : nat) | CAX (c x y : nat).

Definition tup : Type := (nat * nat * nat * nat)%type.

Definition xstep (k : cmd) (q : tup) : option tup :=
  let '(t, w, dd, hh) := q in
  match k with
  | CNIP => if Nat.eqb hh 1 then None else Some (t, snd (unP w), dd, fst (unP w))
  | CDROP => Some (hh, P t w, dd, hh)
  | CMP x => Some (if Nat.eqb (wim t (dd + x)) hh then (dd + x, P 0 w, dd + x, 0) else (0, w, dd + x, 0))
  | CAX c x y => Some (gate (dd + x) (hh + y) c, ax_stack (dd + x) hh (hh + y) c dd t w, 0, 0)
  end.

(** the command packed at [z], and the rest pointer *)
Definition decode (z : nat) : cmd * nat :=
  let '(ac, r) := unP z in
  match ac with
  | 0 => (CNIP, r)
  | 1 => (CDROP, r)
  | 2 => let '(x, r') := unP r in (CMP x, r')
  | S (S (S c)) => let '(y, r') := unP r in let '(x, r'') := unP r' in (CAX c x y, r'')
  end.

Definition tupof (s : state) : tup := (tw s, ws s, d s, h s).

Definition enum_step (s : state) : option state :=
  let '(pl1, np1) := if Nat.eqb (pl s) 0 then (np s, S (np s)) else (pred (pl s), np s) in
  let '(k, r) := decode pl1 in
  match xstep k (tupof s) with
  | Some (t, w, dd, hh) => Some (mkState r np1 t w dd hh)
  | None => None
  end.

(** [run n s]: n steps from s, [None] if a step halts on the way *)
Fixpoint run (n : nat) (s : state) : option state :=
  match n with
  | 0 => Some s
  | S n => match enum_step s with Some s' => run n s' | None => None end
  end.
