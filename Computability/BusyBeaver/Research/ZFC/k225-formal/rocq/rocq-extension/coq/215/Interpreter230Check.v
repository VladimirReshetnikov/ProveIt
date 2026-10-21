(** Runtime-only fork of coq/tm/Interpreter230Check.v; original SHA256 031a654d6b6ffdbfc000dd60bf219549abf8fc90af1e52432aee32764f01d08a.
    Sparse labels [79, 121, 140, 175, 183, 191, 192, 202, 208, 219, 224, 226, 227, 228, 229] are disabled; the 215's startup frame (boot
    registers R0p); site paths of up to 48 bits. Original source immutable. *)
From K215F Require Import Prog215 Regs215.
(** Finite check of every K230 leaf; exact logical-to-physical permutation. *)
From Coq Require Import Lists.List Bool.Bool Arith.Arith Lia.
From BusyCoq Require Import TM.
From K230 Require Import RM RMEquiv Prog230 Interpreter230Leaves.
From K215F Require Import TM230 Zip Runtime230Core Interpreter230Sites.
Import ListNotations.

Definition phys_order : list nat := [2; 8; 1; 4; 3; 7; 0; 5; 6].
Definition phys_of (r : nat) : nat := nth r [6; 2; 0; 4; 3; 7; 8; 5; 1] 0.
Definition vregs (Rg : regs) : list nat := map Rg phys_order.

Definition check_edge (Qs : list bool) (e : edge) : bool :=
  if Nat.leb (length Qs) 48 then
    match e with
    | EInc r => if Nat.ltb r 9 then check_site Qs (OInc (phys_of r)) else false
    | EDecnz r => if Nat.ltb r 9 then check_site Qs (ODec (phys_of r)) else false
    | EBreak k => check_site Qs (OBrk k)
    | EContinue k => check_site Qs (OCont k)
    | EHalt => check_site Qs OHalt
    | ENode _ => false
    end
  else false.

Definition leaves230 : list (list bool * edge) := leaves p215 (nnodes p215 + 1) (root p215).

Lemma all_leaves_check : forallb (fun x => check_edge (fst x) (snd x)) leaves230 = true.
Proof. Time vm_compute. reflexivity. Qed.

Lemma leaf_check P e d :
  walk p215 (nnodes p215 + 1) (root p215) P 0 = Some (e, d) ->
  check_edge (firstn d (P ++ repeat false d)) e = true.
Proof.
  intros W. apply leaves_root in W.
  pose proof all_leaves_check as A. rewrite forallb_forall in A. exact (A _ W).
Qed.
