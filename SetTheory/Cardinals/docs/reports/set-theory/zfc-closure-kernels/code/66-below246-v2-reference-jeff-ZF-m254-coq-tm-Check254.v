(** * Check254: every leaf of [p254] passes the symbolic-executor check.

    Registers: [p254] numbers them in source.py declaration order; on the tape they appear in the
    physical order wffstack, param1, axiomcode, scratch2, scratch1, prooflist, nextproof, topwff,
    param2.  [phys_of r] is the tape position of register [r]; [vregs R] the first nine blocks. *)

From Coq Require Import Lists.List Bool.Bool Arith.Arith Lia.
From BusyCoq Require Import TM.
From M254 Require Import RM RMEquiv Prog254 Leaves TM254 Zip SymExec Site.
Import ListNotations.

Definition phys_order : list nat := [2; 4; 3; 7; 6; 8; 0; 1; 5].
Definition phys_of (r : nat) : nat := nth r [6; 7; 0; 2; 1; 8; 4; 3; 5] 0.
Definition vregs (Rg : regs) : list nat := map Rg phys_order.

Definition check_edge (Qs : list bool) (e : edge) : bool :=
  if Nat.leb (length Qs) 34 then
    match e with
    | EInc r => if Nat.ltb r 9 then check_site Qs (OInc (phys_of r)) else false
    | EDecnz r => if Nat.ltb r 9 then check_site Qs (ODec (phys_of r)) else false
    | EBreak k => check_site Qs (OBrk k)
    | EContinue k => check_site Qs (OCont k)
    | EHalt => check_site Qs OHalt
    | ENode _ => false
    end
  else false.

Definition leaves254 : list (list bool * edge) := leaves p254 (nnodes p254 + 1) (root p254).

Lemma all_leaves_check : forallb (fun x => check_edge (fst x) (snd x)) leaves254 = true.
Proof. Time vm_compute. reflexivity. Qed.

Lemma leaf_check P e d :
  walk p254 (nnodes p254 + 1) (root p254) P 0 = Some (e, d) ->
  check_edge (firstn d (P ++ repeat false d)) e = true.
Proof.
  intros W. apply leaves_root in W.
  pose proof all_leaves_check as A. rewrite forallb_forall in A. exact (A _ W).
Qed.
