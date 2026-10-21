(** The 215's boot registers: nextproof = 4, every other register zero. *)
From K230 Require Import RM.
Definition R0p : regs := upd regs0 0 4.
