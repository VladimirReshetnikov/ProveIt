(** * Thm254: the machine's calculus at the level of codes.

    [thm254 n]: n is derivable from the AX rows and gated bundles by MP and GEN, with the
    truth code 0 as an axiom (stack zeros, failed MP and failed gates produce 0).
    L1 proves  enum254_halts <-> thm254 1;  the bridge relates thm254 to the set theory SIR. *)
From Coq Require Import Arith Lia.
From M254L Require Import Codes254.

Inductive thm254 : nat -> Prop :=
  | T_true : thm254 0
  | T_mp t b : thm254 t -> thm254 (wim t b) -> thm254 b
  | T_gen a h : thm254 h -> thm254 (wal a h)
  | T_r1 a b : thm254 (rho1 a b)
  | T_r2 a b c : thm254 (rho2 a b c)
  | T_r3 a b c : thm254 (rho3 a b c)
  | T_r4 a b c : thm254 (rho4 a b c)
  | T_r5 a b c : thm254 (rho5 a b c)
  | T_r6 a b : thm254 (rho6 a b)
  | T_r7 a b c : thm254 (rho7 a b c)
  | T_r8 a b c u : thm254 (rho8 a b c u)
  | T_bundle a b c : c <> a -> c <> b -> thm254 (bundle a b c).
