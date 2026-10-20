(** * Thm224: the 224's numerical calculus K'.

    K230's code calculus [thm230] with its gated bundle replaced by the 224's [bundle224]: the K
    core and the membership vacuity are kept (up to double-negation fusion), and the equality
    vacuity is restricted to the single binder [wel a b]. *)
From Stdlib Require Import Arith Lia.
From K230L Require Import Codes230.
From K224 Require Import Codes224.

Inductive thm224 : nat -> Prop :=
  | U_true : thm224 0
  | U_mp t b : thm224 t -> thm224 (wim t b) -> thm224 b
  | U_gen a h : thm224 h -> thm224 (wal a h)
  | U_r1 a b : thm224 (rho1 a b)
  | U_r2 a b c : thm224 (rho2 a b c)
  | U_r3 a b c : thm224 (rho3 a b c)
  | U_r4 a b c : thm224 (rho4 a b c)
  | U_r5 a b c : thm224 (rho5 a b c)
  | U_r6 a b : thm224 (rho6 a b)
  | U_r7 a b c : thm224 (rho7 a b c)
  | U_r8 a b c u : thm224 (rho8 a b c u)
  | U_bundle a b c : c <> a -> c <> b -> thm224 (bundle224 a b c).
