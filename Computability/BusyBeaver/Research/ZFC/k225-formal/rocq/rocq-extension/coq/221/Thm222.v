(** Copy of rocq224/src/Thm222.v (SHA256 bb08f4d7b5d5b7cb7318f15de5756c6cc46d7c433fb7e9f6fb51e210d6ba305e) under namespace K221F. *)
(** * Thm222: the seed-K 222's numerical calculus.

    K230's [thm230] with rho7 replaced by the merged equality row [growG] and the gated bundle
    replaced by the helper-free seed bundle [bundle222]. *)
From Stdlib Require Import Arith Lia.
From K230L Require Import Codes230.
From K221F Require Import Codes222.

Inductive thm222 : nat -> Prop :=
  | W_true : thm222 0
  | W_mp t b : thm222 t -> thm222 (wim t b) -> thm222 b
  | W_gen a h : thm222 h -> thm222 (wal a h)
  | W_r1 a b : thm222 (rho1 a b)
  | W_r2 a b c : thm222 (rho2 a b c)
  | W_r3 a b c : thm222 (rho3 a b c)
  | W_r4 a b c : thm222 (rho4 a b c)
  | W_r5 a b c : thm222 (rho5 a b c)
  | W_r6 a b : thm222 (rho6 a b)
  | W_rG a b c : thm222 (growG a b c)
  | W_r8 a b c u : thm222 (rho8 a b c u)
  | W_bundle a b c : c <> a -> c <> b -> thm222 (bundle222 a b c).
