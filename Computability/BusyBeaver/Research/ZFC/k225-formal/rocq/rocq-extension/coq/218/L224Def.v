(** Copy of rocq224/src/L224Def.v (SHA256 13c1860396cbb15d3ed29a56fa2919feb0b9db728813f8a3ac1b4098d5d83045) under namespace K218F. *)
(** * L224Def: Jeff's pure-logic calculus [lprov] (ZF/stdzf L1_LDef.v) for the 224's calculus.

    Identical to [lprov] except for the atomic vacuity axiom LB6a: membership vacuity keeps every
    fresh binder ([MB6r]), and equality vacuity is the 224's helper, with the single binder
    [wel x y] ([MB6h]). *)
From ZF Require Import Logic.
From K230S Require Import KCode230.

Inductive lprov224 : wff -> Prop :=
  | MDET a b : lprov224 (Wim a b) -> lprov224 a -> lprov224 b
  | MGEN x a : lprov224 a -> lprov224 (Wal x a)
  | MB1 a b c : lprov224 (Wim (Wim a b) (Wim (Wim b c) (Wim a c)))
  | MB2 a : lprov224 (Wim (Wim (Wn a) a) a)
  | MB3 a b : lprov224 (Wim a (Wim (Wn a) b))
  | MB4 x a b : lprov224 (Wim (Wal x (Wim a b)) (Wim (Wal x a) (Wal x b)))
  | MB6r x y z : x <> z -> y <> z -> lprov224 (Wim (Wel x y) (Wal z (Wel x y)))
  | MB6h x y : lprov224 (Wim (Weq x y) (Wal (wel x y) (Weq x y)))
  | MB6b x y a : lprov224 (Wim (Wal x (Wal y a)) (Wal y (Wal x a)))
  | MB6c x a : lprov224 (Wim (Wex x (Wal x a)) a)
  | MB7 x y : lprov224 (Wex x (Weq x y))
  | MB8a x y z : lprov224 (Wim (Weq x y) (Wim (Weq x z) (Weq y z)))
  | MB8b x y z : lprov224 (Wim (Weq x y) (Wim (Wel x z) (Wel y z)))
  | MB8c x y z : lprov224 (Wim (Weq x y) (Wim (Wel z x) (Wel z y))).
