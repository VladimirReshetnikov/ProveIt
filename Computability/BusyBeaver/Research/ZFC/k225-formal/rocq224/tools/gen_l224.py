"""Write L224Def.v and L224Prop.v: Jeff's pure-logic calculus lprov with the atomic vacuity axiom
LB6a split into membership vacuity (any fresh binder) and the 224's equality helper (binder
wel x y only), and his generated propositional lemmas transferred to it by renaming."""
import re
from pathlib import Path

BASE = Path(r"C:\Users\vresh\AppData\Local\Temp\claude\C--ProveIt--claude-worktrees-merge-article-groups-491e11\31b37d1b-6b02-4181-babf-8c85ac50cb17\scratchpad")
J = BASE / "rocq225/pkg/vendor/jeff-reference/ZF/stdzf/coq"
OUT = BASE / "k224rocq/src"

DEF = """(** * L224Def: Jeff's pure-logic calculus [lprov] (ZF/stdzf L1_LDef.v) for the 224's calculus.

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
"""
(OUT / "L224Def.v").write_text(DEF, newline="\n")

p = (J / "L1_LProp.v").read_text()
assert "LB6" not in p and "LB7" not in p and "LB8" not in p and "LGEN" not in p
p = p.replace("From Coq Require Import Arith.Arith.\nFrom ZF Require Import Logic L1_LDef.",
              "From Stdlib Require Import Arith.Arith.\nFrom ZF Require Import Logic.\nFrom K224 Require Import L224Def.")
assert "L224Def" in p
p = re.sub(r"\blprov\b", "lprov224", p)
p = re.sub(r"\bLDET\b", "MDET", p)
p = re.sub(r"\bLB([123])\b", r"MB\1", p)
p = re.sub(r"\b(llp\d+|lpc_\w+)\b", lambda m: "m" + m.group(1), p)
p = "(** Jeff's propositional lemmas (ZF/stdzf L1_LProp.v) for [lprov224], by renaming (gen_l224.py). *)\n" + p
(OUT / "L224Prop.v").write_text(p, newline="\n")
print("wrote L224Def.v, L224Prop.v")
