#!/usr/bin/env python3
"""Fork Enum222.lean into EnumDom.lean: the enumerator of the 217-state machine (Source 149).

  python generate_enumdom.py      (from Computability/BusyBeaver/Lean)

Only the AX command changes. Its wire `(c, z, y, x)` (the fields of `.ax c x y u` in order) now
reads `U = d + z`, `A = U + x`, `B = h + y`: the rows are emitted at `(A, B, c)` with the fourth
rho8 argument `U` and the generalization `wal U h`, so every emitted rho8 instance has `U ≤ A`.
Soundness is unchanged (every emitted code is a C222 row); completeness compiles derivations of
the dominated calculus `KCodeDom.CDom`, whose rho8 leaf `rho8 a b c u` (`u ≤ a`) is the command
`AX(c, u, b, a - u)`, and `CDom` derives every C222 code (`KCodeDom.cdom_of_c222`).
"""
from pathlib import Path

D = Path("BusyBeaver/ZFC")
s = (D / "Enum222.lean").read_text(encoding="utf-8")
head = s.index("import BusyBeaver.ZFC.KCode222")
s = s[head:]


def rep(a, b, n=1):
    global s
    assert s.count(a) == n, (a[:70], s.count(a))
    s = s.replace(a, b)


rep("import BusyBeaver.ZFC.KCode222", "import BusyBeaver.ZFC.KCodeDom")
a = s.index("/-!")
b = s.index("-/", a) + 2
s = s[:a] + """/-!
The abstract proof enumerator of the 217-state machine (Source 149's dominated AX), and L1.

The registers and the MP, DROP and NIP commands are `Enum222`'s. The AX command reads its three
fields `z, y, x` as

```text
3 + c  AX   z y x   U := d + z; A := U + x; B := h + y;
                    push tw, All(U,h), rho8(A,B,c,U), G(A,B,c), rho6 … rho1 at (A,B,c);
                    tw := (c = A or c = B ? 0 : bundle A B c); d := 0; h := 0
```

so every emitted rho8 instance has its fourth argument at most its first.

Main theorem `enum_halts_iff`: the enumerator halts from the zero state iff the falsity code 1
is derivable in `C222`. Soundness is `Enum222`'s stack invariant. Completeness compiles a
derivation of the dominated calculus `KCodeDom.CDom` into command blocks (a dominated rho8 leaf
`rho8 a b c u`, `u ≤ a`, is `AX(c, u, b, a - u)`), and `CDom` derives every `C222` code.
Forked from `Enum222.lean` by `Research/ZFC/k225-formal/generate_enumdom.py`.
-/""" + s[b:]
rep("namespace SetTheory.BusyBeaver.ZFC.Enum222", "namespace SetTheory.BusyBeaver.ZFC.EnumDom")
rep("end SetTheory.BusyBeaver.ZFC.Enum222", "end SetTheory.BusyBeaver.ZFC.EnumDom")
rep("open SetTheory.BusyBeaver.ZFC.Code254 SetTheory.BusyBeaver.ZFC.KCode222",
    "open SetTheory.BusyBeaver.ZFC.Code254 SetTheory.BusyBeaver.ZFC.KCode222\n"
    "open SetTheory.BusyBeaver.ZFC.KCodeDom")

# the stack: GEN of the cache at U
rep("""/-- The stack after AX: `tw` first, then GEN of the cache, then rho8 … rho1. -/
def axStack (a h b c u t w : Nat) : Nat :=
  P (rho1 a b) (P (rho2 a b c) (P (rho3 a b c) (P (rho4 a b c) (P (rho5 a b c)
    (P (rho6 a c) (P (growG a b c) (P (rho8 a b c u) (P (wal a h) (P t w)))))))))""",
    """/-- The stack after AX: `tw` first, then GEN of the cache at `u`, then rho8 … rho1. -/
def axStack (a h b c u t w : Nat) : Nat :=
  P (rho1 a b) (P (rho2 a b c) (P (rho3 a b c) (P (rho4 a b c) (P (rho5 a b c)
    (P (rho6 a c) (P (growG a b c) (P (rho8 a b c u) (P (wal u h) (P t w)))))))))""")
rep("""  | .ax c x y u, ⟨t, s, d, h⟩ =>
      some ⟨gate (d + x) (h + y) c, axStack (d + x) h (h + y) c u t s, 0, 0⟩""",
    """  | .ax c x y u, ⟨t, s, d, h⟩ =>
      some ⟨gate (d + x + u) (h + y) c, axStack (d + x + u) h (h + y) c (d + x) t s, 0, 0⟩""")
rep("""      some ⟨(unP (unP (unP (unP pl1).2).2).2).2, np1,
            gate (s.d + (unP (unP pl1).2).1) (s.h + (unP (unP (unP pl1).2).2).1) c,
            axStack (s.d + (unP (unP pl1).2).1) s.h (s.h + (unP (unP (unP pl1).2).2).1) c
              (unP (unP (unP (unP pl1).2).2).2).1 s.tw s.ws, 0, 0⟩""",
    """      some ⟨(unP (unP (unP (unP pl1).2).2).2).2, np1,
            gate (s.d + (unP (unP pl1).2).1 + (unP (unP (unP (unP pl1).2).2).2).1)
              (s.h + (unP (unP (unP pl1).2).2).1) c,
            axStack (s.d + (unP (unP pl1).2).1 + (unP (unP (unP (unP pl1).2).2).2).1) s.h
              (s.h + (unP (unP (unP pl1).2).2).1) c (s.d + (unP (unP pl1).2).1) s.tw s.ws, 0, 0⟩""")

# soundness: the generalization is at u
rep("good_cons (C222.r8 a b c u) <| good_cons (C222.gen a hh) <|",
    "good_cons (C222.r8 a b c u) <| good_cons (C222.gen u hh) <|")

# the compiler
rep("""def axList (a h b c u : Nat) : List Nat :=
  [rho1 a b, rho2 a b c, rho3 a b c, rho4 a b c, rho5 a b c, rho6 a c, growG a b c,
   rho8 a b c u, wal a h]""",
    """def axList (a h b c u : Nat) : List Nat :=
  [rho1 a b, rho2 a b c, rho3 a b c, rho4 a b c, rho5 a b c, rho6 a c, growG a b c,
   rho8 a b c u, wal u h]""")
rep("""theorem cstep_ax (c x y u t S d h : Nat) :
    cstep (.ax c x y u) ⟨t, S, d, h⟩ =
      some ⟨gate (d + x) (h + y) c, axStack (d + x) h (h + y) c u t S, 0, 0⟩ := rfl""",
    """theorem cstep_ax (c x y u t S d h : Nat) :
    cstep (.ax c x y u) ⟨t, S, d, h⟩ =
      some ⟨gate (d + x + u) (h + y) c, axStack (d + x + u) h (h + y) c (d + x) t S, 0, 0⟩ := rfl""")
rep("""  rw [show gate (0 + 1) (0 + 0) 1 = 0 from gate_self _ _, axStack_eq]
  exact cexec_nips 0 S 0 (axList (0 + 1) 0 (0 + 0) 1 0) 0 0 (by omega) (axList_ne_one _ _ _ _ _)""",
    """  rw [show gate (0 + 1 + 0) (0 + 0) 1 = 0 from gate_self _ _, axStack_eq]
  exact cexec_nips 0 S 0 (axList (0 + 1 + 0) 0 (0 + 0) 1 (0 + 1)) 0 0 (by omega)
    (axList_ne_one _ _ _ _ _)""")

# leaves: AX(c, u, b, a - u) puts U = u, A = a; every row but rho8 takes u = a
rep("""/-- After `discard`, an AX command with `x = a`, `y = b` pushes the rows at `(a, b, c, u)`. -/
theorem cexec_discard_ax (T S a b c u : Nat) (rest : List Cmd) :
    cexec (discard ++ (.ax c a b u :: rest)) ⟨T, S, 0, 0⟩ =
      cexec rest ⟨gate a b c, pushL (axList a 0 b c u ++ [0]) S, 0, 0⟩ := by
  rw [cexec_append, cexec_discard]
  simp only
  rw [cexec_cons_some (cstep_ax c a b u 0 S 0 0)]
  simp only [Nat.zero_add]
  rfl""",
    """/-- After `discard`, `AX(c, u, b, a - u)` with `u ≤ a` pushes the rows at `(a, b, c, u)`. -/
theorem cexec_discard_ax (T S a b c u : Nat) (hu : u ≤ a) (rest : List Cmd) :
    cexec (discard ++ (.ax c u b (a - u) :: rest)) ⟨T, S, 0, 0⟩ =
      cexec rest ⟨gate a b c, pushL (axList a 0 b c u ++ [0]) S, 0, 0⟩ := by
  rw [cexec_append, cexec_discard]
  simp only
  rw [cexec_cons_some (cstep_ax c u b (a - u) 0 S 0 0)]
  simp only [Nat.zero_add, show u + (a - u) = a by omega]
  rfl""")
rep("""def leaf (j a b c u : Nat) : List Cmd :=
  discard ++ (.ax c a b u :: (nips j ++ (.drop 0 :: nips (11 - j))))""",
    """def leaf (j a b c u : Nat) : List Cmd :=
  discard ++ (.ax c u b (a - u) :: (nips j ++ (.drop 0 :: nips (11 - j))))""")
rep("""      rho8 a b c u, wal a 0]) : ∀ y, y ∈ L → y ≠ 1 := by""",
    """      rho8 a b c u, wal u 0]) : ∀ y, y ∈ L → y ≠ 1 := by""")
rep("""theorem leaf_contract (j a b c u x : Nat) (L1 L2 : List Nat)
    (hsplit : axList a 0 b c u = L1 ++ x :: L2)""",
    """theorem leaf_contract (j a b c u x : Nat) (L1 L2 : List Nat) (hu : u ≤ a)
    (hsplit : axList a 0 b c u = L1 ++ x :: L2)""")
rep("  rw [leaf, cexec_discard_ax, hsplit, ← hk, ← hj]",
    "  rw [leaf, cexec_discard_ax T S a b c u hu, hsplit, ← hk, ← hj]")
# the seven non-rho8 leaves now take u = a (so that U = A = a)
for old, new in [
    ("theorem leaf1 (a b : Nat) : Contract (leaf 1 a b 0 0) (rho1 a b) :=\n  leaf_contract 1 a b 0 0 _ [] _ rfl rfl rfl",
     "theorem leaf1 (a b : Nat) : Contract (leaf 1 a b 0 a) (rho1 a b) :=\n  leaf_contract 1 a b 0 a _ [] _ (Nat.le_refl a) rfl rfl rfl"),
    ("theorem leaf2 (a b c : Nat) : Contract (leaf 2 a b c 0) (rho2 a b c) :=\n  leaf_contract 2 a b c 0 _ [_] _ rfl rfl rfl",
     "theorem leaf2 (a b c : Nat) : Contract (leaf 2 a b c a) (rho2 a b c) :=\n  leaf_contract 2 a b c a _ [_] _ (Nat.le_refl a) rfl rfl rfl"),
    ("theorem leaf3 (a b c : Nat) : Contract (leaf 3 a b c 0) (rho3 a b c) :=\n  leaf_contract 3 a b c 0 _ [_, _] _ rfl rfl rfl",
     "theorem leaf3 (a b c : Nat) : Contract (leaf 3 a b c a) (rho3 a b c) :=\n  leaf_contract 3 a b c a _ [_, _] _ (Nat.le_refl a) rfl rfl rfl"),
    ("theorem leaf4 (a b c : Nat) : Contract (leaf 4 a b c 0) (rho4 a b c) :=\n  leaf_contract 4 a b c 0 _ [_, _, _] _ rfl rfl rfl",
     "theorem leaf4 (a b c : Nat) : Contract (leaf 4 a b c a) (rho4 a b c) :=\n  leaf_contract 4 a b c a _ [_, _, _] _ (Nat.le_refl a) rfl rfl rfl"),
    ("theorem leaf5 (a b c : Nat) : Contract (leaf 5 a b c 0) (rho5 a b c) :=\n  leaf_contract 5 a b c 0 _ [_, _, _, _] _ rfl rfl rfl",
     "theorem leaf5 (a b c : Nat) : Contract (leaf 5 a b c a) (rho5 a b c) :=\n  leaf_contract 5 a b c a _ [_, _, _, _] _ (Nat.le_refl a) rfl rfl rfl"),
    ("theorem leaf6 (a b : Nat) : Contract (leaf 6 a 0 b 0) (rho6 a b) :=\n  leaf_contract 6 a 0 b 0 _ [_, _, _, _, _] _ rfl rfl rfl",
     "theorem leaf6 (a b : Nat) : Contract (leaf 6 a 0 b a) (rho6 a b) :=\n  leaf_contract 6 a 0 b a _ [_, _, _, _, _] _ (Nat.le_refl a) rfl rfl rfl"),
    ("theorem leaf7 (a b c : Nat) : Contract (leaf 7 a b c 0) (growG a b c) :=\n  leaf_contract 7 a b c 0 _ [_, _, _, _, _, _] _ rfl rfl rfl",
     "theorem leaf7 (a b c : Nat) : Contract (leaf 7 a b c a) (growG a b c) :=\n  leaf_contract 7 a b c a _ [_, _, _, _, _, _] _ (Nat.le_refl a) rfl rfl rfl"),
    ("theorem leaf8 (a b c u : Nat) : Contract (leaf 8 a b c u) (rho8 a b c u) :=\n  leaf_contract 8 a b c u _ [_, _, _, _, _, _, _] _ rfl rfl rfl",
     "theorem leaf8 (a b c u : Nat) (hu : u ≤ a) : Contract (leaf 8 a b c u) (rho8 a b c u) :=\n  leaf_contract 8 a b c u _ [_, _, _, _, _, _, _] _ hu rfl rfl rfl"),
]:
    rep(old, new)
rep("def bundleLeaf (a b c : Nat) : List Cmd := discard ++ (.ax c a b 0 :: nips 10)",
    "def bundleLeaf (a b c : Nat) : List Cmd := discard ++ (.ax c a b (a - a) :: nips 10)")
rep("""  rw [bundleLeaf, cexec_discard_ax]
  have hg : gate a b c = bundle222 a b c := by
    simp [gate, h1, h2]
  rw [hg, show nips 10 = nips ((axList a 0 b c 0).length + 1) from rfl]
  exact cexec_nips (bundle222 a b c) S 0 (axList a 0 b c 0) 0 0 (by omega) (axList_ne_one _ _ _ _ _)""",
    """  rw [bundleLeaf, cexec_discard_ax T S a b c a (Nat.le_refl a)]
  have hg : gate a b c = bundle222 a b c := by
    simp [gate, h1, h2]
  rw [hg, show nips 10 = nips ((axList a 0 b c a).length + 1) from rfl]
  exact cexec_nips (bundle222 a b c) S 0 (axList a 0 b c a) 0 0 (by omega) (axList_ne_one _ _ _ _ _)""")

# generalization: AX(i, i, 0, 0) from d = 0 gives U = A = i
rep("""    rw [cexec_cons_some (cstep_ax i i 0 0 0 S 0 H)]
    simp only [Nat.zero_add, Nat.add_zero]
    rw [show gate i H i = 0 from gate_self i H, axStack_eq]
    have hsplit : axList i H H i 0 ++ [0] =
        [rho1 i H, rho2 i H i, rho3 i H i, rho4 i H i, rho5 i H i, rho6 i i, growG i H i,
          rho8 i H i 0] ++ [wal i H] ++ [0] := rfl""",
    """    rw [cexec_cons_some (cstep_ax i i 0 0 0 S 0 H)]
    simp only [Nat.zero_add, Nat.add_zero]
    rw [show gate i H i = 0 from gate_self i H, axStack_eq]
    have hsplit : axList i H H i i ++ [0] =
        [rho1 i H, rho2 i H i, rho3 i H i, rho4 i H i, rho5 i H i, rho6 i i, growG i H i,
          rho8 i H i i] ++ [wal i H] ++ [0] := rfl""")
rep("""    have hL : ∀ y, y ∈ [rho1 i H, rho2 i H i, rho3 i H i, rho4 i H i, rho5 i H i, rho6 i i,
        growG i H i, rho8 i H i 0] → y ≠ 1 := fun y hy =>
      axList_ne_one i H H i 0 y (by simp [axList] at hy ⊢; omega)
    rw [show nips 9 = nips ([rho1 i H, rho2 i H i, rho3 i H i, rho4 i H i, rho5 i H i, rho6 i i,
        growG i H i, rho8 i H i 0].length + 1) from rfl, ← pushL_append]""",
    """    have hL : ∀ y, y ∈ [rho1 i H, rho2 i H i, rho3 i H i, rho4 i H i, rho5 i H i, rho6 i i,
        growG i H i, rho8 i H i i] → y ≠ 1 := fun y hy =>
      axList_ne_one i H H i i y (by simp [axList] at hy ⊢; omega)
    rw [show nips 9 = nips ([rho1 i H, rho2 i H i, rho3 i H i, rho4 i H i, rho5 i H i, rho6 i i,
        growG i H i, rho8 i H i i].length + 1) from rfl, ← pushL_append]""")

# modus ponens block: AX(B, 0, 0, 0) from d = B gives U = A = B
rep("""        rw [show gate B 0 B = 0 from gate_self B 0, axStack_eq,
          show nips 10 = nips ((axList B 0 0 B 0).length + 1) from rfl, cexec_append,
          cexec_nips 0 (P 0 S) 0 (axList B 0 0 B 0) 0 B (by omega) (axList_ne_one _ _ _ _ _)]""",
    """        rw [show gate B 0 B = 0 from gate_self B 0, axStack_eq,
          show nips 10 = nips ((axList B 0 0 B B).length + 1) from rfl, cexec_append,
          cexec_nips 0 (P 0 S) 0 (axList B 0 0 B B) 0 B (by omega) (axList_ne_one _ _ _ _ _)]""")

# derivations of the dominated calculus
rep("theorem build : ∀ {n : Nat}, C222 n → ∃ p : List Cmd, Contract p n := by",
    "theorem build : ∀ {n : Nat}, CDom n → ∃ p : List Cmd, Contract p n := by")
rep("  | r8 a b c u => exact ⟨_, leaf8 a b c u⟩", "  | r8 a b c u hu => exact ⟨_, leaf8 a b c u hu⟩")
rep("  obtain ⟨p, hp⟩ := build h", "  obtain ⟨p, hp⟩ := build (cdom_of_c222 h)")
rep("""  rcases hp (gate (d + 1) (hh + 1) 0) (axStack (d + 1) hh (hh + 1) 0 0 t S) with hn | hs""",
    """  rcases hp (gate (d + 1 + 0) (hh + 1) 0) (axStack (d + 1 + 0) hh (hh + 1) 0 (d + 1) t S) with hn | hs""")

(D / "EnumDom.lean").write_text(
    "/- Forked by Research/ZFC/k225-formal/generate_enumdom.py from Enum222.lean: the 217's "
    "dominated AX command (Source 149). -/\n" + s, encoding="utf-8", newline="\n")
print("wrote EnumDom.lean")
