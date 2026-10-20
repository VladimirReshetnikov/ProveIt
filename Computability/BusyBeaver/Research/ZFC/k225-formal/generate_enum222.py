#!/usr/bin/env python3
"""Fork Enum254.lean (the abstract proof enumerator and L1) into Enum222.lean for the 222/221.

The command interface is unchanged (Elliot Glazer's Enum230 is the same command calculus).
The AX stack is Enum230's: `rho6 a c` (Jeff's 254 stack has `rho6 a b`), the merged equality
row `growG a b c` in rho7's slot, and the gate emits the helper-free seed bundle `bundle222`.
The calculus is `KCode222.C222`. Leaf 6 is re-indexed so that it still derives every
`rho6 a b`. The closing model-theoretic corollaries of Enum254 are dropped.

Usage (from Computability/BusyBeaver/Lean): generate_enum222.py"""
from pathlib import Path

D = Path("BusyBeaver/ZFC")
t = (D / "Enum254.lean").read_text(encoding="utf-8")


def sub(a, b, count=None):
    global t
    n = t.count(a)
    assert n > 0 and (count is None or n == count), (a, n)
    t = t.replace(a, b)


sub("import BusyBeaver.ZFC.Code254", "import BusyBeaver.ZFC.KCode222", 1)
sub("namespace SetTheory.BusyBeaver.ZFC.Enum254", "namespace SetTheory.BusyBeaver.ZFC.Enum222", 1)
sub("end SetTheory.BusyBeaver.ZFC.Enum254", "end SetTheory.BusyBeaver.ZFC.Enum222", 1)
sub("open SetTheory.BusyBeaver.ZFC.Code254\n",
    "open SetTheory.BusyBeaver.ZFC.Code254 SetTheory.BusyBeaver.ZFC.KCode222\n", 1)
sub("(P (rho6 a b) (P (rho7 a b c)", "(P (rho6 a c) (P (growG a b c)", 1)
sub("def gate (a b c : Nat) : Nat := if c = a ∨ c = b then 0 else bundle a b c",
    "def gate (a b c : Nat) : Nat := if c = a ∨ c = b then 0 else bundle222 a b c", 1)
sub("good_cons (C254.r6 a b) <|", "good_cons (C254.r6 a c) <|", 1)
sub("good_cons (C254.r7 a b c)", "good_cons (C254.rG a b c)", 1)
sub("rho6 a b, rho7 a b c,", "rho6 a c, growG a b c,", 2)
sub("rho6 i H, rho7 i H i,", "rho6 i i, growG i H i,", 1)
sub("rho6 i H,\n        rho7 i H i,", "rho6 i i,\n        growG i H i,", 2)
sub("theorem leaf6 (a b : Nat) : Contract (leaf 6 a b 0 0) (rho6 a b) :=\n  leaf_contract 6 a b 0 0 _",
    "theorem leaf6 (a b : Nat) : Contract (leaf 6 a 0 b 0) (rho6 a b) :=\n  leaf_contract 6 a 0 b 0 _", 1)
sub("theorem leaf7 (a b c : Nat) : Contract (leaf 7 a b c 0) (rho7 a b c) :=",
    "theorem leaf7 (a b c : Nat) : Contract (leaf 7 a b c 0) (growG a b c) :=", 1)
sub("Contract (bundleLeaf a b c) (bundle a b c)", "Contract (bundleLeaf a b c) (bundle222 a b c)", 1)
sub("have hg : gate a b c = bundle a b c := by", "have hg : gate a b c = bundle222 a b c := by", 1)
sub("exact cexec_nips (bundle a b c) S", "exact cexec_nips (bundle222 a b c) S", 1)
sub("| r7 a b c => exact ⟨_, leaf7 a b c⟩", "| rG a b c => exact ⟨_, leaf7 a b c⟩", 1)
sub("C254", "C222")
# drop the closing corollaries about the 254 bundle theory
i = t.index("/-- If the enumerator halts, the decoded bundle theory has no irreflexive model. -/")
j = t.index("end SetTheory.BusyBeaver.ZFC.Enum222")
t = t[:i] + t[j:]
head = ("/- Forked by Research/ZFC/k225-formal/generate_enum222.py from Enum254.lean: Elliot "
        "Glazer's Enum230 step with the 222's rows (rho6 a c, growG, bundle222) and calculus C222. -/\n")
(D / "Enum222.lean").write_text(head + t, encoding="utf-8", newline="\n")
print("wrote Enum222.lean")
