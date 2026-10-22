#!/usr/bin/env python3
"""Fork the L2 library of the 219-node program (L2Lib254, L2Macros254, L2Control254) for dag222.

dag222 agrees with dag254 on every node these files use except node 136, where Elliot Glazer's
Dag230 rotates the next-candidate loop: `np++; while s1 {s1--; np++}` (nodes 136/300) instead of
`while s1 {s1--; np++}; np++`. Both add `s1 + 1` to `np` and clear `s1`; the fork proves the
rotated loop (`loop136`) and uses it in the fetch. Everything else is a textual substitution
(`dag254` -> `dag222`, namespace `L2` -> `L2K`); the Lean kernel rechecks every proof on dag222.

Usage (from Computability/BusyBeaver/Lean): generate_l2k222.py"""
from pathlib import Path

D = Path("BusyBeaver/ZFC")
SUBS = [
    ("import BusyBeaver.ZFC.Dag254", "import BusyBeaver.ZFC.Dag222"),
    ("import BusyBeaver.ZFC.Enum254", "import BusyBeaver.ZFC.Code254"),
    ("import BusyBeaver.ZFC.L2Lib254", "import BusyBeaver.ZFC.L2Lib222"),
    ("import BusyBeaver.ZFC.L2Macros254", "import BusyBeaver.ZFC.L2Macros222"),
    ("namespace SetTheory.BusyBeaver.ZFC.L2\n", "namespace SetTheory.BusyBeaver.ZFC.L2K\n"),
    ("end SetTheory.BusyBeaver.ZFC.L2\n", "end SetTheory.BusyBeaver.ZFC.L2K\n"),
    ("open RMDag Dag254 Code254", "open RMDag Dag222 Code254"),
    ("dag254", "dag222"),
]
LOOP136 = '''/-- The rotated next-candidate loop of Dag230 (nodes 136/300):
`np++; while s1 {s1--; np++}`. -/
theorem loop136 : ∀ (k : Nat) (st : AS), st.s1 = k →
    Rn (.node 136) st { st with np := st.np + k + 1, s1 := 0 } := by
  intro k
  induction k with
  | zero =>
      intro st h
      have hinc : Run dag222 (.inc 0) (enc st) .normal (enc { st with np := st.np + 1 }) := by
        have := Run.inc (p := dag222) 0 (enc st)
        rwa [show enc st 0 = st.np from rfl, upd_np] at this
      have hz : Run dag222 (.decnz 6) (enc { st with np := st.np + 1 }) (.brk 1)
          (enc { st with np := st.np + 1 }) := Run.decZero 6 _ (by simp [enc, h])
      have h300 : Run dag222 (.node 300) (enc { st with np := st.np + 1 }) .normal
          (enc { st with np := st.np + 1 }) := Run.carBrk1 300 _ _ hz
      have := Run.cdrNormal (p := dag222) 136 _ _ _ hinc h300
      have e : ({ st with np := st.np + 1 } : AS) = { st with np := st.np + 0 + 1, s1 := 0 } := by
        cases st; simp only at h; subst h; rfl
      rw [e] at this
      exact this
  | succ k ih =>
      intro st h
      have hinc : Run dag222 (.inc 0) (enc st) .normal (enc { st with np := st.np + 1 }) := by
        have := Run.inc (p := dag222) 0 (enc st)
        rwa [show enc st 0 = st.np from rfl, upd_np] at this
      have hdec : Run dag222 (.decnz 6) (enc { st with np := st.np + 1 }) .normal
          (enc { st with np := st.np + 1, s1 := k }) := by
        have := Run.decPos (p := dag222) 6 (enc { st with np := st.np + 1 }) k (by simp [enc, h])
        rwa [upd_s1] at this
      have h300 : Run dag222 (.node 300) (enc { st with np := st.np + 1 }) (.cont 1)
          (enc { st with np := st.np + 1, s1 := k }) :=
        Run.cdrContS 300 0 _ _ _ hdec (Run.contS 1 _)
      have hrest := ih { st with np := st.np + 1, s1 := k } rfl
      have := Run.cdrCont1 (p := dag222) 136 _ _ _ _ _ hinc h300 hrest
      have e2 : ({ ({ st with np := st.np + 1, s1 := k } : AS) with
          np := (({ st with np := st.np + 1, s1 := k } : AS)).np + k + 1, s1 := 0 } : AS) =
          { st with np := st.np + (k + 1) + 1, s1 := 0 } := by
        cases st; simp only; congr 1; omega
      rw [e2] at this
      exact this

'''
OLD_136 = "(seqAS (n := 136) rfl (loop203 _) (inc_AS 0 (by omega) _))"
NEW_136 = "(loop136 _ _ rfl)"

for src, dst in [("L2Lib254", "L2Lib222"), ("L2Macros254", "L2Macros222"), ("L2Control254", "L2Control222")]:
    t = (D / f"{src}.lean").read_text(encoding="utf-8")
    for a, b in SUBS:
        t = t.replace(a, b)
    if src == "L2Control254":
        assert t.count(OLD_136) == 1
        t = t.replace(OLD_136, NEW_136)
        anchor = "/-! ## Fetch, MP and NIP -/"
        assert t.count(anchor) == 1
        t = t.replace(anchor, LOOP136 + anchor)
    head = ("/- Forked by Research/ZFC/k225-formal/generate_l2k222.py from "
            f"{src}.lean for dag222 (Elliot Glazer's Dag230 with the 222's AX node). -/\n")
    (D / f"{dst}.lean").write_text(head + t, encoding="utf-8", newline="\n")
    print("wrote", dst)
