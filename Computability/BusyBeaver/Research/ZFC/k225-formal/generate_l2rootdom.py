#!/usr/bin/env python3
"""Fork L2Root222.lean and Seed222.lean for dagDom: L2RootDom.lean and SeedDom.lean.

  python generate_l2rootdom.py      (from Computability/BusyBeaver/Lean)

The root step (fetch, the two reads, the dispatch) is dag222's: its nodes are the only ones
besides the AX routine from which node 236 is reachable, so it is re-proved here word for word
for dagDom, against EnumDom's step; the AX leaf now runs the dominated AX word
(L2AxiomsDom.ax_eval). The seed argument is Seed222's with EnumDom's AX command and compiler.
"""
from pathlib import Path

D = Path("BusyBeaver/ZFC")


def fork(text, subs):
    for a, b, n in subs:
        assert text.count(a) == n or (n is None and text.count(a) > 0), (a[:70], text.count(a), n)
        text = text.replace(a, b)
    return text


root = (D / "L2Root222.lean").read_text(encoding="utf-8")
root = root[root.index("import BusyBeaver.ZFC.L2Axioms222"):]
root = fork(root, [
    ("import BusyBeaver.ZFC.L2Axioms222", "import BusyBeaver.ZFC.L2AxiomsDom", 1),
    ("""L2: one run of the root of the seed-K 222 program dag222 is one enumerator step.

`ax_eval` evaluates the generated `axioms()` composite symbolically: the
stack becomes `Enum222.axStack` and the current formula the gated bundle.""",
     """L2: one run of the root of the 217's program dagDom is one step of EnumDom.

Forked from `L2Root222.lean` by `Research/ZFC/k225-formal/generate_l2rootdom.py`: the fetch,
the reads and the dispatch are dag222's nodes, re-proved for dagDom; the AX leaf runs the
dominated AX word, which `ax_eval` (`L2AxiomsDom`) evaluates to EnumDom's AX step.""", 1),
    ("namespace SetTheory.BusyBeaver.ZFC.L2K", "namespace SetTheory.BusyBeaver.ZFC.L2Dom", 1),
    ("end SetTheory.BusyBeaver.ZFC.L2K", "end SetTheory.BusyBeaver.ZFC.L2Dom", 1),
    ("open RMDag Dag222 Code254", "open RMDag DagDom Code254\nopen L2K (AS enc Clean upd_ac)", 1),
    ("dag222", "dagDom", None),
    ("Enum222.", "EnumDom.", None),
    ("/-- L2 composed with L1: the seed-K 222 program dagDom, iterated from the boot registers",
     "/-- L2 composed with L1: the 217's program dagDom, iterated from the boot registers", 1),
])
(D / "L2RootDom.lean").write_text(
    "/- Forked by Research/ZFC/k225-formal/generate_l2rootdom.py from L2Root222.lean for dagDom. -/\n"
    + root, encoding="utf-8", newline="\n")

seed = (D / "Seed222.lean").read_text(encoding="utf-8")
seed = fork(seed, [
    ("import BusyBeaver.ZFC.L2Root222", "import BusyBeaver.ZFC.L2RootDom\nimport BusyBeaver.ZFC.Seed222", 1),
    ("""The seed start of the 222/221 enumerator, and the program layer from the boot registers.""",
     """The seed start of the 217's enumerator, and the program layer from the boot registers.

Forked from `Seed222.lean` by `Research/ZFC/k225-formal/generate_l2rootdom.py`, with EnumDom's
AX command; the boot registers are `L2K.bootRegs`.""", 1),
    ("""`dag222_seed_iff`: the structured program `dag222`, iterated from the boot registers, halts
iff the code 1 is derivable in `C222`.""",
     """`dagDom_seed_iff`: the structured program `dagDom`, iterated from the boot registers, halts
iff the code 1 is derivable in `C222`.""", 1),
    ("namespace SetTheory.BusyBeaver.ZFC.Enum222", "namespace SetTheory.BusyBeaver.ZFC.EnumDom", 1),
    ("end SetTheory.BusyBeaver.ZFC.Enum222", "end SetTheory.BusyBeaver.ZFC.EnumDom", 1),
    ("open SetTheory.BusyBeaver.ZFC.Code254 SetTheory.BusyBeaver.ZFC.KCode222",
     "open SetTheory.BusyBeaver.ZFC.Code254 SetTheory.BusyBeaver.ZFC.KCode222\n"
     "open SetTheory.BusyBeaver.ZFC.KCodeDom", 1),
    ("""  rcases hp (gate (d + 1) (hh + 1) 0) (axStack (d + 1) hh (hh + 1) 0 0 t S) with hn | hs""",
     """  rcases hp (gate (d + 1 + 0) (hh + 1) 0) (axStack (d + 1 + 0) hh (hh + 1) 0 (d + 1) t S) with hn | hs""", 1),
    ("  obtain ⟨p, hp⟩ := build h", "  obtain ⟨p, hp⟩ := build (cdom_of_c222 h)", 1),
    ("namespace SetTheory.BusyBeaver.ZFC.L2K", "namespace SetTheory.BusyBeaver.ZFC.L2Dom", 1),
    ("end SetTheory.BusyBeaver.ZFC.L2K", "end SetTheory.BusyBeaver.ZFC.L2Dom", 1),
    ("open RMDag Dag222 Code254", "open RMDag DagDom Code254\nopen L2K (enc bootRegs)", 1),
    ("""/-- The boot registers of the K-family machines: `nextproof = 3`, `param1 = 3`. -/
def bootRegs : Regs := upd (upd (fun _ => 0) 0 3) 4 3

""", "", 1),
    ("theorem enc_seed : enc (toAS Enum222.seed) = bootRegs := by",
     "theorem enc_seed : enc (toAS EnumDom.seed) = bootRegs := by", 1),
    ("rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [enc, toAS, Enum222.seed, bootRegs, upd]",
     "rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [enc, toAS, EnumDom.seed, bootRegs, upd]", 1),
    ("""/-- **L2 + L1 from the boot registers**: `dag222` halts iff the code 1 is derivable. -/
theorem dag222_seed_iff : IterHalts dag222 bootRegs ↔ KCode222.C222 F := by
  rw [← enc_seed, iter_iff]
  exact Enum222.seed_iff

#print axioms dag222_seed_iff""",
     """/-- **L2 + L1 from the boot registers**: `dagDom` halts iff the code 1 is derivable. -/
theorem dagDom_seed_iff : IterHalts dagDom bootRegs ↔ KCode222.C222 F := by
  rw [← enc_seed, iter_iff]
  exact EnumDom.seed_iff

#print axioms dagDom_seed_iff""", 1),
])
(D / "SeedDom.lean").write_text(
    "/- Forked by Research/ZFC/k225-formal/generate_l2rootdom.py from Seed222.lean for dagDom. -/\n"
    + seed, encoding="utf-8", newline="\n")
print("wrote L2RootDom.lean, SeedDom.lean")
