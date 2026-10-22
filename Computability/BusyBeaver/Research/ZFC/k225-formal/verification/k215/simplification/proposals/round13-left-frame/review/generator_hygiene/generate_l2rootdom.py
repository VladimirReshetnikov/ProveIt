#!/usr/bin/env python3
"""Fork L2Root222.lean for dagDom (L2RootDom.lean), and write SeedDom.lean.

  python generate_l2rootdom.py      (from Computability/BusyBeaver/Lean)

The root step (fetch, the two reads, the dispatch) is dag222's: its nodes are the only ones
besides the AX routine from which node 236 is reachable, so it is re-proved here word for word
for dagDom, against EnumDom's step; the AX leaf now runs the dominated AX word
(L2AxiomsDom.ax_eval). SeedDom is an instance of EnumDom.halts_iff.
"""
from pathlib import Path

D = Path("BusyBeaver/ZFC")


def fork(text, subs):
    for a, b, n in subs:
        assert text.count(a) == n or (n is None and text.count(a) > 0), (a[:70], text.count(a), n)
        text = text.replace(a, b)
    return text


root = (D / "L2Root222.lean").read_text(encoding="utf-8")
root = "import BusyBeaver.ZFC.RMDagIteration\n" + root[root.index("import BusyBeaver.ZFC.L2Axioms222"):]
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
    ("open RMDag Dag222 Code254", "open RMDag DagDom\nopen Code254 (P wim F)\nopen L2K (AS enc Clean upd_ac P_zero_zero)", 1),
    ("dag222", "dagDom", None),
    ("Enum222.", "EnumDom.", None),
])
# the zero-state route from `nextproof = 2` is not used: the 217 boots into the seed (SeedDom)
i = root.index("theorem iter_iff_halts ")
root = root[:i] + root[root.index("end SetTheory.BusyBeaver.ZFC.L2Dom", i):]
(D / "L2RootDom.lean").write_text(
    "/- Forked by Research/ZFC/k225-formal/generate_l2rootdom.py from L2Root222.lean for dagDom. -/\n"
    + root, encoding="utf-8", newline="\n")

SEED = """import BusyBeaver.ZFC.L2RootDom
import BusyBeaver.ZFC.Seed222

/-!
The seed start of the 217's enumerator, and the program layer from the boot registers.

The K-family machines boot into Elliot Glazer's seed state (candidate 3, parameter counter 3:
registers `np = 3`, `param1 = 3`, the boot registers `L2K.bootRegs`), a state between candidates
whose registers hold derivable codes, so `EnumDom.halts_iff` applies.

`dagDom_seed_iff`: the structured program `dagDom`, iterated from the boot registers, halts
iff the code 1 is derivable in `C222`.
-/

namespace SetTheory.BusyBeaver.ZFC.EnumDom

open SetTheory.BusyBeaver.ZFC.KCode222

/-- Elliot Glazer's seed: candidate 3, parameter counter 3. -/
def seed : St := ⟨0, 3, 0, 0, 3, 0⟩

theorem seed_iff : HaltsFrom seed ↔ C222 Code254.F :=
  halts_iff rfl ⟨C222.truth, C222.truth, good_zero⟩

end SetTheory.BusyBeaver.ZFC.EnumDom

namespace SetTheory.BusyBeaver.ZFC.L2Dom

open RMDag DagDom
open Code254 (F)
open L2K (enc bootRegs)

theorem enc_seed : enc (toAS EnumDom.seed) = bootRegs := by
  funext i
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [enc, toAS, EnumDom.seed, bootRegs, upd]

/-- **L2 + L1 from the boot registers**: `dagDom` halts iff the code 1 is derivable. -/
theorem dagDom_seed_iff : IterHalts dagDom bootRegs ↔ KCode222.C222 F := by
  rw [← enc_seed, iter_iff]
  exact EnumDom.seed_iff

#print axioms dagDom_seed_iff

end SetTheory.BusyBeaver.ZFC.L2Dom
"""
(D / "SeedDom.lean").write_text(SEED, encoding="utf-8", newline="\n")
print("wrote L2RootDom.lean, SeedDom.lean")
