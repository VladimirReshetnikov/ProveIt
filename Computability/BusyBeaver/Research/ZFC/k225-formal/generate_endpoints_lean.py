#!/usr/bin/env python3
"""Write the K-family endpoints KEndpoint221/219/218/217/215 over KEndpoint's generic composition.

  python generate_endpoints_lean.py [N ...]      (all four when no N is given)

Each endpoint supplies the five machine-specific inputs of `KEndpoint.blank_halts_iff_zfc_refutation`:
the dense bridge, the register lemmas (`KTape.boxLemmas`, with the machine's increment tail), the
boot, the site coverage and the program layer.
"""
from pathlib import Path

Z = Path(__file__).resolve().parents[3] / "Lean" / "BusyBeaver" / "ZFC"

SPEC = {
    221: dict(gap=181, spare=167, tail=".inl ⟨rfl, rfl, rfl⟩",
              tail_doc="ends the increment as K230 does",
              extra_import="", src_doc="""* `KSource221.p221_boot_iff`: the source halts from the boot registers iff the code 1 is derivable
  in the 222 calculus `C222`.""", src=None),
    219: dict(gap=144, spare=130, tail=".inr rfl",
              tail_doc="ends the increment with Source 140's bypass `198/0 → 1 L 40`",
              extra_import="import BusyBeaver.ZFC.Dag219Equiv\n", src_doc=None, src="dag219"),
    218: dict(gap=144, spare=130, tail=".inr rfl",
              tail_doc="ends the increment with the 219's bypass `198/0 → 1 L 40`",
              extra_import="import BusyBeaver.ZFC.Dag219Equiv\n", src_doc=None, src="dag219"),
    217: dict(gap=144, spare=130, tail=".inr rfl",
              tail_doc="ends the increment with the 219's bypass `198/0 → 1 L 40`",
              extra_import="import BusyBeaver.ZFC.SeedDom\n", src_doc=None, src="dagDom"),
    215: dict(gap=65, spare=40, tail=".inr rfl",
              tail_doc="ends the increment with the 219's bypass `198/0 → 1 L 40`",
              extra_import="import BusyBeaver.ZFC.SeedPerm\n", src_doc=None, src="dagPerm",
              regs="L2Perm.bootRegs", regs_doc="`nextproof = 4`"),
}

import sys
only = [int(a) for a in sys.argv[1:]]
for n, s in SPEC.items():
    if only and n not in only:
        continue
    regs = s.get("regs", "L2K.bootRegs")
    regs_doc = s.get("regs_doc", "`nextproof = 3`, `param1 = 3`")
    if s["src"] == "dagPerm":
        src_doc = f"""* `p{n}_boot_iff`: the source halts from the boot registers iff `dagPerm`, iterated, does
  (`KSource{n}`), iff Source 159's command-permuted enumerator halts from the seed
  (`L2Perm.dagPerm_seed_iff`), iff the code 1 is derivable in `C222`: the enumerator compiles
  derivations of the dominated calculus `KCodeDom.CDom`, which derives exactly `C222`'s codes
  (`DomRho8.rho8_all`)."""
        seed = "L2Perm.dagPerm_seed_iff"
    elif s["src"] == "dagDom":
        src_doc = f"""* `p{n}_boot_iff`: the source halts from the boot registers iff `dagDom`, iterated, does
  (`KSource{n}`), iff Source 149's dominated enumerator halts from the seed
  (`L2Dom.dagDom_seed_iff`), iff the code 1 is derivable in `C222`: the enumerator compiles
  derivations of the dominated calculus `KCodeDom.CDom`, which derives exactly `C222`'s codes
  (`DomRho8.rho8_all`)."""
        seed = "L2Dom.dagDom_seed_iff"
    elif s["src"]:
        src_doc = f"""* `p{n}_boot_iff`: the source halts from the boot registers iff `dag219`, iterated, does
  (`KSource{n}`), iff `dag222` does (`Dag219.iter_iff`), iff the code 1 is derivable in the 222
  calculus `C222`."""
        seed = "Dag219.seed_iff"
    if s["src"]:
        src_thm = f"""
/-- **Program layer.** The {n}'s source halts from the boot registers iff the code 1 is
derivable. -/
theorem p{n}_boot_iff :
    RegisterPath.Halts KSource{n}.p{n} ⟨[], {regs}⟩ ↔ KCode222.C222 Code254.F :=
  (KSource{n}.p{n}_halts_iff _).trans ((KSource{n}.path_iff_iter _).trans {seed})
"""
        src_ref = f"p{n}_boot_iff"
    else:
        src_doc, src_thm, src_ref = s["src_doc"], "", f"KSource{n}.p{n}_boot_iff"
    text = f"""import BusyBeaver.ZFC.KEndpoint
import BusyBeaver.ZFC.KTape
import BusyBeaver.ZFC.KDense{n}
import BusyBeaver.ZFC.KBoot{n}
import BusyBeaver.ZFC.KSites{n}
{s["extra_import"]}
/-!
**The {n}-state machine halts iff ZFC is inconsistent.**

The machine-specific inputs of `KEndpoint.blank_halts_iff_zfc_refutation`:

* `KDense{n}.commutes`: the literal dense `Machine {n}` is the K230-label table, relabelled.
* `tm{n}_box`: the table agrees with K230 on the rows the register routines read and
  {s["tail_doc"]}, so K230's register lemmas hold for it.
* `KBoot{n}.boot`: from the blank tape the table reaches the dispatch configuration of the empty
  path with the boot registers ({regs_doc}) and {s["spare"]} spare register blocks.
* `KSites{n}.covered`: every decoder leaf of the {n}'s source passes the symbolic site check.
{src_doc}
-/

namespace SetTheory.BusyBeaver.ZFC.KEndpoint{n}

open KZip KTableCore KDenseBridge KDense{n} KBoot{n} KTape LeanProofs.BoundedZFCConsistency

theorem tm{n}_box : KRuntimeCore.BoxLemmas tm{n} := boxLemmas (by decide) ({s["tail"]})

theorem boot_rel : KSim.Rel KSource{n}.p{n} ⟨[], {regs}⟩ (zc 84 [true] bootRight) := by
  refine ⟨RegisterPathClean.clean_nil _, {s["gap"]}, List.replicate {s["spare"]} 1, by decide, by simp, ?_⟩
  rfl
{src_thm}
/-- **The {n}-state machine halts on the blank tape iff ZFC is refutable.** -/
theorem blank_halts_iff_zfc_refutation : BlankHalts machine{n} ↔ BProv ZFCax_s [] Form.fBot :=
  KEndpoint.blank_halts_iff_zfc_refutation commutes terminal tm{n}_box KSites{n}.covered boot boot_rel
    {src_ref}

/-- **The {n}-state machine runs forever iff ZFC is consistent.** -/
theorem nonhalting_iff_zfc_consistency : (¬ BlankHalts machine{n}) ↔ ¬ BProv ZFCax_s [] Form.fBot :=
  not_congr blank_halts_iff_zfc_refutation

#print axioms blank_halts_iff_zfc_refutation

end SetTheory.BusyBeaver.ZFC.KEndpoint{n}
"""
    (Z / f"KEndpoint{n}.lean").write_text(text.replace("\n\n\n", "\n\n"), encoding="utf-8", newline="\n")
    print("wrote", n)
