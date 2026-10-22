#!/usr/bin/env python3
"""Prepare a reviewable, isolated EnumPerm compiler-fusion proposal.

Only reads the specified ProveIt checkout; all outputs stay below this directory.
"""
from pathlib import Path
import argparse
import difflib
import hashlib
import json

parser = argparse.ArgumentParser()
parser.add_argument("repo", type=Path)
args = parser.parse_args()
here = Path(__file__).resolve().parent
rel = Path("Computability/BusyBeaver/Lean/BusyBeaver/ZFC/EnumPerm.lean")
before = (args.repo / rel).read_text()
after = before

def replace(old, new):
    global after
    assert after.count(old) == 1, (old[:90], after.count(old))
    after = after.replace(old, new)

replace("import BusyBeaver.ZFC.KCodeDom\n",
        "import BusyBeaver.ZFC.KCode222\nimport BusyBeaver.ZFC.DomRho8\n")
replace("open SetTheory.BusyBeaver.ZFC.KCodeDom\n", "")
replace("Completeness compiles a derivation of the dominated calculus `KCodeDom.CDom` into\ncommand blocks (Source 159's compiler: the counter is set by `J u = MP u` from a cleared state,\nand a dominated rho8 leaf `rho8 a b c u` is `J u; AX(c; a - u, b)`) behind `START_Y = AX(0; 1, Y)`,", "Completeness compiles `C222` directly into command blocks, interpreting the generic\ndominated-implication theorem in the predicate `fun n => ∃ p, Contract p n`. Source 159's\ncompiler sets the counter by `J u = MP u` from a cleared state; a dominated rho8 leaf\n`rho8 a b c u` is `J u; AX(c; a - u, b)`. The compiled block follows `START_Y = AX(0; 1, Y)`,")
replace("whose candidate number is at least `Y`; `CDom` derives every `C222` code.",
        "whose candidate number is at least `Y`. No intermediate `CDom` derivation is constructed.")
replace("/-- Every code of the dominated calculus has a block computing it. -/\ntheorem build : ∀ {n : Nat}, CDom n → ∃ p : List Cmd, Contract p n := by\n",
"""/-- Compile directly in the algebra of block contracts. The restricted rho8 theorem is
interpreted here in `fun n => ∃ p, Contract p n`, eliminating the intermediate calculus. -/
theorem build_c222 : ∀ {n : Nat}, C222 n → ∃ p : List Cmd, Contract p n := by
  have hmp {A B : Nat} (hab : ∃ p : List Cmd, Contract p (wim A B))
      (ha : ∃ p : List Cmd, Contract p A) : ∃ p : List Cmd, Contract p B := by
    obtain ⟨pab, hab⟩ := hab
    obtain ⟨pa, ha⟩ := ha
    exact ⟨_, mp_contract ha hab⟩
  have hrow (a b c u : Nat) (hu : u ≤ a) : ∃ p : List Cmd, Contract p (rho8 a b c u) :=
    ⟨leaf 8 a b c u, fun T S => Or.inr (by rw [leaf, cexec_discard_ax _ _ _ _ _ _ hu]; xrun)⟩
""")
replace("  | r8 a b c u hu => exact ⟨leaf 8 a b c u, fun T S => Or.inr (by rw [leaf, cexec_discard_ax _ _ _ _ _ _ hu]; xrun)⟩",
        "  | r8 a b c u =>\n      exact DomRho8.rho8_all_of_restricted (T := fun n => ∃ p : List Cmd, Contract p n)\n        hmp hrow a b c u")
replace("  | mp _ _ ih1 ih2 =>\n      obtain ⟨pa, ha⟩ := ih1\n      obtain ⟨pab, hab⟩ := ih2\n      exact ⟨_, mp_contract ha hab⟩",
        "  | mp _ _ ih1 ih2 => exact hmp ih2 ih1")
replace("  obtain ⟨p, hp⟩ := build (cdom_of_c222 h)",
        "  obtain ⟨p, hp⟩ := build_c222 h")

compat = """import BusyBeaver.ZFC.EnumPerm
import BusyBeaver.ZFC.KCodeDom

/-!
Compatibility import for clients using the former `EnumPerm.build` theorem.
Import this module instead of `EnumPerm` when the CDom-specific API is required.
The active K215 endpoint does not import this adapter.
-/

namespace SetTheory.BusyBeaver.ZFC.EnumPerm

/-- The former compiler interface, now an adapter to direct C222 compilation. -/
theorem build : ∀ {n : Nat}, KCodeDom.CDom n → ∃ p : List Cmd, Contract p n :=
  fun h => build_c222 (KCodeDom.c222_of_cdom h)

end SetTheory.BusyBeaver.ZFC.EnumPerm
"""

audit = """import BusyBeaver.ZFC.EnumPerm

namespace K215CompilerFusionAudit
open SetTheory.BusyBeaver.ZFC

example {n : Nat} (h : KCode222.C222 n) : ∃ p : List EnumPerm.Cmd, EnumPerm.Contract p n :=
  EnumPerm.build_c222 h

example {s : EnumPerm.St} (hpl : s.pl = 0) (hs : EnumPerm.Inv (EnumPerm.toW s)) :
    EnumPerm.HaltsFrom s ↔ KCode222.C222 Code254.F := EnumPerm.halts_iff hpl hs

#print axioms EnumPerm.build_c222
#print axioms EnumPerm.complete
#print axioms EnumPerm.halts_iff
end K215CompilerFusionAudit
"""
compat_audit = """import BusyBeaver.ZFC.EnumPermCompat

namespace K215CompilerFusionCompatAudit
open SetTheory.BusyBeaver.ZFC
example {n : Nat} (h : KCodeDom.CDom n) : ∃ p : List EnumPerm.Cmd, EnumPerm.Contract p n :=
  EnumPerm.build h
#print axioms EnumPerm.build
end K215CompilerFusionCompatAudit
"""

sources = here / "sources"
target = sources / "BusyBeaver/ZFC/EnumPerm.lean"
target.parent.mkdir(parents=True, exist_ok=True)
target.write_text(after)
(target.parent / "EnumPermCompat.lean").write_text(compat)
(sources / "CompilerFusionAudit.lean").write_text(audit)
(sources / "CompilerFusionCompatAudit.lean").write_text(compat_audit)

patch = ''.join(difflib.unified_diff(before.splitlines(True), after.splitlines(True),
    fromfile='a/'+str(rel), tofile='b/'+str(rel)))
crel = rel.with_name('EnumPermCompat.lean')
patch += ''.join(difflib.unified_diff([], compat.splitlines(True),
    fromfile='/dev/null', tofile='b/'+str(crel)))
(here / 'compiler_fusion.patch').write_text(patch)
metrics = {
    'baseline_file': str(rel),
    'baseline_sha256': hashlib.sha256(before.encode()).hexdigest(),
    'proposal_sha256': hashlib.sha256(after.encode()).hexdigest(),
    'baseline': {'lines':len(before.splitlines()),'bytes':len(before.encode())},
    'proposal': {'lines':len(after.splitlines()),'bytes':len(after.encode())},
    'compatibility': {'lines':len(compat.splitlines()),'bytes':len(compat.encode())},
}
(here / 'source_metrics.json').write_text(json.dumps(metrics, indent=2)+'\n')
print(json.dumps(metrics, indent=2))
