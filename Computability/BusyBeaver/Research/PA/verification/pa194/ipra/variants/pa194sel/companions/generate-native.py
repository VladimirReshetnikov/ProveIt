"""Compose the exact selector transfer with a checked parent theorem."""

import sys
from pathlib import Path


PARENTS = {
    "AD": "PA194ADFinal",
    "B": "PA194BNative",
    "HX": "PA194HXFinal",
    "LC": "PA194LCFinal",
    "LCC": "PA194LCCFinal",
}


def main():
    if len(sys.argv) != 3 or sys.argv[1].removesuffix("Fast") not in PARENTS:
        raise SystemExit("usage: generate-native.py CANDIDATE OUTPUT")
    candidate, destination = sys.argv[1:]
    parent = PARENTS[candidate.removesuffix("Fast")]
    if candidate == "LCCFast":
        parent = "PA194LCCFastFinal"
    elif candidate.endswith("Fast"):
        parent = f"PA194{candidate}Native"
    rows = f"PA194{candidate}SELRows"
    module = f"PA194{candidate}SELFinal"
    out = Path(destination)
    out.mkdir(parents=True, exist_ok=True)
    (out / f"{module}.lean").write_text(f"""import ConPAMachineRelative
import {parent}
import {rows}

set_option autoImplicit false

namespace {module}
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint

theorem consistency_iff_literal_nonhalt :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence {rows}.table 194 :=
  ConPA.MachineRelative.consistency_iff _ _ 194 194
    {parent}.consistency_iff_literal_nonhalt
    (fun V _ _ => (PA194GuardedSelectors.sameHalt (V := V) {rows}.certificate).symm)

#print axioms consistency_iff_literal_nonhalt
end {module}
""", encoding="utf-8")


if __name__ == "__main__":
    main()
