#!/usr/bin/env python3
"""Assemble the standalone PA196 Challenge from the statement definitions."""

import argparse
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
HEADER = """module
public import Std
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Max
@[expose] public section
/-!
# Nonhalting and PA-independence of PA196

This binary machine has 196 working states (0 through 195) and 392 transition
rows. It starts in state 0 on a blank tape. State 196 is the halting control.

`Provable PATheory` is derivability in ordinary first-order Peano arithmetic,
including full induction. The halting sentence says there exists a finite
blank-tape computation reaching the halting control, with each step given by
the exact table. The two theorems state that the machine runs forever and that
PA proves neither this arithmetic sentence nor its negation.

The statement below gives the first-order language, the sequent calculus
and PA axioms, the arithmetic trace formula, and the tape semantics. In
the arithmetic trace, three coded sequences record the control and the
two binary tape halves. The four outer existential witnesses are the
three sequence codes and the final time. `nthFormula` is the arithmetic
formula for sequence access, and `rowFormula` gives the relation between
the three coordinates before and after a single step.
-/

"""
THEOREMS = """
namespace PalomarPA.PA196

/-- PA196 runs forever from state zero on the blank tape. -/
theorem machine_nonhalting :
    ¬ ∃ n c, machineRun n blank = some c ∧ machineStep c = none := by
  sorry

/-- Ordinary PA proves neither the exact halting sentence nor its negation. -/
theorem two_sided_independence :
    (¬ Provable PATheory pa196Nonhalting) ∧ (¬ Provable PATheory pa196Halting) := by
  sorry

end PalomarPA.PA196
"""


def declarations(relative):
    text = (ROOT / relative).read_text()
    body = text[text.index("namespace PalomarPA"):].rstrip()
    if relative == "PrimitiveData.lean":
        # The explicit arithmetic formula has over 1,000 straight-line
        # definitions. Group four per line to fit Palomar's source limit.
        lines = body.splitlines()
        start = next(i for i, line in enumerate(lines) if line.startswith("def d0 "))
        end = next(i for i, line in enumerate(lines) if line.startswith("def pair3 "))
        blocks = [" ".join(lines[i:min(i + 4, end)]) for i in range(start, end, 4)]
        body = "\n".join([*lines[:start], *blocks, *lines[end:]])
    return body


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    components = (
        "PACore.lean",
        "PAProof.lean",
        "PATheory.lean",
        "PrimitiveData.lean",
        "FixTemplateCore.lean",
        "PRTemplateCore.lean",
        "MappingTemplateCore.lean",
        "SeqTemplateCore.lean",
        "TemplateNthCore.lean",
        "NthData.lean",
        "ExactCore.lean",
        "PA196/Palomar/Data.lean",
        "PA196/Palomar/PhysicalCore.lean",
    )
    text = HEADER + "\n\n".join(map(declarations, components)) + "\n" + THEOREMS
    path = ROOT / "Challenge.lean"
    if args.check:
        if path.read_text() != text:
            raise SystemExit("Challenge.lean differs from its statement sources.")
    else:
        path.write_text(text)


if __name__ == "__main__":
    main()
