#!/usr/bin/env python3
"""Assemble the checked source intervals using a binary division of the ordinal range."""
from pathlib import Path
import sys

if len(sys.argv) not in (2, 3):
    raise SystemExit("usage: generate-folded-coverage-aggregate.py OUTPUT [LIMIT]")
path = Path(sys.argv[1])
limit = int(sys.argv[2]) if len(sys.argv) == 3 else 3673
lines = [
    f"import PA194FoldedBatch{start}_{min(start+100,3673)}"
    for start in range(0, limit, 100)
]
lines += [
    "",
    "set_option autoImplicit false",
    "set_option maxRecDepth 65536",
    "set_option maxHeartbeats 0",
    "",
    f"namespace {path.stem}",
    "open PA194FoldedChecks PA194FoldedCoverageBatches",
    "",
    f"theorem all (i : Nat) (hi : i < {limit}) : checkAt i = true := by",
]


def generate(first, last, indent):
    if last-first == 1:
        start = first*10
        count = min(10, limit-start)
        lower = "Nat.zero_le _" if start == 0 else "by omega"
        lines.append(indent + f"exact block_sound c{start} ({lower}) (by omega)")
        return
    mid = (first+last)//2
    lines.append(indent + f"by_cases h : i < {10*mid}")
    lines.append(indent + "·")
    generate(first, mid, indent + "  ")
    lines.append(indent + "·")
    generate(mid, last, indent + "  ")


generate(0, (limit+9)//10, "  ")
lines.extend(["", "#print axioms all", f"end {path.stem}"])
path.write_text("\n".join(lines) + "\n")
