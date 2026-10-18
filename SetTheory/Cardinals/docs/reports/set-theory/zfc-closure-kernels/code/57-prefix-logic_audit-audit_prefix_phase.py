#!/usr/bin/env python3
"""Independent instrumented replay of every prefix-decrement affine case.

This checks the complete symbolic target and the extra left-context premise
of each positive-decrement oracle call. Generic box arithmetic is covered by
the mathematical lemmas, not expanded into bounded numeric samples here.
"""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys
from types import SimpleNamespace

from prefix_phase import assert_prefix_phase


def audit(directory: Path) -> dict:
    source = directory / "strict_prefix_decrement.py"
    text = source.read_text()
    # Discard unused upstream audit/CLI entry points. This independent replay
    # uses the already materialized case inventory and its explicit targets.
    text = text.split("\ndef audit(", 1)[0]
    needle = "                left=[('b',1)]+left"
    assert text.count(needle) == 1
    text = text.replace(needle,
        "                PHASES.append(assert_prefix_phase(left))\n" + needle)
    sys.modules["cost_search"] = SimpleNamespace()
    phases: list[dict] = []
    namespace = {"__name__": "independent_prefix_phase_replay",
                 "PHASES": phases, "assert_prefix_phase": assert_prefix_phase}
    exec(compile(text, str(source), "exec"), namespace)
    table = {}
    raw_table = (directory / "native_table.txt").read_bytes()
    raw_cases = (directory / "native_cases.txt").read_bytes()
    for line in raw_table.decode().splitlines():
        q, b, w, direction, target = line.split()
        assert (q, int(b)) not in table
        table[q, int(b)] = int(w), direction, target
    total = Counter()
    minimum_literal = 10**20
    halt_cases = 0
    largest_pc = 0
    cases = raw_cases.decode().splitlines()
    for expected_index, line in enumerate(cases):
        fields = line.split()
        index = int(fields[0])
        assert index == expected_index
        pc = fields[1]
        physical, zero = int(fields[2]), int(fields[3])
        nxt, overflow = fields[4], int(fields[5])
        effect, register, halt = map(int, fields[6:9])
        branch = (physical, bool(zero)) if physical >= 0 else None
        box_effect = ("inc" if effect == 0 else "dec", register) if effect >= 0 else None
        target = [] if nxt == "-" else [("b", int(b)) for b in nxt]
        target += [("r", 0, 1, 43 + overflow + (effect == 1)
                    - (0 if nxt == "-" else len(nxt))),
                   ("b", 1), ("box", ("plain", box_effect))]
        rules, literal = namespace["run"](
            table, pc, branch, namespace["canon"]([("b", 1)], target),
            halt=bool(halt), fuel=1000)
        assert literal > 0
        total.update(rules)
        minimum_literal = min(minimum_literal, literal)
        halt_cases += bool(halt)
        largest_pc = max(largest_pc, len(pc))
    assert len(cases) == 8366 and halt_cases == 1
    assert len(phases) == 1925
    return {
        "status": "passed",
        "guarded_cases": len(cases),
        "halt_cases": halt_cases,
        "maximum_consumed_PC_length": largest_pc,
        "minimum_literal_progress": minimum_literal,
        "positive_decrement_phase_checks": len(phases),
        "minimum_header_phase_one_run": min(p["one_run_minimum"] for p in phases),
        "minimum_preceding_zero_run": min(p["zero_run_minimum"] for p in phases),
        "header_phase_one_run_coefficients": sorted(set(p["one_run_coefficient"] for p in phases)),
        "preceding_zero_run_coefficients": sorted(set(p["zero_run_coefficient"] for p in phases)),
        "rule_counts": dict(total),
        "input_sha256": {
            "native_table": hashlib.sha256(raw_table).hexdigest(),
            "native_cases": hashlib.sha256(raw_cases).hexdigest(),
            "strict_checker": hashlib.sha256(source.read_bytes()).hexdigest(),
        },
        "scope": "All affine n>=0 and all register files satisfying the named guard, conditional on three inherited box lemmas and the new phase-restricted positive decrement lemma.",
        "fresh_kernel_check": False,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--directory", type=Path,
                        default=Path(__file__).resolve().parents[1] / "compression/prefix_best_native")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = audit(args.directory)
    text = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    print(text, end="")
