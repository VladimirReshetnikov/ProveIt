#!/usr/bin/env python3
"""Check the MP no-filler edge in the final unit-stride 253-state runtime.

This script uses the portable runtime reproduction bundle supplied alongside
the report.  It reads a frozen table rather than generating an earlier loader.
It proves no blank-start result or state bound below the counted runtime.

Usage:
  python check_no_filler_unit253.py --runtime-root /path/to/runtime_bundle
Optional --table selects a frozen old-label table.  Results contain only
portable relative source names, source hashes and complete checked row sets.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib
import json
from pathlib import Path
import sys


def ordered(rows):
    return [list(k) for k in sorted(rows, key=lambda pair: (int(pair[0]), pair[1]))]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runtime-root", type=Path, required=True)
    parser.add_argument("--table", type=Path)
    parser.add_argument("--output", type=Path, default=Path("no_filler_unit253"))
    args = parser.parse_args()
    runtime = args.runtime_root.resolve()
    source = args.table.resolve() if args.table else runtime / "machines/gap_clock_unit253_old.tm"
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    sys.path.insert(0, str(runtime / "code"))
    a = importlib.import_module("assemble_gap_runtime")
    loader = importlib.import_module("unit_loader")
    table = a.j.read_table(source)
    baseline_report = json.loads((runtime / "results/assembly_results.json").read_text())
    baseline_used = set(map(tuple, baseline_report["ordinary_used_rows"]))
    baseline_used |= set(map(tuple, baseline_report["protected_box_rows"]))
    baseline_used |= {(str(q), b) for q, b in baseline_report["loader_all_gap_support"]}
    assert len(table) == 506
    assert table["204", 1] == (1, "R", "113")
    assert a.j.NODES[197] == (("N", 169), ("N", 43))
    assert a.j.NODES[43] == (("N", 39), ("N", 42))
    assert a.j.NODES[42] == (("N", 41), ("N", 23))
    table["204", 1] = (1, "R", "132")
    a.j.NODES[197] = (("N", 169), ("N", 42))
    certificate, ordinary_used = a.certify(table)
    assert certificate["passed"] and certificate["cases"] == 8356, certificate
    box_rows = a.j.BOX_PAIRS - {("69", 0), ("69", 1)}
    loader_support = {(str(q), b) for q, b in loader.SUPPORT}
    used = ordinary_used | box_rows | loader_support
    assert used <= set(table)
    int_table = {(int(q), b): (w, direction, int(t))
                 for (q, b), (w, direction, t) in table.items()}
    tests = loader.suite(int_table)
    compact = a.prune(table, used, box_rows)
    compact_text = ("# Conditional prepared-frame runtime with MP truth-filler omitted.\n"
                    "# Blank initialization is not established.\n" + a.j.text_table(compact))
    target = output / "no_filler_unit253_old.tm"
    target.write_text(compact_text)
    report = {
        "status": "PASS conditional runtime contracts",
        "claim": "No blank-start consistency theorem or sub252 machine is asserted.",
        "source_commit": "85633fd2f57b5dca16f87667699134d1b500ebc0",
        "source_table": source.name,
        "source_table_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "runtime_inputs": [{"path": name, "sha256": hashlib.sha256((runtime / name).read_bytes()).hexdigest()}
                           for name in ("code/assemble_gap_runtime.py", "code/unit_loader.py",
                                        "code/joint_rotation_search.py", "code/strict_affine.py",
                                        "inputs/decoder_entries.json", "results/assembly_results.json")],
        "source_edit": {"node": 197, "right_before": 43, "right_after": 42},
        "transition_edit": [204, 1, [1, "R", 113], [1, "R", 132]],
        "instruction_certificate": certificate,
        "loader_contract": "(g,L=0,h) -> (g+1,L=g+1,h-g-2), empty PC, fixed remaining tape; g>=1",
        "loader_samples": len(tests),
        "loader_time_including_dispatch": "2*g*g+15*g+40",
        "protected_box_row_count": len(box_rows),
        "working_states": len(compact) // 2,
        "used_row_count": len(used),
        "unused_rows": ordered(set(table) - used),
        "freed_rows_vs_final_control": ordered(baseline_used - used),
        "newly_required_rows_vs_final_control": ordered(used - baseline_used),
        "ordinary_used_rows": ordered(ordinary_used),
        "protected_box_rows": ordered(box_rows),
        "loader_all_gap_support": ordered(loader_support),
        "all_required_rows": ordered(used),
        "output_table": target.name,
        "output_table_sha256": hashlib.sha256(compact_text.encode()).hexdigest(),
    }
    (output / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items()
                      if not k.endswith("_rows") and k not in ("runtime_inputs", "loader_all_gap_support")},
                     indent=2))


if __name__ == "__main__":
    main()
