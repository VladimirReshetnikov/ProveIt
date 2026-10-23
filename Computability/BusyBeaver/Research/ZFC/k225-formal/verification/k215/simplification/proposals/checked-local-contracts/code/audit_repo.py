#!/usr/bin/env python3
"""Read-only census of the pinned K215 sources and inherited template assignments.

This script is a data/source diagnostic, not a proof compiler. It intentionally
does not certify RoutedEntry, source-occurrence coverage, or an endpoint.
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess

BASE = "cbf94cb552a3b49509e0eee80e7455d4eb5974c6"
RESEARCH = Path("Computability/BusyBeaver/Research/ZFC")
RUNTIME = RESEARCH / "k225-formal/verification/k215/simplification/proposals/round13-left-frame/runtime"
LEAN = Path("Computability/BusyBeaver/Lean/BusyBeaver/ZFC")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", required=True, type=Path)
    ap.add_argument("--out", required=True, type=Path)
    args = ap.parse_args()
    root = args.repo.resolve()
    names = [
        RESEARCH / "candidate-k215/k215.tm",
        RESEARCH / "candidate-k215/k215.native.tm",
        RESEARCH / "candidate-k215/sites215.json",
        RUNTIME / "FORMAL_TEMPLATES.json",
        RUNTIME / "LEFT_FRAME_DISCOVERY.json",
        LEAN / "KSource215Data.lean",
        LEAN / "KSim.lean",
        LEAN / "KEndpoint.lean",
        LEAN / "KEndpoint215.lean",
    ]
    hashes = {str(p): hashlib.sha256((root / p).read_bytes()).hexdigest() for p in names}
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
    if head != BASE:
        raise ValueError("Use the pinned snapshot; HEAD is " + head)
    sites = json.loads((root / names[2]).read_text())
    formal = json.loads((root / names[3]).read_text())
    discovery = json.loads((root / names[4]).read_text())
    counts = Counter(op for _, op, _ in sites)
    if len(sites) != 4751 or len({q for q, _, _ in sites}) != 4751:
        raise ValueError("Unexpected site family")
    templates = formal["templates_data"]
    if len(templates) != 35 or [t["id"] for t in templates] != list(range(35)):
        raise ValueError("Unexpected template IDs")
    assigned = set()
    for record in discovery["guard_records"]:
        index, cut, tid = record["site"], record["cut"], record["template"]
        if index in assigned:
            raise ValueError("Repeated source occurrence")
        assigned.add(index)
        word, op, arg = sites[index]
        template = templates[tid]
        key = template["key"]
        prefix, suffix = word[:cut], word[cut:]
        if not 0 <= cut < len(word) or (suffix, op, arg) != (key[2], key[3], key[4]):
            raise ValueError("Suffix/action binding mismatch")
        if "00000000" in prefix or len(word) > 48:
            raise ValueError("Bad prefix scan or gap bound")
        if len(key[6]) > len(suffix):
            raise ValueError("Unexpected length increase")
    controls = {i for i, (_, op, _) in enumerate(sites) if op in {"CB", "CC"}}
    remaining = controls - assigned
    literals = [{"site": i, "pc": sites[i][0], "op": sites[i][1], "arg": sites[i][2]}
                for i in sorted(remaining)]
    if literals != discovery["literal_controls"] or len(assigned) != 1422:
        raise ValueError("Control coverage census mismatch")
    result = {
        "status": "PASS_STATIC_CENSUS", "baseline_commit": head, "input_hashes": hashes,
        "scope": "Literal source and suffix metadata census only; no routed-entry or endpoint proof",
        "source_leaves": len(sites), "operation_counts": dict(sorted(counts.items())),
        "source_outcomes": len(sites) + counts["CD"],
        "normalized_correspondence_entries": len(re.findall(
            r"\.leaf\s*\(", (root / LEAN / "KSource215Data.lean").read_text())),
        "templates": len(templates),
        "template_symbolic_operations": sum(t["steps"] for t in templates),
        "template_max_symbolic_operations": max(t["steps"] for t in templates),
        "framed_control_occurrences": len(assigned), "literal_control_occurrences": literals,
        "candidate_expensive_execution_checks": 35 + 3 + counts["CI"] + 2 * counts["CD"] + counts["CH"],
        "production_endpoint_rebuilt": False,
        "routed_entry_occurrences_kernel_checked_by_this_script": False,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "input_hashes"}))


if __name__ == "__main__":
    main()
