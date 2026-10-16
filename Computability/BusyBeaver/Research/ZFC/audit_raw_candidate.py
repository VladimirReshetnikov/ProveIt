"""Totalize a pinned named Wade table, number it, and run conservative audits.

The only permitted missing row is 1.inc/read1. It is filled with write1,R,halt,
preserving halting and final tape score under missing-transition halting, with
one final head move. Generated tables and labels stay outside the repository.
No proof-search or consistency calibration is established by this script.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

from recover_wade_dag import ROOT


def normalize_named(data: bytes) -> tuple[bytes, dict[str, int], dict]:
    rows, start = {}, None
    for line_number, raw in enumerate(data.decode().splitlines(), 1):
        line = raw.strip()
        if not line:
            continue
        if line.startswith("#!"):
            parts = line.split()
            if len(parts) != 3 or parts[:2] != ["#!", "start"] or start is not None:
                raise ValueError(f"invalid start directive on line {line_number}")
            start = parts[2]
            continue
        if line.startswith("#"):
            continue
        parts = line.split()
        if len(parts) != 5:
            raise ValueError(f"invalid row on line {line_number}")
        q, read, write, direction, target = parts
        if read not in ("0", "1") or write not in ("0", "1") or direction not in ("L", "R"):
            raise ValueError(f"invalid binary action on line {line_number}")
        key = q, int(read)
        if key in rows:
            raise ValueError("duplicate transition row")
        rows[key] = int(write), direction, target
    states = {q for q, _ in rows}
    if start not in states:
        raise ValueError("start must name a working state")
    terminal = {target for _, _, target in rows.values()} - states
    if terminal != {"halt"}:
        raise ValueError("expected halt as the unique terminal target")
    missing = [(q, b) for q in sorted(states) for b in (0, 1) if (q, b) not in rows]
    if missing != [("1.inc", 1)]:
        raise ValueError(f"unexpected missing transition rows: {missing}")
    rows["1.inc", 1] = 1, "R", "halt"
    order = [start] + sorted(states - {start})
    labels = {name: q for q, name in enumerate(order)}
    labels["halt"] = len(order)
    lines = ["#! start 0"]
    for q in order:
        for b in (0, 1):
            w, direction, target = rows[q, b]
            lines.append(f"{labels[q]} {b} {w} {direction} {labels[target]}")
    encoded = ("\n".join(lines) + "\n").encode()
    metadata = {"named_source_sha256": hashlib.sha256(data).hexdigest(),
                "numeric_table_sha256": hashlib.sha256(encoded).hexdigest(),
                "working_states": len(order), "start_state": 0, "halt_state": len(order),
                "transition_rows_before": len(rows)-1, "transition_rows_after": len(rows),
                "filled_row": {"state": "1.inc", "read": 1, "write": 1,
                               "move": "R", "next": "halt"},
                "missing_row_convention": "Undefined transitions halt; normalization adds one final move and preserves the tape.",
                "canonical_numbering": "Start first, then remaining working names in lexicographic order; halt last."}
    return encoded, labels, metadata


def normalization_self_tests() -> int:
    good = b"#! start q\nq 0 0 R 1.inc\nq 1 1 R halt\n1.inc 0 0 R halt\n"
    encoded, labels, metadata = normalize_named(good)
    if labels != {"q": 0, "1.inc": 1, "halt": 2} or metadata["transition_rows_after"] != 4:
        raise ValueError("normalization positive regression failed")
    bad = [b"#! start x\n" + good,
           good + b"q 0 0 R halt\n",
           good.replace(b"1.inc 0 0 R halt\n", b"1.inc 1 1 R halt\n"),
           good.replace(b"q 1 1 R halt", b"q 1 1 R otherhalt"),
           good.replace(b"q 1 1 R halt", b"q 2 1 R halt"),
           good.replace(b"#! start q", b"#! start absent")]
    for text in bad:
        try:
            normalize_named(text)
        except ValueError:
            pass
        else:
            raise ValueError("normalization negative regression was accepted")
    return 1 + len(bad)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("table", type=Path)
    parser.add_argument("--expected-sha256", required=True)
    parser.add_argument("--expected-states", type=int)
    parser.add_argument("--scratch", type=Path, required=True)
    parser.add_argument("--window-radius", type=int, default=4)
    parser.add_argument("--macro-steps", type=int, default=64)
    parser.add_argument("--output-evidence", type=Path)
    args = parser.parse_args()
    scratch = args.scratch.resolve()
    if scratch == Path("/") or scratch == ROOT or ROOT in scratch.parents:
        parser.error("scratch must be outside the repository and not filesystem root")
    data = args.table.read_bytes()
    if hashlib.sha256(data).hexdigest() != args.expected_sha256:
        parser.error("named input hash differs from the required pin")
    encoded, labels, normalization = normalize_named(data)
    count = normalization["working_states"]
    if args.expected_states is not None and count != args.expected_states:
        parser.error("named working state count differs from expected count")
    scratch.mkdir(parents=True, exist_ok=True)
    numeric_path = scratch / "raw-candidate-total.tm"
    numeric_path.write_bytes(encoded)
    (scratch / "raw-candidate-labels.json").write_text(json.dumps(labels, indent=2, sort_keys=True) + "\n")
    audit_path = scratch / "raw-candidate-numeric-audit.json"
    auditor = Path(__file__).with_name("audit_tm.py")
    completed = subprocess.run([
        sys.executable, str(auditor), str(numeric_path), "--self-test",
        "--expected-sha256", normalization["numeric_table_sha256"],
        "--expected-states", str(count), "--expected-halt", str(count),
        "--window-radius", str(args.window_radius), "--macro-steps", str(args.macro_steps),
        "--output", str(audit_path)], check=True, capture_output=True, text=True)
    result = json.loads(completed.stdout)
    if result != json.loads(audit_path.read_text()):
        raise ValueError("auditor stdout differs from its saved evidence")
    normalization["named_source_filename"] = args.table.name
    result["normalization"] = normalization
    result["normalization_self_tests_passed"] = normalization_self_tests()
    result["normalizer_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    result["auditor_sha256"] = hashlib.sha256(auditor.read_bytes()).hexdigest()
    result["theory_calibration_status"] = "Raw equality-free C_P + global-image collection + irreflexivity candidate; consistency calibration unresolved."
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output_evidence:
        args.output_evidence.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
