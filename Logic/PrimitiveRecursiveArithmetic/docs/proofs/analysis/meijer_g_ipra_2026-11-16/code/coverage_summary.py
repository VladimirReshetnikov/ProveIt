#!/usr/bin/env python3
from collections import Counter
from pathlib import Path
import csv, json

ROOT = Path(__file__).resolve().parents[1]
rows = list(csv.DictReader((ROOT / "claims" / "coverage.csv").open(encoding="utf-8")))
counts = Counter(r["status"] for r in rows)
out = {
    "total": len(rows),
    "status_counts": dict(sorted(counts.items())),
    "definitions": {
        "P": "proved directly by a finite constructive argument",
        "Q": "proved under explicit quantitative certificates omitted by the source",
        "C": "literal source statement corrected for branch/domain/resonance and corrected form proved",
        "R": "reduced to the general compiler/kernel framework; not fully expanded as a standalone proof",
        "X": "not established or literal source statement rejected",
    },
}
text = json.dumps(out, indent=2) + "\n"
(ROOT / "claims" / "coverage_summary.json").write_text(text, encoding="utf-8")
(ROOT / "evidence" / "coverage_summary.json").write_text(text, encoding="utf-8")
print(text, end="")
