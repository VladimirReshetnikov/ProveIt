#!/usr/bin/env python3
"""Compare the ordered literal row fixture with a ProveIt checkout.
Usage: python3 verify_horner_data.py /path/to/ProveIt [HornerResiduePilot.lean]
This is a data audit, not a replacement for Lean kernel checking.
"""
from pathlib import Path
import sys, re, json, hashlib
repo = Path(sys.argv[1])
fixture = Path(sys.argv[2]) if len(sys.argv) > 2 else Path(__file__).resolve().parents[1] / "lean/HornerResiduePilot.lean"
physical = repo / "Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942PhysicalData.lean"
def parse(text):
    chunks = {}
    pattern = r"def (chunk\d+) : List \(ℕ × ℕ\) := \[(.*?)\]"
    for match in re.finditer(pattern, text, re.S):
        chunks[match.group(1)] = [tuple(map(int, p)) for p in re.findall(r"\((\d+),\s*(\d+)\)", match.group(2))]
    match = re.search(r"def rows : List \(ℕ × ℕ\) :=\s*(.*?)(?:\n\n)", text, re.S)
    if match is None:
        raise ValueError("rows definition not found")
    names = re.findall(r"chunk\d+", match.group(1))
    return [pair for name in names for pair in chunks[name]], names
original, names = parse(physical.read_text())
replayed, replay_names = parse(fixture.read_text())
assert original == replayed and names == replay_names
assert len(original) == 941 and len(names) == 59
modulus = 11360848883
base = 10653241607
acc = 0
for _, coefficient in original:
    acc = (acc * base + 2 * coefficient) % modulus
assert acc == 10463387658
print(json.dumps({"row_count": len(original), "chunk_count": len(names),
    "ordered_rows_equal": True, "row_residue": acc,
    "ordered_rows_sha256": hashlib.sha256(json.dumps(original, separators=(",", ":")).encode()).hexdigest()}, indent=2))
