#!/usr/bin/env python3
"""Recompute the two certificates and their human-readable tables."""
from pathlib import Path
import csv
import json
from verify import Semigroup

ROOT = Path(__file__).resolve().parents[1]
CASES = [((4, 5, 6), 43, 51), ((4, 6, 9), 237, 265)]

for generators, left, right in CASES:
    s = Semigroup(generators)
    rows = {x: s.direct_row(x) for x in range(s.F+1, 2*s.F+1)}
    far = {s.cache(s.apery(y)) for y in range(s.F+1) if s.contains(y)} - {3}
    for x in range(2*s.F+1, right):
        rows[x] = s.next_row(rows, x, far)
        if rows[x-s.F][s.full] < 3:
            far.add(rows[x-s.F][s.full])
    name = "s" + "".join(map(str, generators))
    data = {
        "description": "0,1,2 are exact normal-play Grundy values; 3 means >=3.",
        "generators": generators,
        "gaps": s.gaps,
        "pattern_masks": s.patterns,
        "row_start": s.F+1,
        "row_end": right-1,
        "state_repeat": [left, right],
        "apery_four": s.apery(4),
        "rows": ["".join(str(rows[x][c]) for c in s.patterns)
                 for x in range(s.F+1, right)]
    }
    out = ROOT / "certificates" / f"{name}.json"
    # newline="\n" keeps regeneration byte-identical across platforms.
    with out.open("w", encoding="utf-8", newline="\n") as handle:
        handle.write(json.dumps(data, indent=2) + "\n")
    with (ROOT / "data" / f"{name}_low_rows.csv").open(
            "w", encoding="utf-8", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["x"] + [f"mask_{c}" for c in s.patterns])
        for x in range(s.F+1, right):
            writer.writerow([x] + [rows[x][c] for c in s.patterns])
    print("Wrote", out.name)

# The article prints the smaller certificate and its nearby-tail transition.
s = Semigroup((4, 5, 6))
main = json.loads((ROOT / "certificates" / "s456.json").read_text())
lines = [r"{\small\renewcommand{\arraystretch}{0.94}",
         r"\begin{tabular}{r*{9}{c}}", r"\toprule",
         "$x$ & " + " & ".join(f"${c}$" for c in s.patterns) + r"\\",
         r"\midrule"]
for x, encoded in enumerate(main["rows"], main["row_start"]):
    if x in (15, 36, 43, 44):
        lines.append(r"\midrule")
    if 36 <= x <= 42 or 44 <= x <= 50:
        lines.append(r"\rowcolor{pale}")
    symbols = [r"$\sat$" if digit == "3" else f"${digit}$"
               for digit in encoded]
    lines.append(str(x) + " & " + " & ".join(symbols) + r"\\")
lines.extend([r"\bottomrule", r"\end{tabular}}"])
with (ROOT / "data" / "certificate_table.tex").open(
        "w", encoding="utf-8", newline="\n") as handle:
    handle.write("\n".join(lines) + "\n")

lines = [r"\begin{tabular}{r*{7}{r}}", r"\toprule",
         r"$m(C)$ & $d=1$ & $2$ & $3$ & $4$ & $5$ & $6$ & $7$\\",
         r"\midrule"]
for c in s.patterns:
    lines.append(str(c) + " & " + " & ".join(str(s.delta(d, c))
                 for d in range(1, 8)) + r"\\")
lines.extend([r"\bottomrule", r"\end{tabular}"])
with (ROOT / "data" / "delta_table.tex").open(
        "w", encoding="utf-8", newline="\n") as handle:
    handle.write("\n".join(lines) + "\n")
print("Wrote LaTeX certificate and transition tables.")
