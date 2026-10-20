#!/usr/bin/env python3
"""Rebuild the complete TeX table appendix from the exact canonical TM."""
from pathlib import Path
import hashlib

ROOT = Path(__file__).resolve().parents[1]
path = ROOT / "machine/k225_dn.tm"
digest = hashlib.sha256(path.read_bytes()).hexdigest()
if digest != "07d778756d4a061933ecc726ccca4c1f321122380c707e9a2638ab24fdfb7048":
    raise ValueError("Unexpected canonical machine")
rows = {}
for line in path.read_text().splitlines():
    if not line or line.startswith("#"):
        continue
    q, b, w, d, t = line.split()
    rows[int(q), int(b)] = w + r"\," + d + r"\," + ("H" if t == "225" else t)
if set(rows) != {(q, b) for q in range(225) for b in (0, 1)}:
    raise ValueError("Incomplete or duplicate canonical states")
lines = ["% Generated from the exact dense table by build_report_assets.py.",
         r"\section{Complete canonical transition table}",
         r"\label{sec:complete-table}",
         r"Start state 0; halt state $H=225$; blank symbol 0. The table uses 225 working states, including startup. An entry $w\,D\,q$ writes $w$, moves in direction $D$, and enters $q$.",
         r"\begin{quote}\small\nolinkurl{" + digest + r"}\end{quote}"]
for page in range(2):
    if page:
        lines += [r"\clearpage", r"\subsection*{Canonical transition table, continued}"]
    base = page * 114
    groups = [list(range(base + i * 38, min(base + (i + 1) * 38, 225))) for i in range(3)]
    lines += [r"\begin{center}", r"\small", r"\setlength{\tabcolsep}{5pt}",
              r"\renewcommand{\arraystretch}{1.05}",
              r"\begin{tabular}{rll@{\hspace{13pt}}rll@{\hspace{13pt}}rll}", r"\toprule",
              r"$q$ & Read 0 & Read 1 & $q$ & Read 0 & Read 1 & $q$ & Read 0 & Read 1\\", r"\midrule"]
    for index in range(38):
        cells = []
        for group in groups:
            if index < len(group):
                q = group[index]
                cells += [str(q), "$" + rows[q, 0] + "$", "$" + rows[q, 1] + "$"]
            else:
                cells += ["", "", ""]
        lines.append(" & ".join(cells) + r"\\")
    lines += [r"\bottomrule", r"\end{tabular}", r"\end{center}"]
(ROOT / "report/transition_table.tex").write_text("\n".join(lines) + "\n")
print("Complete table appendix rebuilt from " + digest)
