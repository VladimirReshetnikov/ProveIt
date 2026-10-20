#!/usr/bin/env python3
"""Generate the printed table directly from the frozen canonical machine."""
from pathlib import Path
import hashlib

HERE = Path(__file__).resolve().parent
source = HERE.parent / "portable/machine/candidate223.tm"
raw = source.read_bytes()
assert hashlib.sha256(raw).hexdigest() == "c89d3f79ab12a3857092bb4b3d30bfc594079edc0f696b066ce4c386fd00f1b2"
rows = {}
for line in raw.decode("ascii").splitlines():
    if line.startswith("#"):
        continue
    q, b, w, d, target = line.split()
    q, b, w, target = map(int, (q, b, w, target))
    assert (q, b) not in rows and b in (0, 1) and w in (0, 1) and d in ("L", "R")
    rows[q, b] = (w, d, target)
assert set(rows) == {(q, b) for q in range(223) for b in (0, 1)}
assert {z for w, d, z in rows.values()} - set(range(223)) == {223}

lines = [r"\begingroup\footnotesize\setlength{\tabcolsep}{8pt}",
         r"\begin{longtable}{@{}rll@{\hspace{14mm}}rll@{}}",
         r"\toprule",
         r"$q$ & $\delta(q,0)$ & $\delta(q,1)$ & $q$ & $\delta(q,0)$ & $\delta(q,1)$\\",
         r"\midrule\endfirsthead", r"\toprule",
         r"$q$ & $\delta(q,0)$ & $\delta(q,1)$ & $q$ & $\delta(q,0)$ & $\delta(q,1)$\\",
         r"\midrule\endhead",
         r"\midrule\multicolumn{6}{r}{Continued on next page}\\\endfoot",
         r"\bottomrule\endlastfoot"]

def group(q):
    if q >= 223:
        return ["", "", ""]
    entries = [str(q)]
    for b in (0, 1):
        w, d, z = rows[q, b]
        entries.append(f"${w}{d}\\,{z}$")
    return entries

for q in range(112):
    lines.append(" & ".join(group(q) + group(q + 112)) + r"\\")
lines += [r"\end{longtable}", r"\endgroup"]
(HERE / "table223.tex").write_text("\n".join(lines) + "\n")
print("Generated all 446 transition entries from the pinned canonical table.")
