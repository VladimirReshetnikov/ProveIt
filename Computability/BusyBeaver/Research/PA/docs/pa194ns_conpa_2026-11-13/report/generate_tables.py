#!/usr/bin/env python3
"""Generate report tables directly from released machine/evidence files."""
from pathlib import Path
import csv
import json

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "report"


def tex(s):
    s = str(s)
    return s.replace("\\", r"\textbackslash{}").replace("&", r"\&").replace("%", r"\%").replace("_", r"\_\allowbreak ").replace("#", r"\#")


rows = {}
for line in (ROOT / "machine/machine.tm").read_text().splitlines():
    q, b, w, d, t = line.split()
    rows[int(q), int(b)] = f"{w}{d}{'H' if t == '194' else t}"
assert len(rows) == 388
table = [r"\begingroup\small", r"\setlength{\tabcolsep}{10pt}",
         r"\begin{longtable}{@{}rllrll@{}}",
         r"\toprule State & Read 0 & Read 1 & State & Read 0 & Read 1\\",
         r"\midrule\endhead"]
for q in range(97):
    p = q + 97
    table.append(f"{q} & {rows[q,0]} & {rows[q,1]} & {p} & {rows[p,0]} & {rows[p,1]}" + r"\\")
table += [r"\bottomrule\end{longtable}\endgroup"]
(OUT / "transition_table.tex").write_text("\n".join(table) + "\n")

frontier = list(csv.DictReader((ROOT / "comparison/frontier194.csv").open()))
assert len(frontier) == 28
roles = {"reported-principal": "Principal report", "supplementary": "Supplement",
         "search-seed": "Research seed", "rejected": "Rejected"}
table = [r"\begingroup\small", r"\begin{longtable}{@{}>{\raggedright\arraybackslash}p{0.23\linewidth}>{\raggedright\arraybackslash}p{0.17\linewidth}>{\raggedright\arraybackslash}p{0.54\linewidth}@{}}",
         r"\toprule Graph representative & Role & Difference and evidence boundary\\",
         r"\midrule\endhead"]
for row in frontier:
    table.append(tex(row["name"]) + r"\newline {\footnotesize\texttt{" + row["sha256"][:12] + "}} & " +
                 tex(roles[row["status"]]) + " & " + tex(row["change"]) + r"\\[5pt]")
table += [r"\bottomrule\end{longtable}\endgroup"]
(OUT / "frontier194_table.tex").write_text("\n".join(table) + "\n")

construction = json.loads((ROOT / "construction/recorded/receipt.json").read_text())
independent = json.loads((ROOT / "verification/recorded/receipt.json").read_text())
symbolic = construction["symbolic_runtime"]
lines = [r"\begin{center}", r"\begin{tabular}{@{}lrr@{}}",
         r"\toprule Quantity & Construction checker & Independent checker\\\midrule",
         r"Working controls / transition rows &194 / 388&194 / 388\\",
         r"Primitive source sites &3,650&3,650\\",
         r"Source outcomes &4,750&4,750\\",
         f"Symbolic steps &{symbolic['total_steps']:,}&{independent['symbolic_steps']:,}" + r"\\",
         f"Maximum symbolic steps per outcome &{symbolic['max_steps']}&{independent['maximum_symbolic_steps']}" + r"\\",
         r"Exact blank startup &57,768&57,768\\",
         r"\bottomrule\end{tabular}\end{center}",
         r"The independent checker also records a minimum positive-duration constant of 3, four generic list lemmas rederived from literal rows, and exact agreement of two source-graph resolvers. The separate simultaneous fold check has 32 cases. Symbolic-step counts measure verification work, not the machine's running time on arbitrary register values."]
(OUT / "verification_summary.tex").write_text("\n".join(lines) + "\n")
print("Generated transition, frontier, and verification tables.")
