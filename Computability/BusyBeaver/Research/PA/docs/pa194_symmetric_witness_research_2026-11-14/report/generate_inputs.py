#!/usr/bin/env python3
"""Generate the report's exact transition tables and complete family ledger."""
from pathlib import Path
import csv

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def escape(value):
    for old, new in {
        "with1/3": "with 1/3", "All4778": "All 4,778", "startup48320": "startup 48,320",
        "reaches207states": "reaches 207 states", "not194": "not 194", "total194": "total 194",
        "length3": "length 3", "invariants,12": "invariants, 12", "two-way95/72": "two-way 95/72",
        "189 AX tokens;134": "189 AX tokens; 134", "188 AX tokens;134": "188 AX tokens; 134",
        "controls;3677": "controls; 3,677", "controls;3683": "controls; 3,683",
        "symmetric135": "symmetric 135", "or135": "or 135", "with1/3/5": "with 1/3/5",
    }.items():
        value = value.replace(old, new)
    substitutions = {
        "\\": r"\textbackslash{}", "&": r"\&", "%": r"\%",
        "$": r"\$", "#": r"\#", "_": r"\_\allowbreak{}",
        "{": r"\{", "}": r"\}", "~": r"\textasciitilde{}",
        "^": r"\textasciicircum{}", "Γ": r"\(\Gamma\)", "σ": r"\(\sigma\)",
        "→": r"\(\to\)", "−": r"\(-\)", "≥": r"\(\ge\)",
        "≤": r"\(\le\)", "–": "--", "×": r"\(\times\)",
    }
    return "".join(substitutions.get(c, c) for c in value)


def machine_table(name, filename):
    rows = {}
    for line in (ROOT / "machines" / name / "machine.tm").read_text().splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        q, b, w, direction, target = line.split()
        rows[int(q), int(b)] = w + direction + ("H" if target == "194" else target)
    assert set(rows) == {(q, b) for q in range(194) for b in (0, 1)}
    lines = [r"\begin{center}", r"\footnotesize\ttfamily",
             r"\setlength{\tabcolsep}{4pt}\renewcommand{\arraystretch}{1.09}",
             r"\begin{tabular}{rll@{\hspace{16pt}}rll@{\hspace{16pt}}rll@{\hspace{16pt}}rll}",
             r"\toprule", " & ".join(["q", "0", "1"] * 4) + r"\\", r"\midrule"]
    for offset in range(49):
        cells = []
        for group in range(4):
            q = offset + 49 * group
            cells.extend([str(q), rows[q, 0], rows[q, 1]] if q < 194 else ["", "", ""])
        lines.append(" & ".join(cells) + r"\\")
        if offset in (9, 19, 29, 39):
            lines.append(r"\addlinespace[2pt]")
    lines.extend([r"\bottomrule", r"\end{tabular}", r"\end{center}"])
    (HERE / filename).write_text("\n".join(lines) + "\n")


def family_table():
    with (ROOT / "comparison/families_current.csv").open(newline="") as stream:
        families = list(csv.DictReader(stream))
    assert len(families) == 35
    lines = [r"\small", r"\setlength{\tabcolsep}{5pt}",
             r"\begin{longtable}{@{}>{\raggedright\arraybackslash}p{0.295\linewidth}>{\raggedright\arraybackslash}p{0.675\linewidth}@{}}",
             r"\toprule Family and named designs & Semantics, physical change and proof obligation\\\midrule",
             r"\endfirsthead", r"\toprule Family and named designs (continued) & Comparison (continued)\\\midrule", r"\endhead",
             r"\midrule\multicolumn{2}{r}{\emph{Continued on next page}}\\\endfoot",
             r"\bottomrule\endlastfoot"]
    for index, row in enumerate(families, 1):
        left = r"\textbf{" + str(index) + ". " + escape(row["family"]) + r"}\par " + escape(row["designs"])
        right = (r"\textbf{Semantics.} " + escape(row["recurring_behavior"]) +
                 r"\par\textbf{Physical.} " + escape(row["physical_change"]) +
                 r"\par\textbf{Proof.} " + escape(row["proof_obligation"]))
        lines.append(left + " & " + right + r"\\\addlinespace[6pt]")
    lines.extend([r"\end{longtable}", r"\normalsize"])
    (HERE / "families.tex").write_text("\n".join(lines) + "\n")


if __name__ == "__main__":
    machine_table("PA194H5XS", "table_h5xs.tex")
    machine_table("PA194JH5XS", "table_jh5xs.tex")
    family_table()
    print("Generated both complete transition tables and all 35 family entries.")
