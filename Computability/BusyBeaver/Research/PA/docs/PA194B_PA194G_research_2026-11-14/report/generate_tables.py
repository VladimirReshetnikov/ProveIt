#!/usr/bin/env python3
"""Regenerate report tables from the frozen machine and comparison receipts."""
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def esc(value):
    substitutions = {
        "&": r"\&", "%": r"\%", "$": r"\$", "#": r"\#",
        "_": r"\_\allowbreak{}", "{": r"\{", "}": r"\}",
        "~": r"\textasciitilde{}", "^": r"\textasciicircum{}",
        "\\": r"\textbackslash{}", "\n": " ",
        "≤": r"\(\le\)", "≥": r"\(\ge\)", "Γ": r"\(\Gamma\)",
        "→": r"\(\to\)", "↔": r"\(\leftrightarrow\)",
        "Σ": r"\(\Sigma\)", "₁": "1", "₂": "2",
        "–": "--", "—": "---", "−": "-", "‘": "`", "’": "'",
        "“": "``", "”": "''", "\u00a0": " ", "`": "'",
    }
    return "".join(substitutions.get(c, c) for c in str(value))


def write(name, text):
    (HERE / name).write_text(text + "\n")


def transition_table(source, output):
    rows = {}
    for line in (ROOT / source).read_text().splitlines():
        q, b, w, d, n = line.split()
        rows[int(q), int(b)] = f"{w}{d}{n}"
    lines = [r"\begingroup\small",
             r"\setlength{\tabcolsep}{7pt}",
             r"\begin{longtable}{rll@{\qquad\qquad}rll}",
             r"\toprule $q$ & read 0 & read 1 & $q$ & read 0 & read 1\\",
             r"\midrule\endfirsthead",
             r"\toprule $q$ & read 0 & read 1 & $q$ & read 0 & read 1\\",
             r"\midrule\endhead"]
    for q in range(97):
        r = q + 97
        lines.append(f"{q} & {rows[q,0]} & {rows[q,1]} & {r} & {rows[r,0]} & {rows[r,1]}" + r"\\")
    lines.extend([r"\bottomrule\end{longtable}", r"\endgroup"])
    write(output, "\n".join(lines))


def main():
    transition_table("machine/pa194B.tm", "transition_table.tex")
    transition_table("generalizer/machine.tm", "generalizer_transition_table.tex")

    frontier = json.loads((ROOT / "comparison/frontier194.json").read_text())["classes"]
    cat_names = {
        "reported principal construction": "Principal report",
        "supplementary construction": "Supplementary",
        "research auxiliary": "Research auxiliary",
        "rejected design": "Rejected",
        "source-validated rotation": "Source-validated rotation",
    }
    lines = [r"\begingroup\footnotesize",
             r"\begin{longtable}{@{}p{0.39\linewidth}p{0.31\linewidth}p{0.23\linewidth}@{}}",
             r"\toprule Historical name & Evidence category & Graph hash prefix\\\midrule\endfirsthead",
             r"\toprule Historical name & Evidence category & Graph hash prefix\\\midrule\endhead"]
    for item in frontier:
        cat = cat_names.get(item["evidence_category"], item["evidence_category"])
        lines.append(esc(item["name"]) + " & " + esc(cat) + " & " +
                     r"\texttt{" + item["graph_hash"][:12] + "}" + r"\\[3pt]")
    lines += [r"\bottomrule\end{longtable}", r"\endgroup"]
    write("frontier_ledger.tex", "\n".join(lines))

    packets = json.loads((ROOT / "comparison/packet_ledger.json").read_text())["packets"]
    lines = [r"\begingroup\footnotesize",
             r"\begin{longtable}{@{}p{0.43\linewidth}p{0.51\linewidth}@{}}",
             r"\toprule Packet and location & Reported contribution\\\midrule\endfirsthead",
             r"\toprule Packet and location & Reported contribution\\\midrule\endhead"]
    for i, packet in enumerate(packets, 1):
        title = f"{i}. " + esc(packet["packet"])
        where = "filed" if packet["location"] == "filed" else "incoming ZIP"
        summary = packet.get("reported_contribution", "See packet ledger.")
        lines.append(title + r"\newline\emph{" + where + "} & " + esc(summary) + r"\\[5pt]")
    lines += [r"\bottomrule\end{longtable}", r"\endgroup"]
    write("packet_ledger.tex", "\n".join(lines))

    data = json.loads((ROOT / "verification.json").read_text())
    values = [
        ("Working states / rows", "194 / 388"),
        ("Original primitive source sites", "3,673"),
        ("Universal symbolic source outcomes", "4,780"),
        ("Exceptional two-cell cases", "4"),
        ("Ordinary row cases under the control map", "384"),
        ("Maximum exceptional physical segment", "5 transitions"),
        ("Symbolic iterations, new table", f"{data['symbolic_runtime']['total_steps']:,}"),
        ("Maximum symbolic iterations for one outcome", str(data['symbolic_runtime']['max_steps'])),
        ("Exact primary blank startup", "58,154 transitions"),
        ("Exact PA194B blank startup", f"{data['startup']['steps']:,} transitions"),
        ("Visits to the dedicated selector during startup", str(data['startup']['helper_visits'])),
        ("Exact full-tape source-seed equality", "Passed"),
        ("Dense/native transition conjugacy", "Passed"),
        ("Prior 194-state graphs / self loops each", "82 / 21"),
        ("PA194B self loops", "22"),
    ]
    lines = [r"\begin{center}\small", r"\begin{tabular}{@{}ll@{}}",
             r"\toprule Check & Observed result\\\midrule"]
    lines += [esc(a) + " & " + esc(b) + r"\\" for a, b in values]
    lines += [r"\bottomrule\end{tabular}\end{center}"]
    write("verification_table.tex", "\n".join(lines))


if __name__ == "__main__":
    main()
