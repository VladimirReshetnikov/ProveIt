#!/usr/bin/env python3
"""Regenerate printable appendices from the exact delivered data (stdlib only)."""
from pathlib import Path
import csv
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def tex(value):
    translate = {"\\": r"\textbackslash{}", "&": r"\&", "%": r"\%", "$": r"\$",
                 "#": r"\#", "_": r"\_\allowbreak{}", "{": r"\{", "}": r"\}",
                 "~": r"\textasciitilde{}", "^": r"\textasciicircum{}"}
    return "".join(translate.get(c, c) for c in str(value)).replace("×", r"$\times$")


def csv_rows(relative):
    with (ROOT / relative).open(newline="") as stream:
        return list(csv.DictReader(stream))


def write(name, lines):
    (HERE / name).write_text("\n".join(lines) + "\n")


def transitions():
    table = {}
    for line in (ROOT / "machine/machine.tm").read_text().splitlines():
        q, bit, write_bit, direction, target = line.split()
        table[int(q), int(bit)] = f"{write_bit}{direction}{'H' if target == '194' else target}"
    assert set(table) == {(q, b) for q in range(194) for b in (0, 1)}
    lines = [r"\begingroup\small\setlength{\tabcolsep}{15pt}",
             r"\begin{longtable}{@{}rll@{\qquad\qquad}rll@{}}",
             r"\toprule State & Read 0 & Read 1 & State & Read 0 & Read 1\\\midrule\endhead"]
    for a in range(97):
        b = a + 97
        lines.append(f"{a} & \\texttt{{{table[a,0]}}} & \\texttt{{{table[a,1]}}} & "
                     f"{b} & \\texttt{{{table[b,0]}}} & \\texttt{{{table[b,1]}}}" + r"\\")
    lines += [r"\bottomrule\end{longtable}\endgroup"]
    write("transition_table.tex", lines)


def folds():
    data = json.loads((ROOT / "machine/folds.json").read_text())
    lines = [r"\begin{table}[htbp]\centering\small",
             r"\begin{tabular}{@{}rrll@{}}\toprule",
             r"Removed & Retained & Retained read 0 & Retained read 1\\\midrule"]
    for removed, retained, actions in data:
        entries = [f"{w}{'R' if d else 'L'}{q}" for w, d, q in actions]
        lines.append(f"{removed} & {retained} & \\texttt{{{entries[0]}}} & \\texttt{{{entries[1]}}}" + r"\\")
    lines += [r"\bottomrule\end{tabular}",
              r"\caption{The seven simultaneous folds, with native transition labels.}\label{tab:folds}",
              r"\end{table}"]
    write("folds.tex", lines)


def frontier():
    rows = csv_rows("comparison/all_194_designs.csv")
    assert len(rows) == 94
    categories = ["reported principal construction", "supplementary construction", "research auxiliary",
                  "research seed", "rejected", "rejected diagnostic"]
    names = {"reported principal construction": "Principal", "supplementary construction": "Supplementary",
             "research auxiliary": "Auxiliary", "research seed": "Seed", "rejected": "Rejected",
             "rejected diagnostic": "Diagnostic"}
    rows.sort(key=lambda r: (categories.index(r["category"]), r["name"]))
    assert len({r["canonical_class"][:12] for r in rows}) == 94
    lines = [r"\begingroup\footnotesize\setlength{\tabcolsep}{4pt}",
             r"\begin{longtable}{@{}p{0.27\linewidth}p{0.13\linewidth}p{0.55\linewidth}@{}}",
             r"\toprule Name / class identifier & Status & Mechanism or reported limitation\\\midrule\endhead"]
    for i, row in enumerate(rows, 1):
        name = r"\href{" + row["source_url"] + "}{" + tex(row["name"]) + "}"
        label = f"{i}. {name}" + r"\newline\texttt{" + row["canonical_class"][:12] + "}"
        if row["filed_or_incoming"] == "incoming":
            label += r"\newline Current incoming"
        lines.append(label + " & " + names[row["category"]] + " & " + tex(row["mechanism"]) + r"\\[5pt]")
    lines += [r"\bottomrule\end{longtable}\endgroup"]
    write("frontier.tex", lines)


def packets():
    rows = csv_rows("comparison/packet_ledger82.csv")
    assert len(rows) == 82
    prefix = "https://github.com/VladimirReshetnikov/ProveIt/"
    revision = "32d0d8b7d93a63ad4106c18cdb29b37927acdad2"
    lines = [r"\begingroup\footnotesize\setlength{\tabcolsep}{4pt}",
             r"\begin{longtable}{@{}p{0.37\linewidth}p{0.58\linewidth}@{}}",
             r"\toprule Packet and arrival & Reported contribution / comparison\\\midrule\endhead"]
    for i, row in enumerate(rows, 1):
        source = row["source"]
        url = source if source.startswith("https://") else prefix + ("tree/" if source.endswith("/") else "blob/") + revision + "/" + source
        label = f"{i}. " + r"\href{" + url + "}{" + tex(row["packet"]) + "}"
        label += r"\newline " + tex(row["arrival"]) + r"\newline " + tex(row["location"])
        lines.append(label + " & " + tex(row["reported_result"]) + r"\\[5pt]")
    lines += [r"\bottomrule\end{longtable}\endgroup"]
    write("packets.tex", lines)


def terminal_search():
    # Frozen completed-run counts, not an extrapolation from timings.
    runs = json.loads((ROOT / "research/grammar/summary.json").read_text())["runs"]
    labels = {"run": "Four terminal variants", "safe": "Eleven screened endings"}
    entries = [(labels[r["prefix"]], r["iterations"], r["accepted_mutations"]) for r in runs]
    lines = [r"\begin{center}\small\begin{tabular}{@{}lrrrr@{}}\toprule",
             r"Input family & Iterations & Accepted & Best score & Sub-194 hits\\\midrule"]
    for name, iterations, accepted in entries:
        lines.append(f"{name} & {iterations:,} & {accepted:,} & 60 & 0" + r"\\")
    lines += [r"\bottomrule\end{tabular}\end{center}"]
    write("terminal_search.tex", lines)


if __name__ == "__main__":
    transitions()
    folds()
    frontier()
    packets()
    terminal_search()
    print("Generated the exact 194-state table, seven folds, 94-class ledger, 82-packet ledger, and search table.")
