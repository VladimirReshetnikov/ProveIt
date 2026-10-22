#!/usr/bin/env python3
"""Regenerate the two LaTeX appendices from the distributed exact JSON."""
from pathlib import Path
import json


def main():
    root = Path(__file__).resolve().parent.parent
    packet = json.loads((root / "data/fixed_blank_67.json").read_text())["packet"]
    lines = [
        r"\begingroup\footnotesize",
        r"\setlength{\tabcolsep}{3pt}",
        r"\begin{longtable}{rll}", r"\toprule",
        r"No. & Output register & Operation \\",
        r"\midrule", r"\endfirsthead", r"\toprule",
        r"No. & Output register & Operation \\",
        r"\midrule", r"\endhead", r"\bottomrule\endfoot",
    ]
    for n, (dst, op, a, b) in enumerate(packet["source"], 1):
        lines.append(str(n) + r" & \src{" + str(dst) + r"} & \src{"
                     + str(a) + " " + op + " " + str(b) + r"} \\")
    lines += [r"\end{longtable}", r"\endgroup"]
    (root / "circuit.tex").write_text("\n".join(lines) + "\n")
    data = json.loads((root / "data/blank_alphabet_cardinality.json").read_text())
    labels = {
        "nonhalt-write0-move-1": "Nonhalting, write 0, left",
        "nonhalt-write0-move1": "Nonhalting, write 0, right",
        "nonhalt-write1-move-1": "Nonhalting, write 1, left",
        "nonhalt-write1-move1": "Nonhalting, write 1, right",
        "headless-0": "Headless, symbol 0",
        "headless-1": "Headless, symbol 1",
        "halt-0": "Halt, symbol 0",
        "halt-1": "Halt, symbol 1",
        "initial-L": "Initial L", "initial-Q": "Initial Q",
        "initial-R": "Initial R", "V": "Vertical boundary",
        "H": "Horizontal boundary",
    }
    lines = [
        r"\begin{center}\small", r"\begin{tabular}{lrr}", r"\toprule",
        r"Center category & Multiplicity & Crosses per center \\",
        r"\midrule",
    ]
    for c in data["categories"]:
        lines.append(labels[c["name"]] + " & " + str(c["center_multiplicity"])
                     + " & " + f'{c["crosses_per_center"]:,}' + r" \\")
    lines += [
        r"\midrule", r"All centers & 439 & Total: "
        + f'{data["valid_crosses"]:,}' + r" \\",
        r"\bottomrule", r"\end{tabular}", r"\end{center}",
    ]
    (root / "cross_counts.tex").write_text("\n".join(lines) + "\n")
    print("Regenerated circuit.tex and cross_counts.tex.")


if __name__ == "__main__":
    main()
