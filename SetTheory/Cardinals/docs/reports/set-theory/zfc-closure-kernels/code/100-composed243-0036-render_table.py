#!/usr/bin/env python3
"""Generate the report's complete transition table from the canonical artifact."""
from pathlib import Path
import argparse
import hashlib

ROOT = Path(__file__).resolve().parents[1]
SHA = "a3860fb49d6b96e58ead6293134f246d59b3958231cb56850273c4b8a8138791"


def generate():
    source = ROOT / "machine/machine.tm"
    if hashlib.sha256(source.read_bytes()).hexdigest() != SHA:
        raise ValueError("Canonical table identity changed.")
    rows = {}
    for line in source.read_text().splitlines():
        if line.startswith("#") or not line:
            continue
        q, b, w, direction, target = line.split()
        rows[int(q), int(b)] = f"{w}{direction}{target}"
    if set(rows) != {(q, b) for q in range(243) for b in (0, 1)}:
        raise ValueError("Incomplete table.")
    lines = [r"\section{Complete canonical transition table}",
             r"\label{sec:table}",
             r"The initial state is 0, the initial head position is 0, and the tape is all zero.",
             r"An entry $wDq$ writes bit $w$, moves in direction $D$, and enters state $q$.",
             r"Target 243 is the separate halt state. Every state 0--242 is a working state.",
             r"This table is generated from \path{machine/machine.tm}; the label bijection is",
             r"\path{machine/renumbering.json}. All 486 binary transitions are printed below.",
             r"\begingroup\small\setlength{\tabcolsep}{7pt}",
             r"\begin{longtable}{@{}rll@{\hspace{15pt}}rll@{\hspace{15pt}}rll@{}}",
             r"\toprule",
             r"State & Read 0 & Read 1 & State & Read 0 & Read 1 & State & Read 0 & Read 1\\",
             r"\midrule\endfirsthead",
             r"\toprule",
             r"State & Read 0 & Read 1 & State & Read 0 & Read 1 & State & Read 0 & Read 1\\",
             r"\midrule\endhead",
             r"\midrule\multicolumn{9}{r}{Continued on the next page.}\\\endfoot",
             r"\bottomrule\endlastfoot"]
    for i in range(81):
        cells = []
        for q in (i, i + 81, i + 162):
            cells += [str(q), r"\texttt{" + rows[q, 0] + "}",
                      r"\texttt{" + rows[q, 1] + "}"]
        lines.append(" & ".join(cells) + r"\\")
    lines += [r"\end{longtable}", r"\endgroup", ""]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    target = ROOT / "sections/transition_table.tex"
    text = generate()
    if args.check:
        if target.read_text() != text:
            raise ValueError("Printed transition table is stale.")
        print("PASS: all 486 printed transitions match the canonical table.")
    else:
        target.write_text(text)
        print("Generated complete canonical transition table.")


if __name__ == "__main__":
    main()
