#!/usr/bin/env python3
"""Export the poisoned <4,6,9> certificate rows as a LaTeX longtable."""
import json
import math
from pathlib import Path


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    certificate = json.loads((root/"certificates"/"s469_poisoned.json").read_text(encoding="utf-8"))
    items = list(zip(range(certificate["row_first"], certificate["row_last"]+1),
                     certificate["rows"]))
    height = math.ceil(len(items)/3)
    lines = [r"\begingroup", r"\footnotesize", r"\setlength{\tabcolsep}{5pt}",
             r"\renewcommand{\arraystretch}{1.03}",
             r"\begin{longtable}{r l @{\hspace{7pt}} r l @{\hspace{7pt}} r l}",
             r"\caption{All 253 certified bounded-Grundy row vectors.}\label{tab:certificate}\\",
             r"\toprule", r"$x$ & $w_x$ & $x$ & $w_x$ & $x$ & $w_x$\\",
             r"\midrule", r"\endfirsthead", r"\toprule",
             r"$x$ & $w_x$ & $x$ & $w_x$ & $x$ & $w_x$\\",
             r"\midrule", r"\endhead", r"\midrule",
             r"\multicolumn{6}{r}{\small Continued on the next page}\\",
             r"\endfoot", r"\bottomrule", r"\endlastfoot"]
    for row in range(height):
        cells = []
        for column in range(3):
            index = row + column*height
            if index < len(items):
                x, word = items[index]
                cells.extend([str(x), r"\texttt{"+word+"}"])
            else:
                cells.extend(["", ""])
        lines.append(" & ".join(cells)+r"\\")
    lines.extend([r"\end{longtable}", r"\endgroup"])
    target = root/"data"/"s469_certificate_tables.tex"
    with target.open("w", encoding="utf-8", newline="\n") as handle:
        handle.write("\n".join(lines)+"\n")


if __name__ == "__main__":
    main()
