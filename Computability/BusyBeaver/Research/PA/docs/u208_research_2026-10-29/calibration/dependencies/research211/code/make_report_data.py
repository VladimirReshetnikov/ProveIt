#!/usr/bin/env python3
"""Generate the exact dense transition appendix directly from the frozen table."""
from pathlib import Path
from core import census, read_table

ROOT = Path(__file__).resolve().parents[1]


def main():
    table = read_table(ROOT / "machine/u211.tm")
    states = sorted(census(table, 211, 211))
    def action(q, b):
        w, d, t = table[q, b]
        return f"{w}\\,{('R' if d == 1 else 'L')}\\,{('H' if t == 211 else t)}"
    lines = [r"\begingroup\footnotesize", r"\setlength{\tabcolsep}{6pt}\renewcommand{\arraystretch}{1.08}",
             r"\begin{longtable}{rll@{\hspace{5mm}}rll@{\hspace{5mm}}rll}",
             r"\caption{The complete dense U211 table. Each action is write, move, next state.}\label{tab:machine}\\",
             r"\toprule State & Read 0 & Read 1 & State & Read 0 & Read 1 & State & Read 0 & Read 1\\\midrule",
             r"\endfirsthead", r"\toprule State & Read 0 & Read 1 & State & Read 0 & Read 1 & State & Read 0 & Read 1\\\midrule",
             r"\endhead", r"\midrule\multicolumn{9}{r}{Continued on next page}\\\endfoot",
             r"\bottomrule\endlastfoot"]
    height = (len(states) + 2) // 3
    for index in range(height):
        row = []
        for column in range(3):
            position = index + column * height
            if position < len(states):
                q = states[position]
                row += [str(q), "$" + action(q, 0) + "$", "$" + action(q, 1) + "$"]
            else:
                row += ["", "", ""]
        lines.append(" & ".join(row) + r"\\")
    lines += [r"\end{longtable}", r"\endgroup"]
    (ROOT / "paper/transition_table.tex").write_text("\n".join(lines) + "\n")
    print("Generated paper/transition_table.tex from all 422 literal rows")


if __name__ == "__main__":
    main()
