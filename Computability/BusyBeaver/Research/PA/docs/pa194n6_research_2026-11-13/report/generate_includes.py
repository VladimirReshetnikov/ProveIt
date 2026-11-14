#!/usr/bin/env python3
"""Generate deterministic report tables from the delivered evidence."""
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def load(path):
    return json.loads((ROOT / path).read_text())


def tex(value):
    replacements = {
        "\\": r"\textbackslash{}", "_": r"\_", "&": r"\&",
        "%": r"\%", "#": r"\#", "$": r"\$", "{": r"\{", "}": r"\}",
        "→": r"$\to$", "Γ": r"$\Gamma$", "ρ": r"$\rho$",
        "≤": r"$\le$", "≥": r"$\ge$", "−": "-", "–": "--", "—": "---",
    }
    return "".join(replacements.get(c, c) for c in str(value))


def write(name, text):
    (HERE / name).write_text(text + "\n")


construction = load("machine/receipt.json")
independent = load("machine/independent/receipt.json")
native_hash = hashlib.sha256((ROOT / "machine/machine.native.tm").read_bytes()).hexdigest()
dense_hash = hashlib.sha256((ROOT / "machine/machine.tm").read_bytes()).hexdigest()
assert dense_hash == construction["dense_sha256"] == independent["dense_sha256"]
assert native_hash == construction["native_sha256"] == independent["native_sha256"]

write("identity.tex", r"""\begin{center}
\begin{tabular}{@{}lr@{}}\toprule
Machine property & Value\\\midrule
Working states / complete binary rows & 194 / 388\\
Dense initial / halt labels & 0 / 194\\
Native initial / halt labels & 74 / 254\\
Source instructions / primitive outcomes & 3,776 / 4,877\\
Unfolded controls / simultaneous folds & 202 / 8\\
Exact blank startup & 58,320 transitions\\\bottomrule
\end{tabular}
\end{center}
The exact dense-table SHA-256 is
\begin{center}\small\file{""" + dense_hash + r"""}.\end{center}
The native-table SHA-256 is
\begin{center}\small\file{""" + native_hash + r"""}.\end{center}""")

write("verification.tex", r"""\begin{center}\small
\begin{tabular}{@{}lrr@{}}\toprule
Verified quantity & Construction executor & Independent executor\\\midrule
Source instructions & 3,776 & 3,776\\
Primitive outcomes & 4,877 & 4,877\\
Symbolic operations & 1,531,094 & 1,115,525\\
Maximum operations per outcome & 499 & 397\\
Minimum positive duration constant & --- & 3\\
List lemmas derived from literal rows & inherited boxes & 4\\
Exact startup transitions & 58,320 & 58,320\\\bottomrule
\end{tabular}
\end{center}
The operation counts describe certificate execution, not a uniform number
of Turing-machine transitions for arbitrary register values. A third review
separately replays all 32 fold traces and all 28 incoming-context rows,
checks the source splice and label bijection, and simulates startup in
lockstep with M6. It confirms that the edited row is never read during
startup or inside a fold trace.""")

rows = {}
for line in (ROOT / "machine/machine.tm").read_text().splitlines():
    q, b, w, d, t = line.split()
    rows[int(q), int(b)] = (int(w), d, int(t))
assert len(rows) == 388


def action(q, b):
    w, d, t = rows[q, b]
    return rf"$\act{{{w}}}{{{d}}}{{{t}}}$"


table = [r"\begin{center}\small\setlength{\tabcolsep}{11pt}",
         r"\begin{longtable}{@{}rrr@{\hspace{22pt}}rrr@{}}",
         r"\toprule $q$ & Read 0 & Read 1 & $q$ & Read 0 & Read 1\\\midrule\endfirsthead",
         r"\toprule $q$ & Read 0 & Read 1 & $q$ & Read 0 & Read 1\\\midrule\endhead",
         r"\midrule\multicolumn{6}{r}{\small Continued on the next page}\\\endfoot",
         r"\bottomrule\endlastfoot"]
for q in range(97):
    table.append(f"{q} & {action(q, 0)} & {action(q, 1)} & "
                 f"{q + 97} & {action(q + 97, 0)} & {action(q + 97, 1)}" + r"\\")
table.append(r"\end{longtable}\end{center}")
write("transition_table.tex", "\n".join(table))

frontier = load("comparison/frontier194_current.json")
table = [r"{\small\renewcommand{\arraystretch}{1.12}",
         r"\begin{longtable}{@{}p{0.23\linewidth}p{0.12\linewidth}p{0.59\linewidth}@{}}",
         r"\toprule Class & Status & Distinguishing construction\\\midrule\endfirsthead",
         r"\toprule Class & Status & Distinguishing construction\\\midrule\endhead",
         r"\midrule\multicolumn{3}{r}{Continued on the next page}\\\endfoot",
         r"\bottomrule\endlastfoot"]
for item in frontier:
    status = item["status"].lower()
    status = "Rejected" if "reject" in status else "Auxiliary" if "auxiliary" in status else "Supported"
    table.append(f"{tex(item['name'])} & {status} & {tex(item['change'])}" + r"\\[4pt]")
table.append(r"\end{longtable}}")
write("frontier.tex", "\n".join(table))

packets = load("comparison/packet_ledger_current.json")
table = [r"{\small\renewcommand{\arraystretch}{1.12}",
         r"\begin{longtable}{@{}p{0.38\linewidth}p{0.58\linewidth}@{}}",
         r"\toprule Packet & Reported contribution\\\midrule\endfirsthead",
         r"\toprule Packet & Reported contribution\\\midrule\endhead",
         r"\midrule\multicolumn{2}{r}{Continued on the next page}\\\endfoot",
         r"\bottomrule\endlastfoot"]
for i, item in enumerate(packets, 1):
    name = r"\file{" + item["packet"] + "}"
    table.append(f"{i}. {name} & {tex(item['reported_contribution'])}" + r"\\[5pt]")
table.append(r"\end{longtable}}")
write("packet_ledger.tex", "\n".join(table))

write("search_results.tex", r"""Two new grammar moves were explored beyond
single local rotations. A global dynamic-programming reparser rebuilds the
190-token AX word using distinct substrings and randomized repetition costs.
A second reparser replaces a whole subtree using the currently shared
subtree dictionary. Both preserve the macro word and use the inherited
simultaneous-fold scorer and scanner penalties; any promising score would
still need exact source and physical validation.

\begin{center}\small
\begin{tabularx}{\linewidth}{@{}lrrX@{}}\toprule
Search & Proposal slots & Time cap & Observed result\\\midrule
Global word reparse & 3,278 & 180 s & Best 60 effective AX controls; total 194.\\
Dictionary subtree reparse & 1,113,967 & 180 s & Best total 194; 733,412 accepted slots.\\
MILP-skeleton binarization & 1,220,188 & 60 s & Best penalized reader score 69; no accepted machine.\\\bottomrule
\end{tabularx}
\end{center}
Proposal slots include repetitions, no-ops, and skipped candidates; they
are not counts of distinct verified machines. CPU-time caps are dependent
on the execution environment.

A separate mixed-integer model considers the 226 repeated AX substrings
and the whole word, minimizing the sum of right-hand-side lengths minus
one, with inherited increment macros free. After 180 seconds HiGHS had
feasible cost 67 and reported a dual bound 63, with a remaining gap.
This is a finite grammar objective, not a physical state objective; the
numerical solver output is not a formally checked lower-bound certificate.

The new PA194N6 table also received fresh local-state screens. Collecting
all 4,877 source outcomes, generic list proofs, unary-loop interiors, and
the complete startup produced 19,318 symbolic local views. Their conservative
radius-five expansions give 29,282 eleven-cell windows covering every one
of the 194 controls. With a 300-step local bound, a common-action merger
and a per-incoming-edge bypass each returned zero candidates. A separate
uniform-history screen of the unfolded 202-control parent considered all
129 eligible controls and found exactly the eight existing disjoint fold
opportunities, with no ninth.

The complete drivers, frozen inputs, receipts, and empty candidate lists
are under \file{research/}. The new searches were completed; historical
million-proposal counts are not being passed off as fresh work. These
negative results leave open larger local windows, longer detours,
simultaneous changes to several helper controls, new tape encodings,
different logical interfaces, and other global redesigns. They give no
lower bound for arbitrary PA-consistency machines. The accepted fallback
does not depend on the success or reproducibility of a stochastic search.""")

write("reproduction.tex", r"""Python 3.10 or later and its standard library
suffice for the accepted construction and its independent physical audit.
Run with assertions enabled, without \file{-O} or \file{PYTHONOPTIMIZE}.
From the package root:
\begin{verbatim}
python3 -B construction/build.py --output generated
python3 -B verification/check.py generated
python3 -B verification/review_structure.py
python3 -B comparison/check_current_novelty.py generated/machine.tm
\end{verbatim}
The first two commands reconstruct the literal table, complete source,
folds and certificates, then run the separate literal implementation.
The third is a read-only structural/fold/startup audit against the frozen
parent. The fourth compares the new table with the bundled current census.
No network or repository checkout is required for these commands.

Optional local reduction screens use a C++17 compiler:
\begin{verbatim}
cd research
python3 replay_physical.py
\end{verbatim}
The research README gives the longer grammar-search commands; only the
optional MILP experiment requires NumPy and SciPy. Recomputing the full
external corpus inventory additionally requires a checkout of the pinned
ProveIt revision and \file{rg}; this is separate from verifying the machine.

To regenerate the report's data tables and compile its PDF:
\begin{verbatim}
cd report
python3 generate_includes.py
pdflatex -interaction=nonstopmode -halt-on-error pa194n6_research.tex
pdflatex -interaction=nonstopmode -halt-on-error pa194n6_research.tex
\end{verbatim}
Run one further LaTeX pass if requested for references or long-table widths.
Standard TeX Live packages named in the preamble are sufficient.""")
print("Generated identity, verification, transition, comparison, search and reproduction includes.")
