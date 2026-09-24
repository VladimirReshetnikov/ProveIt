import sys
sys.path.insert(0, str(__import__("pathlib").Path(__file__).resolve().parent))
import round4_1980_operation_count as M
labels = (["pow"]*8 + ["E1"]*7 + ["E2"]*3 + ["E3"]*2 + ["E4"]*2 + ["E5"]*2
          + ["E7"]*33 + ["E12"]*5 + ["E8"]*3 + ["E9"]*6 + ["E10"]*5 + ["E11"]*4
          + ["E13"]*3 + ["E14"]*8 + ["E15"]*6 + ["E16"]*5 + ["E17"]*13
          + ["E18"]*7 + ["E19"]*4 + ["E20"]*3)
assert len(labels) == len(M.SCHEDULE) == 129, (len(labels), len(M.SCHEDULE))
def tex(nm):
    if isinstance(nm, int):
        return r"5^{60}" if nm == 5**60 else str(nm)
    return r"\mathit{" + nm + "}"
rows = []
for k, ((tg, op, l, r), lab) in enumerate(zip(M.SCHEDULE, labels), 1):
    o = {"+": "+", "-": "-", "*": r"\cdot"}[op]
    assign = f"${tex(tg)} = {tex(l)} {o} {tex(r)}$"
    check = f"${tex(tg)} + {tex(r)} = {tex(l)}$" if op == "-" else f"${tex(l)} {o} {tex(r)} = {tex(tg)}$"
    rows.append(f"{k} & {lab} & {assign} & {check} \\\\")
RE = chr(92) * 2  # LaTeX row end
head = r"""% Generated from round4_1980_operation_count.py (SCHEDULE); do not edit by hand.
\begin{longtable}{@{}rlll@{}}
\toprule
No. & Eq. & Assignment & Addition/multiplication check@@RE@@
\midrule
\endfirsthead
\toprule
No. & Eq. & Assignment & Addition/multiplication check@@RE@@
\midrule
\endhead
\bottomrule
\endfoot
""".replace("@@RE@@", RE)
open(__import__("pathlib").Path(__file__).resolve().parent.parent / "1980" / "jones1980_theorem5_schedule.tex", "w", encoding="utf-8", newline="\n").write(head + "\n".join(rows) + "\n" + r"\end{longtable}" + "\n")
print("rows", len(rows))
