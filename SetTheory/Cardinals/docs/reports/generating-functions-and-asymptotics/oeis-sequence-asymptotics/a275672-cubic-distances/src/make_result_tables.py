#!/usr/bin/env python3
"""Regenerate the finite-results table and OEIS draft from verified data."""
from pathlib import Path
import csv
import json

from finite_bounds import row

ROOT = Path(__file__).resolve().parents[1]
historical = {0:0, 1:1, 2:3, 3:4, 4:6, 5:7, 6:9}
catalog = json.loads((ROOT/"data/witnesses.json").read_text())["witnesses"]
lower = {w["n"]:w["size"] for w in catalog}
proofs = {}
for path in list((ROOT/"data").glob("*_exact_certificate.json")) + list(
        (ROOT/"data").glob("*_upper_certificate.json")):
    certificate = json.loads(path.read_text())
    if not certificate.get("case_coverage_verified"):
        raise ValueError(f"Unverified case coverage: {path}")
    n = certificate["n"]
    upper = certificate["target_ruled_out"]-1
    proofs[n] = min(proofs.get(n, upper), upper)

rows = []
for n in range(31):
    r = row(n)
    upper = min(r["combined_upper"], historical.get(n, 10**6), proofs.get(n, 10**6))
    lo = lower[n]
    assert lo <= upper
    rows.append({
        "n":n, "lower_bound":lo, "upper_bound":upper,
        "exact_value":lo if lo == upper else None,
        "distance_count":r["distance_count"],
        "palette_upper":r["palette_upper"], "parity_upper":r["parity_upper"],
        "evidence": "historical exact" if n in historical else
                    ("new exact search plus witness" if lo == upper else
                     "witness plus exhaustive upper bound" if n in proofs else
                     "witness plus arithmetic upper bound")
    })
(ROOT/"data/finite_results.json").write_text(json.dumps(rows, indent=2)+"\n")
with (ROOT/"data/finite_results.csv").open("w", newline="") as f:
    writer = csv.DictWriter(f, fieldnames=list(rows[0]))
    writer.writeheader()
    writer.writerows(rows)

baseline = {7:(10,12), 8:(11,13), 9:(12,15), 10:(13,17)}
lines = [
    r"The exhaustive computations and integer-coordinate witnesses give",
    r"the following improvements over the retrieved OEIS entry.",
    r"\begin{table}[ht]", r"\centering",
    r"\caption{Advances beyond the retrieved OEIS baseline.}",
    r"\label{tab:small-results}",
    r"\begin{tabular}{rlll}", r"\toprule",
    r"\(n\)&Published interval&Conclusion here&Evidence\\", r"\midrule",
]
for n, (oldlo, oldhi) in baseline.items():
    r=rows[n]
    result = (rf"a_{{{n}}}={r['lower_bound']}" if r["exact_value"] is not None else
              rf"{r['lower_bound']}\le a_{{{n}}}\le{r['upper_bound']}")
    evidence = ("Witness and exhaustive search" if n in proofs else "New witness")
    lines.append(
        rf"{n}&\({oldlo}\le a_{{{n}}}\le{oldhi}\)&\({result}\)&{evidence}\\"
    )
lines += [r"\bottomrule", r"\end{tabular}", r"\end{table}",
          r"A catalogue of integer-coordinate witnesses is supplied for every",
          r"side length from 7 through 30. The larger examples are lower bounds",
          r"unless the table explicitly labels an exact value."]
(ROOT/"article/computation_summary.tex").write_text("\n".join(lines)+"\n")

larger = [
    r"\subsection{The complete finite catalogue through side length thirty}",
    r"All lower bounds in Table~\ref{tab:catalogue} have explicit coordinate",
    r"certificates. The upper bounds shown there are the elementary palette",
    r"and parity bounds; no exactness is asserted for these larger sizes.",
    r"\begin{table}[ht]", r"\centering",
    r"\caption{Certified bounds beyond side length ten. All point lists are supplied.}",
    r"\label{tab:catalogue}",
    r"\begin{tabular}{rrr@{\qquad}rrr}", r"\toprule",
    r"\(n\)&Lower&Upper&\(n\)&Lower&Upper\\", r"\midrule"
]
for a,b in zip(range(11,21), range(21,31)):
    left,right=rows[a],rows[b]
    larger.append(
        f"{a}&{left['lower_bound']}&{left['upper_bound']}&"
        f"{b}&{right['lower_bound']}&{right['upper_bound']}"+r"\\"
    )
larger += [r"\bottomrule",r"\end{tabular}",r"\end{table}"]
(ROOT/"article/larger_catalogue.tex").write_text("\n".join(larger)+"\n")

exact_end=0
while exact_end+1<len(rows) and rows[exact_end+1]["exact_value"] is not None:
    exact_end+=1
oeis=ROOT/"oeis"
oeis.mkdir(exist_ok=True)
(oeis/"b275672.txt").write_text(
    "".join(f"{r['n']} {r['exact_value']}\n" for r in rows[:exact_end+1])
)
draft = [
    "Proposed OEIS update, prepared 2026-10-08; not submitted.",
    "",
    "Exact initial segment:",
    ", ".join(str(r["exact_value"]) for r in rows[:exact_end+1]),
    "",
    "New calculations are documented in the accompanying article and code.",
    "Impossibility claims rely on audited exhaustive C++ search, with complete",
    "diameter-case records. They are not formal SAT proof traces.",
    "",
    "Additional certified intervals:"
]
for r in rows[exact_end+1:11]:
    draft.append(f"{r['lower_bound']} <= a({r['n']}) <= {r['upper_bound']}.")
draft += ["",
          "Asymptotic theorem proved in the article:",
          "limsup a(n)/n <= sqrt(1/(6*kappa)) < 1.849,",
          "kappa = 48755553510102913673137 / 10^24.",
          "The published lower bound Omega(n^(2/3)*log(n)^(1/3))",
          "is due to Lefmann and Thiele (Combinatorica 15, 1995).",
          "No claim that publication priority of the new constant was established."]
(oeis/"proposed_update.txt").write_text("\n".join(draft)+"\n")
print(json.dumps({"rows":len(rows), "exact_initial_segment_through":exact_end}))
