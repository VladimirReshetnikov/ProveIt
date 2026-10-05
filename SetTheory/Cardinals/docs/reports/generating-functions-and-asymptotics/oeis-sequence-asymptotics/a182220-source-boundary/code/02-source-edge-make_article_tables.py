#!/usr/bin/env python3
"""Rebuild the article's small LaTeX tables from the recorded verification."""
import json
from pathlib import Path

root = Path(__file__).resolve().parent.parent
report = json.loads((root / "data" / "validation.json").read_text())

parts = [
    r"\subsection{Recorded exact results}",
    r"\begin{center}",
    r"\begin{tabular}{@{}rrl@{}}",
    r"\toprule",
    r"\(n\) & \(u_n\) & Positive source row \(u(n,1),u(n,2),\ldots\) \\",
    r"\midrule",
]
for entry in report["exhaustive_nested_frozenset_generation"]:
    if entry["n"] == 0:
        continue
    row = ", ".join(f"{value:,}" for value in entry["source_row"] if value)
    parts.append(f'{entry["n"]} & {entry["full_sets"]:,} & {row} ' + r"\\")
parts += [
    r"\bottomrule",
    r"\end{tabular}",
    r"\end{center}",
    "",
    "The two recurrences agree on all "
    f'{report["triangle_cells_compared"]:,}'
    r" triangle cells through \(n="
    f'{report["triangle_max_n"]}'
    r"\). The run also checks "
    f'{report["finite_defect_entries_compared"]}'
    " positive finite-deficit entries against the triangle and "
    f'{report["profile_direct_binomial_spot_checks"]}'
    " exact binomial spot checks of the adjacent-coefficient implementation.",
    "",
    r"\subsection{A uniform profile diagnostic}",
    r"At \(q=11\), \(N=1024\), the table gives the coefficient-\(\ell^1\)",
    "bound",
    r"\[",
    r" \sum_{j=0}^{N-1}",
    r" \left|\frac{b_{N+1+j}^{(d)}}{A_q}R_d^j-\rho_d^j\right|",
    r" +\frac{\rho_d^N}{1-\rho_d},",
    r"\]",
    "which bounds the closed-disk profile error. The displayed decimal",
    "values are high-precision evaluations of that bound, without an",
    "interval enclosure for floating-point roundoff.",
    r"\begin{center}",
    r"\begin{tabular}{@{}rrr@{}}",
    r"\toprule",
    r"\(d\) & Coefficient bound & Bound multiplied by \(N/m\) \\",
    r"\midrule",
]
for entry in report["profile_errors_at_largest_q"]:
    parts.append(
        f'{entry["d"]} & {float(entry["coefficient_l1_upper_bound"]):.12f}'
        f' & {float(entry["l1_bound_times_N_over_m"]):.9f} ' + r"\\"
    )
parts += [
    r"\bottomrule",
    r"\end{tabular}",
    r"\end{center}",
    "",
    r"\subsection{A complex radial diagnostic}",
    r"At \(d=0\) and \(\varepsilon=2^{-32}\), the absolute errors in",
    r"\eqref{eq:radial-ratio} are approximately",
    r"\[",
    r" \begin{array}{c|ccc}",
    r" \zeta & -1 & i & e^{i\pi/4}\\ \hline",
]
selected = [entry for entry in report["radial_errors_at_ell_32"] if entry["d"] == 0]
numbers = []
for entry in selected:
    number = float(entry["absolute_error"])
    mantissa, exponent = f"{number:.4e}".split("e")
    numbers.append(mantissa + r"\times10^{" + str(int(exponent)) + "}")
parts += [
    r" \text{absolute error} & " + " & ".join(numbers) + r"\\",
    r" \end{array}",
    r"\]",
    "The recorded run contains "
    f'{report["radial_ratio_tests"]}'
    " radial comparisons and "
    f'{report["profile_complex_point_tests"]}'
    " complex profile evaluations in total.",
]
(root / "data" / "article_tables.tex").write_text("\n".join(parts) + "\n")
