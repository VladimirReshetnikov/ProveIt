#!/usr/bin/env python3
"""Reproduce high-precision numerical diagnostics (requires mpmath)."""
from __future__ import annotations
import argparse
import csv
from pathlib import Path
import mpmath as mp
from coefficients import read_coefficients

ROOT = Path(__file__).resolve().parent.parent


def bell_numbers(n_max: int) -> list[int]:
    """Bell triangle: exact integer additions only."""
    row, result = [1], [1]
    for _ in range(n_max):
        new = [row[-1]]
        for value in row:
            new.append(new[-1] + value)
        row = new
        result.append(row[0])
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--precision", type=int, default=70)
    args = parser.parse_args()
    if args.precision < 30:
        parser.error("--precision must be at least 30 decimal digits")
    mp.mp.dps = args.precision
    a = read_coefficients(ROOT / "data" / "coefficients.txt")
    bell = bell_numbers(len(a) - 1)
    rows: dict[int, list[mp.mpf]] = {}
    with (ROOT / "data" / "diagnostics.csv").open("w", newline="", encoding="utf-8") as out:
        writer = csv.writer(out)
        writer.writerow(["n", "log_a_n", "log10_a_n", "root_normalization_Q_n",
                         "ratio_a_n_over_a_n_minus_1", "W_n", "ratio_minus_n_over_W_n",
                         "log_a_n_over_Bell_n", "log_conjectural_constant_estimator",
                         "candidate_ratio", "actual_minus_candidate_ratio"])
        for n in range(2, len(a)):
            log_a = mp.log(a[n])
            w = mp.lambertw(n)
            ratio = mp.mpf(a[n]) / a[n - 1]
            q = mp.e * mp.log(n) / n * mp.exp(log_a / n)
            log_ab = log_a - mp.log(bell[n])
            d = log_ab - w * w - 3 * w
            candidate = n / w + 2 + w / (2 * (1 + w) ** 2)
            vals = [log_a, log_a / mp.log(10), q, ratio, w,
                    ratio - n / w, log_ab, d, candidate, ratio - candidate]
            rows[n] = vals
            writer.writerow([n] + [mp.nstr(v, 40) for v in vals])
    selected = [20, 50, 100, 200, 400, 800, 1200]
    with (ROOT / "data" / "diagnostics_table.tex").open("w", encoding="utf-8") as out:
        out.write(r"\begin{table}[htbp]" + "\n" + r"\centering\small" + "\n")
        out.write(r"\begin{tabular}{rrrrr}\toprule" + "\n")
        out.write(r"$n$ & $\log_{10}a_n$ & $Q_n$ & $R_n-n/W(n)$ & $D_n^{\mathrm{num}}$ \\" + "\n")
        out.write(r"\midrule" + "\n")
        for n in selected:
            if n not in rows:
                continue
            v = rows[n]
            # Six decimal places are enough for a printed diagnostic table.
            out.write(f"{n} & {float(v[1]):.6f} & {float(v[2]):.6f} & "
                      f"{float(v[5]):.6f} & {float(v[7]):.6f} " + r"\\" + "\n")
        out.write(r"\bottomrule\end{tabular}" + "\n")
        out.write(r"\caption{Diagnostics from independently generated exact coefficients. "
                  r"Only the limit $Q_n\to1$ is proved here. The final column tests "
                  r"the conjecture of Section~\ref{sec:finer}.}" + "\n")
        out.write(r"\label{tab:diagnostics}\end{table}" + "\n")
    for n in selected:
        if n in rows:
            v = rows[n]
            print(f"n={n}: Q={mp.nstr(v[2],12)}, ratio-n/W={mp.nstr(v[5],12)}, "
                  f"log(C_n)={mp.nstr(v[7],12)}, ratio residual={mp.nstr(v[9],10)}")
    print("Wrote data/diagnostics.csv and data/diagnostics_table.tex")


if __name__ == "__main__":
    main()
