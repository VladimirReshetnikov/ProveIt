#!/usr/bin/env python3
"""Make numerical diagnostics and LaTeX tables from the delivered exact data.

Requires mpmath and matplotlib. Does not evaluate a floating-point determinant.
Decimal evaluations are checked at 90 and 180 digits, but are not interval
certificates. Only the already-proved limiting constant is drawn as a limit.
"""
from __future__ import annotations
import csv
import json
from pathlib import Path
import mpmath as mp
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from apery_exact import read_table

ROOT = Path(__file__).resolve().parents[1]


def psi(s: mp.mpf) -> mp.mpf:
    def f(t: mp.mpf) -> mp.mpf:
        return t*t*mp.log(t) if t else mp.mpf(0)
    return (f(s+2)-2*f(s+1)+f(s))/2


def evaluate(data: list[int], digits: int) -> tuple:
    with mp.workdps(digits):
        c = 17 + 12*mp.sqrt(2)
        lam = c/4
        logs = [mp.log(d) for d in data]
        rows = []
        for n in range(1,len(data)):
            log_h = logs[n]-logs[n-1]
            rows.append([n, len(str(data[n])), logs[n], mp.exp(logs[n]/n**2),
                         mp.exp(log_h/(2*n)), mp.exp(log_h-2*n*mp.log(lam)),
                         (logs[n]-n*(n+1)*mp.log(lam))/n])
        return c, lam, rows


def tex_table(body: str, caption: str, label: str, columns: str) -> str:
    return ("\\begin{table}[htbp]\n\\centering\n\\small\n"
            f"\\begin{{tabular}}{{{columns}}}\n\\toprule\n{body}"
            "\\bottomrule\n\\end{tabular}\n"
            f"\\caption{{{caption}}}\\label{{{label}}}\n\\end{{table}}\n")


def main() -> None:
    mp.mp.dps = 90
    data = read_table(ROOT/"data/determinants_0_200.txt")
    c, lam, rows = evaluate(data,90)
    _, _, rows_hi = evaluate(data,180)
    worst = max(abs(a-b) for row,row_hi in zip(rows,rows_hi)
                for a,b in zip(row[2:],row_hi[2:]))
    if worst >= mp.mpf("1e-75"):
        raise ArithmeticError("decimal precision stability check failed")
    with (ROOT/"data/convergence.csv").open("w",newline="",encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(["n","decimal_digits_Dn","log_Dn","root_Dn",
                         "root_norm","normalized_norm","linear_log_remainder"])
        for row in rows:
            writer.writerow(row[:2]+[mp.nstr(x,50) for x in row[2:]])
    metadata = {"limit":mp.nstr(lam,75),"C":mp.nstr(c,75),
                "working_decimal_digits":[90,180],
                "max_absolute_difference":mp.nstr(worst,12),
                "status":"PASS", "interval_certified":False,
                "matplotlib_version":matplotlib.__version__,
                "mpmath_version":mp.__version__}
    (ROOT/"data/numerical_evaluation.json").write_text(
        json.dumps(metadata,indent=2)+"\n",encoding="utf-8")

    selected = [1,2,5,10,20,50,100,200]
    body = (r"$n$ & $D_n^{1/n^2}$ & $(D_n/D_{n-1})^{1/(2n)}$ \\\n"
            .replace("\\n","\n") + "\\midrule\n")
    for n in selected:
        row = rows[n-1]
        body += f"{n} & {float(row[3]):.10f} & {float(row[4]):.10f} \\\\\n"
    (ROOT/"data/convergence_table.tex").write_text(tex_table(
        body,"Root diagnostics computed from exact integers; the common limit is "
        r"$\Lambda=8.492640687119\ldots$.","tab:numerical","rrr"))

    report = json.loads((ROOT/"data/verification.json").read_text())
    descriptions = [
        ("recurrence_vs_binomial_moments",r"Recurrence vs. defining binomial sum ($0\leq k\leq400$)"),
        ("oeis_displayed_prefix",r"Displayed OEIS prefix ($D_0,\ldots,D_9$)"),
        ("python_vs_delivered_exact_determinants",r"Python vs. GMP ($D_0,\ldots,D_{40}$)"),
        ("rational_gaussian_determinants",r"Independent rational Gaussian determinants ($n\leq12$)"),
        ("modular_gaussian_determinants",r"Independent modular determinants (11 sizes, 3 primes)"),
        ("shifted_condensation_identities",r"Shifted Desnanot--Jacobi identities"),
        ("cauchy_power_weight_determinants",r"Power-weight Cauchy determinants, rational parameters"),
        ("central_binomial_inequalities",r"Central-binomial inequality ($0\leq k\leq500$)")]
    body = "Check & Count & Result \\\\\n\\midrule\n"
    for key,text in descriptions:
        body += f"{text} & {report['checks'][key]} & Pass \\\\\n"
    (ROOT/"data/verification_table.tex").write_text(tex_table(
        body,"Exact verification results. The full integer divisions were also "
        "checked during generation.","tab:verification",r"p{0.75\linewidth}rr"))

    xs = list(range(10,len(data)))
    fig, ax = plt.subplots(figsize=(7.0,3.9))
    ax.plot(xs,[float(rows[n-1][3]) for n in xs],label=r"$D_n^{1/n^2}$")
    ax.plot(xs,[float(rows[n-1][4]) for n in xs],
            label=r"$(D_n/D_{n-1})^{1/(2n)}$")
    ax.plot([xs[0],xs[-1]],[float(lam),float(lam)],linestyle="--",label=r"$\Lambda=C/4$")
    ax.set_xlabel("Determinant index n (matrix order n + 1)")
    ax.set_ylabel("Root diagnostic")
    ax.legend()
    fig.tight_layout()
    fig.savefig(ROOT/"figures/convergence.pdf")
    fig.savefig(ROOT/"figures/convergence.png",dpi=160)
    plt.close(fig)

    experiments = json.loads((ROOT/"data/shift_experiments.json").read_text())["rows"]
    out_rows=[]
    body = r"$(m,\rho)$ & Proved limit & $n=20$ & $n=40$ & $n=80$ \\"+"\n\\midrule\n"
    for m,rho in [(1,1),(2,0),(2,1)]:
        predicted=mp.exp((m+rho)*mp.log(c)-psi(mp.mpf(rho)/m))
        values={}
        for row in experiments:
            if (row["stride"],row["rho"]) != (m,rho):
                continue
            n=row["n"]
            actual=mp.exp(mp.log(int(row["exact_determinant"]))/n**2)
            values[n]=actual
            out_rows.append({"n":n,"stride":m,"shift":row["shift"],
                             "root":mp.nstr(actual,50),
                             "proved_limit":mp.nstr(predicted,50)})
        body += (f"$({m},{rho})$ & {float(predicted):.7f} & "
                 + " & ".join(f"{float(values[n]):.7f}" for n in [20,40,80])
                 + " \\\\\n")
    (ROOT/"data/shift_diagnostics.json").write_text(json.dumps(out_rows,indent=2)+"\n")
    (ROOT/"data/shift_table.tex").write_text(tex_table(
        body,r"Numerical values of $(H_n^{(m,r_n)})^{1/n^2}$ for $r_n=\rho n$. "
        "The limits follow from the theorem, not from extrapolation.",
        "tab:shifts","rrrrr"))
    print(json.dumps(metadata,indent=2))


if __name__ == "__main__":
    main()
