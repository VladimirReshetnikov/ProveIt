#!/usr/bin/env python3
"""Numerical illustrations, kept distinct from exact checks and proofs.

Large-k deficit plots use the first-collision model, not an exact sample
from all walks. The critical plot evaluates the explicit simple-forest
contribution in its hub window. Neither plot proves an asymptotic theorem.
"""
from pathlib import Path
import json
from math import comb, ceil, floor, log, sqrt
import numpy as np
import scipy.special as sc
import scipy.stats as st
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from fractions import Fraction
from verify_exact import touchard_values

ROOT = Path(__file__).resolve().parents[1]
DATA, FIGURES = ROOT/"data", ROOT/"figures"
DATA.mkdir(exist_ok=True)
FIGURES.mkdir(exist_ok=True)
plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 10,
                     "axes.spines.top": False, "axes.spines.right": False,
                     "axes.labelcolor": "#233444", "text.color": "#233444",
                     "savefig.bbox": "tight"})


def fresh_law(k, c, maximum_s=None, width=12):
    """Positive Dobinski saddle sum for the fresh deficit distribution.

    Numerical truncation uses width standard deviations plus a 20-point
    cushion. Repeating at widths 12 and 15 checks numerical stability.
    """
    w = float(sc.lambertw(k/c).real)
    saddle = k/w
    sigma = sqrt(k/(w*(1+w)))
    x = np.arange(max(1, floor(saddle-width*sigma-20)),
                  ceil(saddle+width*sigma+20)+1, dtype=float)
    exponent = k*np.log(x) + x*log(c) - sc.gammaln(x+1)
    exponent -= sc.logsumexp(exponent)
    if maximum_s is None:
        lam = c*w
        maximum_s = min(k-2, ceil(lam+15*sqrt(lam+1)+30))
    s = np.arange(maximum_s+2, dtype=float)
    # All ratios T_(k-s)/T_k come from the same positive tilted sum.
    log_ratios = sc.logsumexp(exponent[None, :] - s[:, None]*np.log(x)[None, :], axis=1)
    ss = s[:-1]
    log_p = (sc.gammaln(k+1)-sc.gammaln(ss+1)-sc.gammaln(k-ss+1)
             +ss*log(c)+log_ratios[:-1])
    log_p -= sc.logsumexp(log_p)
    p = np.exp(log_p)
    ratio = np.exp(log_ratios[1:]-log_ratios[:-1])
    return ss, p, ratio, w


def exact_moment_table():
    records = json.loads((DATA/"exact_rows.json").read_text())
    output = []
    for ctext, values in records.items():
        c = Fraction(ctext)
        maximum = len(values["scaled_moments"])-1
        T = touchard_values(maximum+1, c)
        for k in [16, 32, 64, 128]:
            if k > maximum:
                continue
            moment = Fraction(int(values["scaled_moments"][k]), c.denominator**k)
            H = sum(comb(k, s)*c**s*T[k-s] for s in range(k+1))
            ratio = float(moment/(2*H))
            w = float(sc.lambertw(k/float(c)).real)
            first = float(c)*w*w*(w+2+2*float(c))/(2*k)
            second_log = float(c)*w**5/(6*k*k)
            output.append({"c": ctext, "k": k, "w": w, "moment_over_2H": ratio,
                           "exp_first": float(np.exp(first)),
                           "exp_two_terms": float(np.exp(first+second_log)),
                           "scaled_additive_residual": (ratio-1-first)*k*k/w**6,
                           "asymptotic_additive_constant": float(c*c/8)})
    (DATA/"moment_diagnostics.json").write_text(json.dumps(output, indent=2)+"\n")
    with (DATA/"moment_table.tex").open("w") as out:
        out.write(r"\begin{tabular}{rrrrr}\toprule" + "\n")
        out.write(r"$c$ & $k$ & $m_k/(2H_k)$ & $e^{P_1}$ & $e^{P_1+cw^5/(6k^2)}$ \\\midrule" + "\n")
        for r in output:
            if r["k"] in [32, 128]:
                out.write(f'{r["c"]} & {r["k"]} & {r["moment_over_2H"]:.6f} & '
                          f'{r["exp_first"]:.6f} & {r["exp_two_terms"]:.6f} \\\\\n')
        out.write("\\bottomrule\\end{tabular}\n")
    return output


def deficit_diagnostics():
    output = []
    for c in [0.5, 1., 2.]:
        for k in [1000, 3000, 10000, 30000, 100000, 300000, 1000000]:
            s, p, ratio, w = fresh_law(k, c)
            n = k-s
            G1 = s*(s-1)/2*((n-1)*ratio+2+2*c)/(c*(n+1))
            model = p*(1+G1)
            model /= model.sum()
            lam = c*w
            theta = lam+c*w**3/k
            pi0 = st.poisson.pmf(s, lam)
            pi1 = st.poisson.pmf(s, theta)
            tv0 = .5*np.abs(model-pi0).sum()+.5*st.poisson.sf(s[-1], lam)
            tv1 = .5*np.abs(model-pi1).sum()+.5*st.poisson.sf(s[-1], theta)
            s2, p2, _, _ = fresh_law(k, c, int(s[-1]), width=15)
            stability = float(np.abs(p-p2).sum())
            output.append({"c": c, "k": k, "w": w,
                           "scaled_uncentered_TV": float(tv0*k/w**2.5),
                           "scaled_recentered_TV": float(tv1*k/w**2),
                           "uncentered_limit": sqrt(c/(2*np.pi)),
                           "recentered_limit": float(st.norm.pdf(1)),
                           "fresh_L1_width_change": stability,
                           "model": "Normalized exact fresh law times (1+G1); not full walk law."})
    (DATA/"deficit_diagnostics.json").write_text(json.dumps(output, indent=2)+"\n")
    fig, axes = plt.subplots(1, 2, figsize=(10, 3.8))
    colors = ["#1d5675", "#d67939", "#52887b"]
    for c, color in zip([.5, 1., 2.], colors):
        r = [x for x in output if x["c"] == c]
        axes[0].semilogx([x["k"] for x in r], [x["scaled_uncentered_TV"] for x in r],
                        "o-", color=color, label=f"c = {c:g}", markersize=4)
        axes[0].axhline(sqrt(c/(2*np.pi)), color=color, linestyle=":", linewidth=1)
        axes[1].semilogx([x["k"] for x in r], [x["scaled_recentered_TV"] for x in r],
                        "o-", color=color, label=f"c = {c:g}", markersize=4)
    axes[1].axhline(st.norm.pdf(1), color="#444444", linestyle=":", label="Normal density at 1")
    axes[0].set(title="Unshifted Poisson mean", xlabel="Moment half-length k",
                ylabel=r"$k\,d_{TV}/w^{5/2}$")
    axes[1].set(title="Corrected Poisson mean", xlabel="Moment half-length k",
                ylabel=r"$k\,d_{TV}/w^2$")
    for ax in axes:
        ax.legend(frameon=False, fontsize=8)
        ax.grid(alpha=.16)
    fig.suptitle("First-collision model: finite numerical diagnostics", fontsize=12)
    fig.tight_layout()
    for ext in ["pdf", "png"]:
        fig.savefig(FIGURES/f"deficit_profiles.{ext}", dpi=180)
    plt.close(fig)
    return output


def critical_diagnostics():
    output = []
    for tau in [.25, .5, 1., 2.]:
        for k in [1000, 3000, 10000, 30000, 100000, 300000, 1000000]:
            w = .5*log(k/tau)
            c = sqrt(tau*k)/w
            maximum = min(k-2, ceil(sqrt(tau*k)+15*(tau*k)**.25+30))
            s, p, _, _ = fresh_law(k, c, maximum)
            logQ = (sc.gammaln(k+s)-sc.gammaln(k+1)
                    -sc.gammaln(k)+sc.gammaln(k-s+1))
            # The expression equals zero also at s=0 and s=1.
            log_p = np.full_like(p, -np.inf)
            np.log(p, out=log_p, where=p > 0)
            value = float(np.exp(sc.logsumexp(log_p+logQ)))
            _, p2, _, _ = fresh_law(k, c, maximum, width=15)
            output.append({"tau": tau, "k": k, "w": w, "c": c,
                           "simple_forest_over_2H": value,
                           "limit": float(np.exp(tau)),
                           "relative_difference": value/float(np.exp(tau))-1,
                           "fresh_L1_width_change": float(np.abs(p-p2).sum()),
                           "scope": "Numerical fresh-law average of exact Catalan quotient in a concentrated window."})
    (DATA/"critical_diagnostics.json").write_text(json.dumps(output, indent=2)+"\n")
    fig, ax = plt.subplots(figsize=(7.8, 4))
    for tau, color in zip([.25, .5, 1., 2.], ["#52887b", "#1d5675", "#d67939", "#884f80"]):
        r = [x for x in output if x["tau"] == tau]
        ax.semilogx([x["k"] for x in r], [x["simple_forest_over_2H"] for x in r],
                    "o-", color=color, label=rf"$\tau={tau:g}$", markersize=4)
        ax.axhline(np.exp(tau), color=color, linestyle=":", linewidth=1)
    ax.set(xlabel="Moment half-length k", ylabel="Simple forest contribution / fresh normalization",
           title="Critical growing mean degree: exact Catalan quotient")
    ax.grid(alpha=.16)
    ax.legend(frameon=False, ncol=2)
    fig.tight_layout()
    for ext in ["pdf", "png"]:
        fig.savefig(FIGURES/f"critical_transition.{ext}", dpi=180)
    plt.close(fig)
    return output


if __name__ == "__main__":
    a = exact_moment_table()
    b = deficit_diagnostics()
    d = critical_diagnostics()
    result = {"moment_rows": len(a), "deficit_model_rows": len(b),
              "critical_rows": len(d),
              "largest_L1_change_under_wider_saddle_sum": max(
                  [x["fresh_L1_width_change"] for x in b+d]),
              "warning": "Floating-point illustrations, not interval certificates or asymptotic proof."}
    (DATA/"numerical_summary.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))
