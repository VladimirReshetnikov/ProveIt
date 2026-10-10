#!/usr/bin/env python3
"""Numerical illustrations of the proved Euler bounds; not proof certificates."""
from pathlib import Path
from math import comb
import csv
import json
import mpmath as mp
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[1]
mp.mp.dps = 90


def axis_constant(b):
    return mp.dirichlet(b, [0, 1, 0, -1]) + mp.power(2, -b) * mp.altzeta(b)


def euler_values(a, b, indices):
    last = max(indices)
    harmonics = [mp.mpf(0)]
    for n in range(1, 2 * last):
        harmonics.append(harmonics[-1] + mp.power(n, -b))
    f = [harmonics[2*n] / mp.power(2*n+1, a) for n in range(last)]
    result = {}
    for N in indices:
        tails = [0] * N
        total = 0
        for j in range(N, 0, -1):
            total += comb(N, j)
            tails[j-1] = total
        result[N] = mp.fsum((-1)**n * f[n] * tails[n] for n in range(N)) / 2**N
    return result


def main():
    out = ROOT / "figures"
    data = ROOT / "data"
    out.mkdir(exist_ok=True)
    data.mkdir(exist_ok=True)
    bstar = mp.findroot(lambda b: mp.diff(axis_constant, b), (mp.mpf("1.2"), mp.mpf("1.4")))
    cstar = axis_constant(bstar)
    bs = [mp.mpf("0.025") + mp.mpf("5.975")*j/239 for j in range(240)]
    axis = [(b, axis_constant(b)) for b in bs]
    records = []
    specifications = [
        (mp.mpf(0), bstar, r"$a=0,\ b=b_*$", "#225d9a"),
        (mp.mpf("0.1"), bstar, r"$a=0.1,\ b=b_*$", "#2d8a74"),
        (mp.mpf(1), mp.mpf(1), r"$a=b=1$", "#ba6b24"),
    ]
    series = []
    for a,b,label,color in specifications:
        indices = list(range(1,33)) + [240]
        values = euler_values(a,b,indices)
        g = -axis_constant(b)/2 if a == 0 else (
            -mp.pi*mp.log(2)/8 if a == b == 1 else values[240])
        scaled = [2**N * (values[N]-g) for N in range(1,33)]
        for N, value in enumerate(scaled,1):
            records.append([mp.nstr(a,35),mp.nstr(b,35),N,mp.nstr(value,50)])
        series.append((scaled,label,color))
    plt.rcParams.update({"font.family":"DejaVu Sans","font.size":9,
                         "axes.spines.top":False,"axes.spines.right":False,
                         "axes.labelsize":10,"legend.fontsize":8,
                         "pdf.fonttype":42,"ps.fonttype":42})
    fig,ax=plt.subplots(1,2,figsize=(7.25,3.45),layout="constrained")
    ax[0].plot([float(b) for b,c in axis],[float(c) for b,c in axis],
               lw=2,color="#225d9a")
    ax[0].axhline(57/50,color="#777777",lw=1,ls=":",label=r"proved budget $57/50$")
    ax[0].scatter([float(bstar)],[float(cstar)],s=24,zorder=4,color="#a43b39")
    ax[0].annotate(r"$C_*\approx1.136561$",xy=(float(bstar),float(cstar)),
                   xytext=(2.2,1.114),fontsize=8,
                   arrowprops={"arrowstyle":"-","color":"#a43b39"})
    ax[0].set(xlabel=r"Inner order $b$",ylabel=r"$C(b)=\beta(b)+2^{-b}\eta(b)$",
              xlim=(0,6),ylim=(0.995,1.146),title="A. Sharp order-dependent constant")
    ax[0].legend(loc="lower right",frameon=False)
    for scaled,label,color in series:
        ax[1].plot(range(1,33),[float(x) for x in scaled],label=label,
                   color=color,lw=1.8,marker="o",markersize=2.2,markevery=3)
    ax[1].axhline(float(cstar),lw=1,ls="--",color="#777777")
    ax[1].text(30,1.154,r"$C_*$",ha="right",fontsize=8,color="#555555")
    ax[1].set(xlabel=r"Truncation index $N$",ylabel=r"$2^N(E_N-g_{a,b})$",
              xlim=(1,32),ylim=(0,1.21),title="B. Fixed-order scaled remainders")
    ax[1].legend(loc="upper right",frameon=False,bbox_to_anchor=(1,0.88))
    for a in ax:
        a.grid(axis="y",alpha=.15)
    fig.savefig(out/"euler_bounds.pdf",bbox_inches="tight")
    fig.savefig(out/"euler_bounds.png",dpi=210,bbox_inches="tight")
    plt.close(fig)
    with (data/"euler_plot_samples.csv").open("w",newline="") as f:
        writer=csv.writer(f);writer.writerow(["a","b","N","scaled_remainder"])
        writer.writerows(records)
    with (data/"euler_axis_samples.csv").open("w",newline="") as f:
        writer=csv.writer(f);writer.writerow(["b","C_b"])
        writer.writerows([[mp.nstr(b,35),mp.nstr(c,50)] for b,c in axis])
    result={"status":"numerical illustration; proofs are in the article",
            "working_digits":mp.mp.dps,"b_star":mp.nstr(bstar,60),
            "C_star":mp.nstr(cstar,60),
            "nonclosed_gaussian_value":"E_240; analytic tail below (5/4)*2^(-240), finite arithmetic not interval-certified",
            "figure_files":["figures/euler_bounds.pdf","figures/euler_bounds.png"]}
    (data/"euler_plot_diagnostics.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))


if __name__ == "__main__":
    main()
