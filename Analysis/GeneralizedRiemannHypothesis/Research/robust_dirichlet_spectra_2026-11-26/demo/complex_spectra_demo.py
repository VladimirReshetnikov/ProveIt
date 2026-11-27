#!/usr/bin/env python3
"""Illustrate robust identification from signed Dirichlet zero ordinates.

This is numerical exploration, not a certified zero enumeration. Sign-change
scanning can miss even-multiplicity zeros and close pairs. The general theorem
is proved separately; neither this program nor its finite output proves GRH.

Characters modulo 5 use generator 2:
    chi(2)=i, chi_bar(2)=-i, chi_squared(2)=-1.
We evaluate L by the finite Hurwitz-zeta expression, normalize its completion
to a real Hardy function, scan for sign changes, and refine each detected root.
The conjugate character's signed spectrum is obtained by reflection and its
roots are also checked by independent evaluation of its own L-function.

The edit distance allows partial matching and charges one per unmatched
occurrence, and min(1, |x-y|) per matched pair. SciPy solves the finite assignment.
Its implementation is independently checked on small exact rational examples.

Dependencies: mpmath, numpy, scipy, matplotlib.
Usage: python3 complex_spectra_demo.py --height 40 --output .
"""
from __future__ import annotations
import argparse
import csv
from fractions import Fraction
from functools import lru_cache
import json
import math
from pathlib import Path
import random
import time

import mpmath as mp
import numpy as np
import scipy
from scipy.optimize import linear_sum_assignment

CHARACTER_NAMES = ["quartic", "conjugate_quartic", "quadratic"]
DISPLAY_NAMES = {
    "quartic": r"$\chi(2)=i$",
    "conjugate_quartic": r"$\bar\chi(2)=-i$",
    "quadratic": r"$\chi^2(2)=-1$",
}


def character_values(name):
    if name == "quartic":
        return [mp.mpc(0), mp.mpc(1), mp.j, -mp.j, mp.mpc(-1)]
    if name == "conjugate_quartic":
        return [mp.mpc(0), mp.mpc(1), -mp.j, mp.j, mp.mpc(-1)]
    if name == "quadratic":
        return [mp.mpc(0), mp.mpc(1), mp.mpc(-1), mp.mpc(-1), mp.mpc(1)]
    raise ValueError(name)


def root_number(name):
    values = character_values(name)
    parity = 0 if name == "quadratic" else 1
    tau = sum(values[a] * mp.exp(2 * mp.pi * mp.j * a / 5) for a in range(1, 5))
    return tau / (mp.j**parity * mp.sqrt(5))


def hurwitz_values(s):
    return [mp.zeta(s, mp.mpf(a)/5) for a in range(1, 5)]


def l_function(s, name, hurwitz=None):
    if hurwitz is None:
        hurwitz = hurwitz_values(s)
    vals = character_values(name)
    return mp.power(5, -s) * sum(vals[a] * hurwitz[a-1] for a in range(1, 5))


def normalized_completion(t, name, l_value=None):
    """The real Hardy function with the positive gamma modulus divided out."""
    parity = 0 if name == "quadratic" else 1
    s = mp.mpf("0.5") + mp.j*t
    if l_value is None:
        l_value = l_function(s, name)
    phase = (
        -mp.arg(root_number(name))/2
        + t*mp.log(5/mp.pi)/2
        + mp.im(mp.loggamma((s+parity)/2))
    )
    return mp.exp(mp.j*phase) * l_value


def hardy(t, name):
    return mp.re(normalized_completion(t, name))


def detect_roots(height, step, scan_dps, refine_dps):
    names = ["quartic", "quadratic"]
    brackets = {name: [] for name in names}
    max_imag = {name: mp.mpf(0) for name in names}
    with mp.workdps(scan_dps):
        count = int(mp.ceil(2*height/step))
        grid = [mp.mpf(-height) + (2*mp.mpf(height))*j/count for j in range(count+1)]
        previous = {}
        for j,t in enumerate(grid):
            s = mp.mpf("0.5") + mp.j*t
            hz = hurwitz_values(s)
            for name in names:
                z = normalized_completion(t,name,l_function(s,name,hz))
                value = mp.re(z)
                max_imag[name] = max(max_imag[name], abs(mp.im(z)))
                if j and previous[name]*value < 0:
                    brackets[name].append((str(grid[j-1]), str(t)))
                elif value == 0:
                    raise RuntimeError("A scan point is exactly zero; refine the scan convention.")
                previous[name] = value
            if j and j % 160 == 0:
                print(f"Scanned {j}/{count} common Hurwitz-zeta grid points", flush=True)
    roots = {}
    diagnostics = {}
    with mp.workdps(refine_dps):
        for name in names:
            roots[name] = []
            residuals = []
            for left,right in brackets[name]:
                a,b = mp.mpf(left),mp.mpf(right)
                root = mp.findroot(lambda t: hardy(t,name), (a,b),
                                   tol=mp.mpf(10)**(-refine_dps+12),
                                   maxsteps=35, verify=True)
                if not a < root < b:
                    raise AssertionError((name, "refined root outside scan bracket"))
                residual = abs(l_function(mp.mpf("0.5")+mp.j*root,name))
                if residual >= mp.mpf(10)**(-refine_dps+20):
                    raise AssertionError((name, "L residual too large", str(residual)))
                roots[name].append(+root)
                residuals.append(residual)
            diagnostics[name] = {
                "detected_occurrences": len(roots[name]),
                "largest_absolute_L_residual": mp.nstr(max(residuals),12),
                "max_scan_imaginary_Hardy_residual": mp.nstr(max_imag[name],12),
                "brackets": brackets[name],
            }
            print(f"Refined {len(roots[name])} detected {name} ordinates",flush=True)
        roots["conjugate_quartic"] = [-x for x in reversed(roots["quartic"])]
        residuals = [abs(l_function(mp.mpf("0.5")+mp.j*t,"conjugate_quartic"))
                     for t in roots["conjugate_quartic"]]
        diagnostics["conjugate_quartic"] = {
            "detected_occurrences": len(roots["conjugate_quartic"]),
            "largest_absolute_L_residual": mp.nstr(max(residuals),12),
            "method": "Reflection of quartic list, followed by direct conjugate L evaluations.",
        }
        for name in roots:
            diagnostics[name]["negative_detected"] = sum(t<0 for t in roots[name])
            diagnostics[name]["positive_detected"] = sum(t>0 for t in roots[name])
        return roots,diagnostics


def edit_distance(x,y,return_matching=False):
    x,y = np.asarray(x,dtype=float),np.asarray(y,dtype=float)
    m,n = len(x),len(y)
    if not m+n:
        return (0.0,[],[],[]) if return_matching else 0.0
    costs = np.zeros((m+n,m+n),dtype=float)
    costs[:m,:n] = np.minimum(1.0,np.abs(x[:,None]-y[None,:]))
    costs[:m,n:] = 1.0
    costs[m:,:n] = 1.0
    rows,cols = linear_sum_assignment(costs)
    value = float(costs[rows,cols].sum())
    if not return_matching:
        return value
    matched = [(int(i),int(j)) for i,j in zip(rows,cols) if i<m and j<n]
    removed = [int(i) for i,j in zip(rows,cols) if i<m and j>=n]
    added = [int(j) for i,j in zip(rows,cols) if i>=m and j<n]
    return value,matched,removed,added


def exact_partial_matching_cost(x,y):
    """Independent exhaustive rational minimization; no assignment solver."""
    m,n = len(x),len(y)
    @lru_cache(None)
    def rec(i,mask):
        if i==m:
            return Fraction(n-mask.bit_count())
        best = Fraction(1) + rec(i+1,mask)
        for j in range(n):
            if not (mask>>j)&1:
                value = min(Fraction(1),abs(x[i]-y[j])) + rec(i+1,mask|(1<<j))
                best = min(best,value)
        return best
    return rec(0,0)


def check_edit_distance():
    rng = random.Random(20261126)
    cases=0
    for m in range(5):
        for n in range(5):
            for _ in range(8):
                x=[Fraction(rng.randrange(-8,9),4) for _ in range(m)]
                y=[Fraction(rng.randrange(-8,9),4) for _ in range(n)]
                exact=exact_partial_matching_cost(x,y)
                numeric=edit_distance(x,y)
                assert abs(numeric-float(exact))<1e-12,(x,y,exact,numeric)
                cases+=1
    return {"exact_rational_cases":cases,"status":"passed"}


def make_corruption(roots,height):
    base = [float(t) for t in roots]
    removed = sorted({len(base)//3,2*len(base)//3})
    records=[]
    jitter_total=0.0
    for j,t in enumerate(base):
        if j in removed:
            continue
        jitter=0.012*math.sin(1.7*j+0.3)
        jitter_total+=abs(jitter)
        records.append({"value":t+jitter,"source_index":j,"kind":"jittered",
                        "displacement":jitter})
    for t in [-height+2.25,3.125,height-1.25]:
        records.append({"value":t,"source_index":None,"kind":"inserted","displacement":None})
    records.sort(key=lambda z:z["value"])
    return {
        "deleted_source_indices":removed,
        "deleted_ordinates":[base[j] for j in removed],
        "inserted_ordinates":[z["value"] for z in records if z["kind"]=="inserted"],
        "max_individual_jitter":max(abs(z["displacement"]) for z in records if z["kind"]=="jittered"),
        "sum_absolute_jitter":jitter_total,
        "construction_cost_upper_bound":len(removed)+3+jitter_total,
        "records":records,
    }


def make_plot(output,roots,corruption,costs,height):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    plt.rcParams.update({"font.family":"DejaVu Sans","font.size":10,
                         "axes.spines.top":False,"axes.spines.right":False,
                         "axes.labelcolor":"#18394b","text.color":"#18394b"})
    fig,axs=plt.subplots(3,1,figsize=(10,8.2),
                         gridspec_kw={"height_ratios":[1.3,1.05,1.1]})
    colors={"quartic":"#176f8a","conjugate_quartic":"#9b5c39","quadratic":"#727784"}
    for row,name in enumerate(CHARACTER_NAMES):
        y=2-row
        values=[float(t) for t in roots[name]]
        axs[0].vlines(values,y-.17,y+.17,color=colors[name],lw=1.5)
    axs[0].set(yticks=[2,1,0],yticklabels=[DISPLAY_NAMES[n] for n in CHARACTER_NAMES],
               xlim=(-height,height),ylim=(-.4,2.4),xlabel="Signed ordinate")
    axs[0].axvline(0,color="#c2c7cc",lw=.7)
    axs[0].set_title("Three primitive characters, all of conductor 5",loc="left",fontweight="bold")
    axs[0].grid(axis="x",alpha=.14)
    original=[float(t) for t in roots["quartic"]]
    axs[1].scatter(original,[0]*len(original),s=15,color=colors["quartic"],label="Original")
    observed=[z["value"] for z in corruption["records"]]
    ordinary=[z for z in corruption["records"] if z["kind"]=="jittered"]
    inserted=corruption["inserted_ordinates"]
    axs[1].scatter([z["value"] for z in ordinary],[1]*len(ordinary),s=15,color=colors["quartic"])
    for z in ordinary:
        axs[1].plot([original[z["source_index"]],z["value"]],[0,1],color="#a5c7d0",lw=.55,zorder=-1)
    axs[1].scatter(corruption["deleted_ordinates"],[0]*len(corruption["deleted_ordinates"]),
                   marker="x",s=65,lw=1.7,color="#b34839",label="Deleted")
    axs[1].scatter(inserted,[1]*len(inserted),marker="D",s=30,color="#b34839",label="Inserted")
    axs[1].set(xlim=(-height,height),ylim=(-.65,1.4),yticks=[0,1],
               yticklabels=["Original","Observed"],xlabel="Signed ordinate")
    axs[1].set_title("Damaged observation: 2 deleted, 3 inserted, remaining ordinates jittered",loc="left",fontsize=10)
    axs[1].legend(loc="lower right",ncol=3,fontsize=8,frameon=False)
    vals=[costs[n] for n in CHARACTER_NAMES]
    bars=axs[2].barh(range(3),vals,color=[colors[n] for n in CHARACTER_NAMES],height=.53)
    axs[2].set_yticks(range(3),[DISPLAY_NAMES[n] for n in CHARACTER_NAMES])
    axs[2].invert_yaxis()
    axs[2].set_xlabel("Clipped edit distance from the damaged observation")
    axs[2].set_title("The generating character remains the nearest candidate",loc="left",fontweight="bold")
    xmax=max(vals)
    axs[2].set_xlim(0,xmax*1.16)
    for bar,value in zip(bars,vals):
        axs[2].text(value+xmax*.018,bar.get_y()+bar.get_height()/2,f"{value:.3f}",va="center",fontsize=10)
    fig.suptitle("Recovering an oriented complex character from a noisy zero list",
                 fontsize=14,fontweight="bold",x=.08,ha="left",y=.985)
    fig.text(.08,.013,"Numerical exploration only. Sign-change scans do not certify completeness or multiplicity.",
             fontsize=8,color="#6d5350")
    fig.tight_layout(rect=(.02,.035,.99,.96),h_pad=1.7)
    for suffix in ["pdf","png"]:
        fig.savefig(output/f"complex_zero_lists.{suffix}",dpi=170,bbox_inches="tight")
    plt.close(fig)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--height",type=int,default=40)
    ap.add_argument("--scan-step",type=float,default=0.125)
    ap.add_argument("--scan-dps",type=int,default=28)
    ap.add_argument("--refine-dps",type=int,default=60)
    ap.add_argument("--output",type=Path,default=Path("."))
    ap.add_argument("--reuse-roots",action="store_true",
                    help="Read the saved numerical root strings instead of rescanning.")
    args=ap.parse_args()
    if args.height < 10:
        ap.error("The fixed illustrative corruption requires --height >= 10.")
    if args.scan_step <= 0 or args.scan_dps < 20 or args.refine_dps < 40:
        ap.error("Require a positive scan step, >=20 scan digits, and >=40 refinement digits.")
    output=args.output.resolve();output.mkdir(parents=True,exist_ok=True)
    started=time.time()
    mp.mp.dps=args.refine_dps
    metric_check=check_edit_distance()
    if args.reuse_roots:
        stored=json.loads((output/"zero_lists.json").read_text())
        if stored["height"] != args.height:
            raise ValueError("Saved root height does not match requested height.")
        roots={name:[mp.mpf(t) for t in ts] for name,ts in stored["ordinates"].items()}
        diagnostics=stored["diagnostics"]
    else:
        roots,diagnostics=detect_roots(args.height,args.scan_step,args.scan_dps,args.refine_dps)
    zero_data={
        "status":"numerical_exploration_not_certified",
        "caveat":"Sign changes can miss even-multiplicity zeros or multiple roots in one scan interval.",
        "conductor":5,
        "height":args.height,
        "scan_step_maximum":args.scan_step,
        "scan_decimal_digits":args.scan_dps,
        "refinement_decimal_digits":args.refine_dps,
        "character_values":["chi(1)=1","chi(2)=i","chi(3)=-i","chi(4)=-1"],
        "root_number_quartic":{"real":mp.nstr(mp.re(root_number("quartic")),50),
                               "imag":mp.nstr(mp.im(root_number("quartic")),50)},
        "ordinates":{name:[mp.nstr(t,52) for t in ts] for name,ts in roots.items()},
        "diagnostics":diagnostics,
    }
    (output/"zero_lists.json").write_text(json.dumps(zero_data,indent=2)+"\n")
    with (output/"zero_ordinates.csv").open("w",newline="") as f:
        writer=csv.writer(f);writer.writerow(["character","detected_index","signed_ordinate"])
        for name in CHARACTER_NAMES:
            for j,t in enumerate(roots[name]):
                writer.writerow([name,j,mp.nstr(t,52)])
    pair_costs={a:{b:edit_distance(roots[a],roots[b]) for b in CHARACTER_NAMES}
                for a in CHARACTER_NAMES}
    corruption=make_corruption(roots["quartic"],args.height)
    observed=[z["value"] for z in corruption["records"]]
    costs={name:edit_distance(observed,roots[name]) for name in CHARACTER_NAMES}
    winner=min(costs,key=costs.get)
    assert winner=="quartic",costs
    assert costs[winner] <= corruption["construction_cost_upper_bound"]+1e-9
    summary={
        "status":"numerical_exploration_not_certified",
        "metric":"unmatched occurrences plus sum min(1, absolute matched displacement)",
        "assignment_check":metric_check,
        "pairwise_clean_distances":pair_costs,
        "damaged_observation_distances":costs,
        "nearest_candidate":winner,
        "strict_distance_margin":min(v for k,v in costs.items() if k!=winner)-costs[winner],
        "corruption":corruption,
        "elapsed_seconds":round(time.time()-started,3),
        "packages":{"mpmath":mp.__version__,"numpy":np.__version__,"scipy":scipy.__version__},
    }
    (output/"demo_results.json").write_text(json.dumps(summary,indent=2)+"\n")
    with (output/"corrupted_observation.csv").open("w",newline="") as f:
        writer=csv.DictWriter(f,fieldnames=["value","source_index","kind","displacement"])
        writer.writeheader();writer.writerows(corruption["records"])
    make_plot(output,roots,corruption,costs,args.height)
    print(json.dumps({k:summary[k] for k in ["assignment_check","pairwise_clean_distances",
          "damaged_observation_distances","nearest_candidate","strict_distance_margin","elapsed_seconds"]},
          indent=2))


if __name__=="__main__":
    main()

