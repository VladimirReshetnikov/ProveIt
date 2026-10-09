"""Reproduce all tables, figures, exact certificates, and numerical audits.

Run from any directory: python code/reproduce.py
No network, random simulation, or external data is needed.  The randomized
spectral audit uses a fixed seed; it checks formulas rather than sampling Q.
"""

from __future__ import annotations

import csv
from fractions import Fraction
import json
import math
from pathlib import Path
import platform

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np
import scipy
from scipy.optimize import brentq, minimize_scalar
import sympy as sp

from spectral_concentration import (
    deficit_coefficient, exact_cgf, kernel, phi, radau_cgf, radau_constant, radau_nodes,
    radau_rate, radau_saddle, sharp_constant, signed_cgf, signed_rate,
    signed_saddle, spectral_moments,
)

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data"
FIGURES = ROOT / "figures"
DATA.mkdir(exist_ok=True)
FIGURES.mkdir(exist_ok=True)


def write_csv(name, rows):
    with (DATA / name).open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def exact_radau_example(k):
    """Exact probability for +1 (2k copies), -1/2 (16k copies), t=6k."""
    n = 9 * k - 1
    numerator = sum(math.comb(n, j) * 2 ** (n - j) for j in range(k))
    return Fraction(numerator, 3 ** n)


def log_fraction(value):
    return math.log(value.numerator) - math.log(value.denominator)


def exact_spectral_rate(values, u):
    """Independent root solve of the full spectral log-MGF derivative."""
    x = np.asarray(values, dtype=float)
    x = x / np.max(np.abs(x))
    r = float(x @ x)
    target = r * u
    positive = x[x > 0]
    if len(positive):
        high = (1.0 - 1e-12) / np.max(positive)
    else:
        if target >= -float(x.sum()):
            return math.inf
        high = 1.0
        while float(np.sum(high * x * x / (1.0 - high * x))) < target:
            high *= 2.0
    z = brentq(lambda zz: float(np.sum(zz * x * x / (1.0 - zz * x))) - target,
               0.0, high, xtol=1e-13)
    return z * target / 2.0 - math.fsum(phi(z * a) for a in x)


def symbolic_audit():
    z, s, u, a, w, x, h = sp.symbols("z s u a w x h", real=True)
    H = -((1+s)*sp.log(1-z)+(1-s)*sp.log(1+z))/4-s*z/2
    target = z*(1+s*z)/(2*(1-z*z))
    assert sp.simplify(sp.diff(H,z)-target) == 0
    expected = -z*z*(s*(1+z*z)+2*z)/(2*(1-z*z)**2)
    assert sp.simplify(sp.diff(2*H-z*sp.diff(H,z),z)-expected) == 0
    chord = (1+x)/(2*(1-h))+(1-x)/(2*(1+h))
    assert sp.factor(chord-1/(1-h*x)-h*h*(1-x*x)/((1-h*h)*(1-h*x))) == 0
    D = -z/2-sp.log(1-z)/8+5*sp.log(1+z)/8+1/(4*(1+z))-sp.Rational(1,4)
    assert sp.simplify(sp.diff(D,z)-z**3/(2*(1-z)*(1+z)**2)) == 0
    residual = sp.expand(u*(1-z*a)*(1-z)-z*((1-w)*(1-z)+w*(1-z*a)))
    expected = u-z*(1+u*(1+a))+z*z*(u*a+1-w+w*a)
    assert sp.simplify(residual-expected) == 0
    return 5


def numerical_audit():
    rng = np.random.default_rng(20261008)
    families = [[1.0], [-1.0], [1.0, -1.0], [1.0] + [-0.5]*8,
                [1.0] + [0.01]*99, [-1.0, -0.2, -0.01], [1.0, 0.0, -1.0]]
    for _ in range(180):
        n = int(rng.integers(2, 120))
        vals = rng.uniform(-1, 1, n) * np.exp(rng.uniform(-5, 0, n))
        families.append((vals/np.max(np.abs(vals))).tolist())
    cgf_checks = rate_checks = 0
    smallest_cgf_gap = math.inf
    smallest_rate_gap = math.inf
    max_two_level_error = 0.0
    for vals in families:
        m = spectral_moments(vals)
        ss = max(-1.0, min(1.0, m.s))
        kk = max(ss*ss, min(1.0, m.k))
        for z in [1e-5, .01, .1, .3, .6, .85, .97]:
            exact = exact_cgf(vals, z/(2*m.L))/m.r
            fourth = radau_cgf(ss, kk, z)
            third = signed_cgf(ss, z)
            baseline = signed_cgf(1.0, z)
            gap = min(fourth-exact, third-fourth, baseline-third)
            assert gap >= -3e-11, (vals, z, gap)
            if ss != -1.0:
                assert third-exact >= (1-kk)*deficit_coefficient(z)-3e-11
            smallest_cgf_gap = min(smallest_cgf_gap, gap)
            cgf_checks += 1
        for u in [.01, .1, .5, 1, 2, 5]:
            fourth = m.r*radau_rate(ss,kk,u)
            exact = exact_spectral_rate(vals,u)
            third = m.r*signed_rate(ss,u)
            baseline = m.r*signed_rate(1.0,u)
            assert fourth >= third - 1e-9
            assert third >= baseline - 1e-9
            assert fourth <= exact + 2e-8, (u, fourth, exact)
            if math.isfinite(exact):
                smallest_rate_gap = min(smallest_rate_gap, exact-fourth)
            rate_checks += 1
    for a in [-.9,-.5,-.05,.0,.2,.8]:
        vals = [1.0]*3+[a]*17
        m = spectral_moments(vals)
        for u in [.02,.4,1.,3.]:
            gap = abs(m.r*radau_rate(m.s,m.k,u)-exact_spectral_rate(vals,u))
            max_two_level_error = max(max_two_level_error,gap)
            assert gap < 2e-10
    # Independent generic scalar optimization of the analytic Radau saddle.
    saddle_checks = 0
    for ss in [-.9,-.5,0,.4,.8]:
        for fraction in [.1,.5,.9]:
            kk = ss*ss+(1-ss*ss)*fraction
            for u in [.1,1.,10.]:
                opt = minimize_scalar(lambda z:radau_cgf(ss,kk,z)-u*z/2,
                                      bounds=(0,1-1e-10),method="bounded",
                                      options={"xatol":1e-13})
                assert abs(-opt.fun-radau_rate(ss,kk,u)) < 1e-9
                saddle_checks += 1
    # High precision independent integral representation of the kernel/defect.
    mp.mp.dps = 70
    integral_checks = 0
    for zz in ["0.000001","0.1","0.7","0.99"]:
        z=mp.mpf(zz)
        d=mp.quad(lambda y:y**3/(2*(1-y)*(1+y)**2),[0,z])
        assert abs(float(d)-deficit_coefficient(float(z))) < 2e-15
        for xx in ["-1","-0.37","0","0.41","1"]:
            x=mp.mpf(xx)
            g=z*z/2*mp.quad(lambda t:t/(1-z*t*x),[0,1])
            assert abs(float(g)-kernel(float(z),float(x))) < 3e-14
            integral_checks += 1
    return {"spectra":len(families),"cgf_hierarchy_checks":cgf_checks,
            "tail_exponent_hierarchy_checks":rate_checks,
            "independent_optimizer_checks":saddle_checks,
            "high_precision_kernel_integrals":integral_checks,
            "smallest_cgf_gap_float":smallest_cgf_gap,
            "smallest_exact_vs_radau_rate_gap_float":smallest_rate_gap,
            "largest_two_level_rate_error":max_two_level_error}


def outputs():
    boundary=brentq(lambda s:signed_rate(s,1)-.25,-.99,0,xtol=1e-14)
    rows=[{"s":s,"c_s":sharp_constant(s),"J_s_1":signed_rate(s,1)}
          for s in [-1,-.9,-.8,boundary,-.7,-.5,0,.5,1]]
    write_csv("sharp_constants.csv",rows)
    J4=4*math.log(4/3)/3-math.log(3)/6
    cert_rows=[]
    certificate={"event":"chi_square(2k) >= 0.5 chi_square(16k)",
                 "method":"exact integer beta-binomial identity","certificates":[]}
    for k in [1,2,5,10,20,50,100,200,500]:
        probability=exact_radau_example(k)
        logp=log_fraction(probability)
        prefactor=math.exp(logp+6*k*J4)*3*math.sqrt(math.pi*k)
        cert_rows.append({"k":k,"dimension":18*k,"v":6*k,
                          "log_exact_probability":logp,"rate_per_v":-logp/(6*k),
                          "norm_exponent":6*k*sharp_constant(1),
                          "cubic_exponent":6*k*sharp_constant(0),
                          "radau_exponent":6*k*J4,
                          "asymptotic_prefactor_ratio":prefactor})
        certificate["certificates"].append({"k":k,"numerator":str(probability.numerator),
                                             "denominator":str(probability.denominator)})
        assert logp <= -6*k*J4+1e-11
    write_csv("exact_tail_comparison.csv",cert_rows)
    (DATA/"exact_rational_certificates.json").write_text(json.dumps(certificate,indent=2)+"\n")
    hetero=[1.0,-.8,-.4,.2,.1,.05]*20
    ex=spectral_moments(hetero)
    comparison=[]
    for u in [.1,.25,.5,1.,2.,4.]:
        comparison.append({"u":u,"r":ex.r,"s":ex.s,"k":ex.k,
            "norm_rate":ex.r*signed_rate(1,u),
            "signed_rate":ex.r*signed_rate(ex.s,u),
            "radau_rate":ex.r*radau_rate(ex.s,ex.k,u),
            "full_spectrum_rate":exact_spectral_rate(hetero,u)})
    write_csv("heterogeneous_spectrum_comparison.csv",comparison)
    plt.rcParams.update({"font.family":"DejaVu Sans","font.size":10,
                         "axes.spines.top":False,"axes.spines.right":False,
                         "figure.dpi":160,"savefig.bbox":"tight"})
    ss=np.linspace(-1,1,1201)
    fig,ax=plt.subplots(figsize=(7.4,3.8))
    ax.plot(ss,[sharp_constant(float(s)) for s in ss],color="#126782",lw=2.6,
            label="Optimal coefficient c(s)")
    ax.axhline(sharp_constant(1),color="#9b6a42",ls="--",label="Unrestricted coefficient")
    ax.axvline(boundary,color="#777777",ls=":",lw=1)
    ax.scatter([0],[sharp_constant(0)],color="#ca5c42",zorder=3)
    ax.annotate(f"Transition s = {boundary:.6f}",xy=(boundary,.25),xytext=(-.48,.259),
                arrowprops={"arrowstyle":"-","color":"#777777"},fontsize=9)
    ax.annotate("Zero cubic moment: 0.188714",xy=(0,sharp_constant(0)),xytext=(.1,.22),
                arrowprops={"arrowstyle":"-","color":"#777777"},fontsize=9)
    ax.set(xlabel="Cubic spectral balance s",ylabel="Best constant",ylim=(.14,.27),xlim=(-1,1))
    ax.legend(loc="lower left",frameon=False,fontsize=9)
    fig.savefig(FIGURES/"sharp_constant_frontier.pdf")
    fig.savefig(FIGURES/"sharp_constant_frontier.png")
    plt.close(fig)
    us=np.geomspace(.03,8,350)
    fig,axes=plt.subplots(1,2,figsize=(9.0,3.7))
    styles=[("Norm only",lambda u:signed_rate(1,u),"#888888"),
            ("Cubic moment",lambda u:signed_rate(0,u),"#126782"),
            ("Fourth moment (exact CGF)",lambda u:radau_rate(0,.5,u),"#ca5c42")]
    for label,fn,color in styles:
        axes[0].plot(us,[fn(float(u))/min(u*u,u) for u in us],label=label,color=color,lw=2)
    axes[0].set(xscale="log",xlabel="Normalized deviation u",ylabel="Rate / min(u², u)")
    axes[0].legend(frameon=False,fontsize=8)
    ks=[r["k"] for r in cert_rows]
    axes[1].plot(ks,[r["rate_per_v"] for r in cert_rows],"o-",color="#263d53",label="Exact rational tail")
    axes[1].axhline(J4,color="#ca5c42",ls="--",label="Fourth-moment rate")
    axes[1].axhline(sharp_constant(0),color="#126782",ls=":",label="Cubic-moment rate")
    axes[1].axhline(sharp_constant(1),color="#888888",ls=":",label="Norm-only rate")
    axes[1].set(xscale="log",xlabel=r"Replication parameter $\ell$",ylabel="Negative log probability / v")
    axes[1].legend(frameon=False,fontsize=8)
    fig.tight_layout()
    fig.savefig(FIGURES/"rate_and_exact_tail.pdf")
    fig.savefig(FIGURES/"rate_and_exact_tail.png")
    plt.close(fig)
    return {"transition_s":boundary,"c_zero":sharp_constant(0),
            "c_one":sharp_constant(1),"example_fourth_rate":J4,
            "balanced_exponent_gain_percent":100*(sharp_constant(0)/sharp_constant(1)-1),
            "balanced_sufficient_probe_reduction_percent":100*(1-sharp_constant(1)/sharp_constant(0)),
            "exact_rational_certificates":len(cert_rows)}


def boundary_regressions():
    cases = 0
    for u in [1e16,1e100,1e308]:
        for s,k in [(0.,1.),(0.,.5),(-.5,.8),(.5,.8)]:
            for value in [signed_rate(s,u),radau_rate(s,k,u)]:
                assert math.isfinite(value) and value > 0
                cases += 1
    for thunk in [lambda:signed_rate(2,0),lambda:signed_rate(1,-1),
                  lambda:radau_rate(1,.5,1),lambda:radau_rate(0,-.2,1),
                  lambda:spectral_moments([]),lambda:sharp_constant(float('nan'))]:
        try:
            thunk()
        except ValueError:
            cases += 1
        else:
            raise AssertionError("Invalid data was accepted")
    assert signed_rate(-1,1) == math.inf
    assert radau_rate(-.5,.25,2) == math.inf
    assert radau_rate(0,0,2) == 1.0
    assert abs(radau_constant(0,.5)-(4*math.log(4/3)/3-math.log(3)/6)) < 1e-14
    return cases+4


if __name__ == "__main__":
    results={"symbolic_identities":symbolic_audit(),"numerical_audit":numerical_audit(),
             "boundary_regressions":boundary_regressions(),
             "results":outputs(),"python":platform.python_version(),
             "numpy":np.__version__,"scipy":scipy.__version__,
             "matplotlib":matplotlib.__version__,"sympy":sp.__version__,
             "mpmath":mp.__version__,"validation_kind":"symbolic and numerical; not formal verification"}
    (DATA/"verification_summary.json").write_text(json.dumps(results,indent=2)+"\n")
    print(json.dumps(results,indent=2))
