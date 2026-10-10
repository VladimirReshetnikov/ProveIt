"""Verify the log-gamma moment coefficient and sharp remainder formulas.

All numerical checks use mpmath floating-point arithmetic.  They corroborate
the analytic proofs in the article and are not interval-arithmetic proofs.
Direct quadrature runs to infinity: an inadequately short cutoff can overwhelm
the very small optimal remainder, even if the moment itself looks accurate.

Run: python scripts/verify_moments.py --dps 180 --output data/moment_checks.json
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import time

import mpmath as mp
import sympy as sp


def constants():
    tau = mp.findroot(lambda t: mp.digamma(-t), (mp.mpf(".4"), mp.mpf(".6")))
    rho = tau/mp.gamma(1-tau)
    lam = -mp.log(rho)
    P, Q, R = [mp.polygamma(j, -tau) for j in (1, 2, 3)]
    C = 1/mp.sqrt(2*mp.pi*P)
    d1 = R/(8*P**2)-5*Q**2/(24*P**3)
    return tau, rho, lam, C, d1


def coefficients(max_k):
    """Lagrange coefficient recurrence: no numerical inverse is used."""
    q = [mp.mpf(0), mp.euler] + [mp.zeta(j) for j in range(2, max_k)]
    b = [mp.mpf(0)]
    for k in range(1, max_k+1):
        a = [mp.mpf(1)]
        for j in range(1, k):
            a.append(k*mp.fsum(q[l]*a[j-l] for l in range(1, j+1))/j)
        b.append(a[-1]/k)
    return b


def moment(n):
    """m_n = M_n/n!; substitution x=exp(-t), integrated to infinity."""
    lf = mp.loggamma(n+1)
    def f(t):
        if not t:
            return mp.mpf(0)
        v = mp.loggamma(mp.exp(-t))
        return mp.exp(n*mp.log(v)-t-lf) if v else mp.mpf(0)
    breaks = sorted(set([mp.mpf(0), mp.mpf(".25"), mp.mpf(1), mp.mpf(3),
                          mp.mpf(n)/2, mp.mpf(n), mp.mpf(2*n), mp.mpf(4*n)]))
    return mp.quad(f, breaks+[mp.inf])


def exact_coefficients(max_k=8):
    gamma = sp.Symbol("gamma")
    zz = {1: gamma, **{j: sp.Symbol(f"zeta{j}") for j in range(2, max_k)}}
    z = sp.Symbol("z")
    out = []
    for k in range(1, max_k+1):
        a = [sp.Integer(1)]
        for j in range(1, k):
            a.append(sp.expand(sp.Rational(k, j)*sum(zz[l]*a[j-l] for l in range(1,j+1))))
        value = sp.expand(a[-1]/k)
        # Independent formal exponential expansion of the Lagrange formula.
        exponent = k*sum(zz[l]*z**l/sp.Integer(l) for l in range(1,k))
        direct = sp.expand(sp.series(sp.exp(exponent), z, 0, k).removeO()).coeff(z,k-1)/k
        assert sp.expand(value-direct) == 0
        out.append({"k": k, "formula": str(value), "latex": sp.latex(value)})
    return out


def run(dps, orders, repeat):
    mp.mp.dps = dps
    tau, rho, lam, C, d1 = constants()
    truncations = [int(mp.nint((n+mp.mpf("1.5"))/lam)) for n in orders]
    max_k = max(160, max(truncations))
    b = coefficients(max_k)
    fmt = lambda x, d=70: mp.nstr(x, d)
    out = {"working_digits": dps,
           "status": "floating-point corroboration with separate exact polynomial checks",
           "constants": {k:fmt(v) for k,v in zip(["tau","rho","Lambda","C","d1"],
                                                [tau,rho,lam,C,d1])},
           "exact_coefficients": exact_coefficients(),
           "coefficient_asymptotics": []}
    for k in [10,20,40,80,160]:
        rat = b[k]/(C*rho**(-k)*mp.mpf(k)**mp.mpf("-1.5"))
        out["coefficient_asymptotics"].append({
            "k":k, "ratio":fmt(rat), "k_times_ratio_minus_one":fmt(k*(rat-1)),
            "scaled_after_d1":fmt(k*k*(rat-1-d1/k))})
    checks=[]
    for n, N in zip(orders, truncations):
        eta = N*lam-n
        val = moment(n)
        partial = mp.fsum((-1)**(k-1)*b[k]/mp.mpf(k)**n for k in range(1,N))
        omitted = (-1)**(N-1)*b[N]/mp.mpf(N)**n
        ratio = (val-partial)/omitted
        first = mp.mpf(".5")+(3-2*eta)/(8*N)
        c2 = d1/4 + lam*(6*eta-13)/96
        second = first+c2/N**2
        row={"n":n,"N":N,"eta":fmt(eta),"normalized_moment":fmt(val,dps-15),
             "first_omitted_term":fmt(omitted), "error_over_first_omitted":fmt(ratio),
             "first_correction":fmt(first),"second_correction":fmt(second),
             "N2_after_first":fmt(N*N*(ratio-first)),
             "N3_after_second":fmt(N**3*(ratio-second))}
        if n in repeat:
            with mp.workdps(dps+35):
                _, _, lam2, _, _ = constants()
                bb=coefficients(N)
                vv=moment(n)
                pp=mp.fsum((-1)**(k-1)*bb[k]/mp.mpf(k)**n for k in range(1,N))
                oo=(-1)**(N-1)*bb[N]/mp.mpf(N)**n
                ratio2=(vv-pp)/oo
                diff=abs(ratio-ratio2)
                assert diff < mp.mpf("1e-35"), (n,diff)
                row["precision_repeat_digits"]=dps+35
                row["ratio_repeat_difference"]=fmt(diff)
        assert abs(ratio-mp.mpf(".5")) < mp.mpf(".02")
        checks.append(row)
        print(json.dumps({"n":n,"N":N,"ratio":fmt(ratio,20),
                          "N3_after_second":fmt(N**3*(ratio-second),12)}), flush=True)
    out["moment_remainders"]=checks
    return out


if __name__ == "__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--dps",type=int,default=180)
    parser.add_argument("--orders",type=int,nargs="+",default=[10,20,30,40,60,80])
    parser.add_argument("--repeat",type=int,nargs="*",default=[20,80])
    parser.add_argument("--output",type=Path,default=Path("data/moment_checks.json"))
    args=parser.parse_args()
    start=time.monotonic()
    report=run(args.dps,args.orders,args.repeat)
    report["runtime_seconds"]=round(time.monotonic()-start,3)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({"output":str(args.output),"orders":len(args.orders),
                      "seconds":report["runtime_seconds"]}),flush=True)

