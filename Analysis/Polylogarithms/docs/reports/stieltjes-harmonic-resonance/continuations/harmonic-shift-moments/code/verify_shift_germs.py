#!/usr/bin/env python3
"""Independent diagnostics for the harmonic shift-germ section.

Analytic proofs are in sections/02_shift_germs.tex.  Exact checks use
rational symbolic arithmetic. Numerical checks are floating-point audits,
not interval certificates: their two truncations are recorded explicitly.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import time

import mpmath as mp
import sympy as sp
from sympy.functions.combinatorial.numbers import stirling


def exact_checks():
    a, z, u, E = sp.symbols("a z u E")
    checks = []
    for N in range(7):
        CN = sp.prod(1 + u / (z-j) for j in range(1, N+1))
        PN1 = sp.prod(1 + u / (z-N+j) for j in range(N+1))
        residual = sp.cancel(z*PN1 - (z+u)*CN)
        checks.append({"name": "local-factor", "N": N,
                       "passed": residual == 0})
        residue = sp.cancel(z*PN1).subs(z, 0)
        expected = u*sp.prod(1-u/sp.Integer(j) for j in range(1, N+1))
        checks.append({"name": "tail-residue", "N": N,
                       "passed": sp.expand(residue-expected) == 0})
    for m in range(6):
        def D(r):
            return sp.expand(sum(stirling(m+1, j, kind=2)
                         * sp.ff(a-1, j)*(-sp.Rational(1, j))**(r+1)
                         for j in range(1, m+2)))
        Q = sp.Poly(sp.prod(E+sp.Rational(1, j)
                          for j in range(1, m+2)), E)
        for r in range(5):
            residual = sp.expand(sum(Q.nth(j)*D(r+j)
                                    for j in range(m+2)))
            checks.append({"name": "depth-recurrence", "m": m,
                           "r": r, "passed": residual == 0})
        M = sp.Matrix([[(-sp.Rational(1, j))**(r+1)
                        for j in range(1, m+2)] for r in range(m+1)])
        det = sp.factor(M.det())
        checks.append({"name": "depth-rank", "m": m,
                       "determinant": str(det), "passed": det != 0})
    for r in range(1, 6):
        cr = sp.prod(1/(z-j) for j in range(1, r+1))
        series = sp.series(cr, z, 0, 7).removeO().expand()
        h = [sp.Integer(1)]
        for n in range(1, 7):
            h.append(sp.simplify(sum(
                sum(sp.Rational(1, j)**q for j in range(1, r+1))
                * h[n-q] for q in range(1, n+1))/n))
        for p in range(7):
            residual = sp.simplify(series.coeff(z,p)
                              -(-1)**r*h[p]/sp.factorial(r))
            checks.append({"name": "coordinate-finite-part", "r": r,
                           "p": p, "passed": residual == 0})
    return checks


def K_coefficients(a, rmax):
    """Taylor coefficients from logarithmic Gamma derivatives, K(0)=1."""
    logs = [mp.mpf(0)] + [
        (mp.polygamma(j-1, 1)-mp.polygamma(j-1, a))/mp.factorial(j)
        for j in range(1, rmax+1)]
    coeff = [mp.mpf(1)]
    for n in range(1, rmax+1):
        coeff.append(sum(j*logs[j]*coeff[n-j]
                         for j in range(1,n+1))/n)
    return coeff


def direct_M_jets(s, a, rmax, kmax, terms):
    """Ordinary convergent sums, using harmonic elementary coefficients."""
    sums = [[mp.mpc(0) for _ in range(kmax+1)] for _ in range(rmax+1)]
    elem = [mp.mpf(1)] + [mp.mpf(0)]*rmax
    for n in range(terms):
        logarithm = mp.log(a+n)
        val = mp.exp(-s*logarithm)
        for k in range(kmax+1):
            for r in range(rmax+1):
                sums[r][k] += elem[r]*val
            val *= -logarithm
        inv = 1/(a+n)
        for r in range(rmax, 0, -1):
            elem[r] += inv*elem[r-1]
    return sums


def direct_D_jets(s, a, rmax, kmax, terms, unshifted=None):
    M = direct_M_jets(s, a, rmax, kmax, terms)
    if unshifted is None:
        unshifted = direct_M_jets(s, mp.mpf(1), rmax, kmax, terms)
    coeff = K_coefficients(a, rmax)
    return [[M[r][k]-sum(coeff[j]*unshifted[r-j][k]
                        for j in range(r+1))
             for k in range(kmax+1)] for r in range(rmax+1)]


def finite_differences(s, kmax, terms):
    """A_j and its spectral derivatives by a finite difference tableau."""
    answer = [[mp.mpc(0)]*(terms+1) for _ in range(kmax+1)]
    for k in range(kmax+1):
        row = [mp.mpc(0)] + [mp.power(n,1-s)*(-mp.log(n))**k
                              for n in range(1,terms+1)]
        for j in range(1,terms+1):
            row = [row[n+1]-row[n] for n in range(len(row)-1)]
            answer[k][j] = row[0]
    return answer


def newton_D_jets(s, a, rmax, kmax, terms, differences=None):
    if differences is None:
        differences = finite_differences(s,kmax,terms)
    sums = [[mp.mpc(0) for _ in range(kmax+1)] for _ in range(rmax+1)]
    bino = mp.mpf(1)
    for j in range(1,terms+1):
        bino *= (a-j)/j
        for r in range(rmax+1):
            factor = (-1)**(r+1)*bino/mp.mpf(j)**(r+1)
            for k in range(kmax+1):
                sums[r][k] += factor*differences[k][j]
    return sums


def finite_transport(s, a, rmax, kmax, L, tail):
    finite = [[mp.mpc(0) for _ in range(kmax+1)] for _ in range(rmax+1)]
    elem = [mp.mpf(1)] + [mp.mpf(0)]*rmax
    for n in range(L):
        logarithm = mp.log(a+n)
        val = mp.exp(-s*logarithm)
        for k in range(kmax+1):
            for r in range(rmax+1):
                finite[r][k] += elem[r]*val
            val *= -logarithm
        for r in range(rmax,0,-1):
            elem[r] += elem[r-1]/(a+n)
    return [[finite[r][k]+sum(elem[j]*tail[r-j][k]
                                 for j in range(r+1))
             for k in range(kmax+1)] for r in range(rmax+1)]


def Xi_positive_jets(j, s, kmax):
    """An independent absolutely convergent Arakawa--Kaneko integral."""
    if j == 1:
        return [mp.diff(lambda v:v*mp.zeta(v+1),s,k)
                for k in range(kmax+1)]
    with mp.workdps(65):
        values = []
        for k in range(kmax+1):
            def integrand(t):
                if not t:
                    return mp.mpf(0)
                et = mp.exp(-t)
                w = -mp.expm1(-t)
                poly = mp.polylog(j,w)
                return mp.power(t,s-1)*mp.log(t)**k * et/w * poly
            values.append(mp.quad(integrand,[0,1,4,12,40,mp.inf]))
        gamma = mp.gamma(s)
        out = [values[0]/gamma]
        if kmax >= 1:
            out.append((values[1]-mp.digamma(s)*values[0])/gamma)
        if kmax >= 2:
            out.append((values[2]-2*mp.digamma(s)*values[1]
                        +(mp.digamma(s)**2-mp.polygamma(1,s))*values[0])/gamma)
        return [+v for v in out]


def elementary_reciprocals(r):
    coeff = [mp.mpf(1)]+[mp.mpf(0)]*r
    for j in range(1,r+1):
        for h in range(r,0,-1):
            coeff[h] += coeff[h-1]/j
    return coeff


def encoded(z):
    z = mp.mpc(z)
    return {"real":mp.nstr(z.real,42),"imag":mp.nstr(z.imag,42)}


def compare(name, lhs, rhs, tolerance, **inputs):
    error = abs(lhs-rhs)
    scaled = error/(1+abs(rhs))
    return {"name":name,"inputs":inputs,"left":encoded(lhs),
            "right":encoded(rhs),"absolute_residual":mp.nstr(error,12),
            "scaled_residual":mp.nstr(scaled,12),
            "tolerance":str(tolerance),"passed":bool(scaled<tolerance)}


def numerical_checks(direct_terms, newton_terms, nodes, radius):
    out=[]
    s = mp.mpc("12.25","0.35")
    a = mp.mpc("15.2","0.1")
    rmax,kmax=3,2
    unshifted=direct_M_jets(s,mp.mpf(1),rmax,kmax,direct_terms)
    A=finite_differences(s,kmax,newton_terms)
    direct=direct_D_jets(s,a,rmax,kmax,direct_terms,unshifted)
    newton=newton_D_jets(s,a,rmax,kmax,newton_terms,A)
    for r in range(rmax+1):
        for k in range(kmax+1):
            out.append(compare("defining-sum-versus-Newton",direct[r][k],
                               newton[r][k],mp.mpf("1e-20"),r=r,k=k,
                               s=encoded(s),a=encoded(a)))
    print("Completed defining-sum/Newton comparisons.",flush=True)

    z=mp.mpc("0.27","0.19")
    for N in range(3):
        rr=N+1
        here=direct_D_jets(s,-N+z,rr,1,direct_terms,unshifted)
        tail=direct_D_jets(s,1+z,rr,1,direct_terms,unshifted)
        transported=finite_transport(s,-N+z,rr,1,N+1,tail)
        for r in range(rr+1):
            for k in range(2):
                out.append(compare("negative-shift-finite-transport",
                    here[r][k],transported[r][k],mp.mpf("1e-25"),
                    N=N,r=r,k=k,z=encoded(z)))
    print("Completed negative-shift transport comparisons.",flush=True)

    Xi={j:Xi_positive_jets(j,s,1) for j in range(1,4)}
    for r in range(1,4):
        means=[mp.mpc(0),mp.mpc(0)]
        for n in range(nodes):
            zz=radius*mp.exp(2j*mp.pi*(mp.mpf(n)+mp.mpf("0.5"))/nodes)
            values=direct_D_jets(s,-r+zz,r,1,direct_terms,unshifted)
            amplitude=mp.fprod(1/(zz-j) for j in range(1,r+1))*mp.power(zz,-s)
            for k in range(2):
                means[k] += (values[r][k]-amplitude*(-mp.log(zz))**k)/nodes
        eh=elementary_reciprocals(r)
        for k in range(2):
            expected=(-1)**r*sum(eh[h]*Xi[r-h][k] for h in range(r))
            out.append(compare("Cauchy-boundary-versus-Xi-integral",means[k],
                     expected,mp.mpf("1e-24"),r=r,k=k,s=encoded(s),
                     nodes=nodes,radius=str(radius)))
        print(f"Completed independent first-boundary depth {r}.",flush=True)

    # At nonpositive spectral integers the value is polynomial, while
    # its order derivatives acquire logarithmic germs.  Continue from
    # the positive shift 16+z using the entire Newton expansion.
    for m in range(3):
        ss=mp.mpf(-m)
        AA=finite_differences(ss,2,newton_terms)
        means=[mp.mpc(0) for _ in range(3)]
        for n in range(nodes):
            zz=radius*mp.exp(2j*mp.pi*(mp.mpf(n)+mp.mpf("0.5"))/nodes)
            tail=newton_D_jets(ss,16+zz,1,2,newton_terms,AA)
            values=finite_transport(ss,-1+zz,1,2,17,tail)
            amplitude=mp.power(zz,-ss)/(zz-1)
            for k in range(3):
                means[k] += (values[1][k]-amplitude*(-mp.log(zz))**k)/nodes
        for k in range(3):
            if m==0:
                expected=mp.mpf(-1) if k==0 else (-1)**k*k*mp.stieltjes(k-1)
            else:
                expected=m*mp.diff(mp.zeta,1-m,k)
                if k:
                    expected-=k*mp.diff(mp.zeta,1-m,k-1)
            out.append(compare("polynomial-order-boundary-jets",means[k],expected,
                     mp.mpf("1e-24"),m=m,k=k,nodes=nodes,radius=str(radius)))
        print(f"Completed Stieltjes/zeta boundary at s={-m}.",flush=True)

    # A concrete monodromy case: continuation around -1 creates a pole
    # at 0 on the new sheet, although the original depth-one germ is regular.
    ss=mp.mpc("0.7","0.2")
    aa=mp.mpc("0.4","0.17")
    # Modify only the a+1 logarithm in the finite transport sum.
    jump=(mp.exp(-2j*mp.pi*ss)-1)*mp.power(aa+1,-ss)/aa
    direct_jump=(mp.exp(-ss*(mp.log(aa+1)+2j*mp.pi))
                  -mp.exp(-ss*mp.log(aa+1)))/aa
    out.append(compare("monodromy-single-mode",direct_jump,jump,
                       mp.mpf("1e-90"),s=encoded(ss),a=encoded(aa)))
    # Repeat one independent defining sum with a doubled cutoff.
    twice=direct_D_jets(s,a,1,1,2*direct_terms)
    for r in range(2):
        for k in range(2):
            out.append(compare("doubled-defining-cutoff",direct[r][k],twice[r][k],
                         mp.mpf("1e-26"),r=r,k=k,
                         original_terms=direct_terms,new_terms=2*direct_terms))
    return out


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--output",type=Path,
       default=Path(__file__).resolve().parents[1]/"results"/"shift_germs.json")
    parser.add_argument("--direct-terms",type=int,default=1200)
    parser.add_argument("--newton-terms",type=int,default=180)
    parser.add_argument("--nodes",type=int,default=28)
    args=parser.parse_args()
    start=time.time()
    mp.mp.dps=110
    exact=exact_checks()
    print(f"Completed {len(exact)} exact checks.",flush=True)
    numeric=numerical_checks(args.direct_terms,args.newton_terms,args.nodes,mp.mpf("0.025"))
    report={
        "description":"Harmonic shift germs, boundary constants, and rank jump",
        "evidence":"Exact rational checks and independent floating-point diagnostics; no interval claims",
        "versions":{"mpmath":mp.__version__,"sympy":sp.__version__},
        "settings":{"working_digits":110,"Xi_integral_digits":65,
                    "direct_terms":args.direct_terms,"Newton_terms":args.newton_terms,
                    "Cauchy_nodes":args.nodes,"Cauchy_radius":"0.025"},
        "truncation_note":"The defining sums, Newton series, and discrete Cauchy extraction have separate truncation errors. A doubled defining cutoff is included. Numerical thresholds are diagnostics, not rigorous bounds.",
        "exact_checks":exact,"numerical_checks":numeric,
        "summary":{"exact_count":len(exact),"numeric_count":len(numeric),
                    "all_passed":all(x["passed"] for x in exact+numeric),
                    "max_scaled_numeric_residual":max(
                        (x["scaled_residual"] for x in numeric),key=lambda t:mp.mpf(t)),
                    "elapsed_seconds":round(time.time()-start,2)}}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(report["summary"],indent=2),flush=True)
    if not report["summary"]["all_passed"]:
        for x in exact+numeric:
            if not x["passed"]:
                print("FAILED",x,flush=True)
        raise SystemExit(1)


if __name__=="__main__":
    main()
