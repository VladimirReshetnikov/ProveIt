#!/usr/bin/env python3
"""Exact algebra checks and independent numerical diagnostics for reflected moments.

Run: python code/verify_reflected_moments.py
The analytic theorems are proved in article/sections/gamma.tex. Numerical values here
are diagnostics, not interval certificates or substitutes for those proofs.
"""
from __future__ import annotations

import json
from functools import lru_cache
from pathlib import Path

import mpmath as mp
import sympy as sp

OUT = Path(__file__).resolve().parents[1] / "results"
OUT.mkdir(parents=True, exist_ok=True)


def multiply(a, b, degree):
    return [sum(a[j] * b[k-j] for j in range(max(0, k-len(b)+1),
                 min(k, len(a)-1)+1)) for k in range(degree+1)]


def power(a, m, degree):
    out = [1] + [0] * degree
    for _ in range(m):
        out = multiply(out, a, degree)
    return out


def exponential(log_coeff, degree):
    out = [1]
    for k in range(1, degree+1):
        out.append(sum(j*log_coeff[j]*out[k-j] for j in range(1, k+1))/k)
    return out


def exact_checks():
    gamma = sp.Symbol("gamma")
    maxk = 10
    B = [sp.Integer(0), gamma] + [sp.zeta(j)/j for j in range(2, maxk+2)]
    entries = {}
    coefficients = {}
    for k in range(1, maxk+1):
        E = exponential([k*(-1)**j*B[j] for j in range(k)], k-1)
        for m in range(k):
            H = power(B, m, k-1)
            A = sp.expand(sp.Rational(1,k)*sum(E[k-1-j]*H[j] for j in range(k)))
            coefficients[k, m] = A
            if k <= 6:
                entries[f"A_{k},{m}"] = str(A)

    count = 0
    for m in range(7):
        k = m+1
        expected = gamma**m/k
        assert sp.expand(coefficients[k, m]-expected) == 0
        count += 1
        k = m+2
        expected = gamma**(m-1)*(m*sp.zeta(2)/2-k*gamma**2)/k
        assert sp.expand(coefficients[k, m]-expected) == 0
        count += 1
        k = m+3
        expected = gamma**m/k*(m*sp.zeta(3)/(3*gamma)
            +m*(m-1)*sp.zeta(2)**2/(8*gamma**2)
            +k*(1-m)*sp.zeta(2)/2+k*k*gamma**2/2)
        assert sp.expand(coefficients[k, m]-expected) == 0
        count += 1

    for k in range(1, maxk+1):
        total = sp.expand(sum(sp.Integer(k)**m/sp.factorial(m)*coefficients[k,m]
                              for m in range(k)))
        expected = (sp.pi**(k-1)*sp.binomial(k-1, (k-1)//2)
                    / (k*sp.Integer(2)**(k-1))) if k % 2 else 0
        assert sp.expand(total-expected) == 0
        count += 1

    X, Y, z = sp.symbols("X Y z")
    maxn = 10
    app = [sp.Integer(0), X] + [(1-sp.Integer(2)**(1-j))*sp.zeta(j)/j
                                for j in range(2, maxn+1)]
    P = [sp.expand(v*sp.factorial(j)) for j,v in
         enumerate(exponential(app, maxn))]
    for n in range(maxn+1):
        for j in range(n+1):
            assert sp.expand(P[n].coeff(X,j)-sp.binomial(n,j)*P[n-j].subs(X,0)) == 0
            count += 1
        assert sp.expand(P[n].subs(X,X+Y)-sum(sp.binomial(n,j)*Y**j*P[n-j]
                                            for j in range(n+1))) == 0
        count += 1

    # Independent beta logarithm, via exact polygamma values at 1/2 and 1.
    for j in range(1,maxn+1):
        beta_log = ((-sp.Rational(1,2))**j
                    * (sp.polygamma(j-1, sp.Rational(1,2))-sp.polygamma(j-1,1)))
        expected = sp.log(2) if j == 1 else sp.factorial(j-1)*(1-sp.Integer(2)**(1-j))*sp.zeta(j)
        assert sp.simplify(beta_log-expected) == 0
        count += 1

    even = sum(app[j]*z**j for j in range(2,maxn+1,2))
    trig = sp.series(sp.sqrt(sp.tan(sp.pi*z/2)/(sp.pi*z/2)), z, 0, maxn+1).removeO()
    exp_even = sp.series(sp.exp(even), z, 0, maxn+1).removeO()
    assert sp.expand(trig-exp_even) == 0
    count += 1
    return {"status":"passed", "exact_assertions":count,
            "coefficient_examples":entries,
            "appell_polynomials":{str(n):str(P[n]) for n in range(7)}}


mp.mp.dps = 120


@lru_cache(None)
def numeric_A(k, m):
    degree = k-1
    B = [mp.mpf(0), mp.euler] + [mp.zeta(j)/j for j in range(2,max(k,2))]
    E = exponential([k*B[j] for j in range(k)], degree)
    H = power(B, m, degree)
    return (-1)**(k-1)*mp.fsum(E[degree-j]*(-1)**j*H[j]
                              for j in range(k))/k


def critical_constants():
    tau = mp.findroot(lambda u: -u*mp.digamma(1-u)-1, (mp.mpf(".50"),mp.mpf(".51")))
    rho = tau/mp.gamma(1-tau)
    alpha = -mp.log(rho)
    v = 1+tau*tau*mp.polygamma(1,1-tau)
    C = tau/mp.sqrt(2*mp.pi*v)
    b = -mp.loggamma(1+tau)
    k3 = 1+3*tau*tau*mp.polygamma(1,1-tau)-tau**3*mp.polygamma(2,1-tau)
    k4 = (1+7*tau*tau*mp.polygamma(1,1-tau)
          -6*tau**3*mp.polygamma(2,1-tau)+tau**4*mp.polygamma(3,1-tau))
    G = -b
    DG = tau*mp.digamma(1+tau)
    D2G = DG+tau*tau*mp.polygamma(1,1+tau)
    beta = {}
    for m in range(4):
        amp1 = 1+m*DG/G
        amp2 = 1+2*m*DG/G+m*D2G/G+m*(m-1)*(DG/G)**2
        beta[m] = -amp2/(2*v)+k3*amp1/(2*v*v)+k4/(8*v*v)-5*k3*k3/(24*v**3)
    return tau,rho,alpha,v,C,b,beta


def small_B(x, sign=1):
    if x < mp.mpf("1e-10"):
        return sign*mp.euler*x+mp.fsum(mp.zeta(j)*(sign*x)**j/j for j in range(2,14))
    return mp.loggamma(1-sign*x)


def normalized_moment(n, m):
    # Independent substitution x=exp(-t); neither residues nor inverses used.
    def integrand(t):
        if t == 0:
            return mp.mpf(0)
        x = mp.exp(-t)
        if t < mp.mpf(".125"):
            delta = -mp.expm1(-t)
            f = small_B(delta,1)
            reflected = -mp.log(delta)+small_B(delta,-1)
        else:
            f = t+small_B(x,-1)
            reflected = small_B(x,1)
        return mp.exp(-t)*f**n*reflected**m/mp.factorial(n)
    return mp.quad(integrand,[0,mp.mpf(".25"),1,2,4,8,16,32,64,128,256,mp.inf])


def numstr(v):
    return mp.nstr(v,70)


def numeric_checks():
    tau,rho,alpha,v,C,b,beta = critical_constants()
    late=[]
    for m in range(4):
        for k in [12,24,48,96]:
            value=numeric_A(k,m)
            leading=(-1)**(k+m-1)*C*b**m*rho**(-k)*mp.mpf(k)**mp.mpf("-1.5")
            ratio=value/leading
            late.append({"m":m,"k":k,"ratio_to_leading":numstr(ratio),
                         "k_times_relative_difference":numstr(k*(ratio-1)),
                         "predicted_beta":numstr(beta[m]),
                         "k_squared_corrected_error":numstr(k*k*(ratio-1-beta[m]/k))})

    moments=[]
    for m in [1,2,3]:
        for n in [12,24,48]:
            value=normalized_moment(n,m)
            leading=mp.euler**m/mp.mpf(m+1)**(n+1)
            K=m+2
            finite=mp.fsum(numeric_A(k,m)/mp.mpf(k)**n for k in range(1,K+1))
            next_term=numeric_A(K+1,m)/mp.mpf(K+1)**n
            optK=int(mp.floor(n/alpha-mp.sqrt(n)))
            approx=mp.fsum(numeric_A(k,m)/mp.mpf(k)**n for k in range(1,optK+1))
            observed=abs(value-approx)
            T=tau*mp.loggamma(1-tau)**m
            bound=(alpha**n/mp.factorial(n)*(mp.factorial(m)+n*T/(n-optK*alpha))
                   +T*rho**(-optK-1)/mp.mpf(optK+1)**n
                   *mp.gammainc(n,(optK+1)*alpha,mp.inf)/mp.gamma(n))
            assert observed < bound
            moments.append({"m":m,"n":n,"normalized_moment":numstr(value),
                            "ratio_to_leading":numstr(value/leading),
                            "K_for_next_term_test":K,
                            "residual_divided_by_next_term":numstr((value-finite)/next_term),
                            "optimized_K":optK,"observed_absolute_error":numstr(observed),
                            "explicit_upper_bound":numstr(bound)})

    # Independent small-order reflection check by direct x-quadrature.
    low=[]
    for n,m in [(1,2),(2,2),(2,3)]:
        val=mp.quad(lambda x: mp.loggamma(x)**n*mp.loggamma(1-x)**m,[0,mp.mpf(".5"),1])
        val2=normalized_moment(n,m)*mp.factorial(n)
        rel=abs(val-val2)/max(1,abs(val))
        assert rel < mp.mpf("1e-95")
        low.append({"n":n,"m":m,"value":numstr(val),"independent_relative_difference":numstr(rel)})
    return {"status":"passed (numerical diagnostics, not interval certification)",
            "working_decimal_digits":mp.mp.dps,
            "constants":dict(zip(["tau","rho","alpha","v","C","b"],map(numstr,[tau,rho,alpha,v,C,b]))),
            "beta":{str(m):numstr(v) for m,v in beta.items()},
            "late_coefficients":late,"moment_asymptotics":moments,
            "independent_quadrature":low}


if __name__ == "__main__":
    exact=exact_checks()
    (OUT/"reflected_exact.json").write_text(json.dumps(exact,indent=2)+"\n")
    print(f"Exact checks: {exact['exact_assertions']} assertions passed.",flush=True)
    numeric=numeric_checks()
    (OUT/"reflected_numeric.json").write_text(json.dumps(numeric,indent=2)+"\n")
    print(f"Numerical diagnostics: {len(numeric['late_coefficients'])} late coefficients; "
          f"{len(numeric['moment_asymptotics'])} moment cases; "
          f"{len(numeric['independent_quadrature'])} independent quadratures passed.",flush=True)
