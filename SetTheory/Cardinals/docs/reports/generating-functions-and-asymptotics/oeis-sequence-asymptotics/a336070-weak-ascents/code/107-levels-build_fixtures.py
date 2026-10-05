#!/usr/bin/env python3
"""Regenerate committed finite fixtures; standard-library exact arithmetic only.

This is a development tool, not a validation shortcut. verify_exact.py checks the
result by matrix sums, independent state transitions and independent enumeration.
It does not call this generator or import its mathematical implementations.
"""
from collections import defaultdict
from fractions import Fraction as F
from math import comb
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent
MS = (1, 2, 3, 5, 8, 16)
RS = ("1/5", "1/2", "2/3", "9/10", "99/100", "1")
WS = ("1/10", "1/2", "1", "3/2", "7")
POLYNOMIAL_N = 16
TRANSFORM_N = 50


def text(x):
    return str(F(x))


def case(M, rt):
    r = F(rt)
    endpoint = r == 1
    v = r ** (-M)
    lam = F(M) if endpoint else (v - 1)/(1-r)
    t = v/lam
    if endpoint:
        p = [F(1, M)]*M
        b = [F(M*(M-1)-l*(l-1), 2*M*M) for l in range(M)]
        c = F(M*M-1, 3*M*M)
        h = [F(l*(1-l), 2*M*M) for l in range(M+1)]
    else:
        B, D = r/(1-r), 1-r**M
        p = [(1-r)*r**d/D for d in range(M)]
        b = [(l+B-(M+B)*r**(M-l))/(M*D) for l in range(M)]
        c = (F(M*(M-1), 2)+M*B-(M+B)*B*D)/(M*M*D)
        h = [(c/B+1/(2*M*D*B))*l-F(l*l)/(2*M*D*B) for l in range(M+1)]
    weights = []
    for wt in WS:
        w = F(wt)
        dw = 1+(w-1)*t
        delta = (w-1)*t/dw
        pw = [(w if d == 0 else 1)*p[d]/dw for d in range(M)]
        # Formula side of the weighted Poisson identity, to be checked by direct sum.
        first = [c+delta*(F(l,M)-c) for l in range(M)]
        moments = [sum(p[d]*F(d,M)**k for d in range(M))/dw for k in range(1,5)]
        drift = []
        for l in range(M):
            unweighted = sum(p[(j-l)%M]*(1-F((j-l)%M,M)+F(int(j>=l)*j,M*(M+int(j>=l)))) for j in range(M))
            drift.append(unweighted/dw+delta*(1+F(l,M*(M+1))))
        weights.append({"w":wt, "lambda_w":text(lam+(w-1)*v), "d_w":text(dw),
                        "delta_w":text(delta), "p_w":list(map(text,pw)),
                        "scaled_first_moment":list(map(text,first)),
                        "increment_moments":list(map(text,moments)),
                        "tracker_drift":list(map(text,drift))})
    return {"M":M, "r":rt, "q":"0" if endpoint else "-M log r (symbolic)",
            "scaled_interpretation":"continuous_limit_at_q=0" if endpoint else "divided_by_q",
            "v":text(v), "lambda":text(lam), "t":text(t),
            "f":[text(r**l) for l in range(M)], "p":list(map(text,p)),
            "b_scaled":list(map(text,b)), "c_scaled":text(c), "h_scaled":list(map(text,h)),
            "actual_q0_b_c_h_zero":endpoint,
            "weights":weights}


def polynomials():
    # Direct outgoing transitions keeping the equality exponent explicitly.
    state = {(0,0,0):1}
    result = [[1],[1]]
    for n in range(2,POLYNOMIAL_N+1):
        nxt = defaultdict(int)
        for (K,L,E),count in state.items():
            for j in range(K+2):
                nxt[K+int(j>=L), j, E+int(j==L)] += count
        state = nxt
        poly = [0]*n
        for (K,L,E),count in state.items():
            poly[E] += count
        result.append(poly)
    return result


def ordinary_counts(allow_equal):
    # Direct outgoing strict-ascent transitions (different from verifier's prefix sums).
    state = {(0,0):1}
    totals = [1,1]
    for n in range(2,TRANSFORM_N+1):
        nxt = defaultdict(int)
        for (K,L),count in state.items():
            for j in range(K+2):
                if allow_equal or j != L:
                    nxt[K+int(j>L),j] += count
        state = nxt
        totals.append(sum(state.values()))
    return totals


def build():
    fishburn, primitive = ordinary_counts(True), ordinary_counts(False)
    return {
        "schema":"report107-exact-weighted-levels-v1",
        "scope":"Finite integer/rational checks only; no asymptotic claim is certified.",
        "inventory":{"M":list(MS),"r":list(RS),"w":list(WS),
                     "moment_orders":[1,2,3,4],"zeta":["0","1/3","1"],
                     "polynomial_max_n":POLYNOMIAL_N,"enumeration_max_n":8,
                     "zero_transform_max_n":TRANSFORM_N},
        "frozen_cases":[case(M,r) for M in MS for r in RS],
        "level_polynomials":polynomials(),
        "zero_level":{"fishburn":fishburn,"primitive":primitive,
                      "inverse_transform_rows":[[(-1)**j*comb(n-1,j)*fishburn[n-j] for j in range(n)] for n in range(1,TRANSFORM_N+1)]}
    }


if __name__ == "__main__":
    output = HERE/"fixtures.json"
    output.write_text(json.dumps(build(),indent=2)+"\n",encoding="utf-8")
    print(str(output))
