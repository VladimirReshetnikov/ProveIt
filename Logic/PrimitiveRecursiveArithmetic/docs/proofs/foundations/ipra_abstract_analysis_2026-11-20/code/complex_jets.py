#!/usr/bin/env python3
"""Exact finite checks for the complex-analysis section of the report.

All assertions use Fraction arithmetic. These examples test the implementation
and constants; the universal proofs are in the report, not inferred from tests.
"""
from __future__ import annotations
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import argparse
import json

Z = tuple[F, F]


def add(z: Z, w: Z) -> Z:
    return z[0] + w[0], z[1] + w[1]


def neg(z: Z) -> Z:
    return -z[0], -z[1]


def sub(z: Z, w: Z) -> Z:
    return add(z, neg(w))


def mul(z: Z, w: Z) -> Z:
    return z[0] * w[0] - z[1] * w[1], z[0] * w[1] + z[1] * w[0]


def scale(z: Z, a: F) -> Z:
    return z[0] * a, z[1] * a


def norm_sq(z: Z) -> F:
    return z[0] * z[0] + z[1] * z[1]


def inv(z: Z) -> Z:
    d = norm_sq(z)
    assert d > 0
    return z[0] / d, -z[1] / d


def cpow(z: Z, n: int) -> Z:
    result = (F(1), F(0))
    for _ in range(n):
        result = mul(result, z)
    return result


def ceil_q(a: F) -> int:
    return -(-a.numerator // a.denominator)


def falling(n: int, j: int) -> int:
    if n < j:
        return 0
    answer = 1
    for i in range(j):
        answer *= n - i
    return answer


def jet(coeff: list[Z], z: Z, j: int) -> Z:
    result = (F(0), F(0))
    for n in range(len(coeff) - 1, j - 1, -1):
        result = add(mul(result, z), scale(coeff[n], F(falling(n, j))))
    return result


def schedule(M: F, R: F, r: F, J: int, k: int) -> dict:
    assert M >= 0 and R > 0 and 0 <= r < R and J >= 0 and k >= 0
    s = (r + R) / 2
    rho, theta, sigma = r / R, r / s, s / R
    K = [M * factorial(j) / (s**j * (1-theta)**(j+1) * (1-sigma))
         for j in range(J+1)]
    D = [F(factorial(j)) / (R**j * (1-rho)**(j+1))
         for j in range(J+1)]
    U, V, L0 = max(1, ceil_q(max(K))), max(1, ceil_q(8*max(D))), max(1, ceil_q(M))
    h = ceil_q(1/(1-sigma))
    N, p = J + h*(k+U+2), k+V
    delta = F(1, 2**p)
    cardinal = (2*L0*2**p+1)**(2*(N+1))
    return dict(K=K, D=D, sigma=sigma, U=U, V=V, L0=L0, h=h,
                N=N, p=p, delta=delta, cardinal_bits=cardinal.bit_length())


def quantize(x: F, p: int, L0: int) -> F:
    """Round rational observation to nearest grid; ties round upward."""
    t = x * 2**p
    j = (t + F(1, 2)).numerator // (t + F(1, 2)).denominator
    j = min(L0*2**p, max(-L0*2**p, j))
    return F(j, 2**p)


def run() -> dict:
    count_geom = 0
    for t in [F(0), F(1, 3), F(3, 4), F(9, 10)]:
        for j in range(7):
            for L in range(31):
                value = sum((F(falling(n,j))*t**(n-j) for n in range(j,L+1)), F(0))
                assert value <= F(factorial(j))/(1-t)**(j+1)
                count_geom += 1
    records, tail_tests, quantization_tests = [], 0, 0
    R, M = F(2), F(1)
    for r in [F(0), F(1,2), F(1)]:
        for J in range(3):
            for k in [0, 3, 5]:
                S = schedule(M,R,r,J,k)
                N,p,d = S["N"],S["p"],S["delta"]
                eps = F(1,2**k)
                assert max(S["K"])*S["sigma"]**(N+1) <= eps/4
                assert 2*d*max(S["D"]) <= eps/4
                points = [(F(0),F(0)),(r,F(0)),(-r,F(0)),(F(0),r),
                          (F(0),-r),(r/2,r/2),(-r/2,r/2)]
                coeff = [(R**(-n),F(0)) for n in range(N+1)]
                for z in points:
                    assert norm_sq(z) <= r*r
                    denom_inv = inv(sub((F(1),F(0)),scale(z,F(1,2))))
                    for j in range(J+1):
                        exact = scale(cpow(denom_inv,j+1),F(factorial(j),2**j))
                        difference = sub(exact,jet(coeff,z,j))
                        bound = S["K"][j]*S["sigma"]**(N+1)
                        assert norm_sq(difference) <= bound*bound
                        assert norm_sq(difference) <= (eps/2)**2
                        tail_tests += 1
                # Independently exercise noisy observation + rounding + clipping.
                shortN = min(17,N)
                original, rounded = [], []
                for n in range(shortN+1):
                    b = (F(n%5-2,4),F(n%7-3,6))
                    assert norm_sq(b) <= M*M
                    obs = (b[0]+d/4,b[1]-d/4)
                    q = (quantize(obs[0],p,S["L0"]),quantize(obs[1],p,S["L0"]))
                    assert norm_sq(sub(b,q)) <= (2*d)**2
                    original.append(scale(b,R**(-n)))
                    rounded.append(scale(q,R**(-n)))
                for z in points:
                    for j in range(J+1):
                        e = sub(jet(original,z,j),jet(rounded,z,j))
                        bound = 2*d*S["D"][j]
                        assert norm_sq(e) <= bound*bound
                        quantization_tests += 1
                records.append(dict(radius=str(r),order=J,precision=k,
                                    degree=N,coefficient_bits=p,
                                    net_cardinality_binary_length=S["cardinal_bits"],
                                    tail_bound=str(max(S["K"])*S["sigma"]**(N+1)),
                                    quarter_error_target=str(eps/4)))
    return dict(status="passed",arithmetic="exact fractions and integer comparisons",
                scope="finite implementation diagnostics, not universal proofs",
                finite_geometric_checks=count_geom,
                exact_geometric_function_jet_checks=tail_tests,
                noisy_coefficient_jet_checks=quantization_tests,
                schedules=records)


if __name__ == "__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--output",type=Path,default=Path("evidence/complex_checks.json"))
    args=parser.parse_args()
    result=run()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({k:v for k,v in result.items() if k!="schedules"},indent=2))
