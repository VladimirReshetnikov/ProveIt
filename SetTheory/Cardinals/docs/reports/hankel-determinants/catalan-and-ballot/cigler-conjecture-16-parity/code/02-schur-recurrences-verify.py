#!/usr/bin/env python3
"""Exact finite checks for the accompanying mathematical proof draft.

Run: python code/verify.py
Python's standard library handles all numerical checks. SymPy is used only
for exact polynomial-ring checks; no floating-point arithmetic is used.
Finite checks do not constitute a proof for all indices.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import product
from math import comb, factorial, prod
from pathlib import Path
import json
import platform
import random
import time


def exact_div(a, b):
    q, r = divmod(a, b)
    if r != 0:
        raise ArithmeticError("Bareiss division was not exact")
    return q


def determinant(rows, one=1):
    """Fraction-free elimination over an integral domain, with row pivoting."""
    n = len(rows)
    if any(len(row) != n for row in rows):
        raise ValueError("determinant requires a square matrix")
    if n == 0:
        return one
    a = [list(row) for row in rows]
    previous, sign = one, 1
    for k in range(n - 1):
        if a[k][k] == 0:
            pivot = next((i for i in range(k + 1, n) if a[i][k] != 0), None)
            if pivot is None:
                return 0 * one
            a[k], a[pivot] = a[pivot], a[k]
            sign = -sign
        p = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                a[i][j] = exact_div(p * a[i][j] - a[i][k] * a[k][j], previous)
            a[i][k] = 0 * one
        previous = p
    return sign * a[-1][-1]


def c_moment(r, t):
    if r < 0:
        raise ValueError("moment index must be nonnegative")
    one = t ** 0
    if r == 0:
        return one
    def choose(n, j):
        return comb(n, j) if 0 <= j <= n else 0
    return sum((choose((r - 1) // 2, (j - 1) // 2)
                * choose(r // 2, j // 2) * t ** (j - 1)
                for j in range(1, r + 1)), 0 * one)


def source_hankel(k, n, t):
    moments = [c_moment(r, t) for r in range(k + max(1, 2 * n))]
    return determinant([[moments[k + i + j] for j in range(n)]
                        for i in range(n)], t ** 0)


def complete_homogeneous(alphabet, maximum, one=1):
    h = [one] + [0 * one] * maximum
    for x in alphabet:
        for j in range(1, maximum + 1):
            h[j] += x * h[j - 1]
    return h


def rectangular_sequence(alphabet, height, maximum, one=1):
    if height < 0 or height > len(alphabet) or maximum < 0:
        raise ValueError("invalid rectangle or range")
    if height == 0:
        return [one] * (maximum + 1)
    h = complete_homogeneous(alphabet, maximum + height, one)
    return [determinant([[h[n - i + j] if n - i + j >= 0 else 0 * one
                          for j in range(height)] for i in range(height)], one)
            for n in range(maximum + 1)]


def hankel_schur_sequence(k, maximum, t):
    if k < 1:
        raise ValueError("shift must be positive")
    a, b = k // 2, (k - 1) // 2
    one = t ** 0
    return rectangular_sequence([one] * a + [t] + [t * t] * b,
                                a, maximum, one)


def multiply(p, q):
    out = [0] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            out[i + j] += x * y
    return out


def pole_exponents(k):
    return [1 + q * (k - 1 - q) // 2 for q in range(k)]


def denominator(k, t, signed=False):
    out = [1]
    for q, e in enumerate(pole_exponents(k)):
        factor = [1, 0, t ** (2 * q)] if signed else [1, -(t ** q)]
        for _ in range(e):
            out = multiply(out, factor)
    return out


def convolution_prefix(p, values):
    return [sum(p[j] * values[n - j] for j in range(min(n, len(p) - 1) + 1))
            for n in range(len(values))]


def laurent_multiply(p, q):
    out = {}
    for i, x in p.items():
        for j, y in q.items():
            out[i + j] = out.get(i + j, 0) + x * y
    return out


def toeplitz(p, n):
    return determinant([[p.get(j - i, 0) for j in range(n)] for i in range(n)])


def U(p, m):
    return determinant([[p.get(i - j, 0) + p.get(i + j + 1, 0)
                         for j in range(m)] for i in range(m)])


def V(p, m):
    return determinant([[p.get(i - j, 0) - p.get(i + j + 2, 0)
                         for j in range(m)] for i in range(m)])


def spectral_data(nodes, multiplicities, height):
    records = []
    K = sum(multiplicities)
    C = K - height
    for r in product(*(range(m + 1) for m in multiplicities)):
        if sum(r) != height:
            continue
        s = [m - x for m, x in zip(multiplicities, r)]
        d = sum(x * y for x, y in zip(r, s))
        lam = prod(x ** j for x, j in zip(nodes, r))
        sign = (-1) ** sum(r[i] * s[j] for i in range(len(r))
                           for j in range(i + 1, len(r)))
        leading = Fraction(sign)
        for xi, mi, ri, si in zip(nodes, multiplicities, r, s):
            B = Fraction(prod(factorial(h) for h in range(ri)),
                         prod(factorial(h) for h in range(mi - ri, mi)))
            leading *= B * Fraction(xi) ** (C * ri - ri * si)
        for i in range(len(r)):
            for j in range(i + 1, len(r)):
                leading /= Fraction(nodes[j] - nodes[i]) ** (s[i]*r[j]+r[i]*s[j])
        records.append((lam, d, leading, r))
    if len({v[0] for v in records}) != len(records):
        raise ValueError("verification inputs must have distinct spectral products")
    return records


def projected_leading(values, records, selected):
    lam, d, _, _ = records[selected]
    op = [1]
    divisor = lam ** d * factorial(d)
    for j, (mu, degree, _, _) in enumerate(records):
        count = d if j == selected else degree + 1
        for _ in range(count):
            op = multiply(op, [-mu, 1])
        if j != selected:
            divisor *= (lam - mu) ** (degree + 1)
    return Fraction(sum(c * values[i] for i, c in enumerate(op)), divisor)


def check_equal(actual, expected, context):
    if actual != expected:
        raise AssertionError(f"Failed: {context}\nactual={actual}\nexpected={expected}")


def run(output):
    start = time.monotonic()
    result = {"python": platform.python_version(), "arithmetic": "exact integers and polynomial rings",
              "scope": "finite checks, not a formal or all-index proof", "checks": {}}
    counts = result["checks"]
    count = 0
    for t in (-3, -2, -1, 1, 2, 3, 5):
        for k in range(1, 13):
            values = hankel_schur_sequence(k, 12, t)
            for n, value in enumerate(values):
                C = n * (n - 1) // 2
                check_equal(source_hankel(k, n, t), (-1) ** (k * C) * t ** C * value,
                            ("Hankel-Schur", k, n, t))
                count += 1
    counts["hankel_schur_integer"] = {"cases": count, "k": [1, 12], "n": [0, 12],
                                      "t": [-3,-2,-1,1,2,3,5]}
    print("Hankel-Schur integer:", count, flush=True)

    rng = random.Random(260929)
    count = 0
    for trial in range(12):
        q = {0: rng.randint(-5, 5)}
        for j in range(1, 15):
            q[j] = q[-j] = rng.randint(-5, 5)
        for u in (-3, -2, -1, 0, 1, 2, 3):
            Qq = laurent_multiply({-1:u, 0:1+u*u, 1:u}, q)
            f = laurent_multiply({-1:u, 0:1+u, 1:1}, q)
            for n in range(13):
                m = n // 2
                expected = U(Qq, m) * V(q, m) if n % 2 == 0 else (1+u)*U(q,m+1)*V(Qq,m)
                check_equal(toeplitz(f, n), expected, ("Toeplitz factorization",trial,u,n))
                count += 1
    counts["universal_toeplitz"] = {"cases":count, "seed":260929, "symbols":12,
                                    "n":[0,12],"u":[-3,-2,-1,0,1,2,3]}
    print("Universal Toeplitz:", count, flush=True)

    rec_count = signed_count = coeff_count = 0
    recurrence_samples = []
    for t in (-2, 2, 3):
        for k in range(1, 13):
            e = pole_exponents(k)
            N = sum(e)
            D = (k // 2) * (k - k // 2)
            R = N - k
            values = hankel_schur_sequence(k, 2*N+8, t)
            num = convolution_prefix(denominator(k,t), values)
            check_equal(num[R+1:], [0]*(len(num)-R-1), ("recurrence tail",k,t))
            check_equal(num[R], (-1)**(N+D+1)*t**((k-1)*R//2), ("numerator leading",k,t))
            for j in range(R+1):
                check_equal(Fraction(num[R-j]) * Fraction(t)**((k-1)*R//2-(k-1)*(R-j)),
                            (-1)**(N+D+1)*num[j], ("numerator reciprocity",k,t,j))
                coeff_count += 1
            rec_count += 1
            if t == 2:
                recurrence_samples.append({"k":k,"multiplicities":e,"order":N,"numerator_degree":R})
            if k % 2:
                hat = [(-1)**(n*(n-1)//2)*v for n,v in enumerate(values)]
                hatnum = convolution_prefix(denominator(k,t,True),hat)
                hatR = 2*N-k
                check_equal(hatnum[hatR+1:], [0]*(len(hatnum)-hatR-1), ("signed recurrence",k,t))
                check_equal(hatnum[hatR], (-1)**(k//2)*t**((k-1)*hatR//2), ("signed leading",k,t))
                for j in range(hatR+1):
                    check_equal(Fraction(hatnum[hatR-j])*Fraction(t)**((k-1)*hatR//2-(k-1)*(hatR-j)),
                                (-1)**(k//2)*hatnum[j], ("signed reciprocity",k,t,j))
                    coeff_count += 1
                signed_count += 1
    counts["ordinary_recurrence_and_numerator"]={"cases":rec_count,"k":[1,12],"t":[-2,2,3],
                                                "tested_through":"n=2N_k+8"}
    counts["signed_recurrence_and_numerator"]={"cases":signed_count,"odd_k":[1,11],"t":[-2,2,3]}
    counts["numerator_reciprocity_coefficients"]={"cases":coeff_count}
    result["recurrence_samples"]=recurrence_samples
    print("Recurrences and numerators:", rec_count, signed_count, flush=True)

    cases=0
    systems=[]
    for multiplicities in ([2,1,2],[3,1,2],[2,2,1],[2,2,2],[3,2]):
        nodes=[2,3,5][:len(multiplicities)]
        for height in range(1,sum(multiplicities)):
            records=spectral_data(nodes,multiplicities,height)
            N=sum(d+1 for _,d,_,_ in records)
            alphabet=[xi for xi,mi in zip(nodes,multiplicities) for _ in range(mi)]
            vals=rectangular_sequence(alphabet,height,N-1)
            for j,(_,_,predicted,_) in enumerate(records):
                check_equal(projected_leading(vals,records,j),predicted,
                            ("confluent leading coefficient",nodes,multiplicities,height,j))
                cases += 1
            systems.append({"nodes":nodes,"multiplicities":multiplicities,"height":height})
    for k in range(2,11):
        a,b=k//2,(k-1)//2
        nodes,ms=([1,2,4],[a,1,b]) if b else ([1,2],[a,1])
        records=spectral_data(nodes,ms,a)
        vals=hankel_schur_sequence(k,sum(d+1 for _,d,_,_ in records)-1,2)
        for j,(_,_,expected,_) in enumerate(records):
            check_equal(projected_leading(vals,records,j),expected,("Cigler leading",k,j))
            cases += 1
    counts["confluent_leading_coefficients"]={"cases":cases,"general_systems":systems,"cigler_k":[2,10],"cigler_t":2}
    print("Confluent leading coefficients:", cases, flush=True)

    count=0
    for k in range(1,13):
        a,b=k//2,(k-1)//2
        D=a*(k-a)
        for t in (0,1,-1):
            if t == 0:
                den=[1,-1]
            elif t == 1:
                den=[1]
                for _ in range(D+1): den=multiply(den,[1,-1])
            else:
                eplus=a*b+1
                eminus=(a-1)*(b+1)+1 if a else 0
                den=[1]
                for _ in range(eplus): den=multiply(den,[1,-1])
                for _ in range(eminus): den=multiply(den,[1,1])
            vals=hankel_schur_sequence(k,2*len(den)+6,t)
            num=convolution_prefix(den,vals)
            check_equal(num[len(den):],[0]*(len(num)-len(den)),("special recurrence",k,t))
            if t == 1:
                for n,v in enumerate(vals):
                    expected=prod(Fraction(n+j-i,j-i) for i in range(1,a+1) for j in range(a+1,k+1))
                    check_equal(v,expected,("dimension product",k,n))
            count += 1
    counts["exceptional_parameters"]={"cases":count,"k":[1,12],"t":[0,1,-1]}
    print("Exceptional parameters:",count,flush=True)

    import sympy
    from sympy.polys.rings import ring
    from sympy.polys.domains import ZZ
    ring_t,t=ring('t',ZZ)
    one=ring_t.one
    count=0
    polynomials=[]
    for k in range(1,9):
        vals=hankel_schur_sequence(k,6,t)
        for n,value in enumerate(vals):
            C=n*(n-1)//2
            check_equal(source_hankel(k,n,t),(-1)**(k*C)*t**C*value,("polynomial identity",k,n))
            coeffs=[int(value.get((j,),0)) for j in range((k-1)*n+1)]
            check_equal(coeffs,list(reversed(coeffs)),("polynomial reciprocity",k,n))
            if any(v<=0 for v in coeffs): raise AssertionError("positive support failed")
            if k%2:
                center=(k//2)*n
                for j in range(max(0,center-1)):
                    if coeffs[j]>coeffs[j+2]: raise AssertionError("parity unimodality failed")
            polynomials.append({"k":k,"n":n,"coefficients":coeffs})
            count += 1
    counts["exact_polynomial_identity"]={"cases":count,"k":[1,8],"n":[0,6],"also_checked":["coefficient reciprocity","positive support","odd-shift parity unimodality"]}
    result["sympy"]=sympy.__version__
    output.parent.mkdir(parents=True,exist_ok=True)
    (output.parent/'sample_polynomials.json').write_text(json.dumps(polynomials,indent=2)+'\n')
    result["elapsed_seconds"]=round(time.monotonic()-start,3)
    result["status"]="all checks passed"
    output.write_text(json.dumps(result,indent=2)+'\n')
    print("Polynomial identities:",count,flush=True)
    print("ALL CHECKS PASSED",flush=True)


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'data'/'verification.json')
    args=parser.parse_args()
    run(args.output)
