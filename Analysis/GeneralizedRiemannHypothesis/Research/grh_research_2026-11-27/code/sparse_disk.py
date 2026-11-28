#!/usr/bin/env python3
"""Exact extremal geometric root counts in positive-depth p-adic disks.

No p-adic approximation is used.  The algorithm implements the finite-cutoff
and minimum-basis theorems in papers/sparse_roots.tex.  It optimizes over the
coefficients on the specified support, not over roots in Q_p itself.
Python 3.10+, standard library only.
"""
from __future__ import annotations
import argparse
import json
import math
from fractions import Fraction


def is_prime(p: int) -> bool:
    return p >= 2 and all(p % a for a in range(2, math.isqrt(p) + 1))


def digit_sum(k: int, p: int) -> int:
    s = 0
    while k:
        k, a = divmod(k, p)
        s += a
    return s


def valuation(x: int | Fraction, p: int) -> int:
    if not x:
        raise ValueError("valuation(0) is infinite")
    x = Fraction(x)
    a, b, v = abs(x.numerator), x.denominator, 0
    while a % p == 0:
        a //= p
        v += 1
    while b % p == 0:
        b //= p
        v -= 1
    return v


def factorial_valuation(k: int, p: int) -> int:
    return (k - digit_sum(k, p)) // (p - 1)


def cutoff(p: int, t: int) -> dict:
    if not is_prime(p) or t < 1:
        raise ValueError("p must be prime and t positive")
    D = max(digit_sum(i, p) for i in range(t))
    H = D - 1
    d, power = 0, 1
    while power < t:
        d += 1
        power *= p
    if H <= 0:
        M, R, N = 0, 0, t - 1
    else:
        M = (H + p - 2) // (p - 1)
        R = d + M - 1
        N = max(t - 1, H * p**R)
    S0 = sum(digit_sum(i, p) for i in range(t))
    precision = max(1, (S0 - t + 1 + p - 2) // (p - 1))
    return dict(p=p, t=t, D=D, H=H, d=d, M=M, R=R, N=N,
                residue_precision=precision, residue_modulus=p**precision)


def lenstra_cutoff(p: int, t: int, depth) -> dict:
    """Lenstra's explicit local cutoff (1999, section 3), computed finitely."""
    r = Fraction(depth)
    if not is_prime(p) or t < 1 or r <= 0:
        raise ValueError("prime p, t>=1 and positive rational depth required")
    k = t-1
    if not k:
        return dict(p=p,t=t,N=0,residue_precision=1,residue_modulus=p)
    W = max(r*i-factorial_valuation(i,p) for i in range(t))
    j, power = 0, 1
    while not (r*power-k*j > W and r*power*(p-1) > k):
        j += 1
        power *= p
    def a(n):
        total = 0
        while n:
            n //= p
            total += min(k,n)
        return total
    N = max(n for n in range(power) if r*n-a(n) <= W)
    baseline = sum(factorial_valuation(i,p) for i in range(t))
    largest = sum(factorial_valuation(i,p) for i in range(N-t+1,N+1))
    precision = 1+largest-baseline
    return dict(p=p,t=t,N=N,residue_precision=precision,
                residue_modulus=p**precision,cutoff_search_limit=power-1)


def power_columns(support: list[int], N: int, falling=False) -> list[list[Fraction]]:
    """Coordinates of 1,T,...,T^N modulo prod(T-e), by multiplication."""
    t = len(support)
    poly = [1]
    for e in support:
        q = [0] * (len(poly) + 1)
        for i, a in enumerate(poly):
            q[i] -= e * a
            q[i + 1] += a
        poly = q
    rows = [[Fraction(0) for _ in range(N + 1)] for _ in range(t)]
    col = [1] + [0] * (t - 1)
    for k in range(N + 1):
        for i, a in enumerate(col):
            rows[i][k] = Fraction(a)
        last = col[-1]
        next_col = [-poly[0] * last] + [col[i-1] - poly[i]*last for i in range(1,t)]
        col = [a-k*b for a,b in zip(next_col,col)] if falling else next_col
    return rows


def _pivot(rows, inverse, basis, i, j):
    a = rows[i][j]
    row = [x / a for x in rows[i]]
    inv = [x / a for x in inverse[i]]
    for h in range(len(rows)):
        if h != i and rows[h][j]:
            c = rows[h][j]
            rows[h] = [x - c*y for x,y in zip(rows[h], row)]
            inverse[h] = [x - c*y for x,y in zip(inverse[h], inv)]
    rows[i], inverse[i], basis[i] = row, inv, j


def _weights(p, N, depth, right_limit=False):
    if depth == "open":
        # Lexicographic intercept and right-hand slope at 1/(p-1).
        return [(Fraction(digit_sum(k,p),p-1), k) for k in range(N+1)]
    r = Fraction(depth)
    if r <= 0:
        raise ValueError("closed disk depth must be positive")
    return [(r*k-factorial_valuation(k,p), k if right_limit else 0) for k in range(N+1)]


def solve(support, p, depth="open", make_witness=True, method="auto", right_limit=False):
    E = sorted(int(e) for e in support)
    if not E or len(set(E)) != len(E) or E[0] < 0:
        raise ValueError("support must be nonempty, distinct and nonnegative")
    # A monomial factor is a unit on the disks in question.
    shift = E[0]
    E = [e-shift for e in E]
    t = len(E)
    if method not in ("auto","exponential","binomial"):
        raise ValueError("unknown method")
    exp_valid = depth == "open" or Fraction(depth)>Fraction(1,p-1)
    if method == "auto":
        method = "exponential" if exp_valid else "binomial"
    if method == "exponential" and not exp_valid:
        raise ValueError("exponential method needs depth>1/(p-1)")
    if method == "binomial":
        base = Fraction(1,p-1) if depth=="open" else Fraction(depth)
        bounds = lenstra_cutoff(p,t,base)
    else:
        bounds = cutoff(p,t)
    N = bounds["N"]
    rows = power_columns(E,N,falling=(method=="binomial"))
    inverse = [[Fraction(i==j) for j in range(t)] for i in range(t)]
    basis = list(range(t))
    # Falling factorials are a unit triangular basis, not the power basis.
    if method == "binomial":
        for i in range(t):
            _pivot(rows,inverse,basis,i,i)
    weights = _weights(p,N,depth,right_limit)
    pivots = 0

    def change(i,j):
        a,b = weights[j]
        c,d = weights[basis[i]]
        return (valuation(rows[i][j],p)+a-c, b-d)

    while True:
        best, where = (Fraction(0),0), None
        for j in range(N+1):
            if j in basis:
                continue
            for i in range(t):
                if rows[i][j]:
                    z = change(i,j)
                    if z < best:
                        best, where = z, (i,j)
        if where is None:
            break
        _pivot(rows,inverse,basis,*where)
        pivots += 1

    admissible = set(basis)
    for j in range(N+1):
        if j not in admissible and any(rows[i][j] and change(i,j)==(0,0) for i in range(t)):
            admissible.add(j)
    maximum = max(admissible)
    if maximum not in basis:
        i = next(i for i in range(t) if rows[i][maximum] and change(i,maximum)==(0,0))
        _pivot(rows,inverse,basis,i,maximum)
    i = basis.index(maximum)
    output = {"support":[e+shift for e in E],"normalized_support":E,
              "depth":str(depth),"right_limit":right_limit,"method":method,
              "maximum":maximum,"minimum_basis":sorted(basis),
              "indices_in_minimum_bases":sorted(admissible),"improving_pivots":pivots,
              **bounds}
    # Validity endpoint of this minimum basis as the radius depth increases.
    endpoints = []
    for j in range(N+1):
        for h in range(t):
            if j < basis[h] and rows[h][j]:
                endpoints.append(Fraction(valuation(rows[h][j],p)
                    -factorial_valuation(j,p)+factorial_valuation(basis[h],p),basis[h]-j))
    output["basis_right_endpoint"] = str(min(endpoints)) if endpoints else "infinity"
    if make_witness:
        # Lagrange cardinal polynomials give the coefficient of each X^e.
        functional = inverse[i]
        coeffs = []
        for j,e in enumerate(E):
            q, denominator = [1], 1
            for h,f in enumerate(E):
                if h == j:
                    continue
                v = [0]*(len(q)+1)
                for k,a in enumerate(q):
                    v[k] -= f*a
                    v[k+1] += a
                q = v
                denominator *= e-f
            coeffs.append(sum(functional[k]*a for k,a in enumerate(q))/denominator)
        denominator = math.lcm(*(x.denominator for x in coeffs))
        integers = [int(x*denominator) for x in coeffs]
        common = math.gcd(*integers)
        integers = [x//common for x in integers]
        output["witness_coefficients"] = integers
    return output


def exponential_profile(support,p):
    """All exact closed-disk chambers strictly above the exponential boundary."""
    left = Fraction(1,p-1)
    result = []
    while True:
        row = solve(support,p,"open" if not result else left,False,right_limit=True)
        endpoint = row["basis_right_endpoint"]
        if endpoint == "infinity":
            result.append(dict(left=str(left),right=endpoint,maximum=row["maximum"]))
            break
        right = Fraction(endpoint)
        assert right > left, (left,right,row)
        at = solve(support,p,right,False)["maximum"]
        assert at == row["maximum"], (support,p,left,right,row["maximum"],at)
        result.append(dict(left=str(left),right=str(right),maximum=row["maximum"]))
        left = right
    merged = []
    for row in result:
        if merged and merged[-1]["maximum"]==row["maximum"]:
            merged[-1]["right"]=row["right"]
        else:
            merged.append(row.copy())
    return merged


def newton_count(support, coefficients, p, depth="open"):
    """Independent check from the finite polynomial F(1+Y), no exp series."""
    shift = min(support)
    support = [e-shift for e in support]
    degree = max(support)
    values = [sum(c*math.comb(e,k) for e,c in zip(support,coefficients) if e>=k)
              for k in range(degree+1)]
    if depth == "open":
        # At the boundary, roots strictly inside correspond to the FIRST minimum.
        w = [(valuation(a,p)+Fraction(k,p-1), k) if a else None
             for k,a in enumerate(values)]
        return min((x for x in w if x is not None))[1]
    r = Fraction(depth)
    w = [valuation(a,p)+r*k if a else None for k,a in enumerate(values)]
    v = min(x for x in w if x is not None)
    return max(k for k,x in enumerate(w) if x==v)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prime", type=int, required=True)
    parser.add_argument("--support", required=True, help="comma-separated nonnegative exponents")
    parser.add_argument("--depth", default="open", help="rational depth, or open")
    parser.add_argument("--no-witness", action="store_true")
    parser.add_argument("--method",choices=["auto","exponential","binomial"],default="auto")
    parser.add_argument("--profile",action="store_true",help="all depths above the exponential boundary")
    args = parser.parse_args()
    E = [int(x) for x in args.support.split(",")]
    if args.profile:
        print(json.dumps(exponential_profile(E,args.prime),indent=2))
        return
    result = solve(E,args.prime,args.depth,not args.no_witness,args.method)
    if not args.no_witness and max(E)-min(E) <= 10000:
        result["direct_newton_check"] = newton_count(E,result["witness_coefficients"],args.prime,args.depth)
        assert result["direct_newton_check"] == result["maximum"]
    print(json.dumps(result,indent=2))


if __name__ == "__main__":
    main()
