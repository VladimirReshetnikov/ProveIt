#!/usr/bin/env python3
"""Exact finite diagnostics for the two proved adapters (standard library).

The universal proofs are NORMALIZATION.md and PENTAGONAL_GUARD.md.
The diagnostics do not search for ZFC refutations or certify consistency.
"""
from fractions import Fraction
from itertools import product
from math import isqrt
from pathlib import Path
import json


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def pell(A, n):
    """Return chi_A(n), psi_A(n) by binary powering of a quadratic unit."""
    delta = A*A - 1
    x, y = 1, 0
    a, b = A, 1
    while n:
        if n & 1:
            x, y = x*a + delta*y*b, x*b + y*a
        a, b = a*a + delta*b*b, 2*a*b
        n >>= 1
    return x, y


def normalized_cases():
    rows = []
    for A, R in ((2, 3), (8, 3), (14, 3), (20, 3), (2, 7)):
        delta = A*A-1
        D, c = pell(A, R)
        m = R*c
        f, I = pell(A, m)
        require(I % (c*c) == 0, "normalized ordinate is not divisible by c^2")
        i = I//(c*c)
        require(i > 0 and i % 2 == 1, "normalized scale is not positive odd")
        r = (i-1)//2
        old_i = delta*i
        old_r = (old_i-1)//2
        M = delta*I
        require(old_i == 2*old_r+1, "old odd scale reconstruction failed")
        require(M == (2*old_r+1)*c*c, "old strong coordinate mismatch")
        require(M*M == delta*(f*f-1), "ordinary strong equation failed")
        xx, yy = pell(M, R)
        require(xx % M == 0, "odd-index abscissa quotient not integral")
        V = xx//M
        numerator = V+c+R*f*f
        require(numerator % (c*f*f) == 0, "squared-modulus T not integral")
        T = numerator//(c*f*f)
        require(T > 0 and yy > V > 1, "auxiliary positivity failed")
        require(V == f*f*(c*T-R)-c, "new auxiliary definition mismatch")
        old_T = f*T
        require(V == f*c*old_T-f*f*R-c, "old CRT definition mismatch")
        require(M*M*V*V-(M*M-1)*yy*yy == 1, "auxiliary Pell identity failed")
        require((f*f)%3 == 1 and (D*D)%3 == 1 and (yy*yy)%3 == 1,
                "canonical 3-adic unit check failed")
        rows.append({"A": A, "R": R, "c": c, "m": m,
                     "normalized_i_bits": i.bit_length(), "f_bits": f.bit_length(),
                     "auxiliary_y_bits": yy.bit_length(), "status": "PASS"})
    return rows


L = ((1, 2, 2), (2, 1, -2), (-2, 2, -1))


def matvec(v):
    return tuple(sum(a*b for a, b in zip(row, v)) for row in L)


def norm(v):
    return sum(t*t for t in v)


def choose_lift(v):
    for signs in product((-1, 1), repeat=3):
        w = tuple(s*x for s, x in zip(signs, v))
        if (w[0]-w[1]-w[2]) % 3:
            z = matvec(w)
            require(norm(z) == 9*norm(v), "norm9 identity failed")
            require(all(x%3 for x in z), "lift lost primitivity")
            return z
    raise AssertionError("no primitive sign choice")


def three_odd_squares(M):
    for x in range(1, isqrt(M)+1, 2):
        for y in range(1, isqrt(M-x*x)+1, 2):
            rem = M-x*x-y*y
            z = isqrt(rem)
            if z*z == rem:
                return x, y, z
    raise AssertionError("no three-square representation found")


def pentagonal_cases(limit=3000):
    gram = [[sum(L[k][i]*L[k][j] for k in range(3)) for j in range(3)]
            for i in range(3)]
    require(gram == [[9, 0, 0], [0, 9, 0], [0, 0, 9]], "matrix Gram mismatch")
    residue_cases = 0
    for v in product(range(3), repeat=3):
        if any(v):
            choose_lift(v)
            residue_cases += 1
    max_lifts = 0
    for N in range(1, limit+1):
        M = 24*N-21
        M0, e = M, 0
        while M0 % 9 == 0:
            M0 //= 9
            e += 1
        v = three_odd_squares(M0)
        require(all(x%2 for x in v) and any(x%3 for x in v), "base vector invalid")
        for _ in range(e):
            v = choose_lift(v)
        require(norm(v) == M and all(x%2 and x%3 for x in v), "final vector invalid")
        v = tuple(x if x%6 == 5 else -x for x in v)
        require(all(x%6 == 5 for x in v), "orientation mod6 failed")
        u, w, t = ((x+1)//6 for x in v)
        S = 24*N-21-(6*u-1)**2-(6*w-1)**2
        require(S == (6*t-1)**2 and S%3 == 1, "positivity radicand failed")
        max_lifts = max(max_lifts, e)
    return {"N_range": [1, limit], "primitive_mod3_vectors": residue_cases,
            "max_norm9_lifts": max_lifts, "gram_matrix": gram, "status": "PASS"}


def rational_pell_cases():
    checked = roots = 0
    for Q in range(2, 61):
        for V in range(-40, 41):
            y2 = Fraction(Q*V*V-1, Q-1)
            checked += 1
            if y2 < 0:
                continue
            a, b = isqrt(y2.numerator), isqrt(y2.denominator)
            if a*a == y2.numerator and b*b == y2.denominator:
                roots += 1
                require(b == 1, "nonintegral rational Pell root found")
    return {"assignments": checked, "rational_square_cases": roots, "status": "PASS"}


def main():
    result = {"status": "PASS", "normalization": normalized_cases(),
              "pentagonal_guard": pentagonal_cases(),
              "rational_pell": rational_pell_cases(),
              "scope": "Finite exact diagnostics supplement the unbounded proofs; no consistency search."}
    path = Path(__file__).with_name("ADAPTER_CHECKS.json")
    path.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
