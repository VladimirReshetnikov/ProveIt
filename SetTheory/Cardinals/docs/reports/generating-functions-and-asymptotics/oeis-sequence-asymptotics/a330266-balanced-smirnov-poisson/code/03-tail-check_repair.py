#!/usr/bin/env python3
"""Exact, independently reproducible checks for the Smirnov tail repair.

Requires Python 3 and SymPy. Writes no repository files. The proof is in
repair_note.tex; these finite checks are diagnostics, not substitutes for the proof.
"""
from __future__ import annotations

import json
import hashlib
import argparse
from math import comb, factorial
from fractions import Fraction
from pathlib import Path
import sympy as s

ROOT = Path(__file__).resolve().parent
k, v, m, i = s.symbols('k v m i')
lam = k - 1


def require(condition, message):
    if not condition:
        raise ValueError(message)


def verify_sources():
    manifest = json.loads((ROOT/'source_manifest.json').read_text())
    for row in manifest['files']:
        data = (ROOT/'source'/row['file']).read_bytes()
        digest = hashlib.sha1(f'blob {len(data)}\0'.encode()+data).hexdigest()
        require(digest == row['blob_sha'], f"Source blob mismatch: {row['file']}")


def mul(a, b):
    c = [0] * (len(a) + len(b) - 1)
    for j, x in enumerate(a):
        for ell, y in enumerate(b):
            c[j + ell] += x * y
    return c


def finite_moment_checks():
    total = 0
    for K in range(2, 11):
        R = [factorial(j) * comb(K, j) * comb(K - 1, j) for j in range(K)]
        power = [1]
        for n in range(1, 26):
            power = mul(power, R)
            N = K * n
            falling = 1
            for j, a in enumerate(power):
                if j:
                    falling *= N - j + 1
                require(a * factorial(j) <= (K - 1)**j * falling,
                        f'Moment inequality failed at k={K}, n={n}, m={j}')
                total += 1
    return total


def scalar_remainder_checks():
    total = 0
    for N in range(2, 81):
        falling = 1
        for M in range(N):
            if M:
                falling *= N-M+1
            exact = Fraction(N**M, falling)
            H = [1] + [0]*6
            for x in range(M):
                for r in range(1,7):
                    H[r] += x*H[r-1]
            partial = Fraction(0)
            for q in range(6):
                partial += Fraction(H[q], N**q)
                rem = exact-partial
                bound = exact*Fraction(H[q+1], N**(q+1))
                require(0 <= rem <= bound, f'Scalar remainder N={N}, M={M}, q={q}')
                total += 1
    return total


def formal_coefficients(order=4, inject_error=False):
    # Coefficients a_j work for each integer k, including j >= k (zero).
    a = [s.prod(k-t for t in range(j)) * s.prod(k-1-t for t in range(j))
         / s.factorial(j) for j in range(order+2)]
    ell = [s.S.Zero]
    for j in range(1, order+2):
        ell.append(s.factor(a[j] - sum(t*ell[t]*a[j-t] for t in range(1,j))/j))

    A = [s.S.One]
    for j in range(1, order+1):
        A.append(s.expand(sum(t * ell[t+1]/k * v**(t+1) * A[j-t]
                              for t in range(1,j+1))/j))

    H = [s.S.One]
    power_sums = [s.S.Zero] + [s.summation(i**r, (i, 0, m-1)) for r in range(1,order+1)]
    for r in range(1,order+1):
        H.append(s.expand(sum(power_sums[t]*H[r-t] for t in range(1,r+1))/r))

    def apply_H(r, p):
        hp = s.Poly(H[r], m)
        derivs = [p]
        for _ in range(hp.degree()):
            prev = derivs[-1]
            derivs.append(s.expand(v*s.diff(prev,v) + lam*v*prev))
        return s.expand(sum(coef*derivs[mon[0]] for mon,coef in hp.terms()))

    P, Q = [], [s.S.Zero]
    for j in range(order+1):
        raw = s.Poly(sum(apply_H(r,A[j-r]) for r in range(j+1)),v)
        P.append(sum(s.factor(c)*v**mon[0] for mon,c in raw.terms()))
        if j:
            rawlog = s.Poly(s.expand(P[j] - sum(t*Q[t]*P[j-t] for t in range(1,j))/j),v)
            Q.append(sum(s.factor(c)*v**mon[0] for mon,c in rawlog.terms()))
            require(s.Poly(Q[j],v).degree() <= j+1, f'Log degree at order {j}')

    if inject_error:
        Q[3] += v**5
    expected = [s.S.Zero,
        -lam**2*v**2/2,
        lam**2*v**2*(2*(k-2)*v-3)/6,
        -lam**2*v**2*((k**2-6*k+7)*v**2-4*(k-2)*v+2)/4]
    for j in range(1,4):
        require(s.simplify(Q[j]-expected[j]) == 0, f'Log coefficient {j}')
    expected_p = [s.S.One,-lam**2/2,
                  lam**2*(3*k*k-14*k+7)/24,
                  -lam**4*(k*k-10*k+17)/48]
    for j in range(4):
        require(s.simplify(P[j].subs(v,-1)-expected_p[j]) == 0, f'Probability coefficient {j}')
    expected_p4 = lam**2*(15*k**6-330*k**5+2345*k**4-7212*k**3+13313*k**2-10122*k+2183)/5760
    expected_q4minus = -lam**2*(12*k**3-63*k**2+62*k-13)/60
    require(s.simplify(P[4].subs(v,-1)-expected_p4) == 0, 'Fourth probability coefficient')
    require(s.simplify(Q[4].subs(v,-1)-expected_q4minus) == 0, 'Fourth log-probability coefficient')
    return H,P,Q


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--inject-error', action='store_true', help='Corrupt the third-order log coefficient to test rejection')
    args = parser.parse_args()
    verify_sources()
    count = finite_moment_checks()
    remainder_count = scalar_remainder_checks()
    H,P,Q = formal_coefficients(4, inject_error=args.inject_error)
    lines = [f'Exact coefficientwise factorial-moment inequalities checked: {count}',
             f'Exact rational scalar-remainder inequalities checked: {remainder_count}',
             'All general-k logarithmic and probability coefficients through N^-3 agree.',
             'Logarithmic polynomial degree bound checked through N^-4.']
    for j in range(1,5):
        lines += [f'Q_{j}(v) = {s.factor(Q[j])}',
                  f'[N^-{j}] e^(k-1) p = {s.factor(P[j].subs(v,-1))}']
    lines.append('Fourth-order n^-4 probability coefficients:')
    for K in range(2,7):
        lines.append(f'  k={K}: {s.factor(P[4].subs({v:-1,k:K})/K**4)}')
    text = '\n'.join(lines)+'\n'
    print(text)
    (ROOT/'symbolic_checks.txt').write_text(text)
    (ROOT/'coefficients.json').write_text(json.dumps({
        'normalization':'Phi = exp((k-1)v) sum_j P_j(v)/N^j; log Phi = (k-1)v + sum_j Q_j(v)/N^j; N=kn',
        'P':[str(s.factor(p)) for p in P], 'Q':[str(s.factor(q)) for q in Q],
        'H':[str(s.factor(h)) for h in H]},indent=2)+'\n')


if __name__ == '__main__':
    main()
