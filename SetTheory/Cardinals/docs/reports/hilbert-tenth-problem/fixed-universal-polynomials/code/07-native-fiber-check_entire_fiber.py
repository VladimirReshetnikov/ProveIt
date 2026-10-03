#!/usr/bin/env python3
"""Independent exact-integer auxiliary checks, not an astronomical native tuple.

No upstream program is imported or executed. Every check survives python -O.
Default replay compares a deterministic receipt; --write refreshes that receipt.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from functools import lru_cache
from math import gcd
from pathlib import Path

ROOT = Path(__file__).resolve().parent
REQUIRED_SOURCE_NAMES = ['EXPLORATION_FIXED_MINUS_INDEX_PARITY.md', 'EXPLORATION_ODD_INDEX_PELL_SIGNS.md', 'PELL_RELAXED_AUXILIARY_PROOF.md', 'native_binary_masked_selection63.md', 'native_controller_binary_selector56.md']


def require(value, message):
    if not value:
        raise RuntimeError(message)


def pell(base, n, modulus=None):
    """Binary powering in Z[sqrt(base**2-1)], optionally modulo an integer."""
    require(base >= 2 and n >= 0, 'invalid Pell parameters')
    delta = base * base - 1
    x, y, u, v = 1, 0, base, 1
    while n:
        if n & 1:
            x, y = x*u + delta*y*v, x*v+y*u
            if modulus:
                x, y = x % modulus, y % modulus
        u, v = u*u+delta*v*v, 2*u*v
        if modulus:
            u, v = u % modulus, v % modulus
        n //= 2
    return x, y


def check_divisibility():
    checks, rank_eligible = 0, 0
    for A in range(2, 13):
        delta = A*A-1
        for p in (3, 7, 11, 15, 19):
            d, c = pell(A, p)
            g = gcd(c, delta)
            require(g == gcd(p, delta), 'gcd(c,delta) identity')
            M = p*c//g
            require(M % c == 0 and M > 2*p, 'index lower bound')
            rank_eligible += int(c > A*delta*delta)
            ks = set(range(1, 31))
            for multiple in range(1, 5):
                center = multiple*(c//g)
                ks.update(k for k in range(max(1, center-2), center+3))
            for k in sorted(ks):
                m = p*k
                _, psi_mod = pell(A, m, c*c)
                divisible = delta*psi_mod % (c*c) == 0
                require(divisible == (m % M == 0), 'exact main-index progression')
                require((psi_mod//c - k*pow(d, k-1, c)) % c == 0,
                        'composition quotient congruence')
                checks += 1
    return {'parameter_pairs': 55, 'rank_bound_eligible_pairs': rank_eligible,
            'exact_modular_divisibility_checks': checks}


def check_materialized_auxiliary():
    rows = []
    cases = [(2, 3, 1), (2, 3, 2), (2, 3, 3), (3, 3, 1), (2, 7, 1)]
    for A, p, multiple in cases:
        delta = A*A-1
        _, c = pell(A, p)
        M = p*c//gcd(c, delta)
        m = M*multiple
        f, psi = pell(A, m)
        R = delta*psi
        require(R % (c*c) == 0, 'positive integral i')
        i = R//(c*c)
        require(i > 0 and R > f and R*R == delta*(f*f-1), 'main auxiliary norm')
        ns = [p] if p == 7 else [p, 4*m-p, 4*m+p]
        for n in ns:
            x, y = pell(R, n)
            require(x % R == 0, 'positive integral U')
            U = x//R
            require((U+p) % c == 0 and (U+c) % f == 0, 'minus congruences')
            j, o = (U+p)//c, (U+c)//f
            require(min(f, i, j, o, y) > 0, 'five-coordinate positivity')
            require(j*c-p == o*f-c == U, 'source U identity')
            require(R*R*(U*U-y*y) == 1-y*y, 'normalized source norm')
            require(max(f, i, j, o) <= y and c*c < y, 'height domination')
            rows.append({'A': A, 'p': p, 'm': m, 'n': n,
                         'max_height_bits': y.bit_length(),
                         'rank_bound_holds': c > A*delta*delta})
        if p == 7:
            # Full n=4m+-p would have billions of bits here. Check exactly
            # the needed polynomial congruences in their finite quotient rings.
            for n in (4*m-p, 4*m+p, 8*m-p, 8*m+p):
                mod = R*c*f
                x_mod, _ = pell(R, n, mod)
                require(x_mod % R == 0, 'normalized x divisibility modulo Rcf')
                U_mod = x_mod//R
                require((U_mod+p) % c == 0 and (U_mod+c) % f == 0,
                        'noncanonical large-index congruences')
    return rows


def check_residue_exhaustion():
    rows = []
    for A, p, multiple in [(2, 3, 1), (2, 3, 2), (3, 3, 1)]:
        delta = A*A-1
        _, c = pell(A, p)
        m = multiple*p*c//gcd(c, delta)
        f, psi = pell(A, m)
        R = delta*psi
        modulus = R*c*f
        x, y = 1, 0
        accepted = []
        for n in range(1, 8*m+1):
            x, y = (R*x+(R*R-1)*y) % modulus, (x+R*y) % modulus
            valid = x % R == 0 and (x//R+p) % c == 0 and (x//R+c) % f == 0
            expected = n % (4*m) in {p, 4*m-p}
            require(valid == expected, 'full bounded congruence exhaustion')
            if valid:
                accepted.append(n)
        rows.append({'A': A, 'p': p, 'm': m, 'tested_indices': 8*m,
                     'accepted_indices': accepted})
    return rows


def check_exact_count():
    # Small concrete auxiliary model; it is not asserted to be a complete
    # padded native witness. It satisfies the classification/count hypotheses.
    A, p = 2, 3
    delta = A*A-1
    _, c = pell(A, p)
    M = p*c//gcd(c, delta)

    @lru_cache(None)
    def R_at(l):
        return delta*pell(A, M*l)[1]

    def height(l, n):
        return pell(R_at(l), n)[1]

    def inverse_index(l, H):
        lo, hi = 0, 1
        while height(l, hi) <= H:
            lo, hi = hi, 2*hi
        while hi-lo > 1:
            mid = (lo+hi)//2
            if height(l, mid) <= H:
                lo = mid
            else:
                hi = mid
        return lo

    thresholds = [height(1, p), height(2, p), height(3, p),
                  height(1, 4*M-p), height(1, 4*M+p), height(2, 8*M-p)]
    rows = []
    for index, threshold in enumerate(thresholds, 1):
        for offset in (-1, 0, 1):
            H = threshold+offset
            counted = direct = baseline = 0
            l = 1
            while height(l, p) <= H:
                m = M*l
                T = inverse_index(l, H)
                count = (T+4*m-p)//(4*m)+(T+p)//(4*m)
                counted += count
                baseline += 1
                direct += 1
                k = 1
                while True:
                    lower, upper = 4*m*k-p, 4*m*k+p
                    # Exact inverse T already certifies every excluded n;
                    # do not construct a huge, manifestly over-height tuple.
                    if lower > T:
                        break
                    require(height(l, lower) <= H, 'accepted lower height')
                    direct += 1
                    if upper <= T:
                        require(height(l, upper) <= H, 'accepted upper height')
                        direct += 1
                    k += 1
                l += 1
            require(counted == direct, 'exact count versus direct pair enumeration')
            rows.append({'threshold': index, 'offset': offset,
                         'height_bits': H.bit_length(), 'total': counted,
                         'baseline': baseline, 'nonbaseline': counted-baseline})
    return {'A': A, 'p': p, 'M0': M, 'boundary_tests': rows}


def build_receipt():
    return {
        'status': 'PASS',
        'scope': 'Independent exact auxiliary examples, modular index tests and finite pair counts; not full native tuple materialization or a proof by enumeration',
        'divisibility': check_divisibility(),
        'materialized_auxiliary_tuples': check_materialized_auxiliary(),
        'residue_exhaustion': check_residue_exhaustion(),
        'finite_count': check_exact_count(),
        'source_sha256': {name: hashlib.sha256((ROOT/'source'/name).read_bytes()).hexdigest()
                          for name in REQUIRED_SOURCE_NAMES},
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    receipt = build_receipt()
    target = ROOT/'CHECK-RECEIPT.json'
    if args.write:
        target.write_text(json.dumps(receipt, indent=2)+'\n')
    else:
        require(json.loads(target.read_text()) == receipt, 'receipt mismatch')
    print('PASS: exact divisibility, auxiliary norms/residues, height domination and finite count boundary checks')


if __name__ == '__main__':
    main()
