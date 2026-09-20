#!/usr/bin/env python3
"""Exact algorithms for OEIS A281434 (Python 3.9+, standard library).

The optional --method modular requires NumPy. It is STILL deterministic and
exact: every zero residue is checked by a separate integer coefficient formula.
No zero/nonzero decision is made using floating-point arithmetic.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from typing import Dict, Iterator, List, Tuple

Monomial = Tuple[int, int, int]  # (power of x^x, power of 1/x, power of log x)
Polynomial = Dict[Monomial, int]


def validate_index(n: int) -> None:
    if not isinstance(n, int) or isinstance(n, bool) or n < 0:
        raise ValueError("n must be a nonnegative integer")


def upper_bound(n: int) -> int:
    validate_index(n)
    return 1 if n == 0 else (2*n**3 + 3*n*n + 4*n) // 3


def lower_bound(n: int) -> int:
    validate_index(n)
    if n == 0:
        return 1
    return (7*n**3 + 39*n*n + 26*n + 3*(n & 1)*(n-1)) // 24


def log_range(n: int, k: int, j: int) -> range:
    """The proved candidate interval of logarithm exponents."""
    if not (1 <= k <= n and 0 <= j <= n):
        return range(0)
    lo = max(0, k-j)
    hi = n+k if j == 0 else min(n+k-j-1, 2*(n-j))
    return range(lo, hi+1)


def next_polynomial(p: Polynomial) -> Polynomial:
    """Apply the seven exact coefficient transitions."""
    q: Dict[Monomial, int] = defaultdict(int)
    for (k, j, ell), c in p.items():
        q[k+1, j, ell+2] += c
        q[k+1, j, ell+1] += c
        q[k+1, j+1, ell] += c
        if k:
            kc = k*c
            q[k, j, ell+1] += kc
            q[k, j, ell] += kc
        if j:
            q[k, j+1, ell] -= j*c
        if ell:
            q[k, j+1, ell-1] += ell*c
    return {key: c for key, c in q.items() if c}


def polynomial(n: int) -> Polynomial:
    validate_index(n)
    p: Polynomial = {(0, 0, 0): 1}
    for _ in range(n):
        p = next_polynomial(p)
    return p


def terms(limit: int) -> Iterator[int]:
    """Yield a(0), ..., a(limit), using packed monomial keys.

    O(limit**4) integer arithmetic operations and O(limit**3) live integers.
    This is the dependency-free reference implementation used for the b-file.
    """
    validate_index(limit)
    b, cbase = limit+2, 2*limit+3
    du, dv = b*cbase, cbase
    p = {0: 1}
    yield 1
    for _ in range(limit):
        q: Dict[int, int] = defaultdict(int)
        for key, value in p.items():
            kj, ell = divmod(key, cbase)
            k, j = divmod(kj, b)
            q[key+du+2] += value
            q[key+du+1] += value
            q[key+du+dv] += value
            if k:
                kv = k*value
                q[key+1] += kv
                q[key] += kv
            if j:
                q[key+dv] -= j*value
            if ell:
                q[key+dv-1] += ell*value
        p = {key: value for key, value in q.items() if value}
        yield len(p)


def a(n: int) -> int:
    validate_index(n)
    answer = 1
    for answer in terms(n):
        pass
    return answer


def _times_linear(p: Tuple[int, ...], constant: int) -> Tuple[int, ...]:
    """Coefficient vector of (z+constant)*p(z), with exact integers."""
    out = [0]*(len(p)+1)
    for i, value in enumerate(p):
        out[i] += constant*value
        out[i+1] += value
    return tuple(out)


class CoefficientOracle:
    """Independent exact formula, not the differentiation recurrence.

    Cached Q[j,r](z) = product(i=0..j-1)(z-i) * product(i=1..r)(z+i).
    T(d,p;q) is a noncentral Stirling number of the second kind.
    """
    def __init__(self) -> None:
        self._q_rows: Dict[int, List[Tuple[int, ...]]] = {}
        self._t_rows: Dict[int, List[Tuple[int, ...]]] = {}
        self._binomial_rows: List[Tuple[int, ...]] = [(1,)]

    def binomial(self, n: int, k: int) -> int:
        if k < 0 or k > n:
            return 0
        rows = self._binomial_rows
        while len(rows) <= n:
            prev = rows[-1]
            rows.append((1,) + tuple(prev[i-1]+prev[i]
                                     for i in range(1, len(prev))) + (1,))
        return rows[n][k]

    def q_poly(self, j: int, r: int) -> Tuple[int, ...]:
        if j not in self._q_rows:
            p = (1,)
            for i in range(j):
                p = _times_linear(p, -i)
            self._q_rows[j] = [p]
        rows = self._q_rows[j]
        while len(rows) <= r:
            rows.append(_times_linear(rows[-1], len(rows)))
        return rows[r]

    def noncentral_stirling(self, d: int, p: int, q: int) -> int:
        if p < 0 or p > d:
            return 0
        if p == d:
            return 1
        if p == 0:
            return q**d
        rows = self._t_rows.setdefault(q, [(1,)])
        while len(rows) <= d:
            prev = rows[-1]
            new = [q*prev[0]]
            for i in range(1, len(prev)):
                new.append((q+i)*prev[i] + prev[i-1])
            new.append(1)
            rows.append(tuple(new))
        return rows[d][p]

    def coefficient(self, n: int, k: int, j: int, ell: int) -> int:
        validate_index(n)
        if n == 0:
            return int((k, j, ell) == (0, 0, 0))
        if ell not in log_range(n, k, j):
            return 0
        d = n-j
        h = d+k-ell
        total = 0
        q_min = max(0, k-ell, k-d)
        q_max = min(k, h, j)
        for q in range(q_min, q_max+1):
            s, r = ell-k+q, h-q
            poly = self.q_poly(j, r)
            if h >= len(poly) or not poly[h]:
                continue
            total += (self.binomial(n, s) * self.binomial(h, q)
                      * self.noncentral_stirling(d, k-q, q) * poly[h])
        return total


def modular_polynomial(n: int, modulus: int = 1_000_000_007):
    """Dense, vectorized recurrence in Z/modulus Z. Requires NumPy.

    The integer-size checks prevent signed int64 overflow before reduction.
    Primality of modulus is NOT needed for correctness.
    """
    validate_index(n)
    if not isinstance(modulus, int) or isinstance(modulus, bool) or modulus < 2:
        raise ValueError("modulus must be an integer >= 2")
    if (10*n+10)*modulus >= 2**63:
        raise ValueError("n and modulus are too large for safe int64 arithmetic")
    try:
        import numpy as np
    except ImportError as exc:
        raise RuntimeError("The modular method requires NumPy") from exc
    p = np.ones((1, 1, 1), dtype=np.int64)
    for m in range(n):
        s = m+1
        width = 2*m+1
        out = np.zeros((s+1, s+1, width+2), dtype=np.int64)
        out[1:s+1, :s, 2:width+2] += p
        out[1:s+1, :s, 1:width+1] += p
        out[1:s+1, 1:s+1, :width] += p
        k = np.arange(s, dtype=np.int64)[:, None, None]
        kp = k*p
        out[:s, :s, 1:width+1] += kp
        out[:s, :s, :width] += kp
        j = np.arange(s, dtype=np.int64)[None, :, None]
        out[:s, 1:s+1, :width] -= j*p
        if width > 1:
            ell = np.arange(1, width, dtype=np.int64)[None, None, :]
            out[:s, 1:s+1, :width-1] += ell*p[:, :, 1:]
        out %= modulus
        p = out
    return p


def a_modular(n: int, modulus: int = 1_000_000_007,
              *, details: bool = False):
    """Deterministically exact count: modular sieve + integer zero checks.

    Every nonzero residue certifies a nonzero integer coefficient. Every zero
    residue INSIDE the candidate envelope is tested with CoefficientOracle.
    No probabilistic assumption or unproved support conjecture is used.
    """
    validate_index(n)
    if n == 0:
        return (1, [], 0) if details else 1
    import numpy as np
    p = modular_polynomial(n, modulus)
    oracle = CoefficientOracle()
    holes: List[Monomial] = []
    candidates = 0
    for k in range(1, n+1):
        for j in range(n+1):
            rr = log_range(n, k, j)
            for offset in np.flatnonzero(p[k, j, rr.start:rr.stop] == 0):
                ell = rr.start + int(offset)
                candidates += 1
                if oracle.coefficient(n, k, j, ell) == 0:
                    holes.append((k, j, ell))
    answer = upper_bound(n)-len(holes)
    return (answer, holes, candidates) if details else answer


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int, help="nonnegative derivative order")
    parser.add_argument("--method", choices=("exact", "modular"), default="exact")
    parser.add_argument("--prefix", action="store_true", help="print b-file lines 0..n")
    parser.add_argument("--holes", action="store_true", help="show all missing candidate monomials")
    parser.add_argument("--modulus", type=int, default=1_000_000_007)
    args = parser.parse_args()
    try:
        validate_index(args.n)
        if args.prefix:
            if args.method != "exact" or args.holes:
                parser.error("--prefix uses --method exact and does not accept --holes")
            for i, value in enumerate(terms(args.n)):
                print(i, value, flush=True)
        elif args.method == "modular":
            value, holes, candidates = a_modular(args.n, args.modulus, details=True)
            print(value)
            if args.holes:
                print("modular candidates:", candidates)
                print("actual holes (k,j,ell):", holes)
        elif args.holes:
            p = polynomial(args.n)
            print(len(p))
            print("actual holes (k,j,ell):", [
                (k, j, ell) for k in range(1, args.n+1)
                for j in range(args.n+1) for ell in log_range(args.n, k, j)
                if (k, j, ell) not in p])
        else:
            print(a(args.n))
    except (ValueError, RuntimeError, ImportError) as exc:
        parser.error(str(exc))


if __name__ == "__main__":
    main()
