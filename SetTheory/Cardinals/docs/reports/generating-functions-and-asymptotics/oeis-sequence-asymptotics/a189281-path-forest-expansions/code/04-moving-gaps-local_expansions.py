#!/usr/bin/env python3
"""Exact local all-orders expansions for overlaps of two path forests.

Standard library only. Rod length = number of edges (not vertices).
Coefficients are fractions.Fraction. No floating point enters the engine.
"""
from __future__ import annotations
from collections import defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from math import factorial, comb
from typing import Iterable

Profile = tuple[int, ...]

def stats(p: Profile) -> tuple[int, int, int]:
    k = sum((i + 1) * v for i, v in enumerate(p))
    c = sum(p)
    return k, c, k + c

def pfact(p: Profile) -> int:
    out = 1
    for j in p:
        out *= factorial(j)
    return out

def addp(a: Profile, b: Profile) -> Profile:
    return tuple(x + y for x, y in zip(a, b))

@lru_cache(None)
def profiles(K: int) -> tuple[Profile, ...]:
    """All profiles of edge weight at most K."""
    if K < 0:
        raise ValueError('K must be nonnegative')
    out = []
    def rec(i, left, p):
        if i > K:
            out.append(tuple(p))
            return
        for m in range(left // i + 1):
            rec(i + 1, left - i * m, p + [m])
    rec(1, K, [])
    return tuple(sorted(out, key=lambda p: (stats(p)[0], p)))

def zmul(a, b, K):
    out = defaultdict(Q)
    for p, v in a.items():
        for q, w in b.items():
            r = addp(p, q)
            if stats(r)[0] <= K:
                out[r] += v * w
    return {p: v for p, v in out.items() if v}

@lru_cache(None)
def path_log(N: int, K: int):
    """log T_N(z), T_N the exact interval-tiling polynomial on N vertices."""
    zero = (0,) * K
    f = {}
    for p in profiles(K):
        k, c, v = stats(p)
        if c and v <= N:
            f[p] = Q(factorial(N - k), factorial(N - v) * pfact(p))
    out = defaultdict(Q)
    power = {zero: Q(1)}
    for j in range(1, K + 1):
        power = zmul(power, f, K)
        if not power:
            break
        sign = Q((-1) ** (j + 1), j)
        for p, v in power.items():
            out[p] += sign * v
    return dict(out)

@lru_cache(None)
def local_log_blocks(K: int):
    """L_q = log T_(q+1) - 2 log T_q + log T_(q-1), q=1,...,K."""
    out = []
    for q in range(1, K + 1):
        block = defaultdict(Q)
        for N, sign in [(q + 1, 1), (q, -2), (q - 1, 1)]:
            for p, v in path_log(N, K).items():
                block[p] += sign * v
        block = {p: v for p, v in block.items() if v}
        assert all(stats(p)[0] >= q for p in block)
        out.append(block)
    return tuple(out)

def normalized_tilings(a: Iterable[Q], K: int, M: int):
    """Coefficients of T_F(x*z) at n=1/x, given a_q=S_q(F)/n.

    Returns profile -> list of coefficients of x^0,...,x^M.
    Works for abstract rational a as well as realizable path densities.
    """
    a = tuple(a)
    a = a + (Q(0),) * max(0, K - len(a))
    logf = defaultdict(Q)
    for aq, block in zip(a, local_log_blocks(K)):
        for p, v in block.items():
            logf[p] += aq * v
    zero = (0,) * K
    result = {(zero, 0): Q(1)}
    for p, v in sorted(logf.items()):
        if not v:
            continue
        k, c, _ = stats(p)
        h = c - 1
        if h > M:
            continue
        nxt = defaultdict(Q)
        terms = []
        coeff = Q(1)
        for t in range(K // k + 1):
            if t * h > M:
                break
            if t:
                coeff *= v / t
            terms.append((tuple(t * z for z in p), t * h, t * k, coeff))
        for (r, j), w in result.items():
            kr = stats(r)[0]
            for tp, th, tk, tv in terms:
                if kr + tk <= K and j + th <= M:
                    nxt[(addp(r, tp), j + th)] += w * tv
        result = {key: v for key, v in nxt.items() if v}
    out = {}
    for (p, j), v in result.items():
        out.setdefault(p, [Q(0)] * (M + 1))[j] = v
    return out

def conv(a, b, M):
    out = [Q(0)] * (M + 1)
    for i, v in enumerate(a):
        for j, w in enumerate(b):
            if i + j <= M:
                out[i + j] += v * w
    return out

@lru_cache(None)
def inverse_falling(v: int, M: int):
    """[x^j] prod_(i=0)^(v-1) (1-i*x)^(-1), j <= M."""
    d = [Q(1)] + [Q(0)] * M
    for i in range(1, v):
        d = conv(d, [Q(i ** j) for j in range(M + 1)], M)
    return tuple(d)

def moment_expansions(a, b, theta: int, M: int, K: int | None = None):
    if theta not in (1, 2) or M < 0:
        raise ValueError('theta must be 1 or 2; M must be nonnegative')
    if K is None:
        K = max(1, 2 * M)
    A = normalized_tilings(a, K, M)
    B = normalized_tilings(b, K, M)
    R = [[Q(0)] * (K + 1) for _ in range(M + 1)]
    for p in A.keys() & B.keys():
        k, c, v = stats(p)
        defect = k - c
        if defect > M:
            continue
        z = conv(conv(A[p], B[p], M), inverse_falling(v, M), M)
        factor = theta ** c * pfact(p)
        for j in range(defect, M + 1):
            R[j][k] += factor * z[j - defect]
    return R

def corrections(a, b, theta: int, M: int, extra_check: int = 0):
    """Return B_j(u) as coefficient lists; optionally test vanishing above 2j."""
    a, b = tuple(map(Q, a)), tuple(map(Q, b))
    if not a or not b:
        raise ValueError("Both density vectors must supply at least their one-edge density")
    lam = theta * a[0] * b[0]
    K = max(1, 2 * M + extra_check)
    R = moment_expansions(a, b, theta, M, K)
    out = []
    for j in range(M + 1):
        full = [sum(R[j][k] * (-lam) ** (q-k) / factorial(q-k)
                    for k in range(q+1)) for q in range(K+1)]
        assert all(v == 0 for v in full[2*j+1:]), (j, full)
        out.append(full[:2*j+1])
    return out

def eval_poly(p, u):
    out = 0
    for c in reversed(p):
        out = out * u + c
    return out

def offset_lengths(n: int, r: int) -> list[int]:
    if n < 1 or r < 1 or r > n:
        raise ValueError('Require n >= 1 and 1 <= r <= n')
    return [(n - i) // r + 1 for i in range(1, r+1)]

def densities(lengths: Iterable[int], K: int) -> list[Q]:
    L = tuple(lengths)
    if not L or min(L) < 1:
        raise ValueError('A forest must have at least one positive path length')
    n = sum(L)
    return [Q(sum(max(l-q, 0) for l in L), n) for q in range(1, K+1)]

def exact_tilings(lengths: Iterable[int], K: int):
    """Independent finite product of path-tiling polynomials, integer arithmetic."""
    zero = (0,) * K
    out = {zero: 1}
    for N in lengths:
        local = {}
        for p in profiles(K):
            k, c, v = stats(p)
            if v <= N:
                local[p] = factorial(N-k) // (factorial(N-v) * pfact(p))
        out = zmul(out, local, K)
    return out

def exact_moments(lengths_a, lengths_b, theta, K):
    n = sum(lengths_a)
    if n != sum(lengths_b):
        raise ValueError('Forest orders must agree')
    A, B = exact_tilings(lengths_a, K), exact_tilings(lengths_b, K)
    mu = [Q(0)] * (K+1)
    for p in A.keys() & B.keys():
        k, c, v = stats(p)
        if v <= n:
            mu[k] += Q(theta**c * pfact(p) * A[p] * B[p] * factorial(n-v), factorial(n))
    return mu

def matching_counts(lengths, K):
    p = [1] + [0] * K
    for L in lengths:
        local = [comb(L-j, j) if 2*j <= L else 0 for j in range(K+1)]
        p = [sum(p[i] * local[j-i] for i in range(j+1)) for j in range(K+1)]
    return p

def matching_target_moments(n, r, s, theta, K):
    """Exact moments when s >= n/2, so the value forest is a matching."""
    if 2*s < n:
        raise ValueError('Value forest is not a matching')
    a = matching_counts(offset_lengths(n, r), K)
    b = n - s
    return [Q(theta**k * a[k] * comb(b, k) * factorial(k) * factorial(n-2*k), factorial(n))
            if 2*k <= n and k <= b else Q(0) for k in range(K+1)]

def boundary_polynomial(b, theta, q):
    """H_q=[t^q] theta*B(t)/(1+theta*B(t))."""
    b = [Q(0)] + list(map(Q, b))
    b += [Q(0)] * max(0, q+1-len(b))
    h = [Q(0)] * (q+1)
    for i in range(1, q+1):
        h[i] = theta*b[i] - theta*sum(b[j]*h[i-j] for j in range(1, i))
    return h[q]

def single_path_target_moments(lengths, theta, K):
    """Exact moments against a single value path, via weighted runs of edges."""
    lengths = tuple(lengths)
    if not lengths or min(lengths) < 1 or K < 0 or theta not in (1, 2):
        raise ValueError("Require positive path lengths, K >= 0, and theta in {1, 2}")
    n = sum(lengths)
    total = [1] + [0] * K
    for L in lengths:
        end0 = [1] + [0] * K
        end1 = [0] * (K + 1)
        for _ in range(L - 1):
            nxt0 = [end0[k] + end1[k] for k in range(K + 1)]
            nxt1 = [0] + [theta*end0[k-1] + end1[k-1] for k in range(1,K+1)]
            end0, end1 = nxt0, nxt1
        local = [end0[k] + end1[k] for k in range(K+1)]
        total = [sum(total[i]*local[k-i] for i in range(k+1)) for k in range(K+1)]
    return [Q(total[k] * factorial(n-k), factorial(n)) if k <= n else Q(0)
            for k in range(K+1)]


if __name__ == '__main__':
    a = [Q(1, 2)]
    for theta in (1, 2):
        B = corrections(a, a, theta, 6)
        print('theta =', theta)
        for j, p in enumerate(B):
            print(j, str(eval_poly(p, -1)))

