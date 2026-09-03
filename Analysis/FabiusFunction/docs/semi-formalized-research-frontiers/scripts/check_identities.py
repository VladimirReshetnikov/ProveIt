#!/usr/bin/env python3
"""Numerically check the closed-form identities of the Combinatorial Coefficient Calculus.

Why this exists.  The register tracks whether a result is *formalized*; it says nothing about
whether an unformalized result is *true*.  Of the 179 register rows, 90 are marked `none`,
meaning nothing -- no Lean proof, no gate, in some cases no reader since it was written -- has
ever evaluated them.  That is exactly where a wrong statement survives.

It is not hypothetical.  `thm:second-parity` closed with "S(2n,n) is odd precisely when n is a
power of two", which is false: n = 5 gives S(10,5) = 42525, odd.  Both *displayed equations* of
that theorem were exact, so every formula check passed and the prose around them was still
wrong.  The defect was found by evaluating the claim rather than by reading it.

What this checks is therefore the arithmetic content of statements, at small parameters, with
exact rational arithmetic -- never floating point, so an agreement is an identity check rather
than a numerical coincidence.  It cannot prove a theorem; it can only refute one.  A `PASS`
here means "no counterexample in the tested range", which is weaker than the Lean corpus and
is not a substitute for it.  Its value is that it is cheap enough to run on every change to
the manuscript, and that a false closed form almost never survives it.

Independent of the manuscript by construction: every left-hand side is recomputed from a
definition (a recurrence, a brute-force enumeration over permutations or set partitions, or a
generating-function expansion), never from the formula being tested.

Usage:  python check_identities.py [-v]
Exit status is 1 if any identity fails.
"""
import sys
from fractions import Fraction as F
from itertools import permutations, product
from math import comb, factorial

if hasattr(sys.stdout, 'reconfigure'):
    sys.stdout.reconfigure(encoding='utf-8', errors='replace')

VERBOSE = '-v' in sys.argv
RESULTS = []


def check(label, claim, failures, tested):
    RESULTS.append((label, claim, list(failures), tested))


# --------------------------------------------------------------------- tables
NM = 92          # the parity sweep runs to n = 90; everything else is far smaller
S2 = [[0] * (NM + 2) for _ in range(NM + 2)]
S2[0][0] = 1
C1 = [[0] * (NM + 2) for _ in range(NM + 2)]
C1[0][0] = 1
for n in range(1, NM + 2):
    for k in range(1, n + 1):
        S2[n][k] = k * S2[n - 1][k] + S2[n - 1][k - 1]
        C1[n][k] = (n - 1) * C1[n - 1][k] + C1[n - 1][k - 1]


def bell_complete(xs):
    """B_n(x_1..x_n) from the convolution recurrence, not from any tested formula."""
    n = len(xs)
    B = [F(1)] + [F(0)] * n
    for m in range(1, n + 1):
        B[m] = sum((F(comb(m - 1, i)) * xs[m - 1 - i] * B[i] for i in range(m)), F(0))
    return B[n]


# ------------------------------------------------- thm:second-parity (corrected)
bad, t = [], 0
for n in range(1, 91):
    for k in range(1, n + 1):
        z = n - -((k + 1) // -2)
        w = (k - 1) // 2
        t += 1
        if (S2[n][k] - comb(z, w)) % 2 != 0:
            bad.append(('binomial', n, k))
        if (S2[n][k] % 2 == 1) != (((n - k) & w) == 0):
            bad.append(('bitwise', n, k))
check('thm:second-parity', 'S(n,k) = C(z,w) mod 2, and odd iff (n-k) & floor((k-1)/2) = 0',
      bad, t)

bad, t = [], 0
for n in range(1, 23):
    t += 1
    if (S2[2 * n][n] % 2 == 1) != ((n & (2 * n)) == 0):
        bad.append(n)
check('thm:second-parity (central)',
      'S(2n,n) odd iff n has no two adjacent 1-bits  [NOT iff n is a power of two]', bad, t)

# the false claim this replaced, recorded so the counterexample cannot be lost
bad_pow = [n for n in range(1, 23) if (S2[2 * n][n] % 2 == 1) != (n > 0 and n & (n - 1) == 0)]
check('thm:second-parity (refuted form)',
      'the retracted "power of two" reading is expected to FAIL, and does',
      [] if bad_pow else ['power-of-two form no longer refuted -- investigate'], len(bad_pow))

# ------------------------------------------------------- thm:second-reverse-row
bad, t = [], 0
for m in range(0, 26):
    for n in range(m + 1, 27):
        lhs = (n - (m + 1)) * S2[n][m + 1]
        rhs = sum((factorial(i - 2) * (-1) ** i * comb(m + i, i) if i >= 2 else 0)
                  * (S2[n][m + i] if m + i <= n else 0) for i in range(0, n + 1))
        t += 1
        if lhs != rhs:
            bad.append((m, n))
check('thm:second-reverse-row', '(n-k)S(n,k) = sum (j-2)! C(-k,j) S(n,k+j-1), k = m+1', bad, t)

# ---------------------------------------------------- thm:second-reverse-column
bad, t = [], 0
for n in range(1, 27):
    for k in range(1, n + 1):
        lhs = (n - k) * S2[n][k]
        rhs = sum((-1) ** j * comb(n, j) * (S2[n - j + 1][k] if n - j + 1 >= k else 0)
                  for j in range(2, n - k + 2))
        t += 1
        if lhs != rhs:
            bad.append((n, k))
check('thm:second-reverse-column', '(n-k)S(n,k) = sum (-1)^j C(n,j) S(n-j+1,k)', bad, t)

# -------------------------------------------------------- thm:first-double-sum
bad, t = [], 0
for n in range(1, 9):
    for k in range(1, n + 1):
        tot = F(0)
        for j in range(n, 2 * n - k + 1):
            inner = sum((F((-1) ** (m + n - k) * (1 if j == k else m ** (j - k)),
                           factorial(m) * factorial(j - n - m))
                         for m in range(0, j - n + 1)), F(0))
            tot += F(comb(j - 1, k - 1) * comb(2 * n - k, j)) * inner
        t += 1
        if tot != C1[n][k]:
            bad.append((n, k))
check('thm:first-double-sum', 'c(n,k) as an explicit double sum', bad, t)

# ------------------------------------------ thm:signed-near-diagonal-partition
def _parts(p):
    def rec(r, rem, cur):
        if rem == 0:
            yield dict(cur)
            return
        if r > rem:
            return
        for kr in range(rem // r, -1, -1):
            yield from rec(r + 1, rem - r * kr, cur + ([(r, kr)] if kr else []))
    yield from rec(1, p, [])


bad, t = [], 0
for n in range(1, 9):
    for p in range(0, n):
        tot = F(0)
        for d in _parts(p):
            K = sum(d.values())
            den = 1
            for r, kr in d.items():
                den *= factorial(kr) * factorial(r + 1) ** kr
            tot += F((-1) ** K * factorial(n + K - 1), den)
        t += 1
        if tot / factorial(n - p - 1) != C1[n][n - p] * (-1) ** p:
            bad.append((n, p))
check('thm:signed-near-diagonal-partition', 's(n,n-p) as a sum over partitions of p', bad, t)

# ------------------------------------------------------------ thm:reduced-stirling
def _setparts(n):
    def rec(i, maxb, cur):
        if i == n:
            k = maxb + 1
            blocks = [[] for _ in range(k)]
            for idx, b in enumerate(cur):
                blocks[b].append(idx)
            yield [tuple(b) for b in blocks]
            return
        for b in range(maxb + 2):
            yield from rec(i + 1, max(maxb, b), cur + [b])
    yield from rec(0, -1, [])


def _S_reduced(n, k, d):
    tot = 0
    for blocks in _setparts(n):
        if len(blocks) != k:
            continue
        if all(abs(b[x] - b[y]) >= d
               for b in blocks for x in range(len(b)) for y in range(x + 1, len(b))):
            tot += 1
    return tot


bad, t = [], 0
for d in range(1, 5):
    for n in range(1, 9):
        for k in range(d, n + 1):
            t += 1
            if _S_reduced(n, k, d) != S2[n - d + 1][k - d + 1]:
                bad.append((d, n, k))
check('thm:reduced-stirling', 'S^[d](n,k) = S(n-d+1,k-d+1), by enumerating set partitions',
      bad, t)

bad, t = [], 0
for d in range(1, 4):
    for n in range(1, 6):
        for q in range(0, 5):
            proper = sum(1 for col in product(range(q), repeat=n)
                         if all(not (j - i < d and col[i] == col[j])
                                for i in range(n) for j in range(i + 1, n)))
            rhs = 0
            for k in range(0, n + 1):
                fk = 1
                for i in range(k):
                    fk *= (q - i)
                rhs += _S_reduced(n, k, d) * fk
            t += 1
            if proper != rhs:
                bad.append((d, n, q))
check('chromatic form of S^[d]', 'chi_{G_{n,d}}(q) = sum_k S^[d](n,k) (q)_k', bad, t)

# ------------------------------------------------------------- cor:det-traces-bell
def _det(A):
    A = [r[:] for r in A]
    n = len(A)
    d = F(1)
    for cc in range(n):
        p = next((r for r in range(cc, n) if A[r][cc] != 0), None)
        if p is None:
            return F(0)
        if p != cc:
            A[cc], A[p] = A[p], A[cc]
            d = -d
        d *= A[cc][cc]
        inv = F(1) / A[cc][cc]
        for r in range(cc + 1, n):
            if A[r][cc]:
                f = A[r][cc] * inv
                for kk in range(cc, n):
                    A[r][kk] -= f * A[cc][kk]
    return d


import random
random.seed(20260903)
bad, t = [], 0
for n in range(1, 6):
    for _ in range(10):
        A = [[F(random.randint(-4, 4)) for _ in range(n)] for _ in range(n)]
        P = [[F(int(i == j)) for j in range(n)] for i in range(n)]
        tr = []
        for k in range(1, n + 1):
            P = [[sum(P[i][x] * A[x][j] for x in range(n)) for j in range(n)] for i in range(n)]
            tr.append(-F(factorial(k - 1)) * sum(P[i][i] for i in range(n)))
        t += 1
        if _det(A) != F((-1) ** n, factorial(n)) * bell_complete(tr):
            bad.append(n)
check('cor:det-traces-bell', 'det A = (-1)^n/n! B_n(t_k), t_k = -(k-1)! tr(A^k)', bad, t)

# ------------------------------------------------------------ thm:bell-determinants
bad, t = [], 0
for n in range(1, 8):
    for _ in range(6):
        xs = [F(random.randint(-6, 6), random.randint(1, 4)) for _ in range(n)]
        b = bell_complete(xs)
        H = [[(F(comb(n - i, j - i)) * xs[j - i] if j >= i else (F(-1) if j == i - 1 else F(0)))
              for j in range(1, n + 1)] for i in range(1, n + 1)]
        K = [[(xs[j - i] / F(factorial(j - i)) if j >= i
               else (F(-(i - 1)) if j == i - 1 else F(0)))
              for j in range(1, n + 1)] for i in range(1, n + 1)]
        t += 1
        if _det(H) != b or _det(K) != b:
            bad.append(n)
check('thm:bell-determinants', 'B_n = det H_n = det K_n', bad, t)

# ------------------------------------------------ thm:fixed-point-stirling-moments
bad, t = [], 0
for m in range(0, 7):
    perms = list(permutations(range(m)))
    for n in range(1, 8):
        e = F(sum(sum(1 for i in range(m) if p[i] == i) ** n for p in perms), len(perms))
        t += 1
        if e != sum(S2[n][k] for k in range(0, m + 1)):
            bad.append((m, n))
        if m >= n and e != sum(S2[n][k] for k in range(0, n + 1)):
            bad.append(('bell', m, n))
check('thm:fixed-point-stirling-moments', 'E[Y_m^n] = sum_{k<=m} S(n,k), = Bell n for m >= n',
      bad, t)

# ------------------------------------------------------------------ Eulerian row
E = [[0] * (NM + 2) for _ in range(NM + 2)]
E[0][0] = 1
for n in range(1, 14):
    for k in range(0, n):
        E[n][k] = (k + 1) * E[n - 1][k] + (n - k) * (E[n - 1][k - 1] if k else 0)
bad, t = [], 0
for n in range(1, 13):
    t += 1
    if E[n][0] != 1 or E[n][n - 1] != 1:
        bad.append(('ends', n))
    if sum(E[n][:n]) != factorial(n):
        bad.append(('rowsum', n))
    if E[n][1] != 2 ** n - (n + 1):
        bad.append(('A(n,1)', n))
    if [E[n][k] for k in range(n)] != [E[n][n - 1 - k] for k in range(n)]:
        bad.append(('palindrome', n))
check('eq:eulerian-k1 and row facts', 'A(n,0)=A(n,n-1)=1, sum = n!, A(n,1)=2^n-(n+1), symmetric',
      bad, t)

# ------------------------------------------------- modified Bernoulli normalization
NB = 14
inner = [F(0)] * (NB + 1)
j = 0
while 2 * j <= NB:
    inner[2 * j] = F(1, 4 ** j * factorial(2 * j + 1))
    j += 1
tt = inner[:]
tt[0] -= 1


def _mul(a, b, N):
    r = [F(0)] * (N + 1)
    for i, x in enumerate(a):
        if x:
            for k, y in enumerate(b):
                if i + k > N:
                    break
                r[i + k] += x * y
    return r


res = [F(0)] * (NB + 1)
pw = [F(0)] * (NB + 1)
pw[0] = F(1)
for r in range(1, NB + 1):
    pw = _mul(pw, tt, NB)
    if all(v == 0 for v in pw):
        break
    for i in range(NB + 1):
        res[i] += F((-1) ** (r + 1), r) * pw[i]
half = [v / 2 for v in res]
Bn = [F(0)] * (NB + 2)
Bn[0] = F(1)
for n in range(1, NB + 2):
    Bn[n] = -sum((F(factorial(n + 1), factorial(k) * factorial(n + 1 - k)) * Bn[k]
                  for k in range(n)), F(0)) / (n + 1)
bad, t = [], 0
for n in range(2, 13, 2):
    t += 1
    if half[n] != Bn[n] / (2 * n * n * factorial(n - 1)):
        bad.append(n)
check('eq:merged-modified-bernoulli', 'beta_n^sharp = B_n / (2 n^2 Gamma(n)) for even n', bad, t)

# --------------------------------------------------------- Cauchy polynomials b_n
L = [F((-1) ** i, i + 1) for i in range(9)]
g = [F(0)] * 9
g[0] = F(1) / L[0]
for n in range(1, 9):
    g[n] = -sum((L[k] * g[n - k] for k in range(1, n + 1)), F(0)) / L[0]


def _falling_poly(m):
    p = [F(1)]
    for j in range(m):
        q = [F(0)] * (len(p) + 1)
        for i, cc in enumerate(p):
            q[i + 1] += cc
            q[i] -= cc * j
        p = q
    return p


expected = {0: [F(1)], 1: [F(1, 2), F(1)], 2: [F(-1, 6), F(0), F(1)],
            3: [F(1, 4), F(0), F(-3, 2), F(1)],
            4: [F(-19, 30), F(0), F(4), F(-4), F(1)]}
bad, t = [], 0
for n in range(0, 5):
    acc = [F(0)] * (n + 1)
    for k in range(0, n + 1):
        m = n - k
        f = _falling_poly(m)
        cf = F(factorial(n), factorial(m)) * g[k]
        for i, v in enumerate(f):
            acc[i] += cf * v
    t += 1
    if acc != expected[n]:
        bad.append((n, acc))
check('Cauchy polynomials b_0..b_4', 'the quoted polynomials and b_n(0) values', bad, t)


# --------------------------------------------------------------------- report
width = max(len(lab) for lab, _, _, _ in RESULTS)
failed = 0
print('== closed-form identity checks (exact rational arithmetic) ==')
print()
for lab, claim, bad, t in RESULTS:
    ok = not bad
    failed += 0 if ok else 1
    print('%-*s  %-6s %5d checked' % (width, lab, 'ok' if ok else 'FAIL', t))
    if VERBOSE or not ok:
        print('%s   %s' % (' ' * width, claim))
    if not ok:
        for b in bad[:5]:
            print('%s   counterexample: %s' % (' ' * width, b))
print()
print('%d identities, %d failing' % (len(RESULTS), failed))
print('PASS' if failed == 0 else 'FAIL')
raise SystemExit(1 if failed else 0)
