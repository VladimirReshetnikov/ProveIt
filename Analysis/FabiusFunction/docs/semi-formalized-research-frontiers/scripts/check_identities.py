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
from decimal import Decimal, getcontext
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


# ------------------------------------------------------- set-partition machinery
def _setparts_fs(n):
    def rec(i, maxb, cur):
        if i == n:
            blocks = [[] for _ in range(maxb + 1)]
            for idx, b in enumerate(cur):
                blocks[b].append(idx)
            yield frozenset(frozenset(b) for b in blocks)
            return
        for b in range(maxb + 2):
            yield from rec(i + 1, max(maxb, b), cur + [b])
    yield from rec(0, -1, [])


def _refines(a, b):
    return all(any(x <= y for y in b) for x in a)


# -------------------------------------------------------- thm:merged-partition-mobius
bad, t = [], 0
for n in range(1, 6):
    P = list(_setparts_fs(n))
    mu = {}
    for s in P:
        for p in sorted((q for q in P if _refines(s, q)), key=lambda q: -len(q)):
            mu[(s, p)] = 1 if s == p else -sum(
                mu[(s, tau)] for tau in P
                if _refines(s, tau) and _refines(tau, p) and tau != p)
    for s in P:
        for p in P:
            if not _refines(s, p):
                continue
            prod = 1
            for Cb in p:
                m = sum(1 for x in s if x <= Cb)
                prod *= (-1) ** (m - 1) * factorial(m - 1)
            t += 1
            if mu[(s, p)] != prod:
                bad.append((n, sorted(map(sorted, s)), sorted(map(sorted, p))))
    bot = frozenset(frozenset([i]) for i in range(n))
    top = frozenset([frozenset(range(n))])
    for p in P:
        want = 1
        for B in p:
            want *= (-1) ** (len(B) - 1) * factorial(len(B) - 1)
        t += 2
        if mu[(bot, p)] != want:
            bad.append(('bottom', n))
        if mu[(p, top)] != (-1) ** (len(p) - 1) * factorial(len(p) - 1):
            bad.append(('top', n))
check('thm:merged-partition-mobius',
      'mu(s,p) = prod_C (-1)^{m_C-1}(m_C-1)!, against mu from its own recursion', bad, t)

# --------------------------------------------------- thm:permutohedron-h-polynomial
bad, t = [], 0
for n in range(1, 8):
    d = n - 1
    h = [0] * (d + 2)
    for i in range(0, d + 1):
        f = factorial(i + 1) * S2[n][i + 1]          # f_{i-1} of the dual simplicial polytope
        for j in range(0, d - i + 1):
            h[i + j] += f * ((-1) ** j) * comb(d - i, j)
    hp = h[:d + 1]
    eu = [E[n][k] for k in range(0, max(n, 1))]
    eu += [0] * (len(hp) - len(eu))
    hp += [0] * (len(eu) - len(hp))
    t += 1
    if hp != eu:
        bad.append((n, hp, eu))
check('thm:permutohedron-h-polynomial',
      'h_{P_n}(t) = A_n(t), from the ordered-set-partition face numbers', bad, t)

# ------------------------------------------------------------ thm:bell-poly-partitions
def _partial_bell(n, k, x):
    B = [[F(0)] * (n + 1) for _ in range(n + 1)]
    B[0][0] = F(1)
    for a in range(1, n + 1):
        for b in range(1, a + 1):
            B[a][b] = sum((F(comb(a - 1, i - 1)) * x[i - 1] * B[a - i][b - 1]
                           for i in range(1, a - b + 2)), F(0))
    return B[n][k]


bad, t = [], 0
for n in range(1, 8):
    xs = [F(random.randint(-5, 5), random.randint(1, 3)) for _ in range(n)]
    parts = list(_setparts_fs(n))
    for k in range(1, n + 1):
        tot = F(0)
        for p in parts:
            if len(p) == k:
                w = F(1)
                for B in p:
                    w *= xs[len(B) - 1]
                tot += w
        t += 1
        if tot != _partial_bell(n, k, xs):
            bad.append((n, k))
    tot = F(0)
    for p in parts:
        w = F(1)
        for B in p:
            w *= xs[len(B) - 1]
        tot += w
    t += 1
    if tot != sum((_partial_bell(n, k, xs) for k in range(1, n + 1)), F(0)):
        bad.append(('complete', n))
check('thm:bell-poly-partitions',
      'B_{n,k} is the weight of partitions into k blocks; B_n of all partitions', bad, t)

# ------------------------------------------------- thm:stirling-row-log-concavity
bad, t = [], 0
for n in range(1, 61):
    for k in range(2, n):
        t += 1
        if not (S2[n][k] ** 2 > S2[n][k - 1] * S2[n][k + 1]):
            bad.append(('strict', n, k))
    row = [S2[n][k] for k in range(1, n + 1)]
    up = True
    for i in range(1, len(row)):
        if row[i] > row[i - 1]:
            if not up:
                bad.append(('unimodal', n, i))
                break
        elif row[i] < row[i - 1]:
            up = False
    mx = max(row)
    at = [i for i, v in enumerate(row) if v == mx]
    t += 2
    if not (len(at) == 1 or (len(at) == 2 and at[1] == at[0] + 1)):
        bad.append(('mode', n, at))
check('thm:stirling-row-log-concavity',
      'S(n,k)^2 > S(n,k-1)S(n,k+1) strictly, row unimodal, mode one or two indices', bad, t)

# ------------------------------------------------------------- thm:cycle-index-bell
bad, t = [], 0
for n in range(1, 8):
    a = [F(random.randint(-5, 5), random.randint(1, 3)) for _ in range(n)]
    tot = F(0)
    for p in permutations(range(n)):
        seen = [False] * n
        term = F(1)
        for i in range(n):
            if seen[i]:
                continue
            j, ln = i, 0
            while not seen[j]:
                seen[j] = True
                j = p[j]
                ln += 1
            term *= a[ln - 1]
        tot += term
    t += 1
    if tot / factorial(n) != bell_complete([F(factorial(i)) * a[i]
                                            for i in range(n)]) / factorial(n):
        bad.append(n)
check('thm:cycle-index-bell',
      'Z(S_n) = (1/n!) B_n(0! a_1, .., (n-1)! a_n), against enumeration of S_n', bad, t)

# ------------------------------------------------------- thm:eulerian-irwin-hall
def _irwin_hall_cdf(tt, n):
    """vol{x in [0,1]^n : sum x_i < tt}, exact for integer tt."""
    return F(sum((-1) ** j * comb(n, j) * max(tt - j, 0) ** n for j in range(0, n + 1)),
             factorial(n))


bad, t = [], 0
for n in range(1, 13):
    for k in range(0, n):
        t += 1
        if _irwin_hall_cdf(k + 1, n) - _irwin_hall_cdf(k, n) != F(E[n][k], factorial(n)):
            bad.append((n, k))
check('thm:eulerian-irwin-hall', 'vol{k <= sum x_i < k+1} = A(n,k)/n!, from the Irwin-Hall CDF',
      bad, t)

# ------------------------------------------------- thm:merged-inverse-derivative
def _compose_inverse(a, N):
    """g with f(g(y)) = y, for f = sum_{i>=1} a_i x^i, a_1 invertible."""
    g = [F(0)] * (N + 1)
    g[1] = F(1) / a[1]
    for n in range(2, N + 1):
        gg = g[:]
        gg[n] = F(0)
        pw = [F(0)] * (N + 1)
        pw[0] = F(1)
        tot = [F(0)] * (N + 1)
        for i in range(1, N + 1):
            nxt = [F(0)] * (N + 1)
            for p in range(N + 1):
                if pw[p]:
                    for q in range(1, N + 1 - p):
                        if gg[q]:
                            nxt[p + q] += pw[p] * gg[q]
            pw = nxt
            if a[i]:
                for p in range(N + 1):
                    tot[p] += a[i] * pw[p]
        g[n] = -tot[n] / a[1]
    return g


bad, t = [], 0
NN = 6
for _ in range(20):
    a = [F(0)] * (NN + 2)
    a[1] = F(random.choice([-3, -2, -1, 1, 2, 3]), random.randint(1, 3))
    for i in range(2, NN + 2):
        a[i] = F(random.randint(-4, 4), random.randint(1, 3))
    g = _compose_inverse(a, NN)
    fd = [F(0)] + [F(factorial(k)) * a[k] for k in range(1, NN + 2)]
    gd = [F(0)] + [F(factorial(k)) * g[k] for k in range(1, NN + 1)]
    for n in range(2, NN + 1):
        t += 1
        rhs = -sum((fd[k] * _partial_bell(n, k, gd[1:n + 1])
                    for k in range(2, n + 1)), F(0)) / fd[1]
        if gd[n] != rhs:
            bad.append(('recursion', n))
    f1, f2, f3, f4 = fd[1], fd[2], fd[3], fd[4]
    want = [F(1) / f1, -f2 / f1 ** 3, (3 * f2 ** 2 - f1 * f3) / f1 ** 5,
            (-15 * f2 ** 3 + 10 * f1 * f2 * f3 - f1 ** 2 * f4) / f1 ** 7]
    for idx in range(4):
        t += 1
        if gd[idx + 1] != want[idx]:
            bad.append(('explicit', idx + 1))
check('thm:merged-inverse-derivative',
      'the Bell recursion for g^{(n)} and the four explicit forms, by series reversion',
      bad, t)

# ---------------------------------------------------- cor:merged-harmonic-expansion
# Precision matters here and the naive version of this check is worthless: comparing a
# double-precision H_N at N = 1000 measures the rounding error of the summation (~1e-14),
# not the residual (~4e-21).  H_N is taken exactly and log/gamma to 60 digits, and the test
# is that residual * N^6 approaches the NEXT term -beta_6/6 = -1/252 rather than merely
# staying bounded.
getcontext().prec = 60
GAMMA = Decimal('0.577215664901532860606512090082402431042159335939923598805767')
bad, t = [], 0
ratio = None
for Nn in (10, 20, 40, 80, 160):
    Hn = sum((F(1, k) for k in range(1, Nn + 1)), F(0))
    Hd = Decimal(Hn.numerator) / Decimal(Hn.denominator)
    Nd = Decimal(Nn)
    approx = (Nd.ln() + GAMMA + Decimal(1) / (2 * Nd)
              - Decimal(1) / (12 * Nd ** 2) + Decimal(1) / (120 * Nd ** 4))
    ratio = (Hd - approx) * Nd ** 6
t += 1
if abs(float(ratio) - (-1.0 / 252)) >= 1e-6:
    bad.append(('limit', float(ratio)))
for lab, lhs, rhs in (('-beta_2/2', -F(1, 6) / 2, F(-1, 12)),
                      ('-beta_4/4', -F(-1, 30) / 4, F(1, 120))):
    t += 1
    if lhs != rhs:
        bad.append((lab, lhs, rhs))
check('cor:merged-harmonic-expansion',
      'residual * N^6 -> -1/252, and the quoted terms match -beta_{2r}/(2r)', bad, t)

# ------------------------------- thm:merged-binomial-type-characterization
def _exp_xB(bcoef, NN):
    """p_n(x) as coefficient lists in x, from exp(x B(t))."""
    poly = [[F(0)] * (NN + 1) for _ in range(NN + 1)]
    poly[0][0] = F(1)
    Bp = [F(0)] * (NN + 1)
    Bp[0] = F(1)
    for r in range(1, NN + 1):
        nxt = [F(0)] * (NN + 1)
        for i in range(NN + 1):
            if Bp[i]:
                for j in range(1, NN + 1 - i):
                    if bcoef[j]:
                        nxt[i + j] += Bp[i] * bcoef[j]
        Bp = nxt
        for n in range(NN + 1):
            if Bp[n]:
                poly[n][r] += Bp[n] / factorial(r)
    return [[F(factorial(n)) * cc for cc in poly[n]] for n in range(NN + 1)]


def _shift_xy(p):
    out = {}
    for r, cc in enumerate(p):
        if cc:
            for i in range(r + 1):
                out[(i, r - i)] = out.get((i, r - i), F(0)) + cc * comb(r, i)
    return {k: v for k, v in out.items() if v != 0}


bad, t = [], 0
NB2 = 7
for trial in range(20):
    delta = trial % 2 == 0
    b = [F(0)] * (NB2 + 2)
    b[1] = F(random.randint(1, 4), random.randint(1, 3)) if delta else F(0)
    for k in range(2, NB2 + 2):
        b[k] = F(random.randint(-4, 4), random.randint(1, 3))
    if not delta and all(b[k] == 0 for k in range(2, NB2 + 2)):
        b[2] = F(1)
    p = _exp_xB(b, NB2)
    for n in range(0, NB2 + 1):
        lhs = _shift_xy(p[n])
        rhs = {}
        for k in range(0, n + 1):
            for i, aa in enumerate(p[k]):
                if aa:
                    for j, bb in enumerate(p[n - k]):
                        if bb:
                            rhs[(i, j)] = rhs.get((i, j), F(0)) + F(comb(n, k)) * aa * bb
        rhs = {k: v for k, v in rhs.items() if v != 0}
        t += 2
        if lhs != rhs:
            bad.append(('law', trial, n))
        if max([r for r, cc in enumerate(p[n]) if cc != 0], default=0) > n:
            bad.append(('degree', trial, n))
    exact = all(max([r for r, cc in enumerate(p[n]) if cc != 0], default=0) == n
                for n in range(0, NB2 + 1))
    t += 1
    if exact != delta:
        bad.append(('delta iff', trial, exact, delta))
check('thm:merged-binomial-type-characterization',
      'binomial law, deg p_n <= n, and deg p_n = n for all n iff B is a delta series',
      bad, t)

# ------------------------------------------------------------------ thm:res-subst
# Res_z A(u(z)) u'(z) = Res_u A(u).  Exact Laurent arithmetic: u = z v with v(0) invertible,
# so u^n = z^n v^n for every integer n, negative powers via series inversion.  A is given
# genuine poles -- for a power series the identity is 0 = 0 and would pass for the wrong
# reason.
NR = 26


def _pmul(a, b):
    r = [F(0)] * NR
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if i + j >= NR:
                    break
                r[i + j] += x * y
    return r


def _pinv(a):
    r = [F(0)] * NR
    r[0] = F(1) / a[0]
    for n in range(1, NR):
        r[n] = -sum(a[k] * r[n - k] for k in range(1, n + 1)) / a[0]
    return r


def _ppow(a, n):
    if n < 0:
        return _ppow(_pinv(a), -n)
    r = [F(0)] * NR
    r[0] = F(1)
    for _ in range(n):
        r = _pmul(r, a)
    return r


bad, t = [], 0
for _ in range(25):
    v = [F(random.randint(-4, 4), random.randint(1, 3)) for _ in range(NR)]
    while v[0] == 0:
        v[0] = F(random.randint(1, 4))
    vp = [F(0)] * NR
    for i in range(1, NR):
        vp[i - 1] = v[i] * i
    zvp = [F(0)] * NR
    for i in range(NR - 1):
        zvp[i + 1] = vp[i]
    uprime = [v[i] + zvp[i] for i in range(NR)]
    L, M = random.randint(1, 4), random.randint(0, 3)
    aco = {n: F(random.randint(-5, 5), random.randint(1, 3)) for n in range(-L, M + 1)}
    if all(cc == 0 for cc in aco.values()):
        aco[-1] = F(1)
    tot = F(0)
    for n, cc in aco.items():
        if cc:
            ser = _pmul(_ppow(v, n), uprime)
            idx = -1 - n
            if 0 <= idx < NR:
                tot += cc * ser[idx]
    t += 1
    if tot != aco.get(-1, F(0)):
        bad.append((tot, aco.get(-1, F(0))))
check('thm:res-subst', "Res_z A(u(z))u'(z) = Res_u A(u), Laurent A with poles", bad, t)

# ------------------------------------------------- thm:merged-good (d = 2)
# Lagrange-Good inversion.  Both sides are built independently on truncated bivariate series:
# the left by solving the fixed point w_i = t_i phi_i(w) by iteration and composing F with it,
# the right by forming F * prod phi_i^{n_i} * det(delta_ij - (x_j/phi_i) d phi_i/d x_j).
NG = 7


def _g_mul(a, b):
    r = {}
    for (i, j), u in a.items():
        for (p, q), v in b.items():
            if i + p + j + q < NG:
                r[(i + p, j + q)] = r.get((i + p, j + q), F(0)) + u * v
    return {k: v for k, v in r.items() if v != 0}


def _g_add(a, b):
    r = dict(a)
    for k, v in b.items():
        r[k] = r.get(k, F(0)) + v
    return {k: v for k, v in r.items() if v != 0}


def _g_neg(a):
    return {k: -v for k, v in a.items()}


def _g_one():
    return {(0, 0): F(1)}


def _g_inv(a):
    c = a[(0, 0)]
    r = {(0, 0): F(1) / c}
    for deg in range(1, NG):
        for i in range(deg + 1):
            j = deg - i
            s = F(0)
            for (p, q), u in a.items():
                if (p, q) != (0, 0) and p <= i and q <= j:
                    s += u * r.get((i - p, j - q), F(0))
            if s != 0:
                r[(i, j)] = -s / c
    return {k: v for k, v in r.items() if v != 0}


def _g_pow(a, n):
    r = _g_one()
    for _ in range(n):
        r = _g_mul(r, a)
    return r


def _g_dx(a, which):
    r = {}
    for (i, j), v in a.items():
        if which == 0 and i >= 1:
            r[(i - 1, j)] = r.get((i - 1, j), F(0)) + v * i
        if which == 1 and j >= 1:
            r[(i, j - 1)] = r.get((i, j - 1), F(0)) + v * j
    return {k: v for k, v in r.items() if v != 0}


def _g_shift(a, which):
    out = {}
    for (i, j), v in a.items():
        key = (i + 1, j) if which == 0 else (i, j + 1)
        if key[0] + key[1] < NG:
            out[key] = v
    return out


def _g_comp(Fs, w1, w2):
    p1, p2 = [_g_one()], [_g_one()]
    for _ in range(NG):
        p1.append(_g_mul(p1[-1], w1))
        p2.append(_g_mul(p2[-1], w2))
    res = {}
    for (i, j), c in Fs.items():
        if i < len(p1) and j < len(p2):
            res = _g_add(res, {k: c * v for k, v in _g_mul(p1[i], p2[j]).items()})
    return res


def _g_rand(const_nonzero):
    s = {}
    for i in range(NG):
        for j in range(NG - i):
            if random.random() < 0.55:
                v = F(random.randint(-3, 3), random.randint(1, 2))
                if v != 0:
                    s[(i, j)] = v
    if const_nonzero:
        s[(0, 0)] = F(random.randint(1, 3))
    else:
        s.pop((0, 0), None)
    return s


bad, t = [], 0
for _ in range(5):
    phi1, phi2 = _g_rand(True), _g_rand(True)
    Fs = _g_rand(random.random() < 0.5)
    w1, w2 = {}, {}
    for _ in range(NG + 1):
        w1, w2 = (_g_shift(_g_comp(phi1, w1, w2), 0),
                  _g_shift(_g_comp(phi2, w1, w2), 1))
    lhs = _g_comp(Fs, w1, w2)
    i1, i2 = _g_inv(phi1), _g_inv(phi2)
    m11 = _g_add(_g_one(), _g_neg(_g_mul(i1, _g_shift(_g_dx(phi1, 0), 0))))
    m12 = _g_neg(_g_mul(i1, _g_shift(_g_dx(phi1, 1), 1)))
    m21 = _g_neg(_g_mul(i2, _g_shift(_g_dx(phi2, 0), 0)))
    m22 = _g_add(_g_one(), _g_neg(_g_mul(i2, _g_shift(_g_dx(phi2, 1), 1))))
    det = _g_add(_g_mul(m11, m22), _g_neg(_g_mul(m12, m21)))
    for n1 in range(0, 3):
        for n2 in range(0, 3):
            if n1 + n2 >= NG - 3:
                continue
            rhs = _g_mul(_g_mul(Fs, _g_pow(phi1, n1)), _g_mul(_g_pow(phi2, n2), det))
            t += 1
            if lhs.get((n1, n2), F(0)) != rhs.get((n1, n2), F(0)):
                bad.append((n1, n2))
check('thm:merged-good', 'Lagrange-Good inversion in dimension 2, both sides built separately',
      bad, t)

# ------------------------------------------- thm:shifted-lagrange-reversion
# With v solving v = x + y f(v):  g(v) = g(x) + sum_k (y^k/k!) (d/dx)^{k-1}(f^k g').
# f and g are polynomials, so v is computed exactly as a y-series with polynomial
# coefficients by iterating the fixed point, and the comparison at each y^k is between
# polynomials in x -- an identity, not a check at sample points.
KR = 7


def _q_mul(a, b):
    r = [F(0)] * (len(a) + len(b) - 1)
    for i, u in enumerate(a):
        if u:
            for j, v in enumerate(b):
                r[i + j] += u * v
    return _q_trim(r)


def _q_add(a, b):
    m = max(len(a), len(b))
    return _q_trim([(a[i] if i < len(a) else F(0)) + (b[i] if i < len(b) else F(0))
                    for i in range(m)])


def _q_trim(a):
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def _q_der(a):
    return _q_trim([a[i] * i for i in range(1, len(a))] or [F(0)])


def _q_pow(a, n):
    r = [F(1)]
    for _ in range(n):
        r = _q_mul(r, a)
    return r


def _q_apply(poly, vser):
    """poly(v) where v is a y-series of polynomials."""
    out = [[F(0)] for _ in range(KR)]
    pw = [[[F(1)]] + [[F(0)] for _ in range(KR - 1)]]
    for _d in range(len(poly) - 1):
        prev = pw[-1]
        nxt = [[F(0)] for _ in range(KR)]
        for i in range(KR):
            if prev[i] == [F(0)]:
                continue
            for j in range(KR - i):
                if vser[j] != [F(0)]:
                    nxt[i + j] = _q_add(nxt[i + j], _q_mul(prev[i], vser[j]))
        pw.append(nxt)
    for d, cc in enumerate(poly):
        if cc:
            for i in range(KR):
                out[i] = _q_add(out[i], [cc * z for z in pw[d][i]])
    return out


bad, t = [], 0
for _ in range(10):
    f = _q_trim([F(random.randint(-3, 3), random.randint(1, 2)) for _ in range(4)])
    g = _q_trim([F(random.randint(-3, 3), random.randint(1, 2)) for _ in range(4)])
    v = [[F(0), F(1)]] + [[F(0)] for _ in range(KR - 1)]
    for _ in range(KR):
        fv = _q_apply(f, v)
        v = [[F(0), F(1)]] + [fv[i - 1] for i in range(1, KR)]
    gv = _q_apply(g, v)
    gp = _q_der(g)
    for k in range(1, KR):
        term = _q_mul(_q_pow(f, k), gp)
        term2 = _q_pow(f, k)
        for _ in range(k - 1):
            term = _q_der(term)
            term2 = _q_der(term2)
        t += 2
        if _q_trim(list(gv[k])) != _q_trim([cc / factorial(k) for cc in term]):
            bad.append(('g', k))
        if _q_trim(list(v[k])) != _q_trim([cc / factorial(k) for cc in term2]):
            bad.append(('v', k))
check('thm:shifted-lagrange-reversion',
      "g(v) = g(x) + sum (y^k/k!) d^{k-1}(f^k g'), and the g = id case", bad, t)

# ----------------------------------------------------------- thm:bell-near-diagonal
# B_{n,n-a}(x_1..x_{a+1}) = sum_{j=a+1}^{2a} (j!/a!) C(n,j) x_1^{n-j}
#                             B_{a,j-a}(x_2/2, x_3/3, .., x_{2a-j+2}/(2a-j+2)).
# The inner arguments are both shifted and divided, which is the part of the statement most
# easily mis-transcribed, so it is evaluated rather than read.
bad, t = [], 0
for n in range(2, 11):
    for a in range(1, n):
        xs = [F(random.randint(-5, 5), random.randint(1, 3))
              for _ in range(max(n, 2 * a + 2))]
        lhs = _partial_bell(n, n - a, xs)
        rhs = F(0)
        for j in range(a + 1, 2 * a + 1):
            if j > n:            # C(n,j) = 0 there, and x_1^{n-j} would need a negative power
                continue
            y = [xs[i] / F(i + 1) for i in range(1, max(a, 1) + 1)]
            rhs += (F(factorial(j), factorial(a)) * F(comb(n, j)) * xs[0] ** (n - j)
                    * _partial_bell(a, j - a, y))
        t += 1
        if lhs != rhs:
            bad.append((n, a))
check('thm:bell-near-diagonal',
      'B_{n,n-a} through B_{a,j-a} at shifted and divided arguments', bad, t)

# --------------------------------------------------------------- thm:faa-multivariate
# d^n/(dx_1..dx_n) f(y) = sum_{pi} f^{(|pi|)}(y) prod_{B in pi} d_B y, y = g(x_1,..,x_n).
# The left side is obtained by actually differentiating the composite once in each variable as
# an exact multivariate polynomial; the right by summing over set partitions of [n].  n = 4
# gives 15 partitions across 5 shapes, so the block structure is exercised rather than only
# the two extreme partitions.
def _m_mul(a, b, nv):
    r = {}
    for ea, ca in a.items():
        for eb, cb in b.items():
            e = tuple(ea[i] + eb[i] for i in range(nv))
            r[e] = r.get(e, F(0)) + ca * cb
    return {k: v for k, v in r.items() if v != 0}


def _m_add(a, b):
    r = dict(a)
    for k, v in b.items():
        r[k] = r.get(k, F(0)) + v
    return {k: v for k, v in r.items() if v != 0}


def _m_diff(a, i):
    r = {}
    for e, c in a.items():
        if e[i] > 0:
            e2 = list(e)
            e2[i] -= 1
            r[tuple(e2)] = r.get(tuple(e2), F(0)) + c * e[i]
    return {k: v for k, v in r.items() if v != 0}


def _m_parts(n):
    def rec(i, maxb, cur):
        if i == n:
            blocks = [[] for _ in range(maxb + 1)]
            for idx, b in enumerate(cur):
                blocks[b].append(idx)
            yield blocks
            return
        for b in range(maxb + 2):
            yield from rec(i + 1, max(maxb, b), cur + [b])
    yield from rec(0, -1, [])


bad, t = [], 0
for n in (2, 3, 4):
    for _ in range(4):
        nv = n
        g = {}
        for _k in range(8):
            e = tuple(random.randint(0, 2) for _ in range(nv))
            g[e] = g.get(e, F(0)) + F(random.randint(-3, 3), random.randint(1, 2))
        g = {k: v for k, v in g.items() if v != 0} or {tuple(0 for _ in range(nv)): F(1)}
        fc = [F(random.randint(-3, 3), random.randint(1, 2)) for _ in range(6)]

        def f_at(m, g=g, fc=fc, nv=nv):
            cvec = list(fc)
            for _ in range(m):
                cvec = [cvec[i] * i for i in range(1, len(cvec))] or [F(0)]
            out = {}
            gp = {tuple(0 for _ in range(nv)): F(1)}
            for d, cd in enumerate(cvec):
                if cd:
                    out = _m_add(out, {k: cd * v for k, v in gp.items()})
                gp = _m_mul(gp, g, nv)
            return out

        lhs = f_at(0)
        for i in range(n):
            lhs = _m_diff(lhs, i)
        rhs = {}
        for blocks in _m_parts(n):
            term = f_at(len(blocks))
            for B in blocks:
                dB = dict(g)
                for i in B:
                    dB = _m_diff(dB, i)
                term = _m_mul(term, dB, nv)
                if not term:
                    break
            rhs = _m_add(rhs, term)
        t += 1
        if lhs != rhs:
            bad.append(n)
check('thm:faa-multivariate',
      'mixed partial of f(g) as a sum over set partitions of the variables', bad, t)

# ------------------------------- thm:merged-inverse-derivative-operator
# g^{(n)}(y) = ((1/f') d/dx)^{n-1} (1/f') at x = g(y).  A different statement from the Bell-sum
# form above -- here one operator is iterated -- and checked independently of it: g by exact
# series reversion, the right side by iterating the operator and reading the constant term,
# which is the evaluation at x = g(0) = 0.
NO = 9


def _o_mul(a, b):
    r = [F(0)] * NO
    for i, u in enumerate(a):
        if u:
            for j, v in enumerate(b):
                if i + j >= NO:
                    break
                r[i + j] += u * v
    return r


def _o_inv(a):
    r = [F(0)] * NO
    r[0] = F(1) / a[0]
    for n in range(1, NO):
        r[n] = -sum(a[k] * r[n - k] for k in range(1, n + 1)) / a[0]
    return r


def _o_der(a):
    r = [F(0)] * NO
    for i in range(1, NO):
        r[i - 1] = a[i] * i
    return r


bad, t = [], 0
for _ in range(15):
    M = NO - 2
    a = [F(0)] * (M + 2)
    a[1] = F(random.choice([-3, -2, -1, 1, 2, 3]), random.randint(1, 3))
    for i in range(2, M + 2):
        a[i] = F(random.randint(-4, 4), random.randint(1, 3))
    g = _compose_inverse(a, M)
    fp = [F(0)] * NO
    for i in range(1, min(M + 2, NO + 1)):
        if i - 1 < NO:
            fp[i - 1] = a[i] * i
    invfp = _o_inv(fp)
    cur = invfp[:]
    for n in range(1, M + 1):
        t += 1
        if F(factorial(n)) * g[n] != cur[0]:
            bad.append(n)
        cur = _o_mul(invfp, _o_der(cur))
check('thm:merged-inverse-derivative-operator',
      "g^{(n)} = ((1/f') d/dx)^{n-1}(1/f') at x = g(y)", bad, t)

# ------------------------------ prop:merged-beta-integral, thm:merged-pochhammer
def _poch(a, n):
    r = F(1)
    for i in range(n):
        r *= (a + i)
    return r


def _fall(a, n):
    r = F(1)
    for i in range(n):
        r *= (a - i)
    return r


# int_0^1 t^{a-1}(1-t)^n dt = n!/(a)_{n+1}, the left side by expanding and integrating
# term by term rather than by quoting the Beta function.
bad, t = [], 0
for _ in range(30):
    a = F(random.randint(1, 12), random.randint(1, 5))
    for n in range(0, 9):
        t += 1
        if sum((F((-1) ** k * comb(n, k)) / (a + k) for k in range(n + 1)), F(0)) \
                != F(factorial(n)) / _poch(a, n + 1):
            bad.append((a, n))
check('prop:merged-beta-integral', 'int_0^1 t^{a-1}(1-t)^n = n!/(a)_{n+1}', bad, t)

# (1-z)^{-a} = sum (a)_n z^n/n!, the series generated from (1-z)F' = aF so the closed form
# is not presupposed; plus the two splitting laws.
bad, t = [], 0
NP = 12
for _ in range(20):
    a = F(random.randint(-9, 9), random.randint(1, 4))
    c = [F(1)] + [F(0)] * NP
    for n in range(NP):
        c[n + 1] = (a + n) * c[n] / (n + 1)
    for n in range(NP + 1):
        t += 1
        if c[n] != _poch(a, n) / factorial(n):
            bad.append(('series', n))
for _ in range(40):
    a = F(random.randint(-9, 9), random.randint(1, 4))
    m, n = random.randint(0, 6), random.randint(0, 6)
    t += 2
    if _poch(a, m + n) != _poch(a, m) * _poch(a + m, n):
        bad.append(('rising', m, n))
    if _fall(a, m + n) != _fall(a, m) * _fall(a - m, n):
        bad.append(('falling', m, n))
check('thm:merged-pochhammer',
      'binomial series (1-z)^{-a} = sum (a)_n z^n/n!, and both splitting laws', bad, t)

# --------------------------------------------- thm:bell-quadratic-differential
# Compared as a POLYNOMIAL identity in x_1..x_N, not at sample points: B_n is built
# symbolically from the convolution recurrence and the partials are taken formally.
# The manuscript's caveat that terms with unavailable variables vanish takes care of itself --
# B_{n-1} is weighted-homogeneous of weighted degree n-1, so d^2/dx_j dx_{i-j} drops the
# weighted degree by i and is identically zero at i = n, which is why no x_{n+1} survives.
def _v_var(i, nv):
    e = [0] * nv
    e[i] = 1
    return {tuple(e): F(1)}


def _v_bell(n, nv):
    B = [{tuple([0] * nv): F(1)}]
    for m in range(1, n + 1):
        acc = {}
        for i in range(1, m + 1):
            piece = _m_mul(_v_var(i - 1, nv), B[m - i], nv)
            acc = _m_add(acc, {k: F(comb(m - 1, i - 1)) * v for k, v in piece.items()})
        B.append(acc)
    return B


bad, t = [], 0
for n in range(2, 7):
    nv = n + 2
    B = _v_bell(n, nv)
    Bn, Bm1 = B[n], B[n - 1]
    rhs = {}
    for i in range(2, n + 1):
        for j in range(1, i):
            piece = _m_mul(_m_mul(_v_var(j - 1, nv), _v_var(i - j - 1, nv), nv),
                           _m_diff(Bm1, i - 2), nv)
            rhs = _m_add(rhs, {k: F((i - 1) * comb(i - 2, j - 1)) * v
                               for k, v in piece.items()})
            d2 = _m_diff(_m_diff(Bm1, j - 1), i - j - 1)
            if d2:
                piece = _m_mul(_v_var(i, nv), d2, nv)
                rhs = _m_add(rhs, {k: F(1, comb(i, j)) * v for k, v in piece.items()})
        rhs = _m_add(rhs, _m_mul(_v_var(i - 1, nv), _m_diff(Bm1, i - 2), nv))
    rhs = {k: F(1, n - 1) * v for k, v in rhs.items()}
    t += 1
    if rhs != Bn:
        bad.append(n)
check('thm:bell-quadratic-differential',
      'the quadratic differential recurrence for B_n, as a polynomial identity', bad, t)

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
