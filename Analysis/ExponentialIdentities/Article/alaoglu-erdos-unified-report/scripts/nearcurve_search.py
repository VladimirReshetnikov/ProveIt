r"""Search for subunit near-curve certificates, the corpus's falsifiable-by-computation route.

Setup (Section sec:nearcurve). theta = log_2 3, curve Y = X^theta, dyadic block
2^L <= X < 2^(L+1). A polynomial P in Z[X,Y] with support S is SUBUNIT for the block if

    sup_{X in [2^L, 2^(L+1)]} | sum_{(i,j) in S} c_ij X^(i + j theta) |  <  1.

Every integer curve point in the block is then a zero of P (an integer of modulus < 1 is 0),
and the fewnomial budget caps the zeros at T(P) - 1. Under a counterexample beta the block
carries at least ceil((L+1)/beta) integer points, so any subunit certificate has
T(P) >= ceil((L+1)/beta) + 1. Exhibiting certificates with T = o(L) along an unbounded L
therefore PROVES the conjecture.

Writing lambda_s = i + j*theta and X = 2^L z with z in [1,2], the term is 2^(L lambda_s)
z^lambda_s, so the question is whether a nonzero integer vector can make a weighted
exponential sum uniformly subunit against weights 2^(L lambda_s).

This script (a) does the Minkowski feasibility algebra for the resonant-chain family, and
(b) runs an LLL search for genuine certificates at small L.
"""
import itertools
import math
from mpmath import mp, mpf, log as mlog, power as mpow

mp.dps = 260
THETA = mlog(3) / mlog(2)
LOG2 = mlog(2)


# ------------------------------------------------------------------ (a) resonant-chain algebra
def resonant_chain_feasibility():
    """A resonant chain steps by (-p, +q) with p/q a convergent of theta, so consecutive
    lambda differ by eps = |p - q theta| ~ 1/q. Minkowski's condition for a nonzero integer
    solution is  L log2 * sum(lambda) + log|V| <= 0. Clustering the lambdas in a window of
    width ~T*eps makes the generalized Vandermonde small, but keeping i >= 0 forces
    lambda_0 >= (T-1)p, so the cost grows like T^2 p while the gain grows like T^2 log(eps).
    """
    print("=" * 78)
    print("(a) resonant-chain family: is the Minkowski condition ever satisfiable?")
    print("=" * 78)
    # convergents of theta
    terms, x = [], THETA
    for _ in range(18):
        a = int(x)
        terms.append(a)
        f = x - a
        if f == 0:
            break
        x = 1 / f
    conv, pm1, qm1, pm2, qm2 = [], 1, 0, 0, 1
    for a in terms:
        p, q = a * pm1 + pm2, a * qm1 + qm2
        conv.append((p, q))
        pm2, qm2, pm1, qm1 = pm1, qm1, p, q

    print(f"{'p/q':>16} {'eps=|p-q*th|':>14} {'need eps <=':>14} {'L':>4}  feasible?")
    for L in (1, 2, 4, 8):
        for (p, q) in conv[2:10]:
            eps = abs(mpf(p) - mpf(q) * THETA)
            need = mpow(2, -mpf(p) * (2 * L + 1))
            ok = eps <= need
            print(f"{p:>7}/{q:<8} {float(eps):14.3e} {float(need):14.3e} {L:>4}  "
                  f"{'YES' if ok else 'no'}")
        print()
    print("The requirement is self-defeating: eps ~ 1/q needs q >~ 2^(p(2L+1)), while a")
    print("convergent has p ~ q*theta, so it asks for q >~ 2^(1.585*q*(2L+1)). No q works.")


# ------------------------------------------------------------------ (b) direct LLL search
def lll_int(B):
    """Plain LLL on a list of integer row vectors (delta = 3/4). Adequate for these sizes."""
    from fractions import Fraction
    B = [list(map(int, row)) for row in B]
    n = len(B)

    def dot(u, v):
        return sum(a * b for a, b in zip(u, v))

    def gso(B):
        Bs, mu = [], [[Fraction(0)] * n for _ in range(n)]
        for i in range(n):
            v = [Fraction(x) for x in B[i]]
            for j in range(i):
                d = dot(Bs[j], Bs[j])
                mu[i][j] = Fraction(dot([Fraction(x) for x in B[i]], Bs[j]), d) if d else Fraction(0)
                v = [a - mu[i][j] * b for a, b in zip(v, Bs[j])]
            Bs.append(v)
        return Bs, mu

    Bs, mu = gso(B)
    k = 1
    guard = 0
    while k < n and guard < 20000:
        guard += 1
        for j in range(k - 1, -1, -1):
            if abs(mu[k][j]) > Fraction(1, 2):
                r = int(mu[k][j] + Fraction(1, 2)) if mu[k][j] > 0 else -int(-mu[k][j] + Fraction(1, 2))
                B[k] = [a - r * b for a, b in zip(B[k], B[j])]
                Bs, mu = gso(B)
        if dot(Bs[k], Bs[k]) >= (Fraction(3, 4) - mu[k][k - 1] ** 2) * dot(Bs[k - 1], Bs[k - 1]):
            k += 1
        else:
            B[k], B[k - 1] = B[k - 1], B[k]
            Bs, mu = gso(B)
            k = max(k - 1, 1)
    return B


def sup_norm(coeffs, lams, L, samples=400):
    """max over the block of |sum c_s X^lambda_s|, X = 2^L z, z in [1,2]."""
    best = mpf(0)
    for t in range(samples + 1):
        z = mpf(1) + mpf(t) / samples
        X = mpow(2, L) * z
        v = sum(mpf(c) * mpow(X, lam) for c, lam in zip(coeffs, lams))
        best = max(best, abs(v))
    return best


def search(L, support, scale_bits=None):
    """LLL for a short integer combination; returns (best sup norm, coefficient vector)."""
    lams = [mpf(i) + mpf(j) * THETA for (i, j) in support]
    T = len(support)
    N = T + 2
    nodes = [mpf(1) + mpf(t) / (N - 1) for t in range(N)]
    if scale_bits is None:
        scale_bits = int(float(max(lams)) * L) + 60
    K = mpow(2, scale_bits)
    rows = []
    for s in range(T):
        row = []
        for z in nodes:
            X = mpow(2, L) * z
            row.append(int(mp.nint(K * mpow(X, lams[s]) / mpow(2, L * max(lams)))))
        row += [1 if t == s else 0 for t in range(T)]
        rows.append(row)
    red = lll_int(rows)
    best, bestc = None, None
    for row in red:
        c = row[-T:]
        if all(v == 0 for v in c):
            continue
        s = sup_norm(c, lams, L)
        if best is None or s < best:
            best, bestc = s, c
    return best, bestc


if __name__ == "__main__":
    resonant_chain_feasibility()
    print()
    print("=" * 78)
    print("(b) direct LLL search for subunit certificates at small L")
    print("=" * 78)
    print(f"{'L':>3} {'deg':>4} {'T':>4} {'best sup norm':>18}  subunit?")
    for L in (1, 2, 3, 4):
        for d in (2, 3, 4):
            support = [(i, j) for i in range(d + 1) for j in range(d + 1 - i)]
            T = len(support)
            if T > 12:
                continue
            try:
                best, c = search(L, support)
            except Exception as e:
                print(f"{L:>3} {d:>4} {T:>4}   error {e}")
                continue
            print(f"{L:>3} {d:>4} {T:>4} {float(best):18.6e}  "
                  f"{'YES' if best < 1 else 'no'}")
