r"""How fast does the minimal subunit-certificate size T grow with the block index L?

This is the decisive measurement for the corpus's falsifiable-by-computation route
(Section sec:nearcurve): certified covers with Cap_L = o(L) PROVE the conjecture, and
Cap_L is governed by T. If T_min(L) grows linearly in L the route is closed; if it grows
like L/log L or slower the criterion is reachable.

For each L we find the smallest dense triangular support (degree d, T = (d+1)(d+2)/2)
admitting a nonzero integer c with sup_{X in block} |sum c_ij X^(i+j theta)| < 1.
"""
import sys
from mpmath import mp, mpf, log as mlog, power as mpow
from sympy import Matrix
from sympy.polys.matrices import DomainMatrix
from sympy import ZZ

mp.dps = 400
THETA = mlog(3) / mlog(2)


def sup_norm(c, lams, L, samples=300):
    best = mpf(0)
    for t in range(samples + 1):
        z = mpf(1) + mpf(t) / samples
        X = mpow(2, L) * z
        v = sum(mpf(ci) * mpow(X, lam) for ci, lam in zip(c, lams))
        if abs(v) > best:
            best = abs(v)
    return best


def try_support(L, support, extra_bits=80):
    lams = [mpf(i) + mpf(j) * THETA for (i, j) in support]
    T = len(support)
    N = T + 3
    lam_max = max(lams)
    # scale so the value block dominates the identity block
    K = mpow(2, int(float(lam_max) * L) + extra_bits)
    rows = []
    for s in range(T):
        row = []
        for t in range(N):
            z = mpf(1) + mpf(t) / (N - 1)
            X = mpow(2, L) * z
            row.append(int(mp.nint(K * mpow(X, lams[s]) / mpow(2, L * lam_max))))
        row += [1 if u == s else 0 for u in range(T)]
        rows.append(row)
    M = DomainMatrix([[ZZ(v) for v in r] for r in rows], (T, N + T), ZZ)
    red = M.lll().to_list()
    best, bestc = None, None
    for row in red:
        c = [int(v) for v in row[-T:]]
        if not any(c):
            continue
        s = sup_norm(c, lams, L)
        if best is None or s < best:
            best, bestc = s, c
    return best, bestc


if __name__ == "__main__":
    Ls = [int(a) for a in sys.argv[1:]] or [1, 2, 3, 4, 6, 8, 10, 12, 14, 16]
    print(f"{'L':>4} {'min d':>6} {'T':>5} {'sup norm':>14} {'T/L':>8} {'T/(L/log L)':>12}")
    import math
    for L in Ls:
        found = None
        for d in range(1, 9):
            support = [(i, j) for i in range(d + 1) for j in range(d + 1 - i)]
            T = len(support)
            if T > 55:
                break
            try:
                best, c = try_support(L, support)
            except Exception as e:
                print(f"{L:>4}  d={d} error: {e}")
                continue
            if best is not None and best < 1:
                found = (d, T, best)
                break
        if found:
            d, T, best = found
            ratio = T / L
            r2 = T / (L / math.log(L)) if L > 1 else float("nan")
            print(f"{L:>4} {d:>6} {T:>5} {float(best):14.4e} {ratio:8.3f} {r2:12.3f}",
                  flush=True)
        else:
            print(f"{L:>4}    none found up to d=8", flush=True)
