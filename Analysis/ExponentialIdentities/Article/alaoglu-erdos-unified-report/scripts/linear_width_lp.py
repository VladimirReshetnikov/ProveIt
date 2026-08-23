"""LP layer of the linear-width factorial-cocycle target, control pair (M,A)=(2,3).

P(T) = P_*(T) * S(T) with P_* = 3T^3 - 16T^2 + 28T - 16 (annihilator for M=2, A=3).
Variables: s_0..s_{D} (D = d-3), c = conv(P_*, s).
Constraints: for every prime p <= 3^{n+d}: sum_j c_j V_p(n+j) >= 0,
V_p(t) = v_p((3^t)! / (3^t - 2^t)!) = sum_r (floor(3^t/p^r) - floor((3^t-2^t)/p^r)).
Question per (n,d): does the cone contain a nonzero real vector?
Method: dedupe vectors; LP max t s.t. W (Ps) >= t*1, |s|_inf <= 1; feasible dir iff opt t >= 0
with some nonzero s... we instead solve: max t s.t. W c(s) - t >= 0, sum s_i pinned via two
normalizations (s_D = +-1) to cut the trivial zero.
"""
import sys
import numpy as np
from scipy.optimize import linprog


def sieve(limit):
    bs = bytearray([1]) * (limit + 1)
    bs[0:2] = b"\x00\x00"
    for i in range(2, int(limit ** 0.5) + 1):
        if bs[i]:
            bs[i * i :: i] = b"\x00" * len(bs[i * i :: i])
    return [i for i in range(limit + 1) if bs[i]]

def V(p, t):
    X = 3 ** t
    Y = X - 2 ** t
    tot = 0
    q = p
    while q <= X:
        tot += X // q - Y // q
        q *= p
    return tot

PSTAR = [-16, 28, -16, 3]  # low to high

def conv(s):
    c = np.zeros(len(s) + 3)
    for i, si in enumerate(s):
        for j, pj in enumerate(PSTAR):
            c[i + j] += si * pj
    return c

def run(n, d):
    D = d - 3
    limit = 3 ** (n + d)
    ps = sieve(limit)
    vecs = {}
    for p in ps:
        v = tuple(V(p, n + j) for j in range(d + 1))
        if any(v):
            vecs[v] = vecs.get(v, 0) + 1
    W = np.array(sorted(vecs.keys()), dtype=float)  # rows: distinct valuation vectors
    # matrix mapping s -> c
    Mmap = np.zeros((d + 1, D + 1))
    for i in range(D + 1):
        e = np.zeros(D + 1); e[i] = 1
        Mmap[:, i] = conv(e)
    A = W @ Mmap  # constraints A s >= 0
    results = []
    for sign in (+1, -1):
        # maximize t  s.t.  A s >= t, -1 <= s_i <= 1, s_D = sign
        # linprog minimizes; vars = (s_0..s_D, t)
        nv = D + 2
        cobj = np.zeros(nv); cobj[-1] = -1.0
        A_ub = np.hstack([-A, np.ones((A.shape[0], 1))])  # t - A s <= 0
        b_ub = np.zeros(A.shape[0])
        bounds = [(-1, 1)] * (D + 1) + [(None, None)]
        bounds[D] = (sign, sign)
        res = linprog(cobj, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method="highs")
        results.append((sign, res.status, None if not res.success else res.x[-1], res))
    print(f"n={n} d={d} width_ratio={(d)/(n+d):.3f} primes={len(ps)} distinct_vecs={len(vecs)}")
    feas = False
    for sign, status, topt, res in results:
        print(f"  s_D={sign:+d}: status={status} max_margin={topt}")
        if topt is not None and topt >= -1e-9:
            feas = topt > 1e-9 or True
            if topt > 1e-9:
                s = res.x[:-1]
                print("   FEASIBLE direction s =", np.round(s, 4))
    return feas

if __name__ == "__main__":
    n = int(sys.argv[1])
    for d in range(4, int(sys.argv[2]) + 1):
        if 3 ** (n + d) > 40_000_000: break
        run(n, d)
