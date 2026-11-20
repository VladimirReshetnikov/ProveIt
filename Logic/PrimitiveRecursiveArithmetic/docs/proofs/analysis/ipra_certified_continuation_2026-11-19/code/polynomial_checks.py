#!/usr/bin/env python3
"""Exact rational reference for the polynomial and factor certificates.

This executable checks finite examples and symbolic identities. It is not a
Lean proof or a claim that testing establishes the report's universal results.
Only the Python standard library is required.
"""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json

ASSERTIONS = 0


def check(condition, message):
    global ASSERTIONS
    ASSERTIONS += 1
    if not condition:
        raise AssertionError(message)


def pclean(p):
    return {a: Q(c) for a, c in p.items() if c}


def padd(p, q):
    r = dict(p)
    for a, c in q.items():
        r[a] = r.get(a, Q(0)) + c
    return pclean(r)


def pscale(c, p):
    return pclean({a: c * b for a, b in p.items()})


def pmul(p, q):
    r = {}
    for a, c in p.items():
        for b, e in q.items():
            k = tuple(x + y for x, y in zip(a, b))
            r[k] = r.get(k, Q(0)) + c * e
    return pclean(r)


def pconst(d, c):
    return pclean({(0,) * d: Q(c)})


def pvar(d, j):
    return {tuple(int(i == j) for i in range(d)): Q(1)}


def ppow(p, n, d):
    r = pconst(d, 1)
    for _ in range(n):
        r = pmul(r, p)
    return r


def peval(p, x):
    ans = Q(0)
    for a, c in p.items():
        term = c
        for v, e in zip(x, a):
            term *= v ** e
        ans += term
    return ans


def pshift(p, center):
    d = len(center)
    out = {}
    for alpha, c in p.items():
        term = pconst(d, c)
        for j, e in enumerate(alpha):
            term = pmul(term, ppow(padd(pconst(d, center[j]), pvar(d, j)), e, d))
        out = padd(out, term)
    return out


def compile_update(F, center, B):
    d = len(F)
    shifted = [pshift(p, center) for p in F]
    ans = []
    for i in range(d):
        p = pvar(d, i)
        for j in range(d):
            p = padd(p, pscale(-B[i][j], shifted[j]))
        ans.append(p)
    return ans


def gain_matrix(T, radii):
    d = len(T)
    W = [[Q(0) for _ in range(d)] for _ in range(d)]
    for i, p in enumerate(T):
        for alpha, c in p.items():
            for j in range(d):
                if alpha[j] == 0:
                    continue
                b = abs(c) * alpha[j]
                for k in range(d):
                    b *= radii[k] ** (alpha[k] - int(k == j))
                W[i][j] += b
    return W


def matmul(A, B):
    return [[sum((a * B[k][j] for k, a in enumerate(row)), Q(0))
             for j in range(len(B[0]))] for row in A]


def matvec(A, x):
    return [sum((a * b for a, b in zip(row, x)), Q(0)) for row in A]


def identity(d):
    return [[Q(i == j) for j in range(d)] for i in range(d)]


def inverse(A):
    n = len(A)
    M = [[Q(t) for t in row] + erow for row, erow in zip(A, identity(n))]
    for j in range(n):
        candidates = [i for i in range(j, n) if M[i][j] != 0]
        if not candidates:
            raise ValueError('singular candidate')
        i = candidates[0]
        M[i], M[j] = M[j], M[i]
        pivot = M[j][j]
        M[j] = [a / pivot for a in M[j]]
        for k in range(n):
            if k != j:
                mult = M[k][j]
                M[k] = [a - mult * b for a, b in zip(M[k], M[j])]
    return [row[n:] for row in M]


def weighted(x, v):
    return max([Q(0)] + [abs(a) / b for a, b in zip(x, v)])


def sub(x, y):
    return [a - b for a, b in zip(x, y)]


def l1(x):
    return sum(map(abs, x), Q(0))


def certify(T, B, C, v, r):
    d = len(T)
    if d == 0 or r <= 0 or any(w <= 0 for w in v):
        return None
    if matmul(C, B) != identity(d):
        return None
    W = gain_matrix(T, [r * w for w in v])
    origin = [Q(0)] * d
    if any(2 * abs(peval(T[i], origin)) > r * v[i] for i in range(d)):
        return None
    if any(2 * s > w for s, w in zip(matvec(W, v), v)):
        return None
    return W


def conv(a, b):
    out = [Q(0)] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i + j] += ai * bj
    return out


def poly_pad_add(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else Q(0)) + (b[i] if i < len(b) else Q(0))
            for i in range(n)]


def sylvester_map(g, h):
    r, s = len(g) - 1, len(h) - 1
    n = r + s
    columns = []
    for j in range(r):
        columns.append(([Q(0)] * j + h + [Q(0)] * n)[:n])
    for j in range(s):
        columns.append(([Q(0)] * j + g + [Q(0)] * n)[:n])
    return [[columns[j][i] for j in range(n)] for i in range(n)]


def factor_run(delta, steps=7):
    g, h = list(map(Q, [0, 0, 1])), list(map(Q, [4, -4, 1]))
    L = sylvester_map(g, h)
    S = inverse(L)
    check(matmul(L, S) == identity(4), 'right inverse')
    check(matmul(S, L) == identity(4), 'left inverse')
    K = max(Q(1), max(sum(abs(S[i][j]) for i in range(4)) for j in range(4)))
    Lnorm = max(sum(abs(L[i][j]) for i in range(4)) for j in range(4))
    rho = 1 / (4 * K)
    E = [delta, Q(0), Q(0), Q(0)]
    check(K == Q(3, 2), 'worked K')
    check(rho == Q(1, 6), 'worked radius')
    check(abs(delta) <= 1 / (8 * K * K), 'factor residual guard')
    z = [[Q(0)] * 4]
    f = poly_pad_add(conv(g, h), [delta])
    for n in range(steps):
        u, v = z[-1][:2], z[-1][2:]
        uv = conv(u, v) + [Q(0)]
        nxt = matvec(S, sub(E, uv))
        check(l1(nxt) <= rho, 'factor invariant')
        check(l1(sub(nxt, z[-1])) <= K * abs(delta) / 2 ** n, 'factor increment')
        gp, hp = poly_pad_add(g, u), poly_pad_add(h, v)
        residual = sub(f, conv(gp, hp))
        linear_residual = matvec(L, sub(nxt, z[-1])) + [Q(0)]
        check(residual == linear_residual, 'exact factor residual identity')
        check(l1(residual) <= Lnorm * K * abs(delta) / 2 ** n, 'factor residual bound')
        z.append(nxt)
    for n in range(steps + 1):
        for m in range(n, steps + 1):
            check(l1(sub(z[m], z[n])) <= 2 * K * abs(delta) / 2 ** n, 'factor finite tail')
    return z, K


def main():
    # Full symbolic coefficient compiler, with a nonzero center.
    center = [Q(1, 3), Q(-1, 2)]
    F = [{(0, 0): Q(2), (2, 1): Q(3, 4), (0, 2): Q(-2)},
         {(1, 0): Q(-2, 3), (0, 0): Q(1), (1, 2): Q(5, 7)}]
    B = [[Q(1), Q(1, 3)], [Q(-1, 5), Q(2)]]
    Tcompiled = compile_update(F, center, B)
    grid = [Q(-1), Q(-1, 3), Q(0), Q(1, 2), Q(1)]
    for x in product(grid, repeat=2):
        directF = [peval(p, [a + b for a, b in zip(center, x)]) for p in F]
        direct = sub(x, matvec(B, directF))
        check([peval(p, x) for p in Tcompiled] == direct, 'symbolic compiler')

    # Automatic Jacobian radius: sqrt(2) from the rational center 3/2.
    sqrt_map = compile_update([{(2,): Q(1), (0,): Q(-2)}], [Q(3, 2)], [[Q(1, 3)]])
    check(sqrt_map == [{(0,): Q(-1, 12), (2,): Q(-1, 3)}], 'linear cancellation under preconditioning')
    check(certify(sqrt_map, [[Q(1, 3)]], [[Q(3)]], [Q(1)], Q(1, 2)) == [[Q(1, 3)]],
          'automatic Jacobian-radius certificate')

    # Finite theta-power to ordinary-derivative coefficient identity.
    stirling = [[1]]
    for n in range(6):
        prev = stirling[-1]
        stirling.append([j * (prev[j] if j < len(prev) else 0) +
                         (prev[j - 1] if j > 0 else 0) for j in range(n + 2)])
    for n in range(7):
        for m in range(10):
            falling, total = 1, 0
            for j in range(n + 1):
                if j > 0:
                    falling *= m - (j - 1)
                total += stirling[n][j] * falling
            check(total == m ** n, 'theta derivative expansion')

    # The report's coupled nonlinear example.
    T = [{(0, 0): Q(1, 10), (0, 1): Q(1), (2, 0): Q(1, 100)},
         {(0, 0): Q(1, 20), (1, 0): Q(1, 32), (0, 2): Q(1, 100)}]
    v, r = [Q(4), Q(1)], Q(1, 4)
    W = certify(T, identity(2), identity(2), v, r)
    check(W is not None, 'accept nonlinear certificate')
    check(W == [[Q(1, 50), Q(1)], [Q(1, 32), Q(1, 200)]], 'computed gain')
    check(matvec(W, v) == [Q(27, 25), Q(13, 100)], 'weighted gain values')
    check(sum(W[0]) > 1, 'unweighted contraction test fails')
    points = list(product([Q(-1), Q(-1, 2), Q(0), Q(1, 2), Q(1)],
                          [Q(-1, 4), Q(0), Q(1, 4)]))
    for a in points:
        for b in points:
            difference = [abs(peval(p, a) - peval(p, b)) for p in T]
            majorant = matvec(W, [abs(c - d) for c, d in zip(a, b)])
            check(all(x <= y for x, y in zip(difference, majorant)), 'coefficient Lipschitz')
    orbit = [[Q(0), Q(0)]]
    c0 = weighted([peval(p, orbit[0]) for p in T], v)
    for n in range(8):
        nxt = [peval(p, orbit[-1]) for p in T]
        check(weighted(nxt, v) <= r, 'nonlinear invariant')
        check(weighted(sub(nxt, orbit[-1]), v) <= c0 / 2 ** n, 'nonlinear increment')
        orbit.append(nxt)
    for n in range(len(orbit)):
        for j in range(len(orbit) - n):
            actual = weighted(sub(orbit[n + j], orbit[n]), v)
            bound = 2 * c0 * Q(1, 2 ** n) * (1 - Q(1, 2 ** j))
            check(actual <= bound, 'sharp nonlinear finite tail')
    # Reject invalid data instead of silently applying an estimate.
    check(certify(T, identity(2), identity(2), [Q(1), Q(1)], r) is None,
          'reject unweighted certificate')
    check(certify(T, identity(2), identity(2), v, Q(0)) is None,
          'reject zero radius')

    deltas = [Q(-1, 100), Q(0), Q(1, 100), Q(1, 50)]
    runs = {delta: factor_run(delta)[0] for delta in deltas}
    for a in deltas:
        for b in deltas:
            for za, zb in zip(runs[a], runs[b]):
                check(l1(sub(za, zb)) <= 3 * abs(a - b), 'factor parameter stability')

    report = {
        'status': 'all exact rational checks passed',
        'assertions': ASSERTIONS,
        'method': 'Python fractions.Fraction; no floating point tolerance',
        'scope': ['symbolic polynomial shift and preconditioned-map compiler',
                  'weighted coefficient certificate', 'coupled nonlinear finite iteration',
                  'Sylvester inverse and residual identity',
                  'factor tails and coefficient perturbation'],
        'worked_factor': {'K': '3/2', 'radius': '1/6', 'delta_bound': '1/18',
                          'first_correction_at_delta_1_100': [str(q) for q in runs[Q(1, 100)][1]]},
        'limitations': 'Finite examples only. Universal proof is in the report; Lean uncompiled.'
    }
    path = Path(__file__).resolve().parents[1] / 'verification/polynomial_checks.json'
    path.parent.mkdir(exist_ok=True)
    path.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
