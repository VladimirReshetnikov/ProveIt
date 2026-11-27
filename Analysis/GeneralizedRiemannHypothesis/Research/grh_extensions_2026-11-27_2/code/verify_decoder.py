#!/usr/bin/env python3
"""Exact demonstration of the paper's sufficient linear decoder over F_3.

The decoder uses two linear systems, with no enumeration of error locations.
The verifier does enumerate received words to test that decoder independently.
Its guarantee is delta_(d+w)>w, stronger than the optimal information-theoretic
condition delta_d>2w. Run: python3 code/verify_decoder.py
"""
from itertools import product
from pathlib import Path
import json
import time
from verify_unequal_jets import mul, monomials, contacts, distance_products


def solve(rows, rhs, p, variables):
    A = [[v % p for v in r] + [b % p] for r, b in zip(rows, rhs)]
    pivot_cols = []
    h = 0
    for c in range(variables):
        k = next((k for k in range(h, len(A)) if A[k][c]), None)
        if k is None:
            continue
        A[h], A[k] = A[k], A[h]
        inv = pow(A[h][c], -1, p)
        A[h] = [(inv * v) % p for v in A[h]]
        for k in range(len(A)):
            if k != h and A[k][c]:
                a = A[k][c]
                A[k] = [(v-a*u) % p for v, u in zip(A[k], A[h])]
        pivot_cols.append(c)
        h += 1
        if h == len(A):
            break
    if any(all(v == 0 for v in row[:-1]) and row[-1] for row in A):
        raise ValueError("Inconsistent linear system")
    out = [0] * variables
    for i, c in enumerate(pivot_cols):
        out[c] = A[i][-1]
    return out, len(pivot_cols)


def evaluation_basis(u, mons, n, p):
    powers = [[1] + [0] * (n-1)]
    for j in range(1, max([j for _, j in mons], default=0)+1):
        powers.append(mul(powers[-1], u, n, p))
    return [[0]*i + powers[j][:n-i] if i < n else [0]*n for i, j in mons]


def observe(H, branches, precision, p):
    ans = []
    mons = list(H)
    for u, n in zip(branches, precision):
        basis = evaluation_basis(u, mons, n, p)
        ans.append([sum(H[m]*b[k] for m, b in zip(mons, basis)) % p for k in range(n)])
    return ans


def decode(received, branches, precision, d, w, p):
    cutoff = max(precision)
    qmons = monomials(cutoff)
    emons = [(i, j) for i, j in qmons if j < w and i+j >= w]
    rows, rhs = [], []
    for u, n, y in zip(branches, precision, received):
        qb = evaluation_basis(u, qmons, n, p)
        eb = evaluation_basis(u, emons + [(0, w)], n, p)
        ey = [mul(e, y, n, p) for e in eb]
        for k in range(n):
            rows.append([q[k] for q in qb] + [(-e[k]) % p for e in ey[:-1]])
            rhs.append(ey[-1][k])
    sol, _ = solve(rows, rhs, p, len(qmons)+len(emons))
    Q = dict(zip(qmons, sol[:len(qmons)]))
    E = dict(zip(emons, sol[len(qmons):]))
    E[(0, w)] = 1
    hmons = monomials(d)
    rows, rhs = [], []
    for a, b in monomials(d+w):
        rows.append([E.get((a-i, b-j), 0) if a >= i and b >= j else 0 for i, j in hmons])
        rhs.append(Q.get((a, b), 0))
    h, rk = solve(rows, rhs, p, len(hmons))
    assert rk == len(hmons), "Jet quotient is not unique"
    return dict(zip(hmons, h))


def run():
    start = time.time()
    p, d, w = 3, 2, 1
    branches = [[0], [0, 0, 0, 1], [0, 1], [0, 2]]
    precision = [5, 5, 3, 3]
    S = contacts(branches, p)
    higher_distance, _ = distance_products(S, precision, d+w)
    assert higher_distance > w
    messages = [{}, {(0, 0): 1}, {(1, 0): 1}, {(0, 1): 1},
                {(i, j): (i+2*j+i*j+1) % p for i, j in monomials(max(precision))}]
    checked = 0
    for H in messages:
        expected = {m: H.get(m, 0) for m in monomials(d)}
        word = observe(H, branches, precision, p)
        assert decode(word, branches, precision, d, w, p) == expected
        checked += 1
        for bad, n in enumerate(precision):
            for error in product(range(p), repeat=n):
                if not any(error):
                    continue
                received = [b.copy() for b in word]
                received[bad] = [(a+e) % p for a, e in zip(word[bad], error)]
                assert decode(received, branches, precision, d, w, p) == expected
                checked += 1
    data = {"status": "PASS", "field": p, "jet_order": d, "corrupt_blocks": w,
            "precision": precision, "higher_order_distance": higher_distance,
            "messages": len(messages), "received_words_checked": checked,
            "seconds": round(time.time()-start, 3),
            "decoder": "two exact linear systems; no error-location enumeration in decoder",
            "scope": "All single-block corruptions for five stated messages, not a universal machine proof."}
    path = Path(__file__).resolve().parents[1]/"evidence"/"decoder_checks.json"
    path.write_text(json.dumps(data, indent=2)+"\n")
    print(json.dumps(data, indent=2))


if __name__ == "__main__":
    run()
