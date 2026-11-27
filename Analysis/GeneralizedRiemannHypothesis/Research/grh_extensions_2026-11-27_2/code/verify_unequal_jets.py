#!/usr/bin/env python3
"""Exact checks for unequal-precision recovery of formal-series jets.

Three independent computations are compared:
  (1) ranks of all observation matrices over a prime field;
  (2) exhaustive products of d-1 branch equations;
  (3) dynamic programming on the contact tree.
Finite checks support, but do not replace, the paper's proof.
Only the Python standard library is required. Run from the archive root:
    python3 code/verify_unequal_jets.py
"""
from functools import lru_cache
from itertools import combinations_with_replacement, product
from pathlib import Path
import json
import random
import time


def rank(rows, p):
    """Row rank, using exact arithmetic (bit elimination for F_2)."""
    pivots = {}
    if p == 2:
        for row in rows:
            x = row if isinstance(row, int) else sum((v & 1) << i for i, v in enumerate(row))
            while x:
                i = x.bit_length() - 1
                if i in pivots:
                    x ^= pivots[i]
                else:
                    pivots[i] = x
                    break
    else:
        for original in rows:
            row = list(original)
            for i in range(len(row)):
                if row[i] % p:
                    if i in pivots:
                        c = row[i] % p
                        row = [(a - c * b) % p for a, b in zip(row, pivots[i])]
                    else:
                        c = pow(row[i] % p, -1, p)
                        pivots[i] = [(c * a) % p for a in row]
                        break
    return len(pivots)


def mul(a, b, n, p):
    c = [0] * n
    for i, x in enumerate(a[:n]):
        if x:
            for j, y in enumerate(b[:n-i]):
                c[i+j] = (c[i+j] + x*y) % p
    return c


def contacts(branches, p):
    N = len(branches)
    out = [[None] * N for _ in range(N)]
    for i in range(N):
        for j in range(i):
            length = max(len(branches[i]), len(branches[j]))
            a = branches[i] + [0] * (length-len(branches[i]))
            b = branches[j] + [0] * (length-len(branches[j]))
            val = next(k for k in range(length) if (a[k]-b[k]) % p)
            assert val >= 1
            out[i][j] = out[j][i] = val
    return out


def monomials(limit):
    return [(i, t-i) for t in range(limit) for i in range(t+1)]


def observation_rows(branches, precision, d, p):
    cutoff = max([d] + list(precision))
    mons = monomials(cutoff)
    rows = []
    for u, n in zip(branches, precision):
        powers = [[1] + [0] * max(0, cutoff-1)]
        for j in range(1, cutoff):
            powers.append(mul(powers[-1], u, cutoff, p))
        block = []
        for k in range(n):
            row = [powers[j][k-i] if k >= i else 0 for i, j in mons]
            if p == 2:
                row = sum((v & 1) << t for t, v in enumerate(row))
            block.append(row)
        rows.append(block)
    target = []
    for t, (i, j) in enumerate(mons):
        if i+j < d:
            target.append((1 << t) if p == 2 else [int(t == k) for k in range(len(mons))])
    return rows, target


def distance_linear(branches, precision, d, p):
    blocks, target = observation_rows(branches, precision, d, p)
    N = len(branches)
    best = -1
    for mask in range(1 << N):
        size = mask.bit_count()
        if size <= best:
            continue
        rows = [row for b in range(N) if mask >> b & 1 for row in blocks[b]]
        if rank(rows + target, p) > rank(rows, p):
            best = size
    return N-best


def distance_products(s, precision, d):
    N = len(s)
    best, witness = -1, None
    for choices in combinations_with_replacement(range(N), d-1):
        covered = [b for b in range(N) if b in choices or sum(s[b][c] for c in choices) >= precision[b]]
        if len(covered) > best:
            best, witness = len(covered), list(choices)
    return N-best, witness


def contact_tree(s):
    """Compressed rooted tree; incoming lengths count common contacts."""
    nodes = []

    def build(leaves, parent_depth):
        idx = len(nodes)
        nodes.append(None)
        if len(leaves) == 1:
            nodes[idx] = {"leaf": leaves[0], "length": 0, "children": []}
            return idx
        depth = min(s[i][j] for z, i in enumerate(leaves) for j in leaves[z+1:])
        groups = []
        for b in leaves:
            for group in groups:
                if s[b][group[0]] > depth:
                    group.append(b)
                    break
            else:
                groups.append([b])
        children = [build(group, depth) for group in groups]
        nodes[idx] = {"length": depth-parent_depth, "children": children}
        return idx

    root = build(list(range(len(s))), 0)
    return nodes, root


def distance_tree(s, precision, d, weights=None):
    N = len(s)
    weights = [1] * N if weights is None else list(weights)
    nodes, root = contact_tree(s)
    cap = max([0] + list(precision))

    @lru_cache(None)
    def solve(v, j, t):
        node = nodes[v]
        if not node["children"]:
            b = node["leaf"]
            return weights[b] if j or t >= precision[b] else 0
        t = min(cap, t + j * node["length"])
        table = [0] + [-10**12] * j
        for child in node["children"]:
            table = [max(table[h] + solve(child, k-h, t) for h in range(k+1)) for k in range(j+1)]
        return table[j]

    return sum(weights) - solve(root, d-1, 0)


def saturation(s, d):
    return [1 + sum(sorted((v for v in row if v is not None), reverse=True)[:d-1]) for row in s]


def run():
    started = time.time()
    counts = {"binary_exhaustive": 0, "ternary_deterministic": 0, "saturation_boundary": 0}
    B2 = [[0], [0, 0, 1], [0, 1], [0, 1, 0, 1]]
    S2 = contacts(B2, 2)
    for precision in product(range(5), repeat=4):
        for d in (1, 2, 3):
            a = distance_linear(B2, precision, d, 2)
            b, _ = distance_products(S2, precision, d)
            c = distance_tree(S2, precision, d)
            assert a == b == c, (precision, d, a, b, c)
            counts["binary_exhaustive"] += 1
    rng = random.Random(20261127)
    B3 = [[0], [0, 0, 0, 1], [0, 1], [0, 2]]
    S3 = contacts(B3, 3)
    for _ in range(160):
        precision = tuple(rng.randrange(7) for _ in B3)
        d = rng.randrange(1, 5)
        a = distance_linear(B3, precision, d, 3)
        b, _ = distance_products(S3, precision, d)
        c = distance_tree(S3, precision, d)
        assert a == b == c, (precision, d, a, b, c)
        counts["ternary_deterministic"] += 1
    for branches, s, p in [(B2, S2, 2), (B3, S3, 3)]:
        for d in range(1, 5):
            nstar = saturation(s, d)
            assert distance_linear(branches, nstar, d, p) == len(branches)-d+1
            for b in range(len(branches)):
                ns = nstar.copy()
                ns[b] -= 1
                assert distance_linear(branches, ns, d, p) < len(branches)-d+1
                counts["saturation_boundary"] += 1
    examples = []
    for precision, d in [([4, 4, 2, 2], 2), ([3, 4, 2, 2], 2), ([5, 5, 3, 3], 2), ([5, 5, 3, 3], 3)]:
        delta, witness = distance_products(S3, precision, d)
        assert delta == distance_linear(B3, precision, d, 3)
        examples.append({"field": 3, "branches": B3, "contacts": S3, "precision": precision,
                         "jet_order": d, "distance": delta, "extremal_product_indices": witness})
    result = {"status": "PASS", "exact_arithmetic": True, "cases": counts, "examples": examples,
              "binary_contact_tree": contact_tree(S2)[0], "ternary_contact_tree": contact_tree(S3)[0],
              "elapsed_seconds": round(time.time()-started, 3),
              "scope": "Finite prime-field checks; not a formal verification of the universal theorem."}
    dest = Path(__file__).resolve().parents[1] / "evidence" / "unequal_jets_checks.json"
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "cases": counts, "seconds": result["elapsed_seconds"]}, indent=2))


if __name__ == "__main__":
    run()
