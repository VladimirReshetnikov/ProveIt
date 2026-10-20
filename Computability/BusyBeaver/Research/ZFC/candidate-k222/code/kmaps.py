"""Decoder maps of K-labelled K-family tables: from the dispatcher (K label 84), follow every source
prefix through plain decoder rows (write the read bit, move right) and record which state serves
which hash-consed subtree. Compares two tables' rows on common states.
Usage: kmaps.py TA SA TB SB"""
import json, sys
from collections import defaultdict

sys.setrecursionlimit(100000)
DISP = 84


def load(p):
    T = {}
    for l in open(p):
        if l.strip() and not l.startswith("#"):
            q, b, w, d, z = l.split(); T[int(q), int(b)] = (int(w), d, int(z))
    return T


def keys(sites):
    leaf = {s[0]: (s[1], s[2] if len(s) > 2 else None) for s in json.load(open(sites))}
    key = {}
    def go(p):
        k = ("L",) + leaf[p] if p in leaf else (go(p + "0"), go(p + "1"))
        key[p] = k
        return k
    go("")
    return leaf, key


def dmap(T, sites):
    leaf, key = keys(sites)
    serve = defaultdict(set)     # state -> subtree keys (interior)
    where = defaultdict(set)     # subtree key -> states
    leafent = defaultdict(set)   # leaf op -> entry states reached after its last bit
    for p, k in key.items():
        q = DISP; ok = True
        for b in p:
            w, d, z = T[q, int(b)]
            if w != int(b) or d != "R":
                ok = False; break
            q = z
        if not ok:
            continue
        if k[0] == "L":
            leafent[k[1:]].add(q)
        else:
            serve[q].add(k); where[k].add(q)
    return serve, where, leafent, key


if __name__ == "__main__":
    TA, TB = load(sys.argv[1]), load(sys.argv[3])
    sA, wA, lA, kA = dmap(TA, sys.argv[2])
    sB, wB, lB, kB = dmap(TB, sys.argv[4])
    common = set(q for q, _ in TA) & set(q for q, _ in TB)
    diffrows = sorted(q for q in common if TA[q, 0] != TB[q, 0] or TA[q, 1] != TB[q, 1])
    print("states A", len({q for q, _ in TA}), "B", len({q for q, _ in TB}), "common", len(common),
          "common with different rows", len(diffrows))
    print("decoder states A", len(sA), "B", len(sB))
    dec = set(sA) | set(sB)
    eng = sorted(common - dec)
    print("engine-only common states with different rows:", [q for q in diffrows if q not in dec])
    multi = {k: v for k, v in wB.items() if len(v) > 1}
    print("B subtrees served by >1 state:", len(multi))
    ks = set(wA) & set(wB)
    agree = sum(1 for k in ks if wA[k] == wB[k])
    print("subtrees in both:", len(ks), "same serving state:", agree)
    print("leaf entries A:", {k: sorted(v) for k, v in lA.items()})
    print("leaf entries B:", {k: sorted(v) for k, v in lB.items()})
