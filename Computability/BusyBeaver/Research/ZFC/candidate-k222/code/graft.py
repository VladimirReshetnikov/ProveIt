"""Graft a donor's change onto a host source.
Find the smallest path P where DONOR differs from BASE (all differences inside P's subtree);
require HOST's subtree at P to equal BASE's; replace it by DONOR's. Writes OUT sites and prints
node counts. Usage: graft.py BASE DONOR HOST OUT"""
import json, sys

sys.setrecursionlimit(100000)


def tree(path):
    leaf = {s[0]: (s[1], s[2] if len(s) > 2 else None) for s in json.load(open(path))}
    def go(p):
        return ("L",) + leaf[p] if p in leaf else (go(p + "0"), go(p + "1"))
    return go("")


def at(t, p):
    for b in p:
        assert t[0] != "L", "path runs into a leaf"
        t = t[int(b)]
    return t


def put(t, p, s):
    if not p:
        return s
    i = int(p[0])
    return (put(t[0], p[1:], s), t[1]) if i == 0 else (t[0], put(t[1], p[1:], s))


def mindiff(a, b, p=""):
    """smallest path containing every difference of a and b"""
    if a == b:
        return None
    if a[0] == "L" or b[0] == "L":
        return p
    d0, d1 = mindiff(a[0], b[0], p + "0"), mindiff(a[1], b[1], p + "1")
    if d0 is not None and d1 is not None:
        return p
    return d0 if d0 is not None else d1


def sites(t, p="", out=None):
    out = [] if out is None else out
    if t[0] == "L":
        out.append([p, t[1], t[2]])
    else:
        sites(t[0], p + "0", out); sites(t[1], p + "1", out)
    return out


def interior(t):
    ids = set()
    def go(t):
        if t[0] != "L":
            ids.add(t); go(t[0]); go(t[1])
    go(t)
    return len(ids)


def diffs(a, b, p=""):
    """maximal subtrees where a and b differ, descending while both are interior"""
    if a == b:
        return []
    if a[0] == "L" or b[0] == "L":
        return [p]
    return diffs(a[0], b[0], p + "0") + diffs(a[1], b[1], p + "1")


base, donor, host = (tree(f) for f in sys.argv[1:4])
D = diffs(base, donor)
print("donor differs from base at", D, "| donor interior", interior(donor), "host", interior(host))
out = host
for P in D:
    assert at(host, P) == at(base, P), ("host changed the donor region", P)
    out = put(out, P, at(donor, P))
s = sites(out)
z = max(len(x[0]) - len(x[0].rstrip("0")) for x in s)
depth = max(len(x[0]) for x in s)
json.dump(s, open(sys.argv[4], "w"))
print("grafted: leaves", len(s), "interior", interior(out), "depth", depth, "max trailing zero run", z)
