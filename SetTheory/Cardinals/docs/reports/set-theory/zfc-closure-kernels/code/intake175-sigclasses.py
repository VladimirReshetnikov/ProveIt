"""Signature classes of the distinct interior nodes of a source DAG.

signature(n) = the ordered list of n's instructions, each with its control
targets expressed relative to n (internal index, or an escaping break/continue
with the number of ancestors still needed, or halt). This is Source 105's
exact local-control signature (exact_reassociate.signature_by_paths). Two nodes
with equal signatures are interchangeable in every surrounding context.
Usage: sigclasses.py SITES.json
"""
import sys
from collections import defaultdict
from dag import DAG, load_sites

d = DAG(load_sites(sys.argv[1]))
memo = {}


def paths(n):
    if n in memo:
        return memo[n]
    x = d.struct[n]
    if isinstance(x[0], str):
        r = (("", x[0], x[1]),)
    else:
        r = tuple((str(b) + p, o, a) for b in (0, 1) for p, o, a in paths(x[b]))
    memo[n] = r
    return r


def signature(n):
    pp = paths(n)
    count = len(pp)
    iv = {}
    for i, (p, o, r) in enumerate(pp):
        for k in range(len(p) + 1):
            s = p[:k]
            if s not in iv:
                iv[s] = [i, i + 1]
            else:
                iv[s][1] = i + 1

    def brk(p, k):
        cuts = [i for i, b in enumerate(p) if b == "0"]
        if len(cuts) < k:
            return ("break", k - len(cuts))
        dst = iv[p[:cuts[-k]]][1]
        return dst if dst < count else ("break", 0)

    def cont(p, k):
        cuts = [i for i, b in enumerate(p) if b == "1"]
        if len(cuts) < k:
            return ("continue", k - len(cuts))
        return iv[p[:cuts[-k]]][0]

    out = []
    for i, (p, o, r) in enumerate(pp):
        normal = i + 1 if i + 1 < count else ("break", 0)
        dest = ((normal,) if o == "CI" else (brk(p, 1), normal) if o == "CD" else
                (brk(p, r),) if o == "CB" else (cont(p, r),) if o == "CC" else ("halt",))
        out.append((o, r, dest))
    return tuple(out)


cls = defaultdict(list)
for n in d.interior():
    cls[signature(n)].append(n)
multi = {s: ns for s, ns in cls.items() if len(ns) > 1}
print("interior", len(d.interior()), "signature classes", len(cls), "classes with >1 node", len(multi))
for s, ns in sorted(multi.items(), key=lambda kv: len(kv[0])):
    print(f"  {len(s)} instrs, nodes {ns}")
    for n in ns:
        occ = [p for p, m in d.pathnode.items() if m == n]
        print(f"     {n}: {d.shape(n)[:110]}  occurrences {len(occ)} e.g. {occ[:2]}")
