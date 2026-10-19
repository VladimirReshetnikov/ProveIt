"""Re-derive the 236-state construction from the literal files (run from the candidate directory).

1. Rotation: the rotated 237 table differs from the composed 237 table in exactly the
   four decoder rows 177/0, 177/1, 185/0, 185/1.
2. Source: the rotated source has the same ordered instruction list and the same
   control targets for every guard as the composed 237's source (complete control
   graph computed from leaf paths alone), and 224 distinct subtrees.
3. Fold: the 236 table is the rotated 237 table with 223 deleted, 237/0 redirected
   to 182, and 182's rows replaced; every other row is unchanged.
4. Invariant: every row entering old 182 writes 1 and moves right, every row
   entering old 223 writes 0 and moves right, and 95 is neither; so at 182 the cell to
   the left is 1 and at 223 it is 0, on every initial tape.
5. Blocks: each of the four exceptional old steps equals a three-step new block on
   every 7-cell window satisfying the invariant (same tape, head and mapped state).
"""
import itertools
import json
import sys

sys.path.insert(0, __file__.rsplit("code", 1)[0] + "code")
from tm import load  # noqa: E402

T237 = load("ingredients/composed237_old.tm")
ROT = load("ingredients/rotated237_old.tm")
NEW = load("zfc236_old.tm")

# 1. rotation rows
diff = sorted(k for k in T237 if T237[k] != ROT[k])
assert diff == [(177, 0), (177, 1), (185, 0), (185, 1)], diff
print("1. rotation: rows", [f"{q}/{b}: {T237[(q,b)]} -> {ROT[(q,b)]}" for q, b in diff])

# 2. source control graph
def graph(rows):
    leaf = {p: (o, a) for p, o, a in rows}
    internal = {p[:i] for p in leaf for i in range(len(p))}
    assert not internal & leaf.keys() and len(internal) + 1 == len(leaf)
    order = sorted(leaf); ordinal = {p: i for i, p in enumerate(order)}
    def first(p):
        while p not in leaf:
            p += "0"
        return ordinal[p]
    def nxt(p):
        i = p.rfind("0")
        return p[:i] + "1" if i >= 0 else ""
    def cut(p, bit, k):
        f = [i for i, b in enumerate(p) if b == bit]
        return p[:f[-k]] if len(f) >= k else ""
    out = []
    for p in order:
        o, a = leaf[p]
        tg = ([first(nxt(p))] if o == "CI" else [first(nxt(cut(p, "0", 1))), first(nxt(p))] if o == "CD"
              else [first(nxt(cut(p, "0", a)))] if o == "CB" else [first(cut(p, "1", a))] if o == "CC" else ["HALT"])
        out.append((o, a, tuple(tg)))
    return out
def distinct(rows):
    leaf = {p: (o, a) for p, o, a in rows}; ids = {}
    def intern(p):
        key = leaf[p] if p in leaf else (intern(p + "0"), intern(p + "1"))
        return ids.setdefault(key, len(ids))
    intern("")
    return len(ids)
src237 = json.load(open("ingredients/composed237_sites_logical.json"))
src236 = json.load(open("sites_logical.json"))
assert graph(src237) == graph(src236)
print(f"2. source: control graphs equal ({len(src236)} leaves); distinct subtrees "
      f"{distinct(src237)} -> {distinct(src236)}; depth {max(len(p) for p,_,_ in src237)} -> {max(len(p) for p,_,_ in src236)}")

# 3. fold edits
phi = lambda q: 182 if q == 223 else q
expected = {(q, b): (w, d, phi(z)) for (q, b), (w, d, z) in ROT.items() if q != 223}
expected[(182, 0)] = NEW[(182, 0)]; expected[(182, 1)] = NEW[(182, 1)]
assert NEW == expected
print("3. fold: delete 223; 182/0 =", NEW[(182, 0)], " 182/1 =", NEW[(182, 1)], "; other rows map")

# 4. invariant
inc = {s: [(k, v) for k, v in ROT.items() if v[2] == s] for s in (182, 223)}
assert all(v[0] == 1 and v[1] == "R" for _, v in inc[182]) and all(v[0] == 0 and v[1] == "R" for _, v in inc[223])
print("4. invariant: entries", {s: [f"{k[0]}/{k[1]}" for k, _ in v] for s, v in inc.items()})

# 5. blocks
def run(T, q, t, n):
    t = dict(t); h = 0; path = [q]
    for _ in range(n):
        assert h in t
        w, d, z = T[(q, t[h])]; t[h] = w; h += 1 if d == "R" else -1; q = z; path.append(q)
    return q, h, t, path
for q, b in [(182, 0), (182, 1), (223, 0), (223, 1)]:
    left = 1 if q == 182 else 0
    paths = set()
    for vals in itertools.product((0, 1), repeat=7):
        t = dict(zip(range(-4, 3), vals))
        if t[0] != b or t[-1] != left:
            continue
        oq, oh, ot, _ = run(ROT, q, t, 1)
        nq, nh, nt, p = run(NEW, phi(q), t, 3)
        assert (phi(oq), oh, ot) == (nq, nh, nt)
        paths.add(tuple(p))
    assert len(paths) == 1
    print(f"5. block {q}/{b} (left {left}): 1 -> 3: {' -> '.join(map(str, paths.pop()))}")
print("ALL CHECKS PASS")
