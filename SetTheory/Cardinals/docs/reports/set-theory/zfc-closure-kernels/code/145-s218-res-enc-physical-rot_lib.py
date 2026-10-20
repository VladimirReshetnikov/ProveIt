"""In-process version of s235/rotgen.py (same admissibility rules and four-row compile).

rotations(T, sites, maxzr) yields (tag, N, new_sites) for every node-neutral closed rotation
X=(A,(B,C)) -> ((A,B),C) [L] or X=((A,B),C) -> (A,(B,C)) [R] that repurposes the inner node's
unshared decoder state: Y has X as its only parent, Z is new, chunk A has no escaping break and
chunk C no escaping continue, and the rotated source has zero run <= maxzr.
"""
from collections import defaultdict


class Dag:
    def __init__(self, sites):
        self.leaf = {p: (o, a) for p, o, a in sites}
        self.ids, self.S, self.pathnode = {}, [], {}
        self.root = self._intern("")

    def _intern(self, p):
        key = self.leaf[p] if p in self.leaf else (self._intern(p + "0"), self._intern(p + "1"))
        if key not in self.ids:
            self.ids[key] = len(self.S); self.S.append(key)
        n = self.ids[key]; self.pathnode[p] = n
        return n

    def inter(self, n):
        return not isinstance(self.S[n][0], str)


def rotations(T, sites, maxzr=6):
    d = Dag(sites); S = d.S
    qnodes = defaultdict(set)
    for p in sorted({p[:i] for p in d.leaf for i in range(len(p))}):
        q = 84
        for b in p:
            w, mv, z = T[(q, int(b))]
            if w != int(b) or mv != "R":
                break
            q = z
        else:
            qnodes[q].add(d.pathnode[p])
    node_states = defaultdict(set)
    for q, ns in qnodes.items():
        for n in ns:
            node_states[n].add(q)
    def state_of(n):
        qs = node_states.get(n, set())
        if len(qs) != 1:
            return None
        q = next(iter(qs))
        return q if qnodes[q] == {n} else None
    parents = defaultdict(set)
    for n in range(len(S)):
        if d.inter(n):
            for c in S[n]:
                parents[c].add(n)
    memo = {}
    def boundary(n):
        if n in memo:
            return memo[n]
        x = S[n]
        if not d.inter(n):
            o, a = x
            r = (1, 0, False) if o == "CD" else (a, 0, False) if o == "CB" else (0, a, False) if o == "CC" else (0, 0, o == "CH")
        else:
            u, v = boundary(x[0]), boundary(x[1])
            r = (max(max(u[0] - 1, 0), v[0]), max(u[1], max(v[1] - 1, 0)), u[2] or v[2])
        memo[n] = r
        return r
    def rebuild(X, newX):
        out = []
        def emit(n, p):
            if n == X:
                emit_tree(newX, p); return
            x = S[n]
            if not d.inter(n):
                out.append([p, x[0], x[1]]); return
            emit(x[0], p + "0"); emit(x[1], p + "1")
        def emit_tree(t, p):
            if isinstance(t, int):
                emit(t, p); return
            emit_tree(t[0], p + "0"); emit_tree(t[1], p + "1")
        emit(d.root, "")
        return sorted(out)
    existing = set(S)
    for X in range(len(S)):
        if not d.inter(X):
            continue
        qX = state_of(X)
        if qX is None:
            continue
        a, b = S[X]
        for kind in ("L", "R"):
            Y = b if kind == "L" else a
            if not d.inter(Y) or parents[Y] != {X}:
                continue
            qY = state_of(Y)
            if qY is None or qY == qX:
                continue
            if kind == "L":
                A, (B, C) = a, S[Y]
            else:
                (A, B), C = S[Y], b
            if boundary(A)[0] != 0 or boundary(C)[1] != 0:
                continue
            if ((A, B) if kind == "L" else (B, C)) in existing:
                continue
            N = dict(T)
            if kind == "L":
                N[(qX, 0)] = (0, "R", qY); N[(qX, 1)] = (1,) + T[(qY, 1)][1:]
                N[(qY, 0)] = (0,) + T[(qX, 0)][1:]; N[(qY, 1)] = (1,) + T[(qY, 0)][1:]
                newX = ((A, B), C)
            else:
                N[(qX, 0)] = (0,) + T[(qY, 0)][1:]; N[(qX, 1)] = (1, "R", qY)
                N[(qY, 0)] = (0,) + T[(qY, 1)][1:]; N[(qY, 1)] = (1,) + T[(qX, 1)][1:]
                newX = (A, (B, C))
            ns = rebuild(X, newX)
            zr = max(max(map(len, p.split("1"))) for p, _, _ in ns)
            if zr > maxzr:
                continue
            yield f"{kind}_{qX}_{qY}", N, ns, zr
