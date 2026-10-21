"""Generate an offset-bisimulation certificate (K230F/K226F OffsetBisim230.v format).

Emulates exactly the Rocq definitions of K230's RM.v and Bisim230.v: twalk/tsite (bits actually
read, zero padded), inc_path, strip_path, brk, cont and seg with seg_fuel = 1000. Entries are
(P1, P2, z, j, k): checkpoints of program 1 (new source) and program 2 (K230 source) at the same
decrement (offset of the tested register zero) or both at halt; j, k index the entries reached
on the successful-decrement and zero branches. Entry 0 is the target of the root branch.
Usage: gen_cert.py NEW_SITES.json K230_SITES.json NAME OUT.v"""
import json, sys
from collections import deque

sys.setrecursionlimit(100000)
SEG_FUEL = 1000


def load(path):
    out = {}
    for s in json.load(open(path)):
        p, o = s[0], s[1]
        if isinstance(o, str) and " " in o:          # k230 'EInc 8' format
            t = o.split(); o, a = t[0], (int(t[1]) if len(t) > 1 else None)
        else:
            a = s[2] if len(s) > 2 else None
        code = {"CI": "EInc", "CD": "EDecnz", "CB": "EBreak", "CC": "EContinue", "CH": "EHalt"}.get(o, o)
        out[tuple(c == "1" for c in p)] = (code, a)
    return out


class Tree:
    def __init__(self, leaf):
        self.leaf = leaf
        self.inner = {p[:i] for p in leaf for i in range(len(p))}

    def tsite(self, P):
        node = ()
        i = 0
        while True:
            b = P[i] if i < len(P) else False
            node = node + (b,)
            i += 1
            if node in self.leaf:
                d = i
                Q = tuple((list(P) + [False] * d)[:d])
                return self.leaf[node], Q
            if node not in self.inner:
                return None


def inc_path(P):
    l = list(reversed(P)); out = []
    while l:
        x = l.pop(0)
        if not x:
            out.append(True); out.extend(l); break
        out.append(False)
    return tuple(reversed(out))


def strip_path(b, k, P):
    l = list(reversed(P))
    while k > 0 and l:
        x = l.pop(0)
        if x == b:
            k -= 1
    return tuple(reversed(l))


def brk(k, P): return inc_path(strip_path(False, k, P))
def cont(k, P): return strip_path(True, k, P)


def seg(t, P):
    incs = []
    for _ in range(SEG_FUEL):
        r = t.tsite(P)
        if r is None:
            return None
        (op, a), Q = r
        if op == "EInc":
            incs.append(a); P = inc_path(Q)
        elif op == "EBreak":
            P = brk(a, Q)
        elif op == "EContinue":
            P = cont(a, Q)
        elif op in ("EDecnz", "EHalt"):
            return incs, P
        else:
            return None
    return None


def generate(t1, t2):
    index, entries, queue = {}, [], deque()
    def target(A, B, z):
        s1, s2 = seg(t1, A), seg(t2, B)
        assert s1 and s2, ("segment failed", A, B)
        (l1, Q1), (l2, Q2) = s1, s2
        regs = set(l1) | set(l2) | {5}
        for i in regs:
            if i != 5:
                assert l1.count(i) == l2.count(i), ("increment mismatch", i, A, B)
        z2 = z + l1.count(5) - l2.count(5)
        key = (Q1, Q2, z2)
        if key not in index:
            index[key] = len(entries); entries.append([Q1, Q2, z2, None, None]); queue.append(key)
        return index[key]
    root = target((), (), 0)
    assert root == 0
    while queue:
        P1, P2, z = queue.popleft()
        e = entries[index[(P1, P2, z)]]
        (o1, a1), Q1 = t1.tsite(P1); (o2, a2), Q2 = t2.tsite(P2)
        if o1 == "EHalt" and o2 == "EHalt":
            e[3] = e[4] = 0; continue
        assert o1 == o2 == "EDecnz" and a1 == a2 and (a1 != 5 or z == 0), ("checkpoint mismatch", P1, P2, z, o1, a1, o2, a2)
        e[3] = target(inc_path(Q1), inc_path(Q2), z)
        e[4] = target(brk(1, Q1), brk(1, Q2), z)
    return entries


def coq_bits(P): return "[" + ";".join("true" if b else "false" for b in P) + "]"


if __name__ == "__main__":
    new, old, name, out = sys.argv[1:5]
    entries = generate(Tree(load(new)), Tree(load(old)))
    lines = [f"  ({coq_bits(a)}, {coq_bits(b)}, {z}%Z, {j}%N, {k}%N)" for a, b, z, j, k in entries]
    with open(out, "w", newline="\n") as f:
        f.write("(** Generated untrusted paired checkpoint certificate; checked by the offset-aware Bisim checker. *)\n"
                "From Coq Require Import List NArith ZArith.\nImport ListNotations.\n"
                f"Definition {name} : list (list bool * list bool * Z * N * N) := [\n" + ";\n".join(lines) + "\n].\n")
    nz = sum(1 for e in entries if e[2] != 0)
    print(len(entries), "entries;", nz, "with nonzero offset")
