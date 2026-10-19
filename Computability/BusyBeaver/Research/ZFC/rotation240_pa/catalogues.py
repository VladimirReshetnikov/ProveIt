"""Control catalogues of the Prog254 and Rotation240 decoder trees.

Mirrors the Lean definitions exactly:
  * `FiniteControlTable254.leafEntries` (false-first DFS leaf list),
  * `RegisterPath.walk`/`consume`/`incPath`/`breakPath`/`continuePath`,
  * `ArithmeticControlData254.successorNumber` (resolve the outgoing path,
    number = index + 1; halt has successor 0).

Untrusted generator code: every table it emits is re-checked by the Lean kernel.
"""
import json
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
ZFC = os.path.dirname(HERE)
LEAN = os.path.join(os.path.dirname(os.path.dirname(ZFC)), "Lean", "BusyBeaver", "ZFC")

# Edge kinds: ("inc", r) ("decnz", r) ("brk", k) ("cont", k) ("halt", 0)


def parse_lean_tree(text):
    """Parse the literal `RMBisim.Tree` term of ActualTree254.lean."""
    start = text.index("def tree : Tree :=")
    body = text[start + len("def tree : Tree :="):]
    tokens = re.findall(r"\(|\)|\.node|\.leaf|\.none|\.inc|\.decnz|\.brk|\.cont|\.halt|\d+", body)
    pos = 0

    def parse():
        nonlocal pos
        t = tokens[pos]
        if t == "(":
            pos += 1
            v = parse()
            assert tokens[pos] == ")", tokens[pos]
            pos += 1
            return v
        if t == ".node":
            pos += 1
            a = parse()
            b = parse()
            return ("node", a, b)
        if t == ".none":
            pos += 1
            return ("none",)
        if t == ".leaf":
            pos += 1
            e = parse_edge()
            return ("leaf", e)
        raise ValueError(t)

    def parse_edge():
        nonlocal pos
        t = tokens[pos]
        if t == "(":
            pos += 1
            e = parse_edge()
            assert tokens[pos] == ")"
            pos += 1
            return e
        pos += 1
        if t == ".halt":
            return ("halt", 0)
        n = int(tokens[pos])
        pos += 1
        return (t[1:], n)

    return parse()


KIND = {"CD": "decnz", "CI": "inc", "CB": "brk", "CC": "cont", "CH": "halt"}


def tree_from_sites(sites):
    root = None

    def insert(t, path, edge):
        if not path:
            assert t is None, "duplicate leaf"
            return ("leaf", edge)
        a, b = (None, None) if t is None else (t[1], t[2])
        if path[0] == "0":
            a = insert(a, path[1:], edge)
        else:
            b = insert(b, path[1:], edge)
        return ("node", a, b)

    for path, kind, arg in sites:
        edge = (KIND[kind], arg if kind != "CH" else 0)
        root = insert(root, path, edge)

    def close(t):
        if t is None:
            return ("none",)
        if t[0] == "node":
            return ("node", close(t[1]), close(t[2]))
        return t

    return close(root)


def leaf_entries(t):
    if t[0] == "none":
        return []
    if t[0] == "leaf":
        return [((), t[1])]
    return ([((False,) + p, e) for p, e in leaf_entries(t[1])] +
            [((True,) + p, e) for p, e in leaf_entries(t[2])])


def twalk(t, P, d=0):
    """RMBisim.twalk with implicit trailing false bits."""
    i = 0
    while True:
        if t[0] == "none":
            return None
        if t[0] == "leaf":
            return t[1], d
        b = P[i] if i < len(P) else False
        t = t[2] if b else t[1]
        i += 1
        d += 1


def consume(P, d):
    return tuple((list(P) + [False] * d)[:d])


def inc_path(P):
    R = list(reversed(P))
    out = []
    i = 0
    while i < len(R):
        if not R[i]:
            out.append(True)
            out.extend(R[i + 1:])
            return tuple(reversed(out))
        out.append(False)
        i += 1
    return tuple(reversed(out))


def strip_path(b, k, P):
    R = list(reversed(P))
    i = 0
    while k > 0 and i < len(R):
        if R[i] == b:
            k -= 1
        i += 1
    return tuple(reversed(R[i:]))


def break_path(k, P):
    return inc_path(strip_path(False, k, P))


def continue_path(k, P):
    return strip_path(True, k, P)


def outgoing(P, e, positive):
    kind, a = e
    if kind == "inc":
        return inc_path(P)
    if kind == "decnz":
        return inc_path(P) if positive else break_path(1, P)
    if kind == "brk":
        return break_path(a, P)
    if kind == "cont":
        return continue_path(a, P)
    return P


OPCODE = {"inc": 1, "decnz": 2, "brk": 3, "cont": 3, "halt": 4}


class Catalogue:
    def __init__(self, tree):
        self.tree = tree
        self.entries = leaf_entries(tree)
        self.index = {ent: i for i, ent in enumerate(self.entries)}

    def resolve(self, P):
        e, d = twalk(self.tree, P)
        return self.index[(consume(P, d), e)]

    def rows(self):
        """(opcode, logical register, next number on zero, next number on positive)."""
        out = []
        for P, e in self.entries:
            kind, a = e
            op = OPCODE[kind]
            reg = a if kind in ("inc", "decnz") else 0
            if kind == "halt":
                n0 = n1 = 0
            else:
                n0 = self.resolve(outgoing(P, e, False)) + 1
                n1 = self.resolve(outgoing(P, e, True)) + 1
            out.append((op, reg, n0, n1))
        return out

    def start(self):
        return self.resolve(()) + 1


def prog254():
    with open(os.path.join(LEAN, "ActualTree254.lean"), encoding="utf-8") as f:
        return Catalogue(parse_lean_tree(f.read()))


def rotation240():
    with open(os.path.join(ZFC, "candidate-rotation240", "sites_logical.json"), encoding="utf-8") as f:
        return Catalogue(tree_from_sites(json.load(f)))


if __name__ == "__main__":
    a = prog254()
    b = rotation240()
    print("prog254 leaves", len(a.entries), "start", a.start())
    print("rotation240 leaves", len(b.entries), "start", b.start())


def parse_dag254():
    """`Dag254.dagNodes` as {n: (car, cdr)} with edges ("node", m) or leaves."""
    with open(os.path.join(LEAN, "Dag254.lean"), encoding="utf-8") as f:
        text = f.read()
    nodes = {}
    pat = re.compile(r"^  \| (\d+) => \((.*)\)\s*--", re.M)
    edge_pat = re.compile(r"\(?\.(node|inc|decnz|brk|cont|halt)(?: (\d+))?\)?")
    for m in pat.finditer(text):
        n = int(m.group(1))
        es = edge_pat.findall(m.group(2))
        assert len(es) == 2, (n, m.group(2))
        nodes[n] = tuple((k, int(a) if a else 0) for k, a in es)
    return nodes


def dag_tree(nodes, root=0, fuel=220):
    """`RMBisim.toTree (ofDag dag254 219) 220 root`."""
    def go(f, n):
        if f == 0:
            return ("none",)
        car, cdr = nodes[n]

        def child(e):
            return go(f - 1, e[1]) if e[0] == "node" else ("leaf", e)
        return ("node", child(car), child(cdr))
    return go(fuel, root)


def dag254():
    return Catalogue(dag_tree(parse_dag254()))
