"""Check that every occurrence of every dag254 node in the path program
`ofDag dag254 219` is a contiguous control block whose rows follow one
context-independent template, with occurrence-specific exit targets.

Template rows: (op, reg, target0, target1); a target is ("in", j) for the
block's j-th leaf or ("ex", x) for the structured exit x of `RMDag.Run`.
"""
from catalogues import dag254, parse_dag254

NORMAL = ("normal",)


def leaf_template(e):
    k, a = e
    if k == "inc":
        return [(1, a, ("ex", NORMAL), ("ex", NORMAL))]
    if k == "decnz":
        return [(2, a, ("ex", ("brk", 1)), ("ex", NORMAL))]
    if k == "brk":
        x = NORMAL if a == 0 else ("brk", a)
        return [(3, 0, ("ex", x), ("ex", x))]
    if k == "cont":
        assert a >= 1
        return [(3, 0, ("ex", ("cont", a)), ("ex", ("cont", a)))]
    if k == "halt":
        return [(4, 0, None, None)]
    raise ValueError(e)


def retarget_car(t, ncar):
    if t is None or t[0] == "in":
        return t
    x = t[1]
    if x == NORMAL:
        return ("in", ncar)
    if x[0] == "brk":
        return ("ex", NORMAL) if x[1] == 1 else ("ex", ("brk", x[1] - 1))
    return t  # cont k propagates unchanged


def retarget_cdr(t, ncar):
    if t is None:
        return t
    if t[0] == "in":
        return ("in", ncar + t[1])
    x = t[1]
    if x == NORMAL or x[0] == "brk":
        return t
    if x[0] == "cont":
        return ("in", 0) if x[1] == 1 else ("ex", ("cont", x[1] - 1))
    return t


def templates(nodes):
    memo = {}

    def edge(e):
        return node(e[1]) if e[0] == "node" else leaf_template(e)

    def node(n):
        if n in memo:
            return memo[n]
        car, cdr = nodes[n]
        tc, td = edge(car), edge(cdr)
        nc = len(tc)
        out = [(op, r, retarget_car(a, nc), retarget_car(b, nc)) for op, r, a, b in tc]
        out += [(op, r, retarget_cdr(a, nc), retarget_cdr(b, nc)) for op, r, a, b in td]
        memo[n] = out
        return out
    return node


def occurrences(nodes, root=0, fuel=220):
    """(node, first leaf index) for every node occurrence in DFS order."""
    out = []
    pos = 0

    def go(f, n):
        nonlocal pos
        out.append((n, pos))
        car, cdr = nodes[n]
        for e in (car, cdr):
            if e[0] == "node":
                go(f - 1, e[1])
            else:
                pos += 1
    go(fuel, root)
    return out


def main():
    nodes = parse_dag254()
    D = dag254()
    rows = D.rows()
    tmpl = templates(nodes)
    bad = 0
    occ = occurrences(nodes)
    for n, b in occ:
        T = tmpl(n)
        E = {}
        for j, (op, r, t0, t1) in enumerate(T):
            aop, ar, a0, a1 = rows[b + j]
            if (aop, ar) != (op, r):
                bad += 1
                break
            for t, actual in ((t0, a0), (t1, a1)):
                if t is None:
                    continue
                if t[0] == "in":
                    if actual != b + t[1] + 1:
                        bad += 1
                else:
                    if E.setdefault(t[1], actual) != actual:
                        bad += 1
    print("nodes", len(nodes), "occurrences", len(occ), "inconsistent", bad)
    print("root template length", len(tmpl(0)))


if __name__ == "__main__":
    main()
