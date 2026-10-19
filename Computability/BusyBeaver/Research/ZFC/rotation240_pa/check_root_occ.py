"""Python model of `ArithmeticDagRun.occB` for the root of dag254.

Checks that the root (node 0) occupies controls 1..N of the dag254 control
catalogue (`emit_bisim_cert.physical_rows(dag254())`, i.e. the packed
`BisimCertRotation240.tableD`) with exit map E (normal -> 1), at decoder fuel
F. Mirrors `size`, `leafRow`, `carExit`, `cdrExit`, `occB` exactly, so the
kernel check `occB ... = true` in `ArithmeticL2Scheduler254` is predicted.
Usage: check_root_occ.py [FUEL]
"""
import sys
from catalogues import dag254, parse_dag254
from emit_bisim_cert import physical_rows, PHYS

sys.setrecursionlimit(100000)
NODES = parse_dag254()


def size(f, e):
    if f == 0:
        return 0
    if e[0] == "node":
        a, b = NODES[e[1]]
        return size(f - 1, a) + size(f - 1, b)
    return 1


def leaf_row(e, E):
    k, a = e
    if k == "inc":
        return (1, PHYS[a], E(("normal",)), E(("normal",)))
    if k == "decnz":
        return (2, PHYS[a], E(("brk", 1)), E(("normal",)))
    if k == "brk":
        return (3, 0, E(("normal",)), E(("normal",))) if a == 0 else (3, 0, E(("brk", a)), E(("brk", a)))
    if k == "cont":
        return None if a == 0 else (3, 0, E(("cont", a)), E(("cont", a)))
    if k == "halt":
        return (4, 0, 0, 0)
    return None


def car_exit(c, ncar, E):
    def F(X):
        if X[0] == "normal":
            return c + ncar
        if X[0] == "brk":
            return E(("normal",)) if X[1] <= 1 else E(("brk", X[1] - 1))
        if X[0] == "cont":
            return E(X)
        return 0
    return F


def cdr_exit(c, E):
    def F(X):
        if X[0] in ("normal", "brk"):
            return E(X)
        if X[0] == "cont":
            if X[1] == 1:
                return c
            return E(("cont", X[1] - 1)) if X[1] >= 2 else E(("cont", 0))
        return 0
    return F


def occ(rows, f, e, c, E):
    if f == 0:
        return False
    if e[0] == "node":
        a, b = NODES[e[1]]
        na = size(f - 1, a)
        return occ(rows, f - 1, a, c, car_exit(c, na, E)) and occ(rows, f - 1, b, c + na, cdr_exit(c, E))
    r = leaf_row(e, E)
    got = rows.get(c)
    if r is None or got != r:
        print("mismatch at control", c, e, "want", r, "got", got)
        return False
    return True


if __name__ == "__main__":
    fuel = int(sys.argv[1]) if len(sys.argv) > 1 else 221
    rows = {i + 1: r for i, r in enumerate(physical_rows(dag254()))}
    print("rows", len(rows), "root size", size(fuel, ("node", 0)))
    print("occB", occ(rows, fuel, ("node", 0), 1, lambda X: 1))
