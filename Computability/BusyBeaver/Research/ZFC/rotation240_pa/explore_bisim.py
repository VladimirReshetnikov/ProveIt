"""Explore an offset segment bisimulation between two control catalogues.

A state (i, j, alpha, beta) relates A-control number i with register file
f + alpha to B-control number j with file f + beta (common base f arbitrary,
min(alpha, beta) = 0 pointwise). A step runs each side's straight-line
segment (inc / break / continue) up to its next test or halt, then executes
the test. Related tests must read the same register, on which the two
offsets agree after the segments.
"""
import json
import sys
from collections import deque

from catalogues import prog254, rotation240

FUEL = 200


def segment(rows, c):
    """From control number c follow inc/noop rows; return (site, incs, length)."""
    u = [0] * 9
    n = 0
    while True:
        op, r, n0, _ = rows[c - 1]
        if op in (2, 4):
            return c, u, n
        if op == 1:
            u[r] += 1
        c = n0
        n += 1
        if n > FUEL:
            raise RuntimeError("straight-line cycle at %d" % c)


def explore(A, B, startA, startB, cap=1 << 20):
    seen = {}
    order = []
    q = deque()

    def add(st):
        if st not in seen:
            seen[st] = len(order)
            order.append(st)
            q.append(st)

    add((startA, startB, (0,) * 9, (0,) * 9))
    while q:
        i, j, al, be = q.popleft()
        tA, uA, _ = segment(A, i)
        tB, uB, _ = segment(B, j)
        opA, rA, a0, a1 = A[tA - 1]
        opB, rB, b0, b1 = B[tB - 1]
        if opA == 4 and opB == 4:
            continue
        if opA != opB or rA != rB:
            return None, (i, j, al, be, tA, tB, A[tA - 1], B[tB - 1])
        a = [al[k] + uA[k] for k in range(9)]
        b = [be[k] + uB[k] for k in range(9)]
        m = [min(a[k], b[k]) for k in range(9)]
        a = tuple(a[k] - m[k] for k in range(9))
        b = tuple(b[k] - m[k] for k in range(9))
        if a[rA] != 0 or b[rA] != 0:
            return None, ("offset on tested register", i, j, al, be, a, b, rA)
        add((a0, b0, a, b))
        add((a1, b1, a, b))
        if len(order) > cap:
            return None, "cap"
    return order, None


if __name__ == "__main__":
    A = prog254().rows()
    B = rotation240().rows()
    order, err = explore(A, B, 1, 1)
    if err:
        print("FAILED", err)
        sys.exit(1)
    offs = sum(1 for s in order if any(s[2]) or any(s[3]))
    print("entries", len(order), "with nonzero offsets", offs)
    maxoff = max(max(s[2] + s[3]) for s in order)
    print("max offset", maxoff)
    with open("bisim_cert.json", "w", newline="\n") as f:
        json.dump(order, f)
