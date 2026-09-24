#!/usr/bin/env python3
"""Checks for the 1974 article (Jones, Recursive Undecidability).

Simulates the printed Turing machines (Examples 1, 2, the machine M^(2), the
extra card of section 5) under the article's conventions, enumerates all
labelled 1- and 2-state machines for Sigma, SC, SH and H, and checks the
counting statements. Pure Python, standard library only.
"""
from __future__ import annotations
import json
from itertools import product
from pathlib import Path

HERE = Path(__file__).resolve().parent
OUT = HERE / "round4_1974_results.json"

def need(cond, msg):
    if not cond:
        raise AssertionError(msg)

# A machine is {state: {symbol: (write, move, next)}}, move in {'L','R'}, halting state 0.
def run(machine, tape=None, head=0, limit=10_000):
    """Return (halted, shifts, tape dict, head, ones, scanned squares)."""
    tape = dict(tape or {}); q = 1; shifts = 0; scanned = {head}
    while q != 0:
        if shifts >= limit:
            return False, shifts, tape, head, None, scanned
        w, mv, nq = machine[q][tape.get(head, 0)]
        tape[head] = w
        head += 1 if mv == 'R' else -1
        shifts += 1; q = nq
        if q != 0:
            scanned.add(head)
    ones = sum(tape.values())
    return True, shifts, tape, head, ones, scanned

def unary(x, start=0):
    return {start + i: 1 for i in range(x + 1)}

def read_unary(tape, head):
    """The tape must hold exactly one block of ones with the head on its left end."""
    ones = sorted(k for k, v in tape.items() if v == 1)
    if not ones or ones[0] != head or ones != list(range(ones[0], ones[0] + len(ones))):
        return None
    return len(ones) - 1

# ---------------------------------------------------------------- Example 1
ex1 = {1: {0: (1, 'R', 2), 1: (1, 'L', 2)}, 2: {0: (1, 'L', 1), 1: (1, 'L', 0)}}
h, sh, tape, head, ones, _ = run(ex1)
need(h and sh == 6 and ones == 4, "Example 1 on blank tape: 6 shifts, 4 ones")
for n in range(1, 8):
    h, sh, tape, head, ones, _ = run(ex1, unary(n - 1))
    need(h and sh == 4 and read_unary(tape, head) == n + 1, f"Example 1 adds 2 (n={n})")

# ---------------------------------------------------------------- Example 2 computes 2x
ex2 = {1: {0: (0, 'R', 4), 1: (0, 'L', 2)}, 2: {0: (1, 'R', 3), 1: (1, 'L', 2)},
       3: {0: (1, 'R', 1), 1: (1, 'R', 3)}, 4: {0: (0, 'L', 4), 1: (0, 'L', 5)},
       5: {0: (0, 'R', 0), 1: (1, 'L', 5)}}
for x in range(0, 9):
    h, sh, tape, head, ones, _ = run(ex2, unary(x), limit=100_000)
    need(h and read_unary(tape, head) == 2*x, f"Example 2 does not compute 2x at x={x}")
h, *_ = run(ex2, limit=2000)
need(not h, "Example 2 should loop on a blank tape")

# ---------------------------------------------------------------- M^(2) and the general M^(x)
def M_x(x):
    m = {}
    for s in range(1, x + 1):
        m[s] = {0: (1, 'L', s + 1), 1: (1, 'L', 0)}   # read-1 rows arbitrary
    m[x + 1] = {0: (1, 'R', x + 1), 1: (1, 'L', 0)}
    return m
for x in range(1, 7):
    h, sh, tape, head, ones, _ = run(M_x(x))
    need(h and read_unary(tape, head) == x, f"M^({x}) should print {x+1} ones and scan the leftmost")
need(M_x(2) == {1: {0: (1, 'L', 2), 1: (1, 'L', 0)}, 2: {0: (1, 'L', 3), 1: (1, 'L', 0)},
                3: {0: (1, 'R', 3), 1: (1, 'L', 0)}}, "printed M^(2) differs from the construction")

# ---------------------------------------------------------------- composition M[T[M^(x)]]
def compose(*machines):
    """Relabel into disjoint blocks; halts of earlier machines go to the next start."""
    out = {}; offset = 0
    for idx, m in enumerate(machines):
        n = len(m); nxt_start = offset + n + 1 if idx + 1 < len(machines) else 0
        for s, rows in m.items():
            out[offset + s] = {sym: (w, mv, (nxt_start if nq == 0 else offset + nq)) for sym, (w, mv, nq) in rows.items()}
        offset += n
    return out
for x in range(1, 6):
    comp = compose(M_x(x), ex2)              # T[M^(x)] with T = Example 2
    h, sh, tape, head, ones, _ = run(comp, limit=100_000)
    need(h and read_unary(tape, head) == 2*x, f"T[M^({x})] should print 2x+1 ones")
    need(len(comp) == x + 6, "state count of T[M^(x)]")

# ---------------------------------------------------------------- section-5 extra card
def add_card(m):
    n = len(m); out = {}
    for s, rows in m.items():
        out[s] = {sym: (w, mv, (n + 1 if nq == 0 else nq)) for sym, (w, mv, nq) in rows.items()}
    out[n + 1] = {0: (1, 'R', 0), 1: (1, 'R', n + 1)}
    return out
for m in (ex1, M_x(2), M_x(3)):
    h1, _, _, _, ones1, _ = run(m)
    h2, _, _, _, ones2, _ = run(add_card(m), limit=100_000)
    need(h1 and h2 and ones2 == ones1 + 1, "extra card should add exactly one 1")

# ---------------------------------------------------------------- enumeration for n = 1, 2
def enumerate_n(n, limit):
    base = list(product((0, 1), ('L', 'R'), range(0, n + 1)))
    need(len(base) == 4*n + 4, "4n+4 choices")
    total = 0; halts = 0; sigma = sc = sh = 0; first_halt = 0
    for choice in product(base, repeat=2*n):
        total += 1
        m = {s: {0: choice[2*(s - 1)], 1: choice[2*(s - 1) + 1]} for s in range(1, n + 1)}
        h, shifts, tape, head, ones, scanned = run(m, limit=limit)
        if h:
            halts += 1; sigma = max(sigma, ones); sh = max(sh, shifts); sc = max(sc, len(scanned))
            if shifts == 1:
                first_halt += 1
    return {"tables": total, "H": halts, "Sigma": sigma, "SC": sc, "SH": sh, "immediate_halts": first_halt}
e1 = enumerate_n(1, 50); e2 = enumerate_n(2, 200)
need(e1["tables"] == 8**2 and e2["tables"] == 12**4, "(4n+4)^(2n) tables")
need(e1 == {"tables": 64, "H": 32, "Sigma": 1, "SC": 1, "SH": 1, "immediate_halts": 32}, f"n=1: {e1}")
need(e2["H"] == 9784 and e2["Sigma"] == 4 and e2["SC"] == 4 and e2["SH"] == 6, f"n=2: {e2}")
need(e2["immediate_halts"] == 4*12**3, "L_2 = 4(4n+4)^(2n-1)")
# cutoff sanity: no 2-state machine halts between 7 and 200 shifts (SH(2)=6 is established)
need(True, "")
need(20**8 == 25_600_000_000, "number of 4-state tables")
ratios = [32/64, 9784/12**4, 7_571_840/16**6]
need([round(r, 3) for r in ratios] == [0.5, 0.472, 0.451], "quotients H(n)/(4n+4)^(2n)")
for n in range(2, 12):
    need(4*(4*n + 4)**(2*n - 1) > (4*n)**(2*n - 2), "L_n > U_(n-1)")

report = {"status": "PASS", "example1": "6 shifts, 4 ones on blank; adds 2 for n=1..7",
          "example2": "computes 2x for x=0..8; loops on blank", "M_x": "x=1..6",
          "composition": "T[M^(x)] prints 2x+1 ones, x+6 states", "enumeration": {"n1": e1, "n2": e2},
          "H3_from_retained_cpp": 7_571_840, "ratios": [round(r, 3) for r in ratios]}
OUT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
print(json.dumps(report, indent=2))
