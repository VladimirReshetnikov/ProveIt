#!/usr/bin/env python3
"""Checks for the 1984 article (Jones-Matijasevic, register machines).

Independent re-implementation (standard library only):
  * simulates Example 1 and reproduces the printed 19-column trace for input 2;
  * accepted inputs 2..60 are exactly the primes; inputs 0 and 1 do not stop
    within a generous cutoff (the proof of divergence is the invariant check
    after Example 1 in the edition; editorial notes entry 1984-20);
  * builds Q, I, R_j, L_i from the actual computation for several accepted
    inputs and checks conditions (24)-(39) as integers, using the encodings
    (34), (35), (36) exactly as printed (constant 0 encoded as history 0);
  * checks (8), (9), (11), (12), (13), the Lucas lemma, (43), the
    multiplication macro (45), and the section-4 conditions (47), (49),
    including a counterexample to the printed "+I" form of (49).
"""
from __future__ import annotations
import json
from math import comb
from pathlib import Path

HERE = Path(__file__).resolve().parent
OUT = HERE / "round4_1984_results.json"

def need(cond, msg):
    if not cond:
        raise AssertionError(msg)

def mask(r, s):  # r <= s digitwise in binary
    return r >= 0 and s >= 0 and (r & s) == r

# ---------------------------------------------------------------- Example 1
# Each line: ('assign', [(reg, delta), ...]) | ('ifeq0', reg, target) | ('iflt', a, b, target)
# | ('goto', target) | ('stop',). Operands are register numbers or the constant 0.
PROGRAM = [
    ('assign', [(2, +1)]),                  # L0
    ('assign', [(2, +1)]),                  # L1
    ('ifeq0', 3, 5),                        # L2
    ('assign', [(3, -1)]),                  # L3
    ('goto', 2),                            # L4
    ('assign', [(3, +1), (4, +1), (2, -1)]),# L5
    ('iflt', 0, 2, 5),                      # L6  IF 0 < R2
    ('assign', [(2, +1), (4, -1)]),         # L7
    ('iflt', 0, 4, 7),                      # L8  IF 0 < R4
    ('iflt', 3, 1, 5),                      # L9  IF R3 < R1
    ('iflt', 1, 3, 1),                      # L10 IF R1 < R3
    ('iflt', 2, 1, 10),                     # L11 IF R2 < R1
    ('assign', [(1, -1), (2, -1), (3, -1)]),# L12
    ('iflt', 0, 1, 12),                     # L13 IF 0 < R1
    ('stop',),                              # L14
]
NREG = 4; L = len(PROGRAM) - 1  # lines L0..Ll

def val(regs, operand):
    return 0 if operand == 0 else regs[operand]

def run(x, limit=100_000):
    regs = [None, x, 0, 0, 0]; pc = 0; trace = [(pc, regs[1:])]
    while True:
        ins = PROGRAM[pc]
        if ins[0] == 'stop':
            return ('halt', trace)
        if len(trace) > limit:
            return ('limit', trace)
        if ins[0] == 'assign':
            for reg, d in ins[1]:
                need(regs[reg] + d >= 0, "subtraction from zero")
            for reg, d in ins[1]:
                regs[reg] += d
            pc += 1
        elif ins[0] == 'goto':
            pc = ins[1]
        elif ins[0] == 'ifeq0':
            pc = ins[2] if regs[ins[1]] == 0 else pc + 1
        elif ins[0] == 'iflt':
            pc = ins[3] if val(regs, ins[1]) < val(regs, ins[2]) else pc + 1
        trace.append((pc, regs[1:]))

status, trace = run(2)
need(status == 'halt' and len(trace) - 1 == 18 and trace[-1][1] == [0, 0, 0, 0], "input 2: 18 steps, all zero")
printed_R = {1: "0 0 1 1 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2", 2: "0 0 1 1 2 2 2 2 2 1 1 0 0 1 1 2 2 1 0",
             3: "0 0 1 1 2 2 2 2 2 2 2 2 2 1 1 0 0 0 0", 4: "0 0 0 0 0 0 0 0 0 1 1 2 2 1 1 0 0 0 0"}
for j, row in printed_R.items():
    vals = [int(v) for v in row.split()][::-1]   # printed with time increasing to the left
    need(vals == [regs[j - 1] for _, regs in trace], f"trace row R{j} differs from the printed table")
printed_lines = [0, 1, 2, 5, 6, 5, 6, 7, 8, 7, 8, 9, 10, 11, 12, 13, 12, 13, 14]
need([pc for pc, _ in trace] == printed_lines, "trace L rows differ from the printed table")

def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, int(n**0.5) + 1))
for x in range(2, 61):
    st, tr = run(x)
    accepted = st == 'halt' and tr[-1][1] == [0, 0, 0, 0]
    need(accepted == is_prime(x), f"acceptance differs from primality at {x}")
for x in (0, 1):
    need(run(x, limit=20000)[0] == 'limit', f"input {x} stopped unexpectedly")

# ---------------------------------------------------------------- encoding (24)-(39)
def encode(x):
    st, tr = run(x)
    need(st == 'halt', "encoding only for halting runs")
    s = len(tr) - 1
    q = x + s + L + 2; Q = 2**q
    need(x + s < Q//2 and L + 1 < Q, "(24),(25)")
    I = sum(Q**t for t in range(s + 1))
    need(1 + (Q - 1)*I == Q**(s + 1), "(27)")
    R = {j: sum(tr[t][1][j - 1]*Q**t for t in range(s + 1)) for j in range(1, NREG + 1)}
    Lm = {i: sum((1 if tr[t][0] == i else 0)*Q**t for t in range(s + 1)) for i in range(0, L + 1)}
    hist = lambda operand: 0 if operand == 0 else R[operand]
    need(all(mask(R[j], (Q//2 - 1)*I) for j in R), "(29)")
    need(sum(Lm.values()) == I, "(30)")
    need(all(mask(Lm[i], I) for i in Lm), "(31)")
    need(mask(1, Lm[0]), "(32)")
    need(Lm[L] == Q**s, "(33)")
    for i, ins in enumerate(PROGRAM):
        if ins[0] == 'goto':
            need(mask(Q*Lm[i], Lm[ins[1]]), f"(34) at L{i}")
        elif ins[0] == 'assign':
            need(mask(Q*Lm[i], Lm[i + 1]), f"fall-through at L{i}")
        elif ins[0] == 'ifeq0':
            j, k = ins[1], ins[2]
            need(k not in (i, i + 1), "normalization assumption")
            need(mask(Q*Lm[i], Lm[k] + Lm[i + 1]) and mask(Q*Lm[i], Lm[i + 1] + Q*I - 2*R[j]), f"(35) at L{i}")
        elif ins[0] == 'iflt':
            a, b, k = ins[1], ins[2], ins[3]
            need(k not in (i, i + 1), "normalization assumption")
            need(mask(Q*Lm[i], Lm[k] + Lm[i + 1]) and mask(Q*Lm[i], Lm[k] + Q*I + 2*hist(a) - 2*hist(b)), f"(36) at L{i}")
    for j in range(1, NREG + 1):
        inc = sum(Q*Lm[i] for i, ins in enumerate(PROGRAM) if ins[0] == 'assign' and (j, +1) in ins[1])
        dec = sum(Q*Lm[i] for i, ins in enumerate(PROGRAM) if ins[0] == 'assign' and (j, -1) in ins[1])
        need(R[j] == Q*R[j] + inc - dec + (x if j == 1 else 0), f"register equation ({'38' if j == 1 else '39'}) for R{j}")
    return s
steps = {x: encode(x) for x in (2, 3, 5, 7, 11, 13)}

# ---------------------------------------------------------------- section 2 identities
for n in range(0, 9):
    u = 2**n + 1
    for k in range(0, n + 3):
        # (8): unique w, m, v with (u+1)^n = w u^(k+1) + m u^k + v, v < u^k, m < u
        N = (u + 1)**n; v = N % u**k; m = (N // u**k) % u; w = N // u**(k + 1)
        need(N == w*u**(k + 1) + m*u**k + v and m == comb(n, k), f"(8) fails n={n} k={k}")
for x in range(0, 6):
    for y in range(2, 6):
        need((2**(x*y*y)) % (2**(x*y) - x) == x**y, f"(9) fails x={x} y={y}")
for a in range(0, 40):
    need((a > 0 and mask(a, 2*a - 1)) == (a > 0 and a & (a - 1) == 0), "(12)")
    for b in range(0, 40):
        need(mask(a, b) == ((a & b) == a), "(10)")
        for c in range(0, 40):
            need(((a & b) == c) == (mask(c, b) and mask(b, a + b - c)), "(11)")
    need(mask(a, 2*a - 1) == (comb(2*a - 1, a) % 2 == 1) if a > 0 else True, "Lucas lemma")
for r in range(0, 64):
    for s in range(0, 64):
        need(mask(r, s) == (comb(s, r) % 2 == 1), "Lemma (Lucas) r<=s")
Qs = 16
for a in range(Qs):
    for b in range(Qs):
        for c in range(0, 6):
            for d in range(0, 6):
                need((mask(a, b) and mask(c, d)) == mask(a + c*Qs, b + d*Qs), "(13)")
for R_ in range(0, 40):
    need((R_ % 2 == 0) == (2*((R_ + 1)//2) <= R_), "(43)")

# ---------------------------------------------------------------- multiplication macro (45)
def multiply(rj, rk):
    ri = 0
    while True:
        if rk % 2 == 1:
            ri += rj
        rk //= 2; rj += rj
        if not rk > 0:
            return ri
for a in range(0, 12):
    for b in range(0, 12):
        need(multiply(a, b) == a*b, "(45)")

# ---------------------------------------------------------------- (47) and (49) on a synthetic history
# One register R (contents r_t) and one line n executed at the times in `sel`.
def check_47_49(r_hist, sel, q):
    Q = 2**q; s = len(r_hist) - 1
    I = sum(Q**t for t in range(s + 1))
    Rj = sum(r_hist[t]*Q**t for t in range(s + 1))
    Ln = sum((1 if t in sel else 0)*Q**t for t in range(s + 1))
    M = sum(r_hist[t]*Q**t for t in sel)
    J = sum((r_hist[t]//2)*Q**t for t in sel)
    ok47 = mask(M, Rj) and mask(M, (Q - 1)*Ln) and mask(Rj, (Q - 1)*(I - Ln) + M)
    ok49 = mask(2*J, Rj) and mask(J, (Q//2 - 1)*Ln) and mask(Rj, (Q - 1)*(I - Ln) + 2*J + Ln)
    printed49 = mask(2*J, Rj) and mask(J, (Q//2 - 1)*Ln) and mask(Rj, (Q - 1)*(I - Ln) + 2*J + I)
    return ok47, ok49, printed49
counter = None
for hist in ([3, 5, 2, 7], [1, 1, 1], [6, 2, 3, 0, 5], [7, 7, 7, 7]):
    for sel in ({0}, {1}, {0, 2}, {len(hist) - 1}):
        ok47, ok49, printed = check_47_49(hist, sel, 4)
        need(ok47 and ok49, f"(47)/(49) fail for {hist} {sel}")
        if not printed and counter is None:
            counter = {"r_t": hist, "selected_times": sorted(sel), "Q": 16}
need(counter is not None, "expected a counterexample to the printed +I form of (49)")

report = {"status": "PASS", "example1": {"input2_steps": 18, "trace_table": "matches all 19 columns",
          "accepted_2_to_60": "exactly the primes", "inputs_0_1": "no stop within 20000 transitions"},
          "encoding_checked_inputs": steps, "section2": "(8),(9),(10)-(13), Lucas lemma, (43), (45)",
          "section4": {"(47),(49)": "hold on synthetic histories", "printed_+I_counterexample": counter}}
OUT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
print(json.dumps(report, indent=2))
