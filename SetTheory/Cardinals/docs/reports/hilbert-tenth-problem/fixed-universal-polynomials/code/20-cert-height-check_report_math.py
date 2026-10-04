#!/usr/bin/env python3
"""Report46-only bounded corroboration of its self-contained elementary lemmas.
No research source, compiler code, or saved arithmetic schedule is executed.
"""
from math import isqrt
import json

COUNTS = {}

def need(value, label):
    if not value:
        raise RuntimeError(label)
    COUNTS[label] = COUNTS.get(label, 0) + 1

def pell(a, n):
    x, y = 1, 0
    for _ in range(n):
        x, y = a*x+(a*a-1)*y, x+a*y
    return x, y

for H in range(2, 41):
    for v in range(121):
        for y in range(1, 121):
            N = H*v*v-(H-1)*y*y
            if N < 0:
                need(N <= -(H-1), 'negative small norm bound')
            if 0 < N < H:
                need(isqrt(N)**2 == N, 'positive small norm is square')
            if N == -(H-1):
                oldv, oldy = v, y
                steps = 0
                while oldv:
                    nv = (2*H-1)*oldv-2*(H-1)*oldy
                    ny = (2*H-1)*oldy-2*H*oldv
                    need(0 <= nv < oldv and ny > 0, 'equality orbit descent')
                    oldv, oldy = nv, ny
                    steps += 1
                need((oldv, oldy) == (0, 1), 'equality terminal pair')
                cx, sy = pell(2*H-1, steps)
                need((v, y) == (2*(H-1)*sy, cx), 'negative equality orbit formula')

for A in range(2, 31):
    z = 1-A*A
    q0, q1 = 1, 4*z-3
    for h in range(31):
        qh = q0
        need(qh == (-1)**h*pell(A, 2*h+1)[1], 'odd quotient specialization')
        q0, q1 = q1, (4*z-2)*q1-q0

for S in range(2, 31):
    z = S*S
    q0, q1 = 1, 4*z-3
    for h in range(31):
        need(S*q0 == pell(S, 2*h+1)[0], 'odd quotient polynomial')
        q0, q1 = q1, (4*z-2)*q1-q0

rejected = 0
try:
    need(False, 'intentional failing control')
except RuntimeError:
    rejected += 1
need(rejected == 1, 'explicit failures active')

print(json.dumps({
    'status':'PASS',
    'scope':'Bounded corroboration of Report46 small-norm and odd-polynomial proofs; not proof by finite testing.',
    'upstream_code_executed':False,
    'saved_schedule_executed':False,
    'counts':dict(sorted(COUNTS.items())),
    'negative_controls_rejected':rejected,
}, indent=2, sort_keys=True))
