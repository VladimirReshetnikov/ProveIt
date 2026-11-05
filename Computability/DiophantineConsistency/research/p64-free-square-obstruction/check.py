#!/usr/bin/env python3
"""Check a norm-level obstruction; this is not a graph-zero search."""
import math
import sys

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')

a, delta, c, g, i = 2, 15, 3572846569215, 13837575261124, 1
h = 10863410900978748085986480074788652207849081883376
floor_sqrt_h = 3295968886530749410979843

if delta != a*a + 4*a + 3:
    raise RuntimeError('discriminant mismatch')
if g*g != 1 + delta*c*c:
    raise RuntimeError('main norm failed')
if delta*(h-1) != i*i*c**4:
    raise RuntimeError('strong norm failed')
if math.isqrt(h) != floor_sqrt_h or not floor_sqrt_h**2 < h < (floor_sqrt_h+1)**2:
    raise RuntimeError('h is not certified nonsquare')
G, C = 1, 0
for _ in range(15):
    G, C = (a+2)*G + delta*C, G + (a+2)*C
if (G, C) != (g, c):
    raise RuntimeError('Pell recurrence provenance mismatch')
print('PASS: exact main norm, strong norm, and nonsquare h; a=2 is not an admissible positive-beta graph value')
