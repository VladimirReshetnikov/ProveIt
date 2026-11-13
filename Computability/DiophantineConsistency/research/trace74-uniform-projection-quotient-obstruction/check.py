#!/usr/bin/env python3
"""Exact standard-integer scalar diagnostic, not a graph construction."""
import json
import sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('invoke python3 -I -S -B')

def ycoord(n, a):
    prev, cur = 0, 1
    for _ in range(n):
        prev, cur = cur, a * cur - prev
    return prev

q, n, r = 64, 15, 17
Y, X = q**3, 2**200
h, t, K = q-1, 2*Y, 2**r
L = K//4
H = 4*Y*(X+1)-1
left = t*ycoord(n, X*t*t+2)
right = ycoord(r, t*(X+1)+2)
product = h*X*(X-K)*(K*X+1)
rem = product % H
assert q >= 64 and n >= 7 and r == n+2 and r % 2 == 1
assert X >= 32 and Y >= q**3 and X % q == Y % q == 0
assert left < right
assert L*h >= Y
assert rem != 0
print(json.dumps({'status':'PASS','q':q,'Y':Y,'X':'2^200','n':n,'r':r,
    'gap_left_lt_right':left<right, 'Lh':L*h, 'Lh_lt_Y':L*h<Y,
    'projection_remainder':str(rem),'projection_divides':rem==0,
    'scope':'standard integer scalar diagnostic; not a graph zero; weighted projection fails'},sort_keys=True,indent=2))
