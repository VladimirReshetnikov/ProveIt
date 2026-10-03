#!/usr/bin/env python3
"""Independent memoized recurrence and exact reachable-state counterexample."""
from functools import cache
import json

def children(s, u, k):
    return [(s-1, u+int(i>=k), i) if i<s else (s+1, u-int(i<k), i+1)
            for i in range(s+u)]

@cache
def f(n, s, u, k):
    return 1 if n == 0 else sum(f(n-1, *child) for child in children(s, u, k))

x, y, r = (5,1,4), (4,2,4), 19
assert children(6,1,6)[4] == x
assert children(*x)[4] == y
state = (0,1,0)
for _ in range(6):
    state = children(*state)[-1]
assert state == (6,1,6)
counts = [f(18,*x), f(19,*x), f(18,*y), f(19,*y)]
assert counts == [328610526895548, 2835761210180706,
                  1125633749884382, 10225957430377930]
lhs = r*counts[3]*counts[0]
rhs = (r+1)*counts[2]*counts[1]
assert lhs == 63846787924950777938074214657160
assert rhs == 63840570495847624656576542673840
assert lhs-rhs == 6217429103153281497671983320 > 0
print(json.dumps({"passed": True, "r": r, "x": x, "y": y,
                  "counts_f18x_f19x_f18y_f19y": counts,
                  "lhs": lhs, "rhs": rhs, "difference": lhs-rhs}, sort_keys=True))
