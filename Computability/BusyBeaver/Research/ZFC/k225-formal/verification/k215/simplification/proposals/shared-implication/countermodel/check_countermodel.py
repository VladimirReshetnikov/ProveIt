#!/usr/bin/env python3
"""Exhaustively check the explicit algebra; no search or external dependencies."""
from itertools import product
I = ((0, 1, 1), (0, 0, 0), (0, 0, 1))
def imp(a,b): return I[a][b]
def designated(a): return a == 0
def rho8(a,b,c,u): return imp(imp(imp(c,u),a),imp(imp(a,c),imp(b,c)))
assert all(not(designated(imp(a,b)) and designated(a)) or designated(b)
           for a,b in product(range(3),repeat=2))
assert all(designated(rho8(a,b,c,a)) for a,b,c in product(range(3),repeat=3))
failures=[(a,b,c,u) for a,b,c,u in product(range(3),repeat=4)
          if not designated(rho8(a,b,c,u))]
assert failures == [(1,0,2,2),(1,2,2,2)]
print('MP: all 9 cases pass; diagonal rows: all 27 cases pass.')
print('Unrestricted row failures:', failures)
print('Conclusion: diagonal rows plus MP do not imply unrestricted rho8.')
