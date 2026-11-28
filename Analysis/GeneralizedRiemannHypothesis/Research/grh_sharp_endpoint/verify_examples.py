#!/usr/bin/env python3
"""Exact-rational verification of example bookkeeping, not the analytic proof."""
import json
from fractions import Fraction as F


def classify(r, s, u):
    d = r + s + u
    assert d > 0 and min(r, s, u) >= 0
    # Count r zeta polynomial factors, and s odd gamma factors.
    k = 2*r - F(d, 4) + F(s, 2)
    assert k == F(7*r + s - u, 4)
    # Even degrees required by positivity on the whole real axis.
    degrees = [j for j in range(0, d+2, 2) if j+k < -F(1, 2)]
    assert bool(degrees) == (u > 7*r+s+2)
    assert (2 in degrees) == (u > 7*r+s+10)
    if degrees:
        assert degrees[0] == 0
        assert degrees[-1]+2+k >= -F(1, 2)
    status = 'not attained' if not degrees else ('unique' if len(degrees)==1 else 'infinitely many')
    # Permitted degrees are necessary, not a claim that every such degree
    # admits a positive polynomial multiplier. Degree 2 is constructed in paper.
    return {'r':r,'s':s,'u':u,'d':d,'k':str(k),
            'Q_star_to_power_d':4**s*5**u,
            'allowed_even_degrees':degrees,'endpoint':status}


def main():
    n = 0
    for d in range(1, 51):
        for r in range(d+1):
            for s in range(d-r+1):
                classify(r, s, d-r-s)
                n += 1
    cases = [(1,0,0),(0,1,0),(0,0,1),(0,0,2),(0,0,3),(0,0,10),(0,0,11),
             (1,1,10),(1,1,11),(1,1,18),(1,1,19)]
    print(json.dumps({'check':'exact arithmetic; exponent and degree conditions',
                      'total_families_checked':n,'largest_d_checked':50,
                      'examples':[classify(*case) for case in cases]}, indent=2))

if __name__ == '__main__':
    main()
