#!/usr/bin/env python3
"""Exact isolated-residual obstruction to absorbing the ordinary shift."""
from math import isqrt

def N(c,Q,V,h):
    d=c**4
    oneQ=1-Q
    cy=Q*V*V-1
    inside=oneQ*h*h+cy
    t=Q*oneQ
    return (d*inside-t)**2 + 4*d*t*cy

c,Q,V,h=2,64,1,1
assert c>0 and Q>1 and h>0
assert N(c,Q,V,h)==0
# Preserving h^2 permits exactly +/-h; both give n <= 0 for V=1.
assert all(choice-V<=0 for choice in (h,-h))
print(f'c={c}, Q={Q}, V={V}, h={h}, N={N(c,Q,V,h)}; both n=+/-h-V are nonpositive')

# If f is replaced by an unconstrained positive variable, f=1 gives Q=0.
# With T=1, the ordinary graph's V equals -R; n=R+1 yields V+n=1.
for c in range(1, 8):
    for R in range(1, 8):
        assert N(c,0,-R,1)==0
print('for the sampled positive c,R: f=T=1, n=R+1 makes the isolated ordinary residual zero')
