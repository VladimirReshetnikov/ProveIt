"""Exact arithmetic membership in the independently derived disk-minus-orbit set.
This code evaluates a closed arithmetic criterion. It never advances a signal
machine, loads a collision word, or selects/simulates any physical event.
"""
from fractions import Fraction as F
from math import lcm
import json
from pathlib import Path

P=(F(4,205),-F(26,615))
RADIUS_SQUARED=F(4,1845)

def cmul(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def cpow(a,n):
    out=(F(1),F(0))
    while n:
        if n&1:out=cmul(out,a)
        a=cmul(a,a);n//=2
    return out

def valid_normalized(u,v):
    u,v=F(u),F(v)
    norm=u*u+v*v
    if norm<RADIUS_SQUARED:return True
    if norm>RADIUS_SQUARED:return False
    eta=((u*P[0]+v*P[1])/RADIUS_SQUARED,(v*P[0]-u*P[1])/RADIUS_SQUARED)
    denominator=lcm(eta[0].denominator,eta[1].denominator)
    n=0
    while denominator%5==0:
        denominator//=5;n+=1
    if denominator!=1:return True
    return eta!=cpow((F(3,5),-F(4,5)),n)

def valid_rational_gaps(g):
    if len(g)!=3:raise ValueError('Expected three positive rational gap values')
    g=tuple(F(x) for x in g)
    if any(x<=0 for x in g):return False
    d=sum(g);x=g[0];y=g[0]+g[1]
    return valid_normalized(x/d-F(1,3),y/d-F(2,3))

assert valid_normalized(0,0)
assert not valid_normalized(F(1,10),0)
assert not valid_normalized(*P)
checked=0
for n in range(1,65):
    backward=cmul(P,cpow((F(3,5),-F(4,5)),n))
    forward=cmul(P,cpow((F(3,5),F(4,5)),n))
    assert not valid_normalized(*backward)
    assert valid_normalized(*forward)
    checked+=2
outside_orbit=cmul(P,(F(5,13),F(12,13)))
assert valid_normalized(*outside_orbit)
assert valid_rational_gaps((1,1,1))
assert not valid_rational_gaps((217,167,231))
assert not valid_rational_gaps((0,1,1))
receipt={'checks':'PASS','boundary_power_cases':checked,'orientation':'nonnegative inverse powers rejected, positive forward powers accepted','other_tests':7,'physical_execution':False}
print(json.dumps(receipt,indent=2))
Path('/workspace/shared/signal-dimension-boundary57-20261004/rational-membership-result.json').write_text(json.dumps(receipt,indent=2)+'\n')
