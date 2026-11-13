#!/usr/bin/env python3
"""Exact identities for a conditional large-q n5/r7 projection obstruction."""
import json,sys
from collections import defaultdict
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
def add(*ps):
    out=defaultdict(int)
    for p in ps:
        for m,c in p.items():out[m]+=c
    return {m:c for m,c in out.items() if c}
def sc(c,p):return {m:c*v for m,v in p.items() if c*v}
def mul(p,q):
    out=defaultdict(int)
    for (a,b),u in p.items():
        for (c,d),v in q.items():out[a+c,b+d]+=u*v
    return {m:c for m,c in out.items() if c}
def pw(p,n):
    out={(0,0):1}
    for _ in range(n):out=mul(out,p)
    return out
def subst(p,x,y):
    return add(*(sc(c,mul(pw(x,i),pw(y,j))) for (i,j),c in p.items()))
one={(0,0):1};x={(1,0):1};y={(0,1):1}

# y5(u+2) = u⁴+8u³+21u²+20u+5.
u=x;d=add(u,sc(2,one))
y5=add(pw(d,4),sc(-3,pw(d,2)),one)
assert y5==add(pw(u,4),sc(8,pw(u,3)),sc(21,pw(u,2)),sc(20,u),sc(5,one))

# z⁶-y7(z) = (z²-1)(5z²-1).
z=x
c=add(pw(z,6),sc(-5,pw(z,4)),sc(6,pw(z,2)),sc(-1,one))
assert add(pw(z,6),sc(-1,c))==mul(add(pw(z,2),sc(-1,one)),add(sc(5,pw(z,2)),sc(-1,one)))

# For X=32+u, 2X⁶-(X+2)⁶ has strictly positive coefficients.
quart=add(sc(2,pw(x,6)),sc(-1,pw(add(x,sc(2,one)),6)))
shift=subst(quart,add(x,sc(32,one)),y)
assert len(shift)==7 and all(v>0 for v in shift.values())

# Projection reduction, exact over Z[X,Y]. M=4Y, H=M(X+1)-1.
M=sc(4,y);H=add(mul(M,add(x,one)),sc(-1,one));w=mul(M,x);v=add(one,sc(-1,M))
def P(a):return mul(mul(a,add(a,sc(-128,M))),add(sc(128,a),M))
quot=add(sc(128,add(pw(w,2),mul(w,v),pw(v,2))),
         sc(-16383,mul(M,add(w,v))),sc(-128,pw(M,2)))
assert add(P(w),sc(-1,P(v)))==mul(H,quot)
g1=add(sc(4,y),sc(-1,one));g2=add(sc(516,y),sc(-1,one));g3=add(sc(127,y),sc(-32,one))
assert P(v)==sc(-4,mul(mul(g1,g2),g3))

# Reducing g1*g2*g3 and 32H mod 4Y leaves 3Y.
diff=add(mul(mul(g1,g2),g3),sc(-32,H),sc(-3,y))
assert all(j>=1 and v%4==0 for (i,j),v in diff.items())
assert 4*(2**30)>65532**2 and 4*516*127==262128
print(json.dumps({'status':'PASS','sixth_power_terms':len(shift),
 'sixth_power_min_coefficient':min(shift.values()),'q_threshold':2**30,
 'scope':'exact polynomial identities for conditional scalar/projection argument; no Lean or graph binding'},sort_keys=True))
