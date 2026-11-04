#!/usr/bin/env python3
"""Exact identities for conditional n>=7,r=9 projection obstruction."""
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
def subst(p,x,y):return add(*(sc(c,mul(pw(x,i),pw(y,j))) for (i,j),c in p.items()))
def ordinate(d,n):
    a={};b={(0,0):1}
    for _ in range(n-1):a,b=b,add(mul(d,b),sc(-1,a))
    return b
one={(0,0):1};x={(1,0):1};y={(0,1):1}

# y7(2+u) contains u^6 and only positive remaining coefficients.
d=add(x,sc(2,one));y7=ordinate(d,7)
assert y7==add(pw(x,6),sc(12,pw(x,5)),sc(55,pw(x,4)),sc(120,pw(x,3)),sc(126,pw(x,2)),sc(56,x),sc(7,one))
# z^8-y9(z) = (z²-1)*((z²-1)*(7z²-1)+1)+1.
z=x;y9=ordinate(z,9);a=add(pw(z,2),sc(-1,one))
assert add(pw(z,8),sc(-1,y9))==add(mul(a,add(mul(a,add(sc(7,pw(z,2)),sc(-1,one))),one)),one)

# For X=32+u, 2X⁸-(X+2)⁸ has positive coefficients.
shift=subst(add(sc(2,pw(x,8)),sc(-1,pw(add(x,sc(2,one)),8))),add(x,sc(32,one)),y)
assert len(shift)==9 and all(v>0 for v in shift.values())

# r=9 projection reduction, exact over Z[X,Y].
M=sc(4,y);H=add(mul(M,add(x,one)),sc(-1,one));w=mul(M,x);v=add(one,sc(-1,M))
def P(a):return mul(mul(a,add(a,sc(-512,M))),add(sc(512,a),M))
quot=add(sc(512,add(pw(w,2),mul(w,v),pw(v,2))),sc(-262143,mul(M,add(w,v))),sc(-512,pw(M,2)))
assert add(P(w),sc(-1,P(v)))==mul(H,quot)
g1=add(sc(4,y),sc(-1,one));g2=add(sc(2052,y),sc(-1,one));g3=add(sc(511,y),sc(-128,one))
assert P(v)==sc(-4,mul(mul(g1,g2),g3))
diff=add(mul(mul(g1,g2),g3),sc(-128,H),sc(-3,y))
assert all(j>=1 and c%4==0 for (i,j),c in diff.items())
C=1048572
assert 2052*511==C and 16*64**7>C**2 and 64**3>128*64
print(json.dumps({'status':'PASS','eighth_power_terms':len(shift),
 'eighth_power_min_coefficient':min(shift.values()),'q_threshold':64,
 'projection_C':C,'scope':'conditional exact arithmetic; n>=7 graph binding and Lean open'},sort_keys=True))
