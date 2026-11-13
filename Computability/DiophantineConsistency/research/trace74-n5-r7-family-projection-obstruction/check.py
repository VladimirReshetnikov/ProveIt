#!/usr/bin/env python3
"""Exact polynomial projection and Bezout identities for a scalar family."""
import json,sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
def trim(p):
    while p and p[-1]==0:p.pop()
    return p
def add(*ps):
    n=max(map(len,ps),default=0)
    return trim([sum(p[i] if i<len(p) else 0 for p in ps) for i in range(n)])
def sc(c,p):return trim([c*x for x in p])
def mul(p,q):
    if not p or not q:return []
    r=[0]*(len(p)+len(q)-1)
    for i,x in enumerate(p):
        for j,y in enumerate(q):r[i+j]+=x*y
    return trim(r)
def divexact(p,q):
    p=p[:];out=[0]*max(0,len(p)-len(q)+1)
    while p and len(p)>=len(q):
        n=len(p)-len(q);v,r=divmod(p[-1],q[-1]);assert r==0
        out[n]+=v;p=add(p,sc(-v,[0]*n+q))
    assert not p
    return trim(out)

# Ascending coefficient lists. a is arbitrary; H=4Y(X+1)-1 for X=a³,Y=a²/2.
H=[-1,0,2,0,0,2];g1=[-1,0,2];g2=[-1,0,258];g3=[-64,0,127]
identities=[
    (1,[0,4],[-1,-4,-2,0,-4],g1),
    (281370820607,[-283569030144,-8586756],
      [2198209537,8586756,258,2198209536,66564],g2),
    (4292918913,[-260144641,16780353536],
      [-63012098,-262193024,-133169152,4096766,-264257536],g3),
]
for constant,u,v,g in identities:
    assert add(mul(u,H),mul(v,g))==[constant]

# m=4Y=2a², X=a³. The reduction is an exact multiple of H.
m=[0,0,2];X=[0,0,0,1];one=[1]
left=mul(mul(mul(m,m),m),mul(mul(X,add(X,[-128])),add(sc(128,X),one)))
right=mul(mul(add(one,sc(-1,m)),add(one,sc(-129,m))),add([128],sc(-127,m)))
quot=divexact(add(left,sc(-1,right)),H)
assert add(mul(H,quot),right)==left
K=identities[1][0]*identities[2][0]
assert K==1207902117350120440191 and 64*256**9>K
print(json.dumps({'status':'PASS','bezout_constants':[x[0] for x in identities],
 'K':K,'projection_quotient_degree':len(quot)-1,'threshold':256,
 'scope':'integer polynomial identities and conditional family exclusion; no Lean or general graph claim'},sort_keys=True))
