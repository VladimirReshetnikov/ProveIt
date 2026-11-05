#!/usr/bin/env python3
"""Independent exact core and modular complete-DAG controls for the 72 zero."""
import hashlib
import json
import math
import operator
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B without optimization')
root=Path(__file__).resolve().parents[2]
packet=root/'research/p64-qcube72-equal-rank-first-index-obstruction'
graph=root/'research/p64-qcube72-free-main-candidate/graph.json'
pins={packet/'check.py':'20146e38397f75bf678a91061a0f2687b9876123ba4a91cdc011104281ab2ac8',
      packet/'result.json':'f1bba7d2f63c45574674b3166312990f2371f414ef08ed0ea7e37ea66bb09a18',
      graph:'875a9d0972c350e6858e25b68f2dc794b1f330e61f29cd52a5853ece90b24806'}
for f,h in pins.items():
    if hashlib.sha256(f.read_bytes()).hexdigest()!=h: raise RuntimeError('pin mismatch: '+str(f))

def mul(a,b,d,mod=None):
    x,y=a; u,v=b
    z=(x*u+d*y*v,x*v+y*u)
    return z if mod is None else (z[0]%mod,z[1]%mod)

def power(base,e,d,mod=None):
    # Left-to-right binary recursion, independent from the author's
    # right-to-left power loop. For c this avoids repeated huge shifts.
    r=(1,0)
    for byte in e.to_bytes((e.bit_length()+7)//8,'big'):
        for k in range(7,-1,-1):
            r=mul(r,r,d,mod)
            if (byte>>k)&1:r=mul(r,base,d,mod)
    return r

m,j=19259,11720; d=36480; P=4374; H=759; U=729
g,c=power((191,1),m,d); t,k=power((8749,2),j,P*(P+1))
if not (g*g-d*c*c==1 and t*t-P*(P+1)*k*k==1 and 27*k<c<28*k): raise RuntimeError('Pell or interval')
h,rem=divmod(U*(g-6-189*c),H)
if rem or h<=0 or (h%U,k%U,m%U,(h+k-m-1)%U)!=(486,112,305,292): raise RuntimeError('carrier')
if math.gcd(U,H)!=3 or (2*j-m-1)%243!=49 or m%4!=3: raise RuntimeError('index')

# Compute the *symbolically defined* massive witnesses modulo two primes.
# Inversion is legitimate here only after checking each denominator is a unit;
# the integer divisibility is justified separately in the review, not by this test.
dag=json.loads(graph.read_bytes()); ops={'+':operator.add,'-':operator.sub,'*':operator.mul}
controls=[]
for p in (1000000007,1000000009):
    def inv(a):
        if math.gcd(a,p)!=1: raise RuntimeError('modular denominator is not a unit')
        return pow(a,-1,p)
    f,L=power((g%p,c%p),c,d,p)
    i=d*L*inv(c*c%p)%p; I=i*(c%p)**2%p
    x,y=power((I,1),m,(I*I-1)%p,p); V=x*inv(I)%p
    Q=(c+V)*inv(f*f%p)%p; T=(m+Q)*inv(c%p)%p
    vals=dict(beta=2,K0=1,MC=19219,MF=0,J=1,F=1,alpha=1,z=1,
              f=f,i=i,T=T,s=1,w=2,t=t%p,eta=(c-27*k)%p,zeta=(28*k-c)%p,y=y,h=h%p)
    for n,op,a,b in dag['source']:
        vals[n]=ops[op](vals[a] if isinstance(a,str) else a,vals[b] if isinstance(b,str) else b)%p
    if any(vals[n] != x for n,x in [('A0',1),('M',0),('W',0),('Na',1),('Lt',0),('polynomial',0)]):
        raise RuntimeError('full DAG modular residual failure')
    controls.append(p)
print(json.dumps({'status':'PASS','exact_core_bits':c.bit_length(),'old_carrier_mod_729':292,
                  'first_index_mod_243':49,'modular_full_dag_controls':controls,
                  'scope':'Exact core, two modular full-DAG controls and separate symbolic proof; not Lean-checked.'},sort_keys=True))
