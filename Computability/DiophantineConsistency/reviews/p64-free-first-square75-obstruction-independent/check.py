#!/usr/bin/env python3
"""Independent graph, exact core and modular controls for free first square."""
import hashlib
import json
import math
import random
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B without optimization')
root=Path(__file__).resolve().parents[2]
packet=root/'research/p64-free-first-square75-obstruction'
parent=root/'research/p64-qcube76-independent-y-candidate/graph.json'
pins={parent:'196ef3bdf6805c7ed7d44c278359e32c0f658634db357cc19f0e87464ed6b11c',
      packet/'graph.json':'7530bebac8e6aeaa7d7fb8a46715c821521c2011e54754bdd158a647c2c1dfc7',
      packet/'result.json':'4b50c817213588918991f0bbbbb52fbaf16c2d261538c06bb4c8e428845e96f1'}
for p,h in pins.items():
    if hashlib.sha256(p.read_bytes()).hexdigest()!=h:raise RuntimeError('input hash mismatch '+str(p))
old=json.loads(parent.read_text()); new=json.loads((packet/'graph.json').read_text())
rows=old['source']; candidate=new['source']
if len(rows)!=76 or len(candidate)!=75 or [x for x in rows if 't' in x[2:]]!=[['first_unscaled_square','*','t','t']]:
    raise RuntimeError('parent t dependency mismatch')
expected=[[('tFirst' if x=='first_unscaled_square' else x) for x in row]
          for row in rows if row[0]!='first_unscaled_square']
if candidate!=expected or new['witnesses']!=['tFirst' if x=='t' else x for x in old['witnesses']]:
    raise RuntimeError('graph rewrite mismatch')
if {op:sum(row[1]==op for row in candidate) for op in ('*','+','-')}!={'*':41,'+':18,'-':16}:
    raise RuntimeError('operation counts mismatch')
live={'polynomial'}
for name,op,l,r in reversed(candidate):
    if name in live:live.update(x for x in (l,r) if isinstance(x,str))
if any(row[0] not in live for row in candidate) or any(x not in live for x in new['witnesses']):raise RuntimeError('dead row/input')

def eval_graph(rows,env,mod=None):
    env=env.copy()
    for name,op,l,r in rows:
        l=env[l] if isinstance(l,str) else l;r=env[r] if isinstance(r,str) else r
        if op=='+':z=l+r
        elif op=='-':z=l-r
        elif op=='*':z=l*r
        else:raise RuntimeError('unknown gate')
        env[name]=z if mod is None else z%mod
    return env

rng=random.Random(750451)
for _ in range(128):
    values={n:rng.randrange(1,5) for n in old['witnesses']}
    values.update({n:rng.randrange(0,5) for n in old['fixed_numerals']})
    nv=values.copy();nv['tFirst']=nv.pop('t')**2
    if eval_graph(rows,values)['polynomial']!=eval_graph(candidate,nv)['polynomial']:
        raise RuntimeError('forward graph substitution control')

# Exact 2,049-bit first/main core, computed with direct Pell recurrence.
q,X,Y,m=3,3,162,199;U=Y*Y;a=(X+1)*Y;H=4*a+3;D=(a+1)*(a+3);P=X*U
g,c=1,0
for _ in range(m):g,c=(a+2)*g+D*c,g+(a+2)*c
if g*g-D*c*c!=1:raise RuntimeError('main Pell norm')
h,rem=divmod(U*(g-X-a*c),H)
if rem or h<=0:raise RuntimeError('free carrier quotient')
lo=c//(Y+1)+1;k=lo+(m+1-h-lo)%U
eta,zeta=c-Y*k,(Y+1)*k-c
gamma,rem=divmod(h+k-m-1,U)
first=1+P*(P+1)*k*k
if rem or min(eta,zeta,gamma)<=0 or first%5!=2 or math.isqrt(first)**2==first:
    raise RuntimeError('scale, old carrier, or nonsquare core')

# Polynomial ray independently confirms the stated leading degree for
# beta=2; the general degree upper bound is separately argued from the DAG.
prime=1000003
def trim(a):
    while len(a)>1 and a[-1]==0:a.pop()
    return a
def add(a,b,sign=1):
    return trim([((a[i] if i<len(a) else 0)+sign*(b[i] if i<len(b) else 0))%prime for i in range(max(len(a),len(b)))])
def mul(a,b):
    z=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):z[i+j]=(z[i+j]+x*y)%prime
    return trim(z)
poly={name:[1,1] for name in new['witnesses']}
poly.update({name:[2 if name=='beta' else 1] for name in new['fixed_numerals']})
for name,op,l,r in candidate:
    l=poly[l] if isinstance(l,str) else [l];r=poly[r] if isinstance(r,str) else [r]
    poly[name]=mul(l,r) if op=='*' else add(l,r,1 if op=='+' else -1)
if len(poly['polynomial'])-1!=104 or poly['polynomial'][-1]!=pow(2,64,prime):raise RuntimeError('degree ray')

def pairmul(x,y,D,p):return ((x[0]*y[0]+D*x[1]*y[1])%p,(x[0]*y[1]+x[1]*y[0])%p)
def power(x,n,D,p):
    r=(1,0)
    for bit in bin(n)[2:]:
        r=pairmul(r,r,D,p)
        if bit=='1':r=pairmul(r,x,D,p)
    return r
controls=[]
for mod in (1000003,1000033,1000037,1000039):
    f,L=power((g%mod,c%mod),c,D,mod)
    try:
        i=D*L*pow(c*c,-1,mod)%mod;I=i*c*c%mod
        xx,y=power((I,1),m,(I*I-1)%mod,mod)
        V=xx*pow(I,-1,mod)%mod;Q=(c+V)*pow(f*f,-1,mod)%mod;T=(m+Q)*pow(c,-1,mod)%mod
    except ValueError:continue
    values=dict(beta=2,K0=2,MC=159,MF=0,J=1,F=1,alpha=1,z=1,f=f,i=i,T=T,s=6,w=1,
                tFirst=first,eta=eta,zeta=zeta,y=y,gamma=gamma)
    d=eval_graph(candidate,values,mod)
    if [d[x] for x in ('A0','M','W','Na','Lt','polynomial')]!=[1,0,0,1,0,0]:raise RuntimeError('modular full graph')
    controls.append(mod)
    if len(controls)==2:break
if len(controls)!=2:raise RuntimeError('insufficient invertible moduli')
print(json.dumps({'status':'PASS','operations':75,'degree_ray':104,'c_bits':c.bit_length(),
 'first_mod5':first%5,'forward_controls':128,'modular_graph_controls':controls,
 'scope':'arbitrary ports, exact core and symbolic huge witnesses; no Lean or existential inequivalence'},sort_keys=True))
