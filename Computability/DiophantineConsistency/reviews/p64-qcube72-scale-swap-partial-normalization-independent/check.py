#!/usr/bin/env python3
"""Independent finite exact graph controls for the partial normalization."""
import hashlib,json,operator,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize: raise SystemExit('requires python3 -I -S -B')
r=Path(__file__).resolve().parents[2]; p=r/'research/p64-qcube72-scale-swap-partial-normalization'
pins={'README.md':'cc33e3b4a8f7052a817d851ce7ba8a42a421526d897ac8a75c10889b27bb529c','check.py':'3f9f70440bbd666ddaee9c439ca4132e1b0991b977b6215be08874733aae82c7'}
for f,h in pins.items():
 if hashlib.sha256((p/f).read_bytes()).hexdigest()!=h:raise ValueError(('pin',f))
g=r/'research/p64-qcube72-free-main-candidate/graph.json'
if hashlib.sha256(g.read_bytes()).hexdigest()!='875a9d0972c350e6858e25b68f2dc794b1f330e61f29cd52a5853ece90b24806':raise ValueError('graph pin')
a=json.loads(g.read_bytes()); ops={'+':operator.add,'-':operator.sub,'*':operator.mul}
def graph(v):
 d=v.copy()
 for name,op,x,y in a['source']:d[name]=ops[op](d[x] if isinstance(x,str) else x,d[y] if isinstance(y,str) else y)
 return d
passed=blocked=both_transports=0
for beta in range(2,27):
 for u in range(1,6):
  q=2*beta+1; qp=beta+1; w=qp*u; wp=u*q
  for t in range(1,3):
   s=qp**3*t; sp=q**3*t
   for K in range(0,2*beta+1):
    A=K+wp; z,F=divmod(A,beta)
    if F==0:
     # If F,alpha,C are positive and F+alpha+C=beta+1 then 0<F<beta.
     # A≡0 mod beta makes A*C≡0 for every C.
     if any((A*C-F2)%(beta)==0 for C in range(1,beta) for F2 in range(1,beta)):raise ValueError('blocked')
     blocked+=1;continue
    alpha=beta-F; C=1
    if not(z>0 and F>0 and alpha>0 and F+alpha+C==qp and A*C==F+z*beta):raise ValueError('target transport')
    if w*q!=wp*qp or q**3*s!=qp**3*sp:raise ValueError('scale')
    v={'beta':beta,'K0':K,'MC':1,'MF':beta,'J':2,'F':1,'alpha':1,'z':1,'f':2,'i':2,'T':2,'s':s,'w':w,'t':2,'eta':2,'zeta':1,'y':2,'h':3}
    tval=dict(v,J=1,F=F,alpha=alpha,z=z,s=sp,w=wp)
    d=graph(v); e=graph(tval)
    for n in ('X','Y','k','c','a','A0','M','W'):
     if d[n]!=e[n]:raise ValueError(('residual mismatch',n,beta,u,t,K))
    if e['Lt']!=0:raise ValueError('target graph transport')
    # Where possible, also choose the source transport to vanish.
    z0,F0=divmod(K+w,2*beta)
    if z0>0 and F0>0:
     v.update(F=F0,alpha=q-F0-1,z=z0); d=graph(v)
     if d['Lt']!=0 or any(d[n]!=e[n] for n in ('X','Y','k','c','a','A0','M','W')):raise ValueError('two transports')
     both_transports+=1
    passed+=1
print(json.dumps({'status':'PASS_INDEPENDENT_FINITE_CONTROLS','target_transport_and_residual_cases':passed,'blocked_cases':blocked,'both_transport_cases':both_transports,'pins':pins,'scope':'Finite exact graph and arithmetic checks; no positive graph-zero existence or Lean proof of composition.'},sort_keys=True,indent=2))
