#!/usr/bin/env python3
"""Independent source pins, polynomial carrier and root-margin controls."""
from pathlib import Path
import hashlib,itertools,json,math
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
pins=json.loads((HERE/'pins.json').read_text())
for p,h in pins.items():assert hashlib.sha256((ROOT/p).read_bytes()).hexdigest()==h,p
r=ROOT/'research';new=json.loads((r/'ordinary13-qcube-unscale84/candidate.json').read_text());old=json.loads((r/'ordinary13-aux-root87-36/candidate.json').read_text())
assert len(new['source'])==84 and len(old['source'])==87
assert new['witnesses'][7:9]==['s','r'] and old['witnesses'][7:9]==['Y','r']
assert new['witnesses'][:7]+new['witnesses'][8:]==old['witnesses'][:7]+old['witnesses'][8:]
assert new['fixed_numerals']==old['fixed_numerals']
a={x[0]:x for x in new['source']};b={x[0]:x for x in old['source']}
assert set(a)-set(b)=={'Y'} and set(b)-set(a)=={'M','g33','g34','folded_q3Bt'}
for n in a.keys()&b.keys():
 if n not in ('g32','Z','g39'):assert a[n]==b[n],n
def deps(rows,n):
 if isinstance(n,int):return set()
 if n not in rows:return {n}
 _,_,x,y=rows[n];return deps(rows,x)|deps(rows,y)
for n in ('A1','Fa','g72'):assert 'r' not in deps(a,n) and 'r' not in deps(b,n)
# Independent sparse polynomial proof, over Z, with h=q³ and r_old=r_new−s.
N=7
class P:
 def __init__(self,t):self.t={m:c for m,c in t.items() if c}
 def __add__(self,o):
  o=L(o);d=dict(self.t)
  for m,c in o.t.items():d[m]=d.get(m,0)+c
  return P(d)
 __radd__=__add__
 def __neg__(self):return P({m:-c for m,c in self.t.items()})
 def __sub__(self,o):return self+-L(o)
 def __rsub__(self,o):return L(o)+-self
 def __mul__(self,o):
  o=L(o);d={}
  for m,c in self.t.items():
   for n,e in o.t.items():
    k=tuple(x+y for x,y in zip(m,n));d[k]=d.get(k,0)+c*e
  return P(d)
 __rmul__=__mul__
 def __eq__(self,o):return self.t==L(o).t
def L(n):return n if isinstance(n,P) else P({(0,)*N:n})
def var(i):return P({tuple(int(j==i) for j in range(N)):1})
h,b0,ell,k,rnew,s,B=map(var,range(N));y=h*s;rold=rnew-s
z=b0*(ell+k+rnew-k*B)-B
zold=h*b0*(ell+k+rold-k*B)+y*b0-h*B
norm=1+ell*(ell+k);A=z*z-b0*b0*norm;Aold=zold*zold-(h*b0)*(h*b0)*norm
assert zold==h*z and Aold==h*h*A
# Cube cancellation identity in the same exact polynomial ring.
assert (1+b0)*(1+b0)*(1+b0)-b0*(b0*b0+3*b0+3)==1
count=0
for ell,k,s in itertools.product(range(0,31),range(0,31),range(0,16)):
 n=1+ell*(ell+k);tau=math.isqrt(n)
 if tau*tau==n and 3*s<=k and s<=ell:
  assert ell+s<tau;count+=1
# The strict margin may fail without k≥3s (partial fact control only).
m,k,s=1,2,1;ell=m*k;tau=3
assert tau*tau==1+ell*(ell+k) and s<=ell and not 3*s<=k and tau==ell+s
assert 1-2<0
src=(r/'ordinary13-qcube93-model-draft/Ordinary13QCube93Arithmetic.lean.src').read_text()
for x in ['theorem positive_quotient_of_signed_norm','ModelRelationCombining.sq_dvd_sq',
 'cube_dvd_of_dvd_mul','Trace75IntegralTransport.natural_dvd_of_signed']:
 assert x in src,x
p73=(ROOT/'Lean/DiophantineConsistency/Compact44/P73Converse.lean').read_text()
assert 'private theorem tau_gt' in p73 and '(hk : 3 * s ≤ k) (hs : s ≤ ell) (hs0 : 0 ≤ s)' in p73
print(json.dumps({'source_pins':pins,'exact_qcube_root_and_residual_scaling':True,
 'exact_cube_bezout':True,'finite_tau_margin_controls':count,
 'margin_failure_without_k3s_fact_control':True,'lean_executed':False,
 'scope':'source/math audit; no all-model map, provider or endpoint proof'},sort_keys=True,indent=2))
