"""Independently reconstruct and exactly replay the ten finite identities."""
from itertools import combinations_with_replacement as cwr
from fractions import Fraction as F
from collections import defaultdict
from pathlib import Path
import json
import sys
D=11
zero=(0,)*D
Yindex={1:0,2:1,4:2,3:3,5:5,6:7,7:9}
def mon(*indices):
 z=[0]*D
 for i in indices:z[i]+=1
 return tuple(z)
def plus(x,y):return tuple(a+b for a,b in zip(x,y))
def add(p,q,c=1):
 z=defaultdict(F,p)
 for m,a in q.items():z[m]+=c*a
 return {m:a for m,a in z.items() if a}
def mul(p,q):
 z=defaultdict(F)
 for m,a in p.items():
  for n,b in q.items():z[plus(m,n)]+=a*b
 return {m:a for m,a in z.items() if a}
def match(cols):
 masks={0}
 for c in cols:masks={m|e for m in masks for e in (1,2,4) if c&e and not m&e}
 return bool(masks)
def element(mask,n):
 i=Yindex[mask]
 if mask in (1,2,4):return {mon(i):F(1)} if n==1 else {}
 if n==1:return {mon(i):F(1),mon(i+1):F(1)}
 if n==2:return {mon(i,i+1):F(1),mon(i+1,i+1):F(1,2)}
 return {mon(i,i+1,i+1):F(1,2),mon(i+1,i+1,i+1):F(1,6)}
def right_mono(types):
 cnt={s:types.count(s) for s in set(types)};out={zero:F(1)}
 for s,n in cnt.items():out=mul(out,element(s,n))
 return out
profiles=[(1,2,4),(1,3,4),(3,3,4),(4,3,3),(4,7,3),(3,7,3),(7,7,3),(3,5,7),(3,7,7),(7,7,7)]
def target(S1,S2,normal):
 aa={};pp={};tt={};bb={};beta={}
 for i in range(1,8):
  bb=add(bb,element(i,1),F(sum(match([i,v,e]) for v in(S1,S2) for e in(1,2,4))))
  if i&normal:beta=add(beta,element(i,1))
 for I in cwr(range(1,8),2):
  z=right_mono(list(I))
  aa=add(aa,z,sum(match([*I,e]) for e in(1,2,4)))
  pp=add(pp,z,sum(match([*I,v]) for v in(S1,S2)))
 for I in cwr(range(1,8),3):
  if match(I):tt=add(tt,right_mono(list(I)))
 return add(mul(aa,pp),mul(tt,add(bb,beta,F(1,2))),-1)

BASE=Path(__file__).resolve().parents[1]
cert_path=Path(sys.argv[1]) if len(sys.argv)>1 else BASE/'data/exact_certificate.json'
cert=json.loads(cert_path.read_text())
if len(cert['profiles'])!=10 or {tuple(x['profile']) for x in cert['profiles']}!=set(profiles):raise RuntimeError('incomplete profile list')
results=[]
for rec in cert['profiles']:
 profile=tuple(rec['profile'])
 total={};squares=0;remainder=0
 def exp(v):
  if len(v)!=D or any(type(x)!=int or x<0 for x in v):raise RuntimeError('invalid exponent')
  return tuple(v)
 for term in rec['squares']:
  mu=exp(term['multiplier']);m=exp(term['m']);n=exp(term['n']);ratio=F(term['ratio']);weight=F(term['weight'])
  if ratio<=0 or weight<=0 or sum(mu)+2*sum(m)!=4 or sum(mu)+2*sum(n)!=4:raise RuntimeError('invalid square')
  total=add(total,{plus(mu,plus(m,m)):weight*ratio/2})
  total=add(total,{plus(mu,plus(n,n)):weight/(2*ratio)})
  total=add(total,{plus(mu,plus(m,n)):-weight})
  squares+=1
 for term in rec['positive_remainder']:
  e=exp(term['exponent']);c=F(term['coefficient'])
  if c<=0 or sum(e)!=4:raise RuntimeError('invalid remainder')
  total=add(total,{e:c});remainder+=1
 wanted={m:2*c for m,c in target(*profile).items()}
 if total!=wanted:raise RuntimeError(('polynomial mismatch',profile))
 results.append({'profile':profile,'status':'exact identity and nonnegative generators pass','squares':squares,'positive_monomials':remainder,'target_monomials':len(wanted)})
out={'profiles':results,'exact_profiles':sum('squares' in x for x in results),'total_profiles':len(results)}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
