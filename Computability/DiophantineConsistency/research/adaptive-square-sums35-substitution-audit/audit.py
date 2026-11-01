#!/usr/bin/env python3
"""Exact sparse scan of direct positive-coordinate substitutions only."""
import hashlib,json
from pathlib import Path
path=Path(__file__).resolve().parent.parent/'adaptive-square-sums35/candidate.json'
raw=path.read_bytes()
if hashlib.sha256(raw).hexdigest()!='bb3c4a0a02b2735e3726071cdeb480f35a059905a3204d4569ac0eaaa1abd44d':raise ValueError('candidate drift')
D=json.loads(raw); names=D['witnesses']+D['fixed_numerals'];m=len(D['witnesses']);Z=(0,)*len(names)
def c(n):return {Z:n} if n else {}
def add(a,b,sgn=1):
 r=a.copy()
 for k,v in b.items():r[k]=r.get(k,0)+sgn*v
 return {k:v for k,v in r.items() if v}
def mul(a,b):
 r={}
 for k,x in a.items():
  for l,y in b.items():
   z=tuple(i+j for i,j in zip(k,l));r[z]=r.get(z,0)+x*y
 return {k:v for k,v in r.items() if v}
def substitute(p,j,q):
 powers=[c(1)];maxexp=max((k[j] for k in p),default=0)
 for _ in range(maxexp):powers.append(mul(powers[-1],q))
 out={}
 for k,x in p.items():
  kk=k[:j]+(0,)+k[j+1:];out=add(out,mul({kk:x},powers[k[j]]))
 return out
v={n:{Z[:i]+(1,)+Z[i+1:]:1} for i,n in enumerate(names)};rows={r[0]:r for r in D['source']};factors=[]
for n,op,a,b in D['source']:
 x=c(a) if isinstance(a,int) else v[a];y=c(b) if isinstance(b,int) else v[b];v[n]=add(x,y,1 if op=='+' else -1) if op in '+-' else mul(x,y)
 if op=='*' and a==b and (n.endswith('Constraint') or n in ('firstSquare','mainSquare','auxSquare','strongSquare')):factors.append((n,a))
assert len(factors)==22, ('unexpected residual count',len(factors))
print('residuals',len(factors))
scanned=0; unblocked=[]
for n,op,a,b in D['source']:
 if not n.endswith('Difference') or not isinstance(a,str) or a not in D['witnesses'] or not isinstance(b,str):continue
 scanned+=1; j=names.index(a);q=v[b]
 if any(k[j] for k in q):continue
 ds=[]
 for f,r in factors:
  if r==n:continue
  w=substitute(v[r],j,q);deg=max((sum(k[:m]) for k in w),default=0)
  if deg>3:
   groups={}
   for k,coefficient in w.items():
    if sum(k[:m])>3:groups.setdefault(k[:m],[]).append((k[m:],coefficient))
   witness=next(((monomial,terms) for monomial,terms in groups.items()
                 if len(terms)==1 and not any(terms[0][0][1:]) and terms[0][1]),None)
   if witness:ds.append((r,deg,witness))
 if not ds:unblocked.append(a);print('UNRESOLVED',a,'=',b,'definition',rows.get(b))
 else:
  r,deg,(monomial,terms)=ds[0];portpowers,coefficient=terms[0]
  support=[(names[i],power) for i,power in enumerate(monomial) if power]
  print('BLOCKED',a,'=',b,'by',r,'degree',sum(monomial),'coefficient',coefficient,'beta_power',portpowers[0],'monomial',support)

assert scanned==14, ('unexpected coordinate count',scanned)
assert not unblocked, ('no pure-beta degree witness for substitution',unblocked)
print('PASS: 14 direct substitutions each have a degree >3 term when beta is nonzero')
