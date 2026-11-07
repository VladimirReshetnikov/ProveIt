#!/usr/bin/env python3
"""Exact source-pinned Nt divisibility obstruction; not a full-system claim."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];source=D/'research/nine-sharing-sign26-sextic-gap-congruence-candidate/seed.json';digest=hashlib.sha256(source.read_bytes()).hexdigest();assert digest=='36efa7dd3b2ea06d210b8975db2cbfc4f7494549c87204ada18747a720cb1f25';data=json.loads(source.read_text());rows=data['residuals'];assert len(rows)==17 and data['witness_count']==26
# Sparse integer polynomials; monomials are tuples of sorted variable names.
def c(k):return {():k} if k else {}
def atom(x):return {(x,):1}
def add(a,b,k=1):
 d=a.copy()
 for m,v in b.items():d[m]=d.get(m,0)+k*v
 return {m:v for m,v in d.items() if v}
def mul(a,b):
 d={}
 for x,v in a.items():
  for y,w in b.items():
   m=tuple(sorted(x+y));d[m]=d.get(m,0)+v*w
 return {m:v for m,v in d.items() if v}
one=c(1);beta=atom('beta');h=atom('h');v4=atom('v4');v9=atom('v9')
# Set v1=v2=v3=0 and K0=beta*h-v9-1, so H=K0+v9+1=beta*h.
def poly(t):
 op=t[0]
 if op=='num':return c(t[1])
 if op=='var':return c(0) if t[1] in (1,2,3) else atom('v'+str(t[1]))
 if op=='port':return add(add(mul(beta,h),v9,-1),one,-1) if t[1]=='K0' else atom(t[1])
 x,y=poly(t[1]),poly(t[2]);return mul(x,y) if op=='mul' else add(x,y,1 if op=='add' else -1)
def has_v4(t):return (t[0]=='var' and t[1]==4) or any(has_v4(x) for x in t[1:] if isinstance(x,list))
assert [r['gate'] for r in rows if has_v4(r['expr'])]==['Nt']
nt=next(r['expr'] for r in rows if r['gate']=='Nt');actual=poly(nt);expected=add(mul(beta,add(mul(h,add(beta,one,-1)),v4,-1)),one,-1);assert actual==expected
# No integer multiple of beta>=2 is congruent to 1 modulo beta.
for b in range(2,12):
 for K in range(0,25):
  hh=max(1,(K+1+b-1)//b);vv9=b*hh-K-1;assert vv9>=0
  for z in range(0,8):assert (b*(hh*(b-1)-z)-1)%b==b-1
print(json.dumps({'status':'PASS_LOCAL_EXACT_IDENTITY','source_sha256':digest,'coordinate':'v4','only_residual':'Nt','substitutions':'v1=v2=v3=0, K0=beta*h-v9-1','identity':'Nt = beta*(h*(beta-1)-v4)-1','scope':'local Nt row with beta>=2, K0>=0 and h chosen so v9>=0; other rows unrestricted, no full-system counterexample or lower bound'},sort_keys=True,indent=2))
