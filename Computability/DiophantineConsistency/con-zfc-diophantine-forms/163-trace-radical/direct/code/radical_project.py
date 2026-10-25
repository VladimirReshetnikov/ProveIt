#!/usr/bin/env python3
"""Explore and certify monic projections along common quadratic radicals."""
from pathlib import Path
from fractions import Fraction
from functools import reduce
from math import gcd,lcm
import argparse,copy,json,sys
BASE=Path(__file__).resolve().parent.parent/'inherited/factorial_free/direct'
sys.path.insert(0,str(BASE/'parent/code'))
import terminal_elimination as E

def add(a,b,k=1):
 out=a.copy()
 for m,c in b.items():out[m]=out.get(m,0)+k*c
 return {m:c for m,c in out.items() if c}

def kernel(e):
 n=len(e['variables']);rows=[E.normalize(r['terms']) for r in e['residuals']]
 mat=[]
 for p in rows:
  hs={}
  for m,c in p.items():
   if len(m)!=2:continue
   a,b=m
   h=hs.setdefault(a,{})
   h[b]=h.get(b,0)+c
   h=hs.setdefault(b,{})
   h[a]=h.get(a,0)+c
  mat.extend(hs.values())
 piv={}
 for raw in mat:
  r={i:Fraction(c) for i,c in raw.items() if c}
  while r:
   i=min(r)
   if i not in piv:
    a=r[i];piv[i]={j:c/a for j,c in r.items()};break
   r=add(r,piv[i],-r[i])
 free=[i for i in range(n) if i not in piv]
 basis=[]
 for f in free:
  d={f:Fraction(1)}
  for p,r in sorted(piv.items(),reverse=True):
   val=-sum(c*d.get(j,0) for j,c in r.items() if j!=p)
   if val:d[p]=val
  denom=lcm(*(x.denominator for x in d.values()))
  d={i:int(v*denom) for i,v in d.items()}
  g=gcd(*d.values());d={i:v//g for i,v in d.items()}
  basis.append(d)
 return basis

def project(e,outpath):
 e=copy.deepcopy(e);steps=[]
 while True:
  rs=[E.normalize(r['terms']) for r in e['residuals']]
  choices=[]
  for d in kernel(e):
   sv=[i for i,c in d.items() if abs(c)==1]
   if not sv:continue
   for ri,r in enumerate(rs):
    coeff=sum(r.get((v,),0)*c for v,c in d.items())
    if abs(coeff)!=1:continue
    # Choose the gate coordinate, then lowest index, as triangular pivot.
    pv=min(sv,key=lambda i:(e['variables'][i].get('kind')!='gate',i))
    dp={i:c*d[pv] for i,c in d.items()}
    choices.append(((len(d),sum(abs(v) for v in d.values()),pv,ri),dp,pv,ri))
  if not choices:break
  _,d,pv,ri=min(choices)
  trans=rs
  shears=[]
  for w,c in sorted(d.items()):
   if w==pv:continue
   trans=[E.substitute(r,w,{(w,):1,(pv,):c}) for r in trans]
   shears.append([w,pv,c])
  f=E.candidate(trans[ri],pv,False)
  if f is None:raise ValueError('not monic after radical shear')
  if any(pv in m and len(m)>1 for r in trans for m in r):raise ValueError('radical failure')
  trans=[E.substitute(r,pv,f) for j,r in enumerate(trans) if j!=ri]
  if any(E.degree(r)>2 for r in trans):raise ValueError('degree raised')
  keep=sorted({v for r in trans for m in r for v in m});ren={v:i for i,v in enumerate(keep)}
  step={'variables_before':[v['name'] for v in e['variables']], 'direction':sorted(d.items()),'pivot_variable':pv,'pivot_name':e['variables'][pv]['name'],'pivot_row':ri,'shears':shears,'restoration':E.as_terms(f),'retained_variables':keep}
  steps.append(step)
  newrows=[]
  oldmeta=[r for j,r in enumerate(e['residuals']) if j!=ri]
  for meta,r in zip(oldmeta,trans):
   if r:newrows.append(dict(meta,terms=E.as_terms({tuple(ren[v] for v in m):c for m,c in r.items()})))
  e=dict(e,variables=[e['variables'][v] for v in keep],residuals=newrows)
  print('removed',step['pivot_name'],'direction',[(step['variables_before'][i],c) for i,c in d.items()],flush=True)
 poly=E.expand(e)
 metrics={'variables':len(e['variables']),'rows':len(e['residuals']),'degree':max(len(m) for c,m in poly['terms']),'terms':len(poly['terms']),'height':max(abs(c) for c,m in poly['terms'])}
 print(metrics,flush=True)
 if outpath:
  outpath.mkdir(parents=True,exist_ok=True)
  for name,obj in [('equation.json',e),('expanded_polynomial.json',poly),('certificate.json',steps),('METRICS.json',metrics)]:
   (outpath/name).write_bytes(E.canonical_bytes(obj))
 return e,steps,metrics

if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('source',type=Path);a.add_argument('output',type=Path);args=a.parse_args()
 project(json.loads(args.source.read_text()),args.output)
