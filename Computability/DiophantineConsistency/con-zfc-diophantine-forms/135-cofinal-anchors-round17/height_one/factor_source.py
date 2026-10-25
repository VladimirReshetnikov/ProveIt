#!/usr/bin/env python3
"""Exact rank-one affine refactorization before the height-one compiler."""
import argparse, hashlib, json, math
from collections import Counter
from pathlib import Path

def clean(p): return {tuple(m):c for m,c in p.items() if c}
def square(l):
 d=Counter()
 for a,c in l.items():
  for b,e in l.items(): d[tuple(sorted(a+b))]+=c*e
 return clean(d)
def write(p,x): p.parent.mkdir(parents=True,exist_ok=True); p.write_text(json.dumps(x,sort_keys=True,separators=(',',':'))+'\n')

def factor(source,min_terms=3,selected=None):
 variables=list(source['variables']); rows=[]; definitions=[]; records=[]; cache={}
 for r,row in enumerate(source['residuals']):
  p=Counter()
  for c,m in row['terms']: p[tuple(sorted(m))]+=c
  p=clean(p); q={m:c for m,c in p.items() if len(m)==2}; diagonal={m[0]:c for m,c in q.items() if m[0]==m[1]}
  fac=None
  if len(q)>=min_terms and diagonal and (selected is None or r in selected):
   vs=sorted(diagonal); a=vs[0]; sign=1 if diagonal[a]>0 else -1; root=math.isqrt(abs(diagonal[a]))
   if root*root==abs(diagonal[a]):
    lin={(a,):root}; okay=True
    for b in vs[1:]:
     cross=q.get((a,b),0); den=2*sign*root
     if cross%den: okay=False; break
     lin[b,]=cross//den
    if okay and {m:sign*c for m,c in square(lin).items()}==q: fac=(sign,lin)
  if fac is None:
   rows.append(row); continue
  sign,lin=fac
  shifts={0}
  for (v,),c in lin.items():
   den=2*sign*c; z=p.get((v,),0)
   if z%den==0: shifts.add(z//den)
  best=None
  for k in shifts:
   affine=dict(lin)
   if k: affine[()]=k
   expanded=square(affine); rest=Counter(p)
   for m,c in expanded.items(): rest[m]-=sign*c
   rest=clean(rest)
   # Avoid many large leftover affine coefficients; prefer sparse pullbacks.
   score=(len(rest),sum(abs(c).bit_length() for c in rest.values()),abs(k),k)
   if best is None or score<best[0]: best=(score,k,rest,affine)
  _,k,rest,affine=best; key=tuple(sorted(affine.items()))
  if key in cache: pivot=cache[key]
  else:
   pivot=len(variables); cache[key]=pivot; variables.append({'kind':'affine_refactor','source_row':r})
   terms=[[1,[pivot]]]+[[-c,list(m)] for m,c in sorted(affine.items())]
   definitions.append({'label':f'affine_refactor.{r}','terms':terms})
  rest[pivot,pivot]=sign
  rows.append({'label':row['label'],'terms':[[c,list(m)] for m,c in sorted(rest.items())]})
  records.append({'source_row':r,'pivot':pivot,'sign':sign,'affine':[[c,list(m)] for m,c in sorted(affine.items())]})
 result={'domain':source['domain'],'variables':variables,'polynomial':'sum(square(row) for row in residuals)','residuals':definitions+rows}
 cert={'schema':'rank-one-affine-refactor-v1','original_variables':len(source['variables']),'definition_rows':len(definitions),'records':records,
 'row_offset':len(definitions),'min_quadratic_terms':min_terms}
 return result,cert

def main():
 p=argparse.ArgumentParser(); p.add_argument('--source',required=True,type=Path); p.add_argument('--out',required=True,type=Path); p.add_argument('--min-terms',type=int,default=3); p.add_argument('--selection',type=Path); a=p.parse_args()
 raw=a.source.read_bytes(); s=json.loads(raw); f,c=factor(s,a.min_terms,selected=None if a.selection is None else set(json.loads(a.selection.read_text()))); c['source_sha256']=hashlib.sha256(raw).hexdigest()
 write(a.out/'source.json',f); write(a.out/'factor_certificate.json',c)
 print(json.dumps({'variables':len(f['variables']),'rows':len(f['residuals']),'refactored_rows':len(c['records']),'source_terms':sum(len(r['terms']) for r in s['residuals']),'refactored_terms':sum(len(r['terms']) for r in f['residuals'])}))
if __name__=='__main__': main()
