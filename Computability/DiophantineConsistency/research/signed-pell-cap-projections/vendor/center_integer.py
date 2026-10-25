#!/usr/bin/env python3
"""Deterministic finite integer-translation search. It proves no global optimum."""
import argparse,json,copy
from pathlib import Path
from collections import defaultdict
import terminal_elimination as E
import translate_coordinates as T
from build_residue import put,hashobj

def addto(out,p,s):
 for m,c in p.items():
  out[m]=out.get(m,0)+s*c
  if not out[m]:out.pop(m)
def center(source,outdir):
 eq=json.loads((source/'equation.json').read_text());initial=json.loads((source/'translation_certificate.json').read_text());base=json.loads((source/'projected.json').read_text())
 rows=[E.normalize(r['terms']) for r in eq['residuals']];squares=[E.multiply(p,p) for p in rows];total={}
 for p in squares:addto(total,p,1)
 shifts={};history=[]
 def score(p):return(max(map(abs,p.values())),len(p),sum(map(abs,p.values())))
 best=score(total)
 for stage in range(8):
  changes=0
  for v,meta in enumerate(eq['variables']):
   if meta['kind']=='integer_guard':continue
   hits=[r for r,p in enumerate(rows) if any(v in m for m in p)]
   options=[]
   for d in [-8,-4,-3,-2,-1,1,2,3,4,8]:
    nr={r:E.substitute(rows[r],v,{(v,):1,():d}) for r in hits};ns={r:E.multiply(p,p) for r,p in nr.items()};nt=total.copy()
    for r in hits:addto(nt,squares[r],-1);addto(nt,ns[r],1)
    s=score(nt)
    if s<best:options.append((s,abs(d),d,nr,ns,nt))
   if options:
    s,_,d,nr,ns,total=min(options,key=lambda x:x[:3]);best=s
    for r in hits:rows[r]=nr[r];squares[r]=ns[r]
    shifts[v]=shifts.get(v,0)+d;changes+=1;history.append({'pass':stage,'variable':v,'shift':d,'score':list(s)})
  print('pass',stage,'changes',changes,'score',best,flush=True)
  if not changes:break
 final=copy.deepcopy(eq)
 for r,p in zip(final['residuals'],rows):r['terms']=E.as_terms(p)
 final['variant']+=':finite_centering';combined=dict(initial['shifts'])
 for v,d in shifts.items():combined[v]=combined.get(v,0)+d
 combined={v:d for v,d in combined.items() if d}
 direct=T.translate(base,combined)
 if direct['residuals']!=final['residuals']:raise ValueError('composed translation mismatch')
 poly=E.expand(final);metrics={'variables':len(final['variables']),'rows':len(final['residuals']),'degree':max(len(m) for c,m in poly['terms']),'monomials':len(poly['terms']),'height':max(abs(c) for c,m in poly['terms']),'row_height':max(abs(c) for r in final['residuals'] for c,m in r['terms'])}
 cert={'schema':'integral_translation_v1','input_sha256':hashobj(base),'output_sha256':hashobj(final),'shifts':[[v,d] for v,d in sorted(combined.items())],'convention':'old=new+shift','search_history':history,'source_translation_sha256':hashobj(initial),'search_scope':'Eight coordinate-descent passes over non-guard coordinates, local increments ±1,±2,±3,±4,±8; no global optimality claim.'}
 for n,x in [('equation.json',final),('expanded_polynomial.json',poly),('translation_certificate.json',cert),('METRICS.json',metrics),('projected.json',base)]:put(outdir,n,x)
 print(metrics)
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('source',type=Path);a.add_argument('out',type=Path);z=a.parse_args();center(z.source,z.out)
