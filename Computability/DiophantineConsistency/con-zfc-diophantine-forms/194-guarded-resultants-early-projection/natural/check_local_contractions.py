#!/usr/bin/env python3
"""Verify the bounded single-monic-contraction negative result exactly."""
from pathlib import Path
import json
import independent_algebra as A
R=Path(__file__).resolve().parent
s=A.read(R/'natural201/equation.json');c=A.read(R/'natural201/ELIMINATION_TEST.json');rows=[A.load(r['terms'])for r in s['residuals']];candidates=[]
for j,p in enumerate(rows):
 for v in range(len(s['variables'])):
  a=p.get(((v,1),),0)
  if abs(a)!=1 or any(any(i==v for i,k in m)for m in p if m!=((v,1),)):continue
  candidates.append((v,j))
A.need(len(candidates)==c['monic_candidates']==204,'candidate count');A.need(set(candidates)=={(x['variable'],x['defining_row'])for x in c['candidates']},'candidate coverage');A.need(len(c['candidates'])==len(candidates) and c['quadratic_survivors']==[],'candidate duplication or claimed survivor')
for x in c['candidates']:
 v=x['variable'];j=x['defining_row'];p=rows[j];a=p[((v,1),)];f=A.coeff(-a,A.plus(p,A.coeff(-a,A.atom(v))));obs=x['obstruction'];k=obs['row'];A.need(k!=j and 0<=k<len(rows),'invalid obstruction');q=A.replace(rows[k],{v:f});degree=A.degree(q);A.need(degree==obs['degree'] and degree>2,'invalid degree obstruction')
print(json.dumps({'status':'PASS','scope':'Only single monic substitutions in the literal natural201 residual basis; no global lower bound.','monic_candidates':len(candidates),'exact_degree_obstructions':len(candidates)},sort_keys=True,indent=2))
