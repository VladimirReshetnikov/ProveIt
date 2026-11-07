#!/usr/bin/env python3
"""Syntactic weighted-degree screen for literal unit-variable substitutions."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
p=Path(__file__).resolve().parent
seed=p.parent/'nine-sharing-sign26-sextic-gap-congruence-candidate/seed.json'
raw=seed.read_bytes()
if hashlib.sha256(raw).hexdigest()!='36efa7dd3b2ea06d210b8975db2cbfc4f7494549c87204ada18747a720cb1f25':raise SystemExit('seed pin mismatch')
s=json.loads(raw);rows=s['residuals']
def degree(t,which=None,weight=None):
 if not isinstance(t,list) or not t:raise ValueError('bad AST')
 op=t[0]
 if op=='var' and len(t)==2:return weight if t[1]==which else 1
 if op in ('num','port') and len(t)==2:return 0
 if op not in ('add','sub','mul') or len(t)!=3:raise ValueError('unknown AST '+repr(t[:1]))
 a,b=degree(t[1],which,weight),degree(t[2],which,weight)
 return a+b if op=='mul' else max(a,b)
out=[]
for i,r in enumerate(rows):
 e=r['expr']
 if e[0]!='sub' or not isinstance(e[1],list) or e[1][0]!='var':continue
 v=e[1][1];rhs=degree(e[2]);remain=[]
 for j,t in enumerate(rows):
  if j==i:continue
  x=degree(t['expr'],v,rhs)
  if x>3:remain.append({'gate':t['gate'],'syntactic_degree':x})
 out.append({'gate':r['gate'],'kind':r['kind'],'coordinate':v,'rhs_degree':rhs,'max_remaining_degree':max(degree(t['expr'],v,rhs) for j,t in enumerate(rows) if j!=i),'above_three':remain})
if len(out)!=11:raise ValueError('unexpected candidate count')
print(json.dumps({'schema':'sign26_literal_unit_cut_weighted_survey_v1','seed_sha256':hashlib.sha256(raw).hexdigest(),'status':'PASS','scope':'Syntactic upper degrees only: no cancellation, congruence, positivity, or lower-bound claims. Dropped rows must additionally justify natural reconstruction.','cases':out},indent=2,sort_keys=True))
