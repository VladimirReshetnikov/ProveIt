#!/usr/bin/env python3
"""Exact source mutation for even-horizon cofinal beta witnesses.

The t0 translation is not a natural bijection. COFINAL_PROOF.md supplies its
ordinary domain theorem; check_source.py independently checks the finite edit.
"""
from copy import deepcopy
from hashlib import sha256
import json

def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def transform(source,arithmetic):
 E=deepcopy(source);pc=arithmetic
 vs={v['name']:i for i,v in enumerate(E['variables'])};T=vs['t0']
 for r in E['residuals']:
  r['terms']=pc.dump(pc.subst(pc.loadpoly(r['terms']),T,{(T,):2,():-8}))
  if r['label']=='endpoint.first_remainder':
   r['label']='endpoint.cofinal_beta_bound';r['terms']=pc.dump({(vs['y'],):1,():1,(vs['pow0.output'],):-1})
 used=sorted({i for r in E['residuals'] for c,m in r['terms'] for i in m});rename={old:new for new,old in enumerate(used)}
 E['variables']=[E['variables'][i] for i in used]
 for r in E['residuals']:r['terms']=pc.dump(pc.loadpoly([[c,[rename[i] for i in m]] for c,m in r['terms']]))
 E['variant']+='_even_horizon4_cofinal_beta';E['metrics'],exp=pc.metrics_and_polynomial(E)
 cert={'schema':'even_descending_cofinal_beta_v1','source_sha256':sha256(canonical(source)).hexdigest(),'target_sha256':sha256(canonical(E)).hexdigest(),'old_t0_equals':[2,-8],'new_horizon':'t=2*t0+4','deleted_original_variable_index':vs['endpoint.r0'],'retained_original_indices':used,'replaced_row':'endpoint.first_remainder','new_row':'y+1=V','ordinary_proof':'COFINAL_PROOF.md'}
 return E,exp,cert
