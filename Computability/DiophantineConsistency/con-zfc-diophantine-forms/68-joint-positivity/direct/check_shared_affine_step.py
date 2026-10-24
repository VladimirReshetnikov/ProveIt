#!/usr/bin/env python3
"""Exact structure and modular replay; not global/kernel validation."""
import json,random
from pathlib import Path
from collections import defaultdict
R=Path(__file__).resolve().parent
Q=json.loads((R/'affine_shared_step.json').read_text());H=Q['horn_source']
def poly(rs,e,m):
 s=0
 for r in rs:
  x=r['coefficient']
  for k in r['monomial']:x=x*e[k]%m
  s=(s+x)%m
 return s
for b in H['branches']:
 out=defaultdict(int)
 for rows in b['quadratic_residuals']:
  for a in rows:
   for c in rows:out[tuple(sorted(a['monomial']+c['monomial']))]+=a['coefficient']*c['coefficient']
 assert {m:c for m,c in out.items() if c}=={tuple(r['monomial']):r['coefficient'] for r in b['sum_of_squares']}
assert len(Q['witnesses'])==Q['witness_count']==23
assert sum(b['degree'] for b in H['branches'])==Q['exact_degree']==50
rng=random.Random(222510);count=0
for b in H['branches']:
 for i in range(20):
  for mod in (1000000007,1000000009):
   e={x:0 for x in Q['witnesses']};e.update(a=0,b=1,c=2,d=1,p=0,q=0,v=0)
   # Bundle guard: |(c-a)(c-b)|=d+1=2.
   if b['name']=='mp':e['p']=i;e['v']=i+1;e['q']=2*(2*i+1)*(2*i+2)+4*(i+1)
   elif b['name']=='gen':e['p']=i
   for w in b['wires']:e[w['name']]=poly(w['value'],e,mod)
   if b['name'] not in ('truth','mp'):
    assert any(r['monomial']==['v'] and r['coefficient']==1 for r in b['quadratic_residuals'][-1])
    e['v']=(-poly(b['quadratic_residuals'][-1],e,mod))%mod
   assert all(poly(rs,e,mod)==0 for rs in b['quadratic_residuals'])
   e['m']=max(e['p'],e['q'],e['v']);e['M0']=5
   for a,d in [('p','dp'),('q','dq'),('v','dv')]:e[d]=e['m']-e[a]
   M=e['M0']+1;e['S']=1+e['v']*M;e['Sp']=(1+e['p']*M)*(1+e['q']*M)
   assert all(poly(rs,e,mod)==0 for rs in Q['extra_residuals'])
   val=1
   for bb in H['branches']:val=val*poly(bb['sum_of_squares'],e,mod)%mod
   assert val==0
   e['Sp']+=1
   assert poly(Q['extra_residuals'][0],e,mod)==(1+e['v']*M)%mod
   count+=1
print(json.dumps({'status':'pass','exact_branch_sos_expansions':len(H['branches']),'local_modular_replays':count,'witness_count':23,'degree':50,'scope':'local structure and modular checks; commonMultiple block not asserted for these fixtures; global Lean uncompiled'},indent=2))
