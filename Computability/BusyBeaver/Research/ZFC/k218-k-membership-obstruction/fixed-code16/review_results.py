#!/usr/bin/env python3
"""Own finite check of bounded search outputs; no search code imported."""
import hashlib,json
from pathlib import Path
from itertools import product
p=Path(__file__).resolve().parent
rows=json.loads((p/'literal-rows.json').read_text())
selected=['rho1','rho2','rho3','rho4','rho5','rho6','G','bundle222','K','restricted_rho8_RAB']
checks=[]
for name in ['search3-d1.json','search4-d1.json','search5-d2.json']:
 m=json.loads((p/name).read_text());n=m['n'];D=set(range(n-m['nd'],n));t=m['T'];f=m['F']
 def ev(x,env):
  if isinstance(x,str):return env[x]
  return m[x[0]][n*ev(x[1],env)+ev(x[2],env)]
 failed={}
 for r in selected:
  tree,vs=rows[r]
  bad=[dict(zip(vs,vals)) for vals in product(range(n),repeat=len(vs)) if ev(tree,dict(zip(vs,vals),t=t,f=f)) not in D]
  failed[r]=len(bad)
 assert not any(failed.values())
 assert m['I'][n*t+t]==t and m['R'][n*t+t]==f
 assert t in D and f not in D
 assert all(not(a in D and m['I'][n*a+b] in D) or b in D for a,b in product(range(n),repeat=2))
 assert all(m['Q'][n*a+b] in D for a in range(n) for b in D)
 ff=m['I'][n*f+f];assert ff not in D
 assert m['status']=='BOUNDED_NO_MODEL' and m['score']==1 and m['scores']==[0]*9+[1]
 checks.append({'file':name,'sha256':hashlib.sha256((p/name).read_bytes()).hexdigest(),'attempts':m['attempts'],'seconds':m['seconds'],'values':n,'designated_values':sorted(D),'literal_row_failures':failed,'fixed_identity_value':ff,'fixed_identity_designated':False})
result={'status':'BOUNDED_FIXED_CODE16_SEARCH_NO_MODEL','reviews':checks,'attempts_total':sum(x['attempts'] for x in checks),'seconds_total':sum(x['seconds'] for x in checks),'scope':'Own stochastic search of exact K+RAB base calculus plus single native code16 axiom. No candidate, completeness, calibration or inconsistency result. Every saved best table independently passes all unextended literal rows and fails only the new fixed-identity constraint; no arbitrary substitution or identity schema assumed.'}
(p/'review.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
