#!/usr/bin/env python3
"""Independent final-table identity, certificate binding and blank endpoint check."""
from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parents[1]/'combine/candidate238';O=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def table(p):
 t={}
 for l in p.read_text().splitlines():
  if l and not l.startswith('#'):
   q,b,w,d,n=l.split();q,b,w,n=map(int,[q,b,w,n]);assert(q,b)not in t
   assert b in(0,1)and w in(0,1)and d in('L','R');t[q,b]=(w,d,n)
 return t
t=table(R/'zfc_combined238_old.tm');c=table(R/'zfc_combined238.tm');m=json.loads((R/'renumbering.json').read_text());f={int(q):n for q,n in m['old_to_new'].items()}
assert len(t)==len(c)==476 and set(c)=={(q,b)for q in range(238)for b in(0,1)}
assert {n for w,d,n in c.values()}-set(range(238))=={238}
assert all(c[f[q],b]==(w,d,f[n])for(q,b),(w,d,n)in t.items())
assert f[95]==0 and f[96]==84 and f[254]==238
q=95;h=0;cells={}
for _ in range(409835):
 b=cells.get(h,0);w,d,q=t[q,b]
 if w:cells[h]=w
 else:cells.pop(h,None)
 h+=1 if d=='R'else -1
want={-6:1,176:1};p=177
for v in [0,0,0,3,0,0,3,0,0]+[1]*167:
 p+=1
 for i in range(p,p+v+1):want[i]=1
 p+=v+1
assert(q,h)==(96,-5)and cells==want and len(cells)==351
summary=json.loads((R/'universal_runtime.json').read_text());cases=json.loads((R/'universal_runtime_cases.json').read_text());sites=json.loads((R/'sites_logical.json').read_text())
assert summary['status']=='UNIVERSAL_MATHEMATICAL_PASS'and len(cases)==8386
assert summary['table_sha256']==sha(R/'zfc_combined238_old.tm')
assert summary['sites_sha256']==sha(R/'sites_logical.json')
for field,name in [('checker_sha256','check_literal_runtime.py'),('engine_sha256','symbolic_runtime.py'),('helper_sha256','independent_runtime.py')]:assert summary[field]==sha(R/name)
assert [(x['site_index'],x['positive'])for x in cases]==[(i,b)for i,s in enumerate(sites)for b in([False,True]if s[1]=='CD'else[False])]
assert sum(x['symbolic_steps']for x in cases)==2255513
assert min(x['duration'][0]for x in cases)==13
assert all(len(x['duration'])==13 and x['duration'][0]>=13 and all(n>=0 for n in x['duration'])for x in cases)
assert set(map(tuple,summary['directly_used_rows']))==set(t)
report={'status':'PASS','ordinary_mathematical_endpoint':'ACCEPTED','canonical_sha256':sha(R/'zfc_combined238.tm'),'inherited_sha256':sha(R/'zfc_combined238_old.tm'),'working_states':238,'transition_rows':476,'separate_halt':238,'start':0,'dispatch':84,'exact_canonical_isomorphism':True,'independent_startup':{'steps':409835,'old_state':q,'head':h,'full_frame_and_zero_exteriors':True,'one_cells':351},'runtime_certificate_bound_to_exact_table_source_and_engine':True,'all_guard_pairs_exactly_once':8386,'symbolic_steps':2255513,'minimum_positive_constant_duration':13,'all476rows_covered':True,'universal_engine_soundness_review':'AUDIT.md','theorem':'ZFC proves Nonhalt(M238, blank) iff Con(ZFC), composing the inherited exact source calibration with source bisimulation, whole-frame positive runtime simulation and exact blank initialization.','limits':'Ordinary mathematical proof; no new Lean/Rocq kernel endpoint or serialized ZFC derivation.'}
(O/'combined_endpoint_acceptance.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
