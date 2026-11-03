#!/usr/bin/env python3
"""Read-only source/import plan for unchecked witness-preserving drafts."""
from pathlib import Path
from hashlib import sha256
import json,os,re,sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;D=H.parents[1];P=D/'research/trace74-boundary-seed-specialization-rebuild/observations/attempt01/result.json';O=D/'research/trace74-boundary-seed-specialization-rebuild/observations/outer-attempt01/terminal.json';A=D/'reviews/trace74-boundary-seed-specialization-result-independent/README.md';S=D/'research/trace74-boundary-seed-model-facts-draft';BASE=Path('/tmp/trace74-boundary-seed-specialization-vpn0vl6g/lib');PACK=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');CORE=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
pins={P:'cb5339ea9547b274009117466cb68ba56ba4d452eaccf21333949562c0cbd3d3',O:'775418302bea11deb6e7d0cd8d6630cae02cd5645f3980594921decd1d78f9ae',A:'f6d8d0ac136014b81e31310f683521b1cd7fe20ba1dfd79a2b03981a635869ba'};sha=lambda p:sha256(Path(p).read_bytes()).hexdigest()
for p,h in pins.items():assert sha(p)==h,(str(p),'pin')
r=json.loads(P.read_text());o=json.loads(O.read_text());assert r['status']=='PASS' and Path(r['output_root'])/'lib'==BASE and o['exit']==0 and o['child_status']=='PASS' and o['child_result_sha256']==sha(P)
names=['Trace74BoundarySeedModelFacts'];done=set();rows=[];direct={}
def selected(n):
 rel=n.replace('.','/')+'.olean'
 for root in (BASE,PACK,CORE):
  p=root/rel
  if os.path.lexists(p):assert p.is_file(),('dangling',str(p));return p
 raise RuntimeError('missing '+n)
for n in names:
 source=S/(n+'.lean');assert not os.path.lexists(BASE/(n+'.olean')),'stage already exists '+n
 imports=re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',source.read_text(),re.M);reports=re.findall(r'^#print axioms\s+([A-Za-z0-9_.]+)\s*$',source.read_text(),re.M);assert reports==['Trace74BoundarySeedModelFacts.model_facts']
 refs={}
 for dep in imports:
  if dep in names:assert dep in done,(n,dep);refs[dep]={'kind':'stage'}
  else:
   p=selected(dep);x={'kind':'project' if p.is_relative_to(BASE) else 'outside','path':str(p),'resolved':str(p.resolve(strict=True)),'sha256':sha(p)}
   if dep in direct:assert direct[dep]==x
   direct[dep]=x;refs[dep]=x
 rows.append({'module':n,'source':str(source),'source_sha256':sha(source),'imports':imports,'direct':refs,'report':reports[0],'source_scope':'unchecked draft'});done.add(n)
for p,h in pins.items():assert sha(p)==h
out={'status':'PASS','scope':'source and current first direct-import inventory only; one proof draft unchecked; no Lean replay or transitive/source ancestry claim','parent_sha256':sha(P),'outer_sha256':sha(O),'parent_audit_sha256':sha(A),'planner_sha256':sha(__file__),'base':str(BASE),'stages':rows,'direct':direct}
d=H/'observations/plan-attempt01';d.mkdir(parents=True,exist_ok=False);(d/'result.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps({'status':'PASS','stages':len(rows),'direct':len(direct),'outside':[n for n,x in direct.items() if x['kind']=='outside'],'sha256':sha(d/'result.json')}))
