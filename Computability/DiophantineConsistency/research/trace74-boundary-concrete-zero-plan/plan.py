#!/usr/bin/env python3
"""Read-only source/import plan for unchecked witness-preserving drafts."""
from pathlib import Path
from hashlib import sha256
import json,os,re,sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;D=H.parents[1];P=D/'research/trace74-boundary-seed-model-facts-rebuild/observations/attempt02/result.json';O=D/'research/trace74-boundary-seed-model-facts-rebuild/observations/outer-attempt02/terminal.json';A=D/'reviews/trace74-boundary-seed-model-facts-result-independent/README.md';S=D/'research/trace74-boundary-concrete-zero-draft';BASE=Path('/tmp/trace74-boundary-seed-model-facts-8polforg/lib');PACK=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');CORE=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
pins={P:'e64fbe79ab317580c98e7af4c66667c53600993d5d72157a8d9b793e8a72927a',O:'c320a8499e66075f596e1e37e30b98b650d6493bf08dab9c9c1603cb488d79da',A:'fde0dff0ef1ad05118663b5c99bc375ff232ff43e3cef4f48e51452d643a7b8e'};sha=lambda p:sha256(Path(p).read_bytes()).hexdigest()
for p,h in pins.items():assert sha(p)==h,(str(p),'pin')
r=json.loads(P.read_text());o=json.loads(O.read_text());assert r['status']=='PASS' and Path(r['output_root'])/'lib'==BASE and o['exit']==0 and o['child_status']=='PASS' and o['child_result_sha256']==sha(P)
names=['Trace74BoundaryConcreteZero'];done=set();rows=[];direct={}
def selected(n):
 rel=n.replace('.','/')+'.olean'
 for root in (BASE,PACK,CORE):
  p=root/rel
  if os.path.lexists(p):assert p.is_file(),('dangling',str(p));return p
 raise RuntimeError('missing '+n)
for n in names:
 source=S/(n+'.lean');assert not os.path.lexists(BASE/(n+'.olean')),'stage already exists '+n
 imports=re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',source.read_text(),re.M);reports=re.findall(r'^#print axioms\s+([A-Za-z0-9_.]+)\s*$',source.read_text(),re.M);assert reports==['Trace74BoundaryConcreteZero.positive_zero_with_boundary']
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
