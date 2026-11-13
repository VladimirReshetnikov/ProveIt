#!/usr/bin/env python3
"""Read-only source/import plan for unchecked witness-preserving drafts."""
from pathlib import Path
from hashlib import sha256
import json,os,re,sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;D=H.parents[1];P=D/'research/trace74-boundary-compatible-rebuild/observations/attempt03/result.json';O=D/'research/trace74-boundary-compatible-rebuild/observations/outer-attempt03/terminal.json';A=D/'reviews/trace74-boundary-compatible-result-independent/README.md';S=D/'research/trace74-boundary-witness-draft';BASE=Path('/tmp/trace74-boundary-compatible-oq_vacvw/lib');PACK=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');CORE=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
pins={P:'aa17ffeb0a2446d44392d986af54a9cd687dd544c67dc145a87c77f600e7a2d3',O:'2493accc873ec46391494ef5125de3b61d460b4bef61fb56f54f966ccbc036d0',A:'cfce71fa601910a41c86106b8421ddff024d906a711ae02ab5de3c61abc2e14b'};sha=lambda p:sha256(Path(p).read_bytes()).hexdigest()
for p,h in pins.items():assert sha(p)==h,(str(p),'pin')
r=json.loads(P.read_text());o=json.loads(O.read_text());assert r['status']=='PASS' and Path(r['output_root'])/'lib'==BASE and o['exit']==0 and o['child_status']=='PASS' and o['child_result_sha256']==sha(P)
PRIOR=D/'research/trace74-boundary-witness-rebuild/observations/attempt01/result.json';PRIOR_OUTER=D/'research/trace74-boundary-witness-rebuild/observations/outer-attempt01/terminal.json'
assert sha(PRIOR)=='253f56b0df87d41b487f85405f4912ca5c745578a2302a93eaaaf785cf4f555f' and sha(PRIOR_OUTER)=='69e6a0bbedea877a2d5f339b774414cf144f90b36fa075cfa43c2512718cb203'
names=['Trace74BoundaryParentWitness','Trace74BoundaryPartsWitness','Trace74BoundaryNaturalWitness','Trace74BoundaryGraphWitness'];done=set();rows=[];direct={}
def selected(n):
 rel=n.replace('.','/')+'.olean'
 for root in (BASE,PACK,CORE):
  p=root/rel
  if os.path.lexists(p):assert p.is_file(),('dangling',str(p));return p
 raise RuntimeError('missing '+n)
for n in names:
 source=S/(n+'.lean');assert not os.path.lexists(BASE/(n+'.olean')),'stage already exists '+n
 imports=re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',source.read_text(),re.M);reports=re.findall(r'^#print axioms\s+([A-Za-z0-9_.]+)\s*$',source.read_text(),re.M);assert len(reports)==1
 refs={}
 for dep in imports:
  if dep in names:assert dep in done,(n,dep);refs[dep]={'kind':'stage'}
  else:
   p=selected(dep);x={'kind':'project' if p.is_relative_to(BASE) else 'outside','path':str(p),'resolved':str(p.resolve(strict=True)),'sha256':sha(p)}
   if dep in direct:assert direct[dep]==x
   direct[dep]=x;refs[dep]=x
 rows.append({'module':n,'source':str(source),'source_sha256':sha(source),'imports':imports,'direct':refs,'report':reports[0],'source_scope':'unchecked draft'});done.add(n)
for p,h in pins.items():assert sha(p)==h
out={'status':'PASS','scope':'source and current first direct-import inventory only; four proof drafts unchecked; no Lean replay or transitive/source ancestry claim','parent_sha256':sha(P),'outer_sha256':sha(O),'parent_audit_sha256':sha(A),'prior_attempt_sha256':sha(PRIOR),'prior_outer_sha256':sha(PRIOR_OUTER),'planner_sha256':sha(__file__),'base':str(BASE),'stages':rows,'direct':direct}
d=H/'observations/plan-attempt02';d.mkdir(parents=True,exist_ok=False);(d/'result.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps({'status':'PASS','stages':len(rows),'direct':len(direct),'outside':[n for n,x in direct.items() if x['kind']=='outside'],'sha256':sha(d/'result.json')}))
