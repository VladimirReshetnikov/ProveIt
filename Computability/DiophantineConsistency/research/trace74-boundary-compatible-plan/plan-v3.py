#!/usr/bin/env python3
"""Read-only five-stage draft plan; does not compile or validate proof bodies."""
from pathlib import Path
from hashlib import sha256
import json,os,re,sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;D=H.parents[1];P=D/'research/trace75-bfs-ipra-final-assembly-plan/observations/attempt01/result.json';O=D/'research/trace75-bfs-ipra-final-assembly-plan/observations/outer-attempt01/terminal.json';A=D/'reviews/trace75-bfs-final-assembly-result-independent/README.md';MS=D/'research/trace75-mask-coordinate-ring-probe/Trace74Mask.lean';MR=MS.parent/'observations/ring-attempt02/terminal.json'
BASE=Path('/tmp/trace75-final-assembly-7cxl4am4/lib');PACK=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');CORE=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
pins={P:'b05b0970cde855c6c65973b9550ae7231b7cca02f8659140a166f206bf51093c',O:'2188db777c5fe442be871c30d29943de70fe0c1d20325d49b00bb9886e56c69d',A:'d99de3ef2a5bd0b08af624e2421f4cc10f6eb9a9886eb67a94016a237d6b2c6b',MS:'83ad7a62d50b10104099d8769c201c5514ed3afdabcf30ce1df8f4bb7774b7f0',MR:'4be85ee6a9e08695c3f67e1d1154108cdb601308ac4c1da46b6f4a24e9559fc9'}
sha=lambda p:sha256(Path(p).read_bytes()).hexdigest()
for p,h in pins.items():assert sha(p)==h,(str(p),'pin')
r=json.loads(P.read_text());o=json.loads(O.read_text());m=json.loads(MR.read_text());assert r['status']=='PASS' and Path(r['output_root'])/'lib'==BASE and o['exit']==0 and o['child_status']=='PASS' and o['child_result_sha256']==sha(P) and m['exit']==0
ATTEMPT=D/'research/trace74-boundary-compatible-rebuild/observations/attempt01/result.json';assert sha(ATTEMPT)=='e6355b07b8ba9d9e2d156a42a9453cba8f939c1d17623eaa9a590e108b5d7f88'
oldparent=(D/'research/trace74-boundary-parent-binding-draft/Trace74BoundaryParent.lean').read_text();newparent=(D/'research/trace74-boundary-parent-binding-v2/Trace74BoundaryParent.lean').read_text();assert newparent==oldparent.replace("    fin_cases j <;> simp [oldVal,w,old,hmask'] <;> ring","    fin_cases j <;> simp [oldVal,w,old,hmask']") and oldparent!=newparent
for n in ('Trace74BoundaryParts','Trace74BoundaryNatural','Trace74BoundaryGraph'):assert (D/'research/trace74-boundary-parent-binding-v2'/(n+'.lean')).read_bytes()==(D/'research/trace74-boundary-parent-binding-draft'/(n+'.lean')).read_bytes()
ATTEMPT2=D/'research/trace74-boundary-compatible-rebuild/observations/attempt02/result.json';assert sha(ATTEMPT2)=='7fa0e46762ba578eca06fd40b783ce5e0f6c47b483ee5cf5eb1c48772bc2c8ee'
oldgraph=(D/'research/trace74-boundary-parent-binding-v2/Trace74BoundaryGraph.lean').read_text();newgraph=(D/'research/trace74-boundary-parent-binding-v3/Trace74BoundaryGraph.lean').read_text();assert newgraph==oldgraph.replace('set_option maxRecDepth 16384\n','set_option maxRecDepth 16384\nset_option maxHeartbeats 8000000\n') and oldgraph!=newgraph
for n in ('Trace74BoundaryParent','Trace74BoundaryParts','Trace74BoundaryNatural'):assert (D/'research/trace74-boundary-parent-binding-v3'/(n+'.lean')).read_bytes()==(D/'research/trace74-boundary-parent-binding-v2'/(n+'.lean')).read_bytes()
DRAFT=D/'research/trace74-boundary-parent-binding-v3';stages=[('Trace74Mask',MS),('Trace74BoundaryParent',DRAFT/'Trace74BoundaryParent.lean'),('Trace74BoundaryParts',DRAFT/'Trace74BoundaryParts.lean'),('Trace74BoundaryNatural',DRAFT/'Trace74BoundaryNatural.lean'),('Trace74BoundaryGraph',DRAFT/'Trace74BoundaryGraph.lean')];names=[n for n,_ in stages];done=set();rows=[];direct={}
def selected(n):
 rel=n.replace('.','/')+'.olean'
 for root in (BASE,PACK,CORE):
  p=root/rel
  if os.path.lexists(p):assert p.is_file(),('dangling',str(p));return p
 raise RuntimeError('missing '+n)
def record(p):return {'path':str(p),'resolved':str(p.resolve(strict=True)),'sha256':sha(p)}
for n,source in stages:
 assert not os.path.lexists(BASE/(n+'.olean')),'stage already exists '+n
 imports=re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',source.read_text(),re.M);reports=re.findall(r'^#print axioms\s+([A-Za-z0-9_.]+)\s*$',source.read_text(),re.M);assert len(reports)==1
 refs={}
 for dep in imports:
  if dep in names:assert dep in done,(n,dep);refs[dep]={'kind':'stage'}
  else:
   p=selected(dep);x={'kind':'project' if p.is_relative_to(BASE) else 'outside',**record(p)}
   if dep in direct:assert direct[dep]==x
   direct[dep]=x;refs[dep]=x
 rows.append({'module':n,'source':str(source),'source_sha256':sha(source),'imports':imports,'direct':refs,'report':reports[0],'source_scope':'previously checked ring identity' if n=='Trace74Mask' else 'unchecked draft'});done.add(n)
for p,h in pins.items():assert sha(p)==h
out={'status':'PASS','scope':'source and first direct-import inventory only; four proof drafts unchecked; no Lean replay or transitive/source ancestry claim','parent_sha256':sha(P),'outer_sha256':sha(O),'parent_audit_sha256':sha(A),'prior_attempt_sha256':sha(ATTEMPT),'prior_attempt2_sha256':sha(ATTEMPT2),'planner_sha256':sha(__file__),'base':str(BASE),'stages':rows,'direct':direct}
d=H/'observations/plan-attempt03';d.mkdir(parents=True,exist_ok=False);(d/'result.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps({'status':'PASS','stages':len(rows),'direct':len(direct),'outside':[n for n,x in direct.items() if x['kind']=='outside'],'sha256':sha(d/'result.json')}))
