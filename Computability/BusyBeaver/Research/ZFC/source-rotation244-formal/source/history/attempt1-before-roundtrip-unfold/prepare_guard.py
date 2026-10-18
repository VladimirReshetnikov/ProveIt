#!/usr/bin/env python3
"""Own metadata-only adaptation; never imports or executes the guarded programs."""
from pathlib import Path
import ast,difflib,hashlib,json,re
B=Path('/tmp/zfc243-source-bridge')
T=Path('/tmp/zfc243-combined-lean/simulation/check.py')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
d=lambda p:dict(path=str(p),sha256=sha(p))
assert sha(T)=='9129e9f7874dbfc57bb850558e3c9aa728b694aec14663ac06697219e5e4b651'
P={
 'program':('/tmp/zfc243-calibration-plan/run1/verification.json','678a6a766caa23e1004540016d0dd71d04cbeb8561f273e9e3c83d5c81c9e5ab',7,7),
 'loop':('/tmp/zfc-rmdag-loop-rotation/run1/verification.json','f170c9bd2c21450b36aac6ffd988a40d028c0dee731563737efc6a2dbc04cbd6',6,8),
 'context':('/tmp/zfc-rmdag-context-substitution/run1/verification.json','a17b3d4259f3be10a040ebf2fd5cc898ba4fd6e5b3883bd8df4ce5a961eb42b2',5,6)}
parents={};pool={};tools={};compiler=None
for key,(path,h,np,nc) in P.items():
 p=Path(path);assert sha(p)==h;r=json.loads(p.read_text())
 assert r['status']=='PASS' and (r['named_axiom_probes'],r['callers'],r['warnings'])==(np,nc,0)
 assert r['before']==r['after'] and r['all_input_provider_postchecks'] and r['all_fresh_objects_unchanged_after_audit']
 for pp,hh in r['before'].items():assert sha(pp)==hh,pp
 for c in r['commands']:
  assert c['exit_code']==0 and not c['timed_out'] and c['interrupted'] is None
  assert sha(c['log'])==c['log_sha256']==hashlib.sha256(c['output'].encode()).hexdigest()
 names=re.findall(r'^#print axioms (\S+)$',Path(r['audit']['snapshot']).read_text(),re.M)
 assert names==[q['name']for q in r['axiom_reports']] and len(names)==np
 assert len(re.findall(r'^example\b',Path(r['audit']['snapshot']).read_text(),re.M))==nc
 assert len(r['fresh_modules'])==1;f=r['fresh_modules'][0]
 assert r['source_pass_object']==dict(f,source_command_index=0)
 assert r['fresh_first_provider_before_audit']=={k:f[k]for k in ['module','path','sha256']}
 for q in r['reused_modules']+[dict(module=f['module'],source=r['source']['path'],source_sha256=f['source_sha256'],object=f['path'],object_sha256=f['sha256'])]:
  q={k:q[k]for k in ['module','source','source_sha256','object','object_sha256']}
  for k in ['source','object']:assert sha(q[k])==q[k+'_sha256']
  assert q['module']not in pool or pool[q['module']]==q;pool[q['module']]=q
 for q in r['toolchain_providers']:
  q={k:q[k]for k in ['module','object','object_sha256']};assert sha(q['object'])==q['object_sha256']
  assert q['module']not in tools or tools[q['module']]==q;tools[q['module']]=q
 assert compiler is None or compiler==r['compiler'];compiler=r['compiler']
 parents[key]=dict(path=str(p),sha256=h,probes=np,callers=nc,audit_names=names,report_names=names,tools=['Init'])
assert set(pool)=={'BusyBeaver.ZFC.'+x for x in ['RegisterPath','RMDag','RMEquiv','RMBisim','ProgramRouting245','ProgramRotation244','RMDagLoopRotation','RMDagContextSubstitution']}
assert set(tools)=={'Init'}
S=B/'SourceRotation244.lean';A=B/'Audit.lean'
assert sha(S)=='1841efd5e21b70b4384c61cff06f5efe525388f7d0838c0767cc85d28abaafe7'
assert sha(A)=='7e95a46fe93957440d3ac2ccb5cc8496967dfaa006ba43fcb1b42fe24853d989'
probes=[n.rsplit('.',1)[1]for n in re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)]
assert len(probes)==9 and len(re.findall(r'^example\b',A.read_text(),re.M))==10
imps=lambda p:re.findall(r'^import\s+([A-Za-z_][A-Za-z_0-9.]*)\s*$',Path(p).read_text(),re.M)
seen=set()
def visit(m):
 if m=='Init':return
 assert m in pool,m
 if m in seen:return
 seen.add(m)
 for n in imps(pool[m]['source']):visit(n)
for m in imps(S):visit(m)
assert seen==set(pool)
scope='Exact three actual source-level parents; eight selected project pairs and Init. Concrete arbitrary-register logical halting equivalence only; no binary runtime, blank bootstrap, ZF calibration or internal PA claim.'
static=[Path(__file__),T,B/'source-inventory.json',B/'review_finite_data.py',B/'author-finite-data-review.json',Path('/tmp/zfc243-calibration-plan/prepare_concrete_bridge.py'),Path('/tmp/zfc243-calibration-plan/static-dag-review.json'),Path('/tmp/zfc243-calibration-plan/wf-candidate-tables.json')]
boundary=dict(parents=parents,compiler=compiler,reused_modules=list(pool.values()),toolchain_providers=list(tools.values()),scope=scope,static_inputs=[d(p)for p in static])
bp=B/'boundary.json';assert not bp.exists();bp.write_text(json.dumps(boundary,indent=2)+'\n')
old=T.read_text();g=old
changes=[
 ('Concrete Combined243 versus Rotation244 whole-run simulation; exact three parents/seven projects.','Concrete logical source rotation; exact three parents/eight projects.'),
 ("HERE=Path('/tmp/zfc243-combined-lean/simulation')",f'HERE=Path({str(B)!r})'),
 ("MODULE='BusyBeaver.ZFC.Combined243Simulation'","MODULE='BusyBeaver.ZFC.SourceRotation244'"),
 ("PREFIX='SetTheory.BusyBeaver.ZFC.Combined243Simulation.'","PREFIX='SetTheory.BusyBeaver.ZFC.SourceRotation244.'"),
 (re.search(r'^PROBES=.*$',g,re.M)[0],'PROBES='+repr(probes)),
 (re.search(r'^SOURCE_SHA=.*$',g,re.M)[0],'SOURCE_SHA='+repr(sha(S))),
 (re.search(r'^AUDIT_SHA=.*$',g,re.M)[0],'AUDIT_SHA='+repr(sha(A))),
 (re.search(r'^BOUNDARY_SHA=.*$',g,re.M)[0],'BOUNDARY_SHA='+repr(sha(bp))),
 (re.search(r'^PARENT_SHAS=.*$',g,re.M)[0],'PARENT_SHAS='+repr({k:v[1]for k,v in P.items()})),
 ("default=HERE/'Combined243Simulation.lean'","default=HERE/'SourceRotation244.lean'"),
 ("len(pool)==7", "len(pool)==8"),
 ("set(alltools)=={'Init','Lean.Elab.Tactic.Omega'}", "set(alltools)=={'Init'}"),
 ('Wrong seven-project/two-tool union.','Wrong eight-project/Init union.'),
 ("imports(S)==['BusyBeaver.ZFC.PositiveBlockBisimulation','BusyBeaver.ZFC.Rotation244Invariant','BusyBeaver.ZFC.Combined243Blocks']",'imports(S)=='+repr(imps(S))),
 ("len(re.findall(r'^example\\b',A.read_text(),re.M))==4,'Wrong audit4/4.'", "len(re.findall(r'^example\\b',A.read_text(),re.M))==10,'Wrong audit9/10.'"),
 ("scope='Combined243 versus Rotation244 positive-block simulation, arbitrary finite-support start tapes and exact blank halting/nonhalting iff. No consistency calibration, PA internalization or infinite-support tape claim.'",'scope='+repr(scope)),
 ('exact_project_prerequisite_count=7','exact_project_prerequisite_count=8'),
 ('named_axiom_probes=4,callers=4','named_axiom_probes=9,callers=10'),
 ("for pp,h in e['before'].items():pin(pp,h)","for pp,h in e['before'].items():pin(pp,h)\n        for c in e['commands']:\n            require(c['interrupted'] is None and c['log_sha256']==hashlib.sha256(c['output'].encode()).hexdigest(),'Parent raw log binding.')\n            pin(c['log'],c['log_sha256'])")]
for a,z in changes:
 assert g.count(a)==1,(a,g.count(a));g=g.replace(a,z)
ast.parse(g);out=B/'check.py';assert not out.exists();out.write_text(g)
(B/'guard-from-simulation.diff').write_text(''.join(difflib.unified_diff(old.splitlines(True),g.splitlines(True),fromfile=str(T),tofile=str(out))))
(B/'guard-proposal.json').write_text(json.dumps(dict(status='SOURCE_ONLY_UNEXECUTED',source=d(S),audit=d(A),guard=d(out),boundary=d(bp),template=d(T),parents=parents,projects=8,tools=['Init'],probes=9,callers=10,shared_seconds=120,compiler_flags=['-j1','-M4096'],global_option_overrides=[],scope=scope,execution_tail_unchanged_except_census=True,extra_parent_checks='Pin each exact raw log and compare recorded output; require no interruption.',supplied_execution=False),indent=2)+'\n')
print(json.dumps(dict(guard=d(out),boundary=d(bp)),indent=2))
