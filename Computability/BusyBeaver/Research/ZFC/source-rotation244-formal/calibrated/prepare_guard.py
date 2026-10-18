#!/usr/bin/env python3
"""Own static provider selection and guard text adaptation; no proof execution."""
from pathlib import Path
import ast,difflib,hashlib,json,re
B=Path('/tmp/zfc243-calibrated-source');T=Path('/tmp/zfc243-source-bridge/check-v2.py')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
d=lambda p:dict(path=str(p),sha256=sha(p))
assert sha(T)=='52ffd28ccd3eedf2560bd60e4cd36470aef78d22fdcac52ae90789969403f87b'
ps={
 'source_bridge':('/tmp/zfc243-source-bridge/run2/verification.json','cfdc9eda5d94383b6c2dd526a9a5f766bf7a97d7d47a1e30675055f7644dd701',9,10,'modern','path'),
 'calibration_pool':('/tmp/zfc-routing245-endpoint-actual/run2/verification.json','41ff9364f37d9eb33ff1eb2b4bbc0e5f17f0a44ac02a4a7dcdbdfa6c5b1ccf87',11,11,'legacy_output','actual_first_resolved')}
parents={};pool={};toolpool={};compiler=None;tracked={}
def pin(p,h):
 p=Path(p).resolve();assert str(p)not in tracked or tracked[str(p)]==h
 if str(p)not in tracked:assert sha(p)==h,p;tracked[str(p)]=h
for key,(path,h,np,nc,logs,capmode)in ps.items():
 p=Path(path);pin(p,h);r=json.loads(p.read_text())
 assert r['status']=='PASS'and (r['named_axiom_probes'],r['callers'])==(np,nc)and r['before']==r['after']
 for pp,hh in r['before'].items():pin(pp,hh)
 for role in ['source','audit']:pin(r[role]['snapshot'],r[role]['sha256'])
 for c in r['commands']:
  assert c['exit_code']==0 and not c['timed_out'];pin(c['log'],hashlib.sha256(c['output'].encode()).hexdigest())
  if logs=='modern':assert c['interrupted']is None and c['log_sha256']==sha(c['log'])
  else:assert 'interrupted'not in c and 'log_sha256'not in c
 names=re.findall(r'^#print axioms (\S+)$',Path(r['audit']['snapshot']).read_text(),re.M)
 raw=re.findall(r"^'([^\n]+)'[ \t]+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",r['commands'][1]['output'],re.M)
 assert [n for n,_ in raw]==names and len(names)==np
 f,=r['fresh_modules'];assert r['source_pass_object']==dict(f,source_command_index=0)
 cap=r['fresh_first_provider_before_audit'];cp=cap['path']if capmode=='path'else cap['actual_first']
 assert Path(cp).resolve()==Path(f['path']).resolve()and cap['sha256']==f['sha256'];pin(f['path'],f['sha256'])
 if capmode=='actual_first_resolved':assert Path(cap['resolved']).resolve()==Path(f['path']).resolve()
 for q in r['reused_modules']+[dict(module=f['module'],source=r['source']['path'],source_sha256=f['source_sha256'],object=f['path'],object_sha256=f['sha256'])]:
  row={k:q[k]for k in ['module','source','source_sha256','object','object_sha256']}
  for k in ['source','object']:pin(q[k],q[k+'_sha256'])
  assert q['module']not in pool or pool[q['module']]==row;pool[q['module']]=row
 for q in r['toolchain_providers']:
  row={k:q[k]for k in ['module','object','object_sha256']}
  assert q['module']not in toolpool or toolpool[q['module']]==row;toolpool[q['module']]=row
 assert compiler is None or compiler==r['compiler'];compiler=r['compiler']
 actualtools=sorted({q['module']for q in r['actual_first_providers']}-{q['module']for q in r['reused_modules']})
 parents[key]=dict(path=path,sha256=h,probes=np,callers=nc,audit_names=names,report_names=names,tools=sorted(q['module']for q in r['toolchain_providers']),raw_log_schema=logs,first_capture_schema=capmode,actual_tool_names=actualtools)
S=B/'CalibratedRotation244.lean';A=B/'Audit.lean';imps=lambda p:re.findall(r'^import\s+([A-Za-z_][A-Za-z_0-9.]*)\s*$',Path(p).read_text(),re.M)
assert sha(S)=='73dcce68c6caa8823f72741455e191f03ebbf092feb173d2dcd78b8f30a3caec'
assert sha(A)=='d009f2de2cbf5b906d9bc8d036e2c89144ce7e0011f86f736cc8a7e53d47dc34'
seen=set();selectedtools={'Init'}
def visit(m):
 if m=='Init'or m.startswith(('Lean.','Std.')):selectedtools.add(m);return
 assert m in pool,m
 if m in seen:return
 seen.add(m)
 for n in imps(pool[m]['source']):visit(n)
for m in imps(S):visit(m)
assert len(seen)==198 and selectedtools=={'Init'}
assert not any(m.startswith(('BusyBeaver.ZFC.SitesRouting245','BusyBeaver.ZFC.RuntimeInstanceRouting245','BusyBeaver.ZFC.BootRouting245','BusyBeaver.ZFC.BootstrapFrameRouting245'))for m in seen)
probes=[n.rsplit('.',1)[1]for n in re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)]
assert len(probes)==7 and len(re.findall(r'^example\b',A.read_text(),re.M))==9
scope='External calibration of the exact rotated logical register program from LogicalSeed246.initial to native/ZF/ZFC refutation and nonhalting/consistency. Selected198 cached project pairs exclude binary runtime, site coverage and concrete blank startup. No binary-machine endpoint or internal PA claim.'
static=[Path(__file__),T,B/'source-inventory.json',B/'prospective-closure.json']
bound=dict(parents=parents,compiler=compiler,reused_modules=[pool[m]for m in sorted(seen)],toolchain_providers=[toolpool[m]for m in sorted(selectedtools)],scope=scope,static_inputs=[d(p)for p in static],candidate_provider_count=len(pool),excluded_candidate_modules=sorted(set(pool)-seen),selection_policy='Exact import DFS from the three declared logical imports; parent records are provenance pools, not automatic imported modules.')
bp=B/'boundary.json';assert not bp.exists();bp.write_text(json.dumps(bound,indent=2)+'\n')
old=T.read_text();g=old
changes=[
 ('Concrete logical source rotation; exact three parents/eight projects.','Calibrated rotated register program; two actual parents and selected198 projects.'),
 ("HERE=Path('/tmp/zfc243-source-bridge')",f'HERE=Path({str(B)!r})'),
 ("MODULE='BusyBeaver.ZFC.SourceRotation244'","MODULE='BusyBeaver.ZFC.CalibratedRotation244'"),
 ("PREFIX='SetTheory.BusyBeaver.ZFC.SourceRotation244.'","PREFIX='SetTheory.BusyBeaver.ZFC.CalibratedRotation244.'"),
 (re.search(r'^PROBES=.*$',g,re.M)[0],'PROBES='+repr(probes)),
 (re.search(r'^SOURCE_SHA=.*$',g,re.M)[0],'SOURCE_SHA='+repr(sha(S))),
 (re.search(r'^AUDIT_SHA=.*$',g,re.M)[0],'AUDIT_SHA='+repr(sha(A))),
 (re.search(r'^BOUNDARY_SHA=.*$',g,re.M)[0],'BOUNDARY_SHA='+repr(sha(bp))),
 (re.search(r'^PARENT_SHAS=.*$',g,re.M)[0],'PARENT_SHAS='+repr({k:v[1]for k,v in ps.items()})),
 ("default=HERE/'source-v2/SourceRotation244.lean'","default=HERE/'CalibratedRotation244.lean'"),
 ("default=HERE/'boundary-v2.json'","default=HERE/'boundary.json'"),
 ("            require(c['interrupted'] is None and c['log_sha256']==hashlib.sha256(c['output'].encode()).hexdigest(),'Parent raw log binding.')\n            pin(c['log'],c['log_sha256'])", "            log_hash=hashlib.sha256(c['output'].encode()).hexdigest()\n            if desc['raw_log_schema']=='modern':require(c['interrupted'] is None and c['log_sha256']==log_hash,'Modern parent raw log binding.')\n            else:require(desc['raw_log_schema']=='legacy_output' and 'interrupted' not in c and 'log_sha256' not in c,'Unexpected historical raw log schema.')\n            pin(c['log'],log_hash)"),
 ("cap=e['fresh_first_provider_before_audit'];require(cap['module']==f['module']and Path(cap['path']).resolve()==Path(f['path']).resolve()and cap['sha256']==f['sha256'],'Fresh parent first mismatch.');pin(f['path'],f['sha256'])", "cap=e['fresh_first_provider_before_audit']\n        if desc['first_capture_schema']=='path':cap_path=cap['path']\n        else:\n            require(desc['first_capture_schema']=='actual_first_resolved' and Path(cap['actual_first']).resolve()==Path(cap['resolved']).resolve(),'Historical fresh first schema.')\n            cap_path=cap['actual_first']\n        require(cap['module']==f['module']and Path(cap_path).resolve()==Path(f['path']).resolve()and cap['sha256']==f['sha256'],'Fresh parent first mismatch.');pin(f['path'],f['sha256'])\n        actual_names=[q['module']for q in e['actual_first_providers']]\n        require(len(actual_names)==len(set(actual_names)) and set(actual_names)=={q['module']for q in e['reused_modules']}|set(desc['actual_tool_names']),'Unexpected parent first-provider selection.')"),
 ("require(projects==pool and len(pool)==8 and {q['module']:q for q in tools}==alltools and set(alltools)=={'Init'},'Wrong eight-project/Init union.')", "require(len(projects)==198 and all(m in pool and q==pool[m] for m,q in projects.items()),'Wrong selected198-project pairs.')\n    require(len(pool)==b['candidate_provider_count'] and sorted(set(pool)-set(projects))==b['excluded_candidate_modules'],'Changed parent-pool selection.')\n    require({q['module']:q for q in tools}=={'Init':alltools['Init']},'Wrong selected Init boundary.')"),
 ("imports(S)==['BusyBeaver.ZFC.ProgramRotation244', 'BusyBeaver.ZFC.RMDagLoopRotation', 'BusyBeaver.ZFC.RMDagContextSubstitution']",'imports(S)=='+repr(imps(S))),
 ("len(re.findall(r'^example\\b',A.read_text(),re.M))==10,'Wrong audit9/10.'", "len(re.findall(r'^example\\b',A.read_text(),re.M))==9,'Wrong audit7/9.'"),
 (re.search(r"scope='Exact three actual source-level parents;[^']*'",g)[0],'scope='+repr(scope)),
 ('exact_project_prerequisite_count=8','exact_project_prerequisite_count=198'),
 ('named_axiom_probes=9,callers=10','named_axiom_probes=7,callers=9')]
for a,z in changes:
 assert g.count(a)==1,(a,g.count(a));g=g.replace(a,z)
ast.parse(g);out=B/'check.py';assert not out.exists();out.write_text(g)
(B/'guard-from-source-bridge.diff').write_text(''.join(difflib.unified_diff(old.splitlines(True),g.splitlines(True),fromfile=str(T),tofile=str(out))))
(B/'guard-proposal.json').write_text(json.dumps(dict(status='SOURCE_ONLY_UNEXECUTED',source=d(S),audit=d(A),guard=d(out),boundary=d(bp),template=d(T),parents=parents,selected_projects=198,excluded_candidate_projects=len(pool)-198,tools=['Init'],probes=7,callers=9,shared_seconds=120,limits='-j1 -M4096; default proof limits',scope=scope,execution_tail_unchanged_except_census=True,metadata_schema_adaptations=['Exact historical log-output hash rather than nonexistent log_sha256/interrupted fields.','Binary historical first capture uses actual_first and resolved; both identify the recorded object.','Explicit parent actual tool lists; strict subset import DFS rather than entire provenance pool.'],supplied_execution=False),indent=2)+'\n')
assert all(sha(pp)==h for pp,h in tracked.items())
print(json.dumps(dict(source=d(S),audit=d(A),guard=d(out),boundary=d(bp),selected_projects=198,excluded=len(pool)-198),indent=2))
