#!/usr/bin/env python3
"""Own metadata-only guard writer. Never invokes a supplied helper or compiler."""
from pathlib import Path
import ast, difflib, hashlib, json, re
B=Path(__file__).parent
T=Path('/tmp/zfc243-source-bridge/check-v2.py')
P=Path('/tmp/zfc243-source-bridge/run2/verification.json')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
desc=lambda p:dict(path=str(p),sha256=sha(p))
count=0
def ck(x,label):
 global count
 count+=1
 if not x:raise AssertionError(label)
def pin(p,h):ck(sha(p)==h,('pin',str(p)))
def replace_once(s,a,b):
 ck(s.count(a)==1,('single replacement',a[:70]));return s.replace(a,b,1)
for n in ('check.py','boundary.json','guard-proposal.json','guard-from-source244.diff'):
 ck(not (B/n).exists(),('new output',n))
pin(P,'cfdc9eda5d94383b6c2dd526a9a5f766bf7a97d7d47a1e30675055f7644dd701')
e=json.loads(P.read_text());plan=json.loads((B/'provider-plan.json').read_text())
iv=json.loads((B/'source-inventory.json').read_text())
pin(T,e['before'][str(T)])
for name,h in e['before'].items():pin(name,h)
ck(e['before']==e['after'] and e['status']=='PASS' and not e['prepare_only'],'actual parent complete')
for field in ('source','audit'):
 pin(e[field]['path'],e[field]['sha256']);pin(e[field]['snapshot'],e[field]['sha256'])
for c in e['commands']:
 pin(c['log'],c['log_sha256']);ck(Path(c['log']).read_text()==c['output'],'raw parent log')
ck(e['warnings']==0 and e['named_axiom_probes']==9 and e['callers']==10,'parent census')
ck(e['source_object_recorded_before_audit'] and e['source_pass_object']['source_command_index']==0,'source capture')
f=e['fresh_modules'][0]
ck(all(e['source_pass_object'][k]==f[k] for k in ('module','path','sha256','source_sha256')),'source capture exact')
cap=e['fresh_first_provider_before_audit']
ck(cap['module']==f['module'] and cap['path']==f['path'] and cap['sha256']==f['sha256'],'fresh first capture')
pin(f['path'],f['sha256'])
pool=e['reused_modules']+[dict(module=f['module'],source=e['source']['path'],source_sha256=f['source_sha256'],object=f['path'],object_sha256=f['sha256'])]
ck(pool==plan['providers'] and len(pool)==9,'exact nine selected pairs')
for p in pool:
 pin(p['source'],p['source_sha256']);pin(p['object'],p['object_sha256'])
for p in e['toolchain_providers']:pin(p['object'],p['object_sha256'])
for field in ('source','audit'):pin(iv[field]['path'],iv[field]['sha256'])
names=plan['probe_names'];parent_names=re.findall(r'^#print axioms (\S+)$',Path(e['audit']['snapshot']).read_text(),re.M)
scope='Exact actual SourceRotation244 run2 parent; nine selected project pairs and Init. Arbitrary-register source equivalence for the shared row169 rotation only. No binary runtime, startup, complete240-state consistency endpoint or internal PA claim. Historical ancestor cache provenance remains inherited.'
parent=dict(path=str(P),sha256=sha(P),module=f['module'],source_sha256=e['source']['sha256'],audit_sha256=e['audit']['sha256'],probes=9,callers=10,audit_names=parent_names,report_names=parent_names,tools=['Init'])
static=[desc(p) for p in (T,B/'source-inventory.json',B/'provider-plan.json',B/'prepare_inventory.py',B/'inventory-correction.json',Path(__file__),Path('/tmp/zfc240-reflection-review/review.json'),Path('/tmp/zfc240-reflection-review/static-review.json'))]
boundary=dict(status='SOURCE_ONLY_ACTUAL_PARENT_BOUND_NOT_EXECUTED',parents={'source':parent},compiler=e['compiler'],reused_modules=pool,toolchain_providers=e['toolchain_providers'],scope=scope,static_inputs=static)
bt=json.dumps(boundary,indent=2)+'\n';bh=hashlib.sha256(bt.encode()).hexdigest()
s=T.read_text()
replacements=[
 ('"""Concrete logical source rotation; exact three parents/eight projects."""','"""Second logical source rotation; exact actual source parent/nine projects."""'),
 ("HERE=Path('/tmp/zfc243-source-bridge')","HERE=Path('/tmp/zfc-source-rotation240')"),
 ("MODULE='BusyBeaver.ZFC.SourceRotation244'","MODULE='BusyBeaver.ZFC.SourceRotation240'"),
 ("PREFIX='SetTheory.BusyBeaver.ZFC.SourceRotation244.'","PREFIX='SetTheory.BusyBeaver.ZFC.SourceRotation240.'"),
 (next(x for x in s.splitlines() if x.startswith('PROBES=')),'PROBES='+repr([n.rsplit('.',1)[1] for n in names])),
 (next(x for x in s.splitlines() if x.startswith('SOURCE_SHA=')),'SOURCE_SHA='+repr(iv['source']['sha256'])),
 (next(x for x in s.splitlines() if x.startswith('AUDIT_SHA=')),'AUDIT_SHA='+repr(iv['audit']['sha256'])),
 (next(x for x in s.splitlines() if x.startswith('BOUNDARY_SHA=')),'BOUNDARY_SHA='+repr(bh)),
 (next(x for x in s.splitlines() if x.startswith('PARENT_SHAS=')),'PARENT_SHAS='+repr({'source':sha(P)})),
 ("default=HERE/'source-v2/SourceRotation244.lean'","default=HERE/'SourceRotation240.lean'"),
 ("default=HERE/'boundary-v2.json'","default=HERE/'boundary.json'"),
 ("    for key,desc in b['parents'].items():","    require(set(b['parents'])==set(PARENT_SHAS),'Missing or extra actual parents.')\n    for key,desc in b['parents'].items():"),
 ("require(e['status']=='PASS'and(e['named_axiom_probes'],e['callers'])==(desc['probes'],desc['callers']),'Wrong parent outcome.')","require(e['status']=='PASS'and e['prepare_only'] is False and(e['named_axiom_probes'],e['callers'])==(desc['probes'],desc['callers']),'Wrong actual parent outcome.')\n        require(e['shared_timeout_seconds']==120 and e['memory_mebibytes']==4096 and e['LEAN_NUM_THREADS']=='1'and e['global_option_overrides']==[]and not e['compiler_version_query_performed']and not e['dependency_build']and not e['downloads'],'Parent policy differs.')"),
 ("        for k in ['source','audit']:pin(e[k]['snapshot'],e[k]['sha256'])","        for k in ['source','audit']:\n            require(e[k]['sha256']==desc[k+'_sha256'],'Parent source/audit binding differs.')\n            pin(e[k]['path'],e[k]['sha256']);pin(e[k]['snapshot'],e[k]['sha256'])\n        require(e['warnings']==sum(c['output'].count('warning:')for c in e['commands'])==0,'Parent warning census differs.')\n        require(all(c['command'][:3]==[str(C),'-j1','-M4096']for c in e['commands']),'Parent command policy differs.')"),
 ("require(desc['report_names']==ns,'Unexpected parent namespace.')","require(desc['report_names']==ns and rr==e['axiom_reports'],'Unexpected parent namespace/reports.')"),
 ("fs=e['fresh_modules'];require(len(fs)==1,'Wrong parent fresh count.');f=fs[0]","fs=e['fresh_modules'];require(len(fs)==1 and fs[0]['module']==desc['module'],'Wrong parent fresh module.');f=fs[0]"),
 ("            require(pp==C.parent.parent/'lib/lean'/rel(q['module']),'Tool reference mismatch.')","            require(pp==C.parent.parent/'lib/lean'/rel(q['module']),'Tool reference mismatch.')\n            require(e['before'].get(str(pp))==e['after'].get(str(pp))==q['object_sha256'],'Missing parent tool input.')\n            actual=next(x for x in e['actual_first_providers']if x['module']==q['module'])\n            require(Path(actual['actual_first']).resolve()==pp and actual['sha256']==q['object_sha256'],'Wrong historical tool provider.')"),
 ("len(pool)==8","len(pool)==9"),
 ("'Wrong eight-project/Init union.'","'Wrong nine-project/Init union.'"),
 ("imports(S)==['BusyBeaver.ZFC.ProgramRotation244', 'BusyBeaver.ZFC.RMDagLoopRotation', 'BusyBeaver.ZFC.RMDagContextSubstitution']","imports(S)==['BusyBeaver.ZFC.SourceRotation244']"),
 ("==10,'Wrong audit9/10.'","==13,'Wrong audit10/13.'"),
 ("scope='Exact three actual source-level parents; eight selected project pairs and Init. Concrete arbitrary-register logical halting equivalence only; no binary runtime, blank bootstrap, ZF calibration or internal PA claim.'","scope="+repr(scope)),
 ("exact_project_prerequisite_count=8","exact_project_prerequisite_count=9"),
 ("named_axiom_probes=9,callers=10","named_axiom_probes=10,callers=13")]
for old,new in replacements:s=replace_once(s,old,new)
ast.parse(s)
def function(text,name):return next(n for n in ast.walk(ast.parse(text)) if isinstance(n,ast.FunctionDef) and n.name==name)
for name in ('run','post','first','providers'):
 ck(ast.dump(function(s,name),include_attributes=False)==ast.dump(function(T.read_text(),name),include_attributes=False),('unchanged execution helper',name))
ck("deadline=time.monotonic()+120" in s and "obj.parent.mkdir(parents=True,exist_ok=True)" in s,'bounded pair and explicit target dir')
for name,h in e['before'].items():pin(name,h)
(B/'boundary.json').write_text(bt);(B/'check.py').write_text(s)
(B/'guard-from-source244.diff').write_text(''.join(difflib.unified_diff(T.read_text().splitlines(True),s.splitlines(True),fromfile=str(T),tofile=str(B/'check.py'))))
proposal=dict(status='SOURCE_ONLY_GUARD_NOT_INVOKED',guard=desc(B/'check.py'),boundary=desc(B/'boundary.json'),source=iv['source'],audit=iv['audit'],parent=desc(P),template=desc(T),writer=desc(Path(__file__)),delta=desc(B/'guard-from-source244.diff'),static_checks=count,project_count=9,tool_modules=['Init'],probes=10,callers=13,scope=scope,proof_execution=False,root_prepare_command=['python3','-B',str(B/'check.py'),'--prepare-only','--output','/tmp/zfc-source-rotation240/prepared1'],root_actual_command=['python3','-B',str(B/'check.py'),'--output','/tmp/zfc-source-rotation240/run1'])
(B/'guard-proposal.json').write_text(json.dumps(proposal,indent=2)+'\n')
print(json.dumps({'guard':proposal['guard'],'boundary':proposal['boundary'],'proposal':desc(B/'guard-proposal.json'),'checks':count}))
