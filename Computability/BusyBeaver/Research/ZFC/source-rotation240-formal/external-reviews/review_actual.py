#!/usr/bin/env python3
"""Independent reading of existing actual evidence only; no guard or Lean invocation."""
from pathlib import Path
import hashlib,json,re
H=Path(__file__).resolve().parent;B=Path('/tmp/zfc-source-rotation240')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def d(p):return dict(path=str(Path(p).resolve()),sha256=sha(p))
def load(p):return json.loads(Path(p).read_text())
checks=0;inputs={}
def need(x,msg):
 global checks
 checks+=1
 if not x:raise AssertionError(msg)
def pin(p,h):
 p=Path(p).resolve();need(sha(p)==h,'Changed '+str(p));need(str(p)not in inputs or inputs[str(p)]==h,'Conflict');inputs[str(p)]=h
V=B/'run1/verification.json';P=B/'prepared1/verification.json'
pin(V,'aa9d314ede4bb61c5f1962a2390bd6e3d064ab4778597914458e977aded24c7c');r=load(V);p=load(P)
need(r['status']=='PASS'and r['prepare_only']is False and(r['named_axiom_probes'],r['callers'],r['warnings'])==(10,13,0),'Actual complete result')
need(r['before']==r['after']and r['all_input_provider_postchecks']and r['all_fresh_objects_unchanged_after_audit']and r['only_standard_axioms'],'Actual postchecks')
for path,h in r['before'].items():pin(path,h)
need(len(r['before'])==92 and r['shared_timeout_seconds']==120 and r['memory_mebibytes']==4096 and r['LEAN_NUM_THREADS']=='1'and r['global_option_overrides']==[],'Inputs/default limits')
need(not any(r[k]for k in ['compiler_version_query_performed','dependency_build','downloads']),'Execution scope')
for field,h in [('source','bbda8dae8ce42e890b8ad6bd8b22bf62275f0ae0114f8d2350ac558a2e5ac21b'),('audit','1d917d7c124b0349b933051369726959ff0aa8f69f2a51fcdca13825ff3905f7')]:
 need(r[field]['sha256']==h,'Exact selected proof');pin(r[field]['path'],h);pin(r[field]['snapshot'],h)
need([c['label']for c in r['commands']]==['source','audit'],'Command order')
for i,c in enumerate(r['commands']):
 need(c['exit_code']==0 and not c['timed_out']and c['interrupted']is None,'Actual command success')
 pin(c['log'],c['log_sha256']);need(Path(c['log']).read_text()==c['output'],'Raw log identity')
 need(c['command'][:3]==[r['compiler']['path'],'-j1','-M4096']and c['command'][-1]==r[['source','audit'][i]]['snapshot'],'Exact compiler selection')
need(sum(c['seconds']for c in r['commands'])<120 and sum(c['output'].count('warning:')for c in r['commands'])==0,'Deadline/warnings')
raw=re.findall(r"^'([^\n]+)'[ \t]+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",r['commands'][1]['output'],re.M)
rr=[dict(name=n,axioms=sorted({v.strip()for v in a.split(',')if v.strip()}))for n,a in raw]
need(rr==r['axiom_reports']and len(rr)==10 and all(set(q['axioms'])<={'propext','Classical.choice','Quot.sound'}for q in rr),'Raw axiom reports')
A=Path(r['audit']['path']);need(re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==[q['name']for q in rr]and len(re.findall(r'^example\b',A.read_text(),re.M))==13,'Typed audit census')
f=r['fresh_modules'];need(len(f)==1,'One fresh module');f=f[0];pin(f['path'],f['sha256'])
need(f['module']=='BusyBeaver.ZFC.SourceRotation240'and f['source_sha256']==r['source']['sha256'],'Fresh source binding')
need(r['source_object_recorded_before_audit']and r['source_pass_object']==dict(f,source_command_index=0)and r['fresh_first_provider_before_audit']=={k:f[k]for k in ['module','path','sha256']},'Pre-audit first/source captures')
projects={q['module']:q for q in r['reused_modules']};tools={q['module']:q for q in r['toolchain_providers']};first={q['module']:q for q in r['actual_first_providers']}
need(len(projects)==r['exact_project_prerequisite_count']==9 and set(tools)=={'Init'}and set(first)==set(projects)|set(tools),'Exact provider census')
for q in list(projects.values())+list(tools.values()):
 for field in (['object']if q['module']in tools else['source','object']):
  path=Path(q[field]).resolve();pin(path,q[field+'_sha256']);need(r['before'].get(str(path))==r['after'].get(str(path))==q[field+'_sha256'],'Bound current provider')
 need(Path(first[q['module']]['actual_first']).resolve()==Path(q['object']).resolve()and first[q['module']]['sha256']==q['object_sha256'],'Current first provider')
imp=lambda path:re.findall(r'^import\s+([A-Za-z_][A-Za-z_0-9.]*)\s*$',Path(path).read_text(),re.M)
seen=set()
def visit(m):
 if m=='Init':return
 need(m in projects,'Unselected import')
 if m in seen:return
 seen.add(m)
 for child in imp(projects[m]['source']):visit(child)
for m in imp(r['source']['path']):visit(m)
need(seen==set(projects)and sorted(seen)==r['exact_project_import_closure'],'Source-derived closure')
pin(P,sha(P));need(p['status']=='PREPARED_NOT_BUILT'and p['prepare_only']is True and p['commands']==p['fresh_modules']==[]and p['before']==p['after']and p['all_input_provider_postchecks'],'Preparation record')
for path,h in p['before'].items():pin(path,h)
for field in ['reused_modules','toolchain_providers','actual_first_providers','boundary']:need(p[field]==r[field],'Preparation selection matches actual')
pin(B/'check.py','163d9ba03ee5b6bf0edff594eb73c4a205d7d71561059cad60a2ad1807028e1e');need(r['before'][str(B/'check.py')]==sha(B/'check.py'),'Executed guard binding')
need(r['provider_evidence']==[dict(path='/tmp/zfc243-source-bridge/run2/verification.json',sha256='cfdc9eda5d94383b6c2dd526a9a5f766bf7a97d7d47a1e30675055f7644dd701',module='BusyBeaver.ZFC.SourceRotation244')],'Actual parent')
need(all(sha(path)==h for path,h in inputs.items()),'Stable inputs')
receipt=dict(status='EXISTING_ACTUAL_EVIDENCE_REVIEW_PASS',findings=[],checks=checks,verification=d(V),source=d(r['source']['path']),audit=d(r['audit']['path']),guard=d(B/'check.py'),boundary=d(B/'boundary.json'),preparation=d(P),fresh_module=f,reviewer_source=d(Path(__file__)),reviewer_role='Independent current evidence reader; authored the historical SourceRotation244 predecessor, not this source or current guard. Full current source/audit read; source mathematical peer remains separately attributed.',probes=10,callers=13,warnings=0,projects=9,tools=['Init'],current_inputs=inputs,scope='Arbitrary-register logical halting equivalence of the row169 rotation only. No binary/runtime/startup/complete240 consistency or internal PA claim. No full ancestor replay.',proof_execution=False)
(H/'actual-review.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(dict(checks=checks,review=d(H/'actual-review.json')),indent=2))
