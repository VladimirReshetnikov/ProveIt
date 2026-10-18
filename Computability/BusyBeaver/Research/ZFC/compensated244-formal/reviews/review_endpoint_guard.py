#!/usr/bin/env python3
"""Own AST/hash/DFS review only; never imports or executes supplied guard code."""
from pathlib import Path
import ast,json,hashlib,re
B=Path('/tmp/zfc244-endpoint');O=Path(__file__).parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();d=lambda p:dict(path=str(p),sha256=sha(p));load=lambda p:json.loads(Path(p).read_text())
checks=[]
def check(x,s):
 assert x,s
 checks.append(s)
guard=B/'check.py';text=guard.read_text();tree=ast.parse(text)
cfg=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='CFG' for t in n.targets))
check(cfg==load(B/'guard-config.json'),'exact embedded configuration')
old=Path('/tmp/zfc-routing245-endpoint-actual/check-audit-v2.py').read_text()
check(text[text.index(' save()\n try:'):]==old[old.index(' save()\n try:'):],'actual source/audit execution tail byte identical')
check(sha(cfg['source'])==cfg['source_sha256'] and sha(cfg['audit'])==cfg['audit_sha256'],'source/audit frozen pins')
check(re.findall(r'^import (\S+)$',Path(cfg['source']).read_text(),re.M)==cfg['imports'],'exact two direct imports')
check(len(cfg['probes'])==cfg['callers']==6,'six probes/six typed clients')
check(len(re.findall(r'^example\b',Path(cfg['audit']).read_text(),re.M))==6,'typed examples')
pool={};inputs={};parents=[];toolunion={}
for label,e in cfg['parents'].items():
 check(sha(e['path'])==e['sha256'],'parent pin '+label);r=load(e['path']);parents.append(d(e['path']))
 check(r['status']=='PASS' and r['before']==r['after'] and r['all_input_provider_postchecks'] and r['only_standard_axioms'],'parent status '+label)
 check((r['named_axiom_probes'],r['callers'])==(e['probes'],e['callers']),'parent census '+label)
 for p,h in r['before'].items():
  check(sha(p)==h,'parent current '+p)
  check(p not in inputs or inputs[p]==h,'parent common input identity '+p);inputs[p]=h
 pf=r['fresh_modules'][0]
 check(pf['module']==e['module'] and sha(pf['path'])==pf['sha256'],'parent fresh object '+label)
 check(r['source_pass_object']==dict(pf,source_command_index=0),'parent preaudit object '+label)
 cap=r['fresh_first_provider_before_audit'];path=cap.get('actual_first',cap.get('path'))
 check(Path(path).resolve()==Path(pf['path']).resolve() and cap['sha256']==pf['sha256'],'parent preaudit first '+label)
 for c in r['commands']:check(c['exit_code']==0 and not c['timed_out'] and Path(c['log']).read_text()==c['output'],'parent raw log '+label+' '+c['label'])
 reports=re.findall(r"^'([^\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",r['commands'][1]['output'],re.M)
 check([n for n,_ in reports]==re.findall(r'^#print axioms (\S+)$',Path(r['audit']['snapshot']).read_text(),re.M),'parent raw names '+label)
 actual={q['module']:q for q in r['actual_first_providers']};projects={q['module'] for q in r['reused_modules']}
 check(set(actual)==projects|set(e['actual_tool_names']),'explicit parent project/tool census '+label)
 for q in r['reused_modules']+[dict(module=pf['module'],source=r['source']['path'],source_sha256=pf['source_sha256'],object=pf['path'],object_sha256=pf['sha256'])]:
  name=q['module'];row={k:q[k] for k in ['module','source','source_sha256','object','object_sha256']}
  for k in ['source','object']:check(sha(q[k])==q[k+'_sha256'],'selected current '+k+' '+name)
  if name in pool:check((pool[name]['source_sha256'],pool[name]['object_sha256'])==(row['source_sha256'],row['object_sha256']),'same-name union '+name)
  else:pool[name]=row
 for t in r['toolchain_providers']:
  check(sha(t['object'])==t['object_sha256'],'tool current '+t['module'])
  if t['module'] in e['actual_tool_names']:
   z=actual[t['module']];check(Path(z.get('actual_first',z.get('path'))).resolve()==Path(t['object']).resolve() and z['sha256']==t['object_sha256'],'extra actual tool '+t['module'])
  if t['module'] in toolunion:check(toolunion[t['module']]==t['object_sha256'],'same tool union')
  toolunion[t['module']]=t['object_sha256']
seen=set();tools={'Init'}
def visit(m):
 if m in toolunion:tools.add(m);return
 check(m in pool,'DFS provider exists '+m)
 if m in seen:return
 seen.add(m)
 for n in re.findall(r'^import\s+(\S+)\s*$',Path(pool[m]['source']).read_text(),re.M):visit(n)
for m in cfg['imports']:visit(m)
check(seen==set(cfg['expected_modules'])==set(pool) and len(seen)==857,'exact857 imported parent union')
check(tools==set(toolunion)=={'Init','Lean.Elab.Tactic.Omega'},'exact Init/Omega boundary')
pre=B/'prepared1/verification.json';r=load(pre)
check(r['status']=='PREPARED_NOT_BUILT' and r['prepare_only'] and r['commands']==r['fresh_modules']==[],'prepared only no proof commands')
check(not r['source_overridden'] and not r['audit_overridden'],'default source/audit selected')
check(r['before']==r['after'] and r['all_input_provider_postchecks'],'prepared postchecks')
for p,h in r['before'].items():check(sha(p)==h,'prepared current '+p)
check(r['project_module_count']==857 and r['exact_project_import_closure'] and len(r['reused_modules'])==857,'prepared closure')
for q in r['reused_modules']:check({k:q[k] for k in pool[q['module']]}==pool[q['module']],'prepared selected row '+q['module'])
check(r['limits']==dict(threads=1,memory_mebibytes=4096,shared_wall_seconds=120,proof_limits='Lean defaults'),'prepared limits')
check(not any(r[k] for k in ['compiler_version_query_performed','dependency_build','downloads']),'no version/build/download')
for k in ['source','audit']:check(sha(r[k]['path'])==sha(r[k]['snapshot'])==r[k]['sha256'],'prepared snapshot '+k)
for q in r['actual_first_providers']:check(sha(q['actual_first'])==q['sha256'] and Path(q['actual_first']).resolve()==Path(pool[q['module']]['object']).resolve(),'prepared first '+q['module'])
receipt=dict(status='ENDPOINT_SOURCE_GUARD_AND_PREPARATION_REVIEW_PASS',findings=[],reviewer_source=d(__file__),reviewer_role='Independent endpoint source/audit/guard reviewer; author of separate local-invariant prerequisite, not endpoint or guard/execution.',source=d(cfg['source']),audit=d(cfg['audit']),guard=d(guard),configuration=d(B/'guard-config.json'),preparation=d(pre),parent_records=parents,counts=dict(projects=857,tools=2,probes=6,callers=6,parent_unique_before_inputs=len(inputs),prepared_inputs=len(r['before']),proof_commands=0),execution_tail='Byte-identical to successful original BinaryRouting245 guard, aside from configuration used by the inherited generic code.',scope=cfg['scope'],prior_audit_repair_review=d(O/'endpoint-audit-repair-review.json'),supplied_execution=False,check_count=len(checks),checks=checks)
p=O/'endpoint-guard-preparation-review.json';p.write_text(json.dumps(receipt,indent=2)+'\n');print(d(p));print(receipt['counts'])
