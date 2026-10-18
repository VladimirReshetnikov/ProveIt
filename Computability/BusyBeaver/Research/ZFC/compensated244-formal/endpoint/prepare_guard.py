#!/usr/bin/env python3
"""Author-side static endpoint guard emitter. No imports/execution of proof guards."""
from pathlib import Path
import ast,difflib,hashlib,json,re
HERE=Path('/tmp/zfc244-endpoint')
TEMPLATE=Path('/tmp/zfc-routing245-endpoint-actual/check-audit-v2.py')
TEMPLATE_SHA='b237239d138c5e0d3a00e5d8906c6d7bddb655e50e8f79760201a9633be46652'
PARENTS={
 'routing245':dict(path='/tmp/zfc-routing245-endpoint-actual/run2/verification.json',sha256='41ff9364f37d9eb33ff1eb2b4bbc0e5f17f0a44ac02a4a7dcdbdfa6c5b1ccf87',module='BusyBeaver.ZFC.BinaryRouting245',probes=11,callers=11,actual_tool_names=[]),
 'simulation':dict(path='/tmp/zfc244-compensated-lean/simulation/run1/verification.json',sha256='c5155b3f1e58812b2e91f8a7e66294fc0650adb3c170ff07923968d9e55783c7',module='BusyBeaver.ZFC.Compensated244Simulation',probes=4,callers=4,actual_tool_names=['Init','Lean.Elab.Tactic.Omega'])}
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
imp=lambda p:re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',Path(p).read_text(),re.M)
def need(x,m):
 if not x:raise RuntimeError(m)
def desc(p):return dict(path=str(p),sha256=sha(p))
need(sha(TEMPLATE)==TEMPLATE_SHA,'Template changed.')
original=TEMPLATE.read_text(); tree=ast.parse(original)
constants={n.targets[0].id:ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and isinstance(n.targets[0],ast.Name) and n.targets[0].id in ('CFG','TOOLS','COMPILER_SHA')}
tools=constants['TOOLS'];pool={};identities={};parent_details=[]
def pin(p,h):
 p=Path(p).resolve();need(str(p)not in identities or identities[str(p)]==h,'Conflicting current path identity: '+str(p))
 if str(p)not in identities:need(sha(p)==h,'Changed current path: '+str(p));identities[str(p)]=h
 return p
def first(q):return Path(q.get('actual_first',q.get('path'))).resolve()
for label,cfg in PARENTS.items():
 p=pin(cfg['path'],cfg['sha256']);d=json.loads(p.read_text())
 need(d['status']=='PASS'and d['prepare_only']is False and d['before']==d['after'] and d['all_input_provider_postchecks'] and d['all_fresh_objects_unchanged_after_audit'] and d['only_standard_axioms'],'Incomplete parent.')
 need((d['named_axiom_probes'],d['callers'])==(cfg['probes'],cfg['callers']),'Wrong parent census.')
 need([q['label']for q in d['commands']]==['source','audit']and all(q['exit_code']==0 and not q['timed_out']for q in d['commands']),'Wrong commands.')
 for q in d['commands']:need(Path(q['log']).read_text()==q['output'],'Raw parent log differs.');pin(q['log'],sha(q['log']))
 for path,h in d['before'].items():pin(path,h)
 for role in ('source','audit'):pin(d[role]['path'],d[role]['sha256']);pin(d[role]['snapshot'],d[role]['sha256'])
 ns=re.findall(r'^#print axioms (\S+)$',Path(d['audit']['snapshot']).read_text(),re.M)
 rr=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",d['commands'][1]['output'],re.S)
 need([n for n,_ in rr]==ns and len(ns)==cfg['probes']and len(re.findall(r'^example\b',Path(d['audit']['snapshot']).read_text(),re.M))==cfg['callers'],'Exact audit mismatch.')
 need(all({a.strip()for a in block.split(',')if a.strip()}<={'propext','Classical.choice','Quot.sound'}for _,block in rr),'Nonstandard axiom.')
 f=d['fresh_modules'];need(len(f)==1 and f[0]['module']==cfg['module'],'Fresh module differs.');f=f[0]
 need(d['source_object_recorded_before_audit']and d['source_pass_object']['source_command_index']==0 and all(d['source_pass_object'][k]==f[k]for k in ('module','path','sha256','source_sha256')),'Pre-audit binding differs.')
 need(first(d['fresh_first_provider_before_audit'])==Path(f['path']).resolve()and d['fresh_first_provider_before_audit']['sha256']==f['sha256'],'Fresh first differs.')
 actual={q['module']:q for q in d['actual_first_providers']};names={q['module']for q in d['reused_modules']}
 need(len(actual)==len(d['actual_first_providers'])and set(actual)==names|set(cfg['actual_tool_names']),'Actual provider schema differs.')
 tt={q['module']:q for q in d['toolchain_providers']};need(set(tt)==set(tools),'Tool names differ.')
 for name,q in tt.items():
  pin(q['object'],tools[name]);need(q['object_sha256']==tools[name],'Tool digest differs.')
  if name in cfg['actual_tool_names']:need(first(actual[name])==Path(q['object']).resolve()and actual[name]['sha256']==tools[name],'Actual tool differs.')
 for q in d['reused_modules']:
  need(first(actual[q['module']])==Path(q['object']).resolve()and actual[q['module']]['sha256']==q['object_sha256'],'Actual project differs.')
 rows=d['reused_modules']+[dict(module=f['module'],source=d['source']['path'],source_sha256=f['source_sha256'],object=f['path'],object_sha256=f['sha256'])]
 for q in rows:
  for role in ('source','object'):pin(q[role],q[role+'_sha256'])
  if q['module']in pool:need(all(pool[q['module']][k]==q[k]for k in ('source_sha256','object_sha256')),'Conflicting module.')
  else:pool[q['module']]=dict(q,parent=label)
 parent_details.append(dict(label=label,verification=desc(p),project_providers=len(names),actual_first_rows=len(actual),actual_tool_names=cfg['actual_tool_names'],fresh=f,raw_audit_names=ns))
S=HERE/'BinaryCompensated244.lean';A=HERE/'Audit.lean';I=imp(S);closure=[];visiting=set();tool_names={'Init'}
def visit(n):
 if n in closure:return
 need(n in pool and n not in visiting,'Missing/cyclic provider '+n);visiting.add(n)
 for c in imp(pool[n]['source']):
  if c=='Init'or c.startswith(('Lean.','Std.')):tool_names.add(c)
  else:visit(c)
 visiting.remove(n);closure.append(n)
for n in I:visit(n)
need(len(closure)==857 and set(closure)==set(pool) and tool_names==set(tools),'Unexpected exact closure.')
probes=re.findall(r'^theorem (\w+)',S.read_text(),re.M);need(len(probes)==6,'Wrong source census.')
need(re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==['SetTheory.BusyBeaver.ZFC.BinaryCompensated244.'+n for n in probes]and len(re.findall(r'^example\b',A.read_text(),re.M))==6,'Wrong audit census.')
cfg=dict(module='BusyBeaver.ZFC.BinaryCompensated244',source=str(S),source_sha256=sha(S),audit=str(A),audit_sha256=sha(A),imports=I,probes=probes,callers=6,parents=PARENTS,expected_modules=sorted(closure),scope='Closed external Lean blank-halting/refutation and nonhalting/consistency equivalences for exact compensated244 and ZF/ZFC, transferred from the checked Routing245 endpoint using a positive-block Core finite-support-tape simulation. No internal PA derivation or unconditional consistency/nonhalting claim.')
oldcfg=next(l for l in original.splitlines()if l.startswith('CFG = '));out=original.replace(oldcfg,'CFG = '+repr(cfg),1)
def replace(a,b):
 global out
 need(out.count(a)==1,'Expected unique adaptation: '+a);out=out.replace(a,b,1)
replace('Exact routing245 composition unit. Pending parents reject all execution.','Exact compensated244 composition unit from two successful actual parents.')
replace("  actuals={q['module']:q for q in d['actual_first_providers']}\n  need(len(actuals)==len(d['actual_first_providers'])==len(d['reused_modules']),'Duplicate/missing parent provider.')", "  actuals={q['module']:q for q in d['actual_first_providers']}\n  project_names={q['module'] for q in d['reused_modules']}\n  extra_tools=set(cfg['actual_tool_names'])\n  need(len(project_names)==len(d['reused_modules']) and\n       len(actuals)==len(d['actual_first_providers']) and\n       set(actuals)==project_names|extra_tools and extra_tools<=set(TOOLS),\n       'Duplicate/missing/unexpected parent provider.')")
replace("  for t in d['toolchain_providers']:\n   need(t['module'] in TOOLS and t['object_sha256']==TOOLS[t['module']],'Parent tool identity differs.')", "  need({t['module'] for t in d['toolchain_providers']}==set(TOOLS) and\n       len(d['toolchain_providers'])==len(TOOLS),'Parent tool census differs.')\n  for t in d['toolchain_providers']:\n   need(t['module'] in TOOLS and t['object_sha256']==TOOLS[t['module']],'Parent tool identity differs.')\n   if t['module'] in extra_tools:\n    actual=actuals[t['module']]\n    need(first_path(actual)==Path(t['object']).resolve() and actual['sha256']==t['object_sha256'],\n         'Parent extra actual tool differs.')")
replace("  fresh=d['fresh_modules'];need(len(fresh)==1 and fresh[0]['module']==cfg['module'],'Wrong fresh parent module.')", "  parent_audit=Path(d['audit']['snapshot'])\n  need([n for n,_ in reports]==re.findall(r'^#print axioms (\\S+)$',parent_audit.read_text(),re.M) and\n       len(re.findall(r'^example\\b',parent_audit.read_text(),re.M))==cfg['callers'],\n       'Raw parent names/typed callers differ from exact audit snapshot.')\n  for command in d['commands']:\n   log=Path(command['log']).resolve()\n   need(log.read_text()==command['output'],'Parent raw log differs.');inputs.append(log)\n  fresh=d['fresh_modules'];need(len(fresh)==1 and fresh[0]['module']==cfg['module'],'Wrong fresh parent module.')")
replace("  need(all(saved[k]==f[k] for k in ('module','path','sha256','source_sha256')) and", "  need(saved['source_command_index']==0 and\n       all(saved[k]==f[k] for k in ('module','path','sha256','source_sha256')) and")
replace(" # Rehash only snapshots of fresh parents actually imported; evidence-only seed\n # reuse selects LogicalSeed246 and its dependencies, never BinaryPrefix246.", " # Rehash exact source/audit snapshots for both directly imported fresh parents.")
ast.parse(out)
need(out[out.index(' def save()'):]==original[original.index(' def save()'):],'Execution/audit tail changed.')
G=HERE/'check.py';need(not G.exists(),'Refuse replacing guard.');G.write_text(out)
(HERE/'guard-from-binary-routing245.diff').write_text(''.join(difflib.unified_diff(original.replace(oldcfg,'CFG = <old exact inputs>').splitlines(True),out.replace('CFG = '+repr(cfg),'CFG = <new exact inputs>').splitlines(True),fromfile=str(TEMPLATE),tofile=str(G))))
(HERE/'guard-config.json').write_text(json.dumps(cfg,indent=2)+'\n')
for path,h in identities.items():need(sha(path)==h,'Changed during static review: '+path)
receipt=dict(status='AUTHOR_STATIC_SOURCE_AND_PROVIDER_REVIEW',findings=[],reviewer_role='Guard adapter and concrete simulation source author; independent endpoint source is root-authored.',source=desc(S),audit=desc(A),guard=desc(G),author_emitter=desc(Path(__file__)),template=desc(TEMPLATE),parent_records=parent_details,project_module_count=len(closure),exact_project_import_closure=closure,selected_providers=[pool[n]for n in closure],toolchain_sha256=tools,current_deduplicated_input_count=len(identities),current_deduplicated_inputs=identities,source_and_audit_census=dict(probes=6,callers=6),execution_tail_byte_identical=True,guard_or_compiler_executed=False,notes=['Both actual parents are PASS with fresh object captures at source command index 0.','The old endpoint records projects only in actual_first_providers; the new simulation additionally records exactly Init/Omega. Both formats are checked explicitly.','An earlier inline metadata print stopped at the optional actual_axiom_sets key absent from the simulation schema; no artifact was emitted or guard invoked by that read.'])
(HERE/'guard-author-static-review.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(dict(guard=desc(G),source=desc(S),audit=desc(A),receipt=desc(HERE/'guard-author-static-review.json'),project_module_count=len(closure),current_inputs=len(identities)),indent=2))
