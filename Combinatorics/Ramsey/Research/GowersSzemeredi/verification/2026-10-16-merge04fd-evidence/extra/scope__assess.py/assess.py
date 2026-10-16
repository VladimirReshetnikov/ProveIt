import json,hashlib,re,runpy,subprocess,sys
from pathlib import Path
from functools import lru_cache
from datetime import datetime,timezone
sys.setrecursionlimit(20000)
R=Path('/home/codex/.codex/worktrees/9c9b/Proofs');O=Path('/tmp/gowers-merge04fd-current-source-scope-assessment');B=Path('/tmp/gowers-merge68ad-native-tools')
parent='cb7319ce84f72719fa92797c689591a29e547d40';incoming='04fd0fb36e46ff05373664236758eff99665bded'
def load(p):return json.loads(Path(p).read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def pin(p):return {'path':str(p),'sha256':h(Path(p).read_bytes())}
def save(n,d):
 with (O/n).open('x') as f:json.dump(d,f,indent=2);f.write('\n')
def git(*args):return subprocess.check_output(['git',*args],cwd=R)
rows=load(B/'source-rows.json');oldgraph=load(B/'fullgraph-imports.json');modes=load(B/'mode-closures.json');plan=load(B/'plan.json')
assert len(rows)==6021 and set(rows)==set(oldgraph)
configured={str(p.relative_to(R)) for root in [R/'Combinatorics/Ramsey/Lean',R/'lib'] for p in root.rglob('*.lean')}
assert configured=={v['path'] for v in rows.values()},(len(configured),len(rows),list(configured-{v['path'] for v in rows.values()})[:5])
head_before=git('rev-parse','HEAD').decode().strip()
# One read-only Git batch retrieves the exact parent source objects.
queries=[parent+':'+rows[m]['path'] for m in rows]
raw=subprocess.check_output(['git','cat-file','--batch'],input=('\n'.join(queries)+'\n').encode(),cwd=R)
parent_bytes={};pos=0
for m in rows:
 end=raw.index(b'\n',pos);head=raw[pos:end].decode().split();assert len(head)==3 and head[1]=='blob',head
 size=int(head[2]);data=raw[end+1:end+1+size];assert len(data)==size and raw[end+1+size:end+2+size]==b'\n'
 parent_bytes[m]=data;pos=end+2+size
assert pos==len(raw)
del raw
P=runpy.run_path('/tmp/gowers-equation-aware-scoped-parser/legacy-parsers.py')
current={m:(R/r['path']).read_bytes() for m,r in rows.items()}
parent_old_mismatches=[m for m in rows if h(parent_bytes[m])!=rows[m]['sha256']];assert not parent_old_mismatches,parent_old_mismatches
changed={m for m in rows if current[m]!=parent_bytes[m]};sourcepins={};change_rows=[];graph={};import_changes=[]
for m,r in rows.items():
 # Unchanged sources inherit the exact pinned graph; every changed source is independently parsed in both states.
 if m in changed:
  before=P['imports'](parent_bytes[m].decode());after=P['imports'](current[m].decode())
  assert before==oldgraph[m],(m,before,oldgraph[m])
  if before!=after:import_changes.append(m)
  graph[m]=after
  change_rows.append({'module':m,'path':r['path'],'parent_sha256':h(parent_bytes[m]),'current_sha256':h(current[m]),'source_before':len(parent_bytes[m].splitlines()),'source_after':len(current[m].splitlines()),'source_delta':len(current[m].splitlines())-len(parent_bytes[m].splitlines()),'imports_before':before,'imports_after':after})
 else:graph[m]=oldgraph[m]
 sourcepins[m]={'path':r['path'],'parent_sha256':h(parent_bytes[m]),'current_sha256':h(current[m]),'source_before':len(parent_bytes[m].splitlines()),'source_after':len(current[m].splitlines())}
assert not import_changes,import_changes
assert graph==oldgraph
local={m:[x for x in deps if x in rows] for m,deps in graph.items()}
visiting=set()
@lru_cache(None)
def closure(m):
 assert m not in visiting,('cycle',m)
 visiting.add(m);res={m}
 for d in local[m]:res.update(closure(d))
 visiting.remove(m);return frozenset(res)
for m in rows:closure(m)
rev={m:set() for m in rows}
for m,ds in local.items():
 for d in ds:rev[d].add(m)
affected=set(changed);todo=list(changed)
while todo:
 m=todo.pop()
 for c in rev[m]:
  if c not in affected:affected.add(c);todo.append(c)
mode_rows={};own_rows=[];selected=set()
for mode,v in modes.items():
 roots=v['roots'];assert roots==plan[mode]['roots']
 union=set().union(*(closure(m) for m in roots));assert union==set(v['modules']),(mode,len(union),len(v['modules']))
 assert len(union)==plan[mode]['module_count']
 selected.update(union)
 mode_rows[mode]={'roots':roots,'root_count':len(roots),'module_count':len(union),'input_count_with_three_config':len(union)+3,'source_before':sum(sourcepins[m]['source_before'] for m in union),'source_after':sum(sourcepins[m]['source_after'] for m in union),'source_delta':sum(sourcepins[m]['source_after']-sourcepins[m]['source_before'] for m in union),'changed_owners':sorted(changed&union),'affected_consumers_covered':len(affected&union)}
 assert mode_rows[mode]['source_before']==plan[mode]['source_lines']
 for root in roots:
  cs=closure(root);own_rows.append({'mode':mode,'root':root,'module_count':len(cs),'source_before':sum(sourcepins[m]['source_before'] for m in cs),'source_after':sum(sourcepins[m]['source_after'] for m in cs),'changed_owners':sorted(changed&cs)})
missing=sorted(affected-selected);facades=['GowersSzemeredi','GowersSzemeredi.Audit','GowersSzemeredi.PortImportAudit']
assert missing==facades,missing
consumers=[]
for m in sorted(affected):
 cs=closure(m);consumers.append({'module':m,'covered':m in selected,'module_count':len(cs),'source_before':sum(sourcepins[x]['source_before'] for x in cs),'source_after':sum(sourcepins[x]['source_after'] for x in cs),'source_delta':sum(sourcepins[x]['source_after']-sourcepins[x]['source_before'] for x in cs),'changed_owners':sorted(changed&cs)})
# Cross-check changed-path list using read-only Git diff and stable second source hash pass.
changed_git={x for x in git('diff','--name-only',parent,'--','*.lean').decode().splitlines() if x in configured}
assert changed_git=={rows[m]['path'] for m in changed},(len(changed_git),len(changed))
assert all(h((R/r['path']).read_bytes())==sourcepins[m]['current_sha256'] for m,r in rows.items())
config_rows=[]
for rel in ['Combinatorics/Ramsey/scripts/check_gowers.py','lean-toolchain','lake-manifest.json']:
 old=git('show',parent+':'+rel);cur=(R/rel).read_bytes();assert old==cur
 config_rows.append({'path':rel,'sha256':h(cur),'unchanged_vs_parent':True})
inventory=Path('/tmp/gowers-merge04fd-inventory-actual');cmp=load(inventory/'comparison.json')
assert cmp['base_commit']==parent and cmp['merge_head']==incoming
assert h((R/'Combinatorics/Ramsey/gowers-proof-status.json').read_bytes())==cmp['normalized_sha256']==h((inventory/'normalized.json').read_bytes())
assert cmp['row_count']==120 and cmp['companion_occurrences']==544 and len(cmp['whole_object_permutations'])==4 and len(cmp['location_leaf_changes'])==27
summary={'configured_local_modules':len(rows),'changed_lean_owners':len(changed),'global_source_delta':sum(r['source_delta'] for r in change_rows),'imports_changed':import_changes,'acyclic':True,'affected_consumers':len(affected),'covered_consumers':len(affected&selected),'missing_nonfacades':sorted(set(missing)-set(facades)),'excluded_facades':missing,'uncovered_changed_owners':sorted(changed-selected),'selected_root_entries':len(own_rows),'selected_module_union':len(selected),'selected_source_before':sum(sourcepins[m]['source_before'] for m in selected),'selected_source_after':sum(sourcepins[m]['source_after'] for m in selected),'selected_source_delta':sum(sourcepins[m]['source_after']-sourcepins[m]['source_before'] for m in selected),'expected_protected_inputs':len(selected)+3+3+1,'source_stable_across_assessment':True,'parent_all6021_sources_match_prior_a879_rows':True}
save('source-rows.json',sourcepins);save('changed-owners.json',change_rows);save('mode-costs.json',mode_rows);save('root-costs.json',own_rows);save('consumer-coverage.json',consumers)
report={'status':'PASS static actual-merge source/import/consumer assessment; fresh native validation required','recorded_at':datetime.now(timezone.utc).isoformat(),'workspace':str(R),'comparison_parent':parent,'incoming_commit':incoming,'observed_head_before':head_before,'observed_head_after':git('rev-parse','HEAD').decode().strip(),'source_scope':'Actual working-tree merged sources only; no NEXT2111, further643 or progression311 overlay applied or consulted. Source file hashes bind this pre-commit assessment independently of eventual merge commit identity.','summary':summary,'mode_costs':mode_rows,'configuration':config_rows,'inventory_observation':{'comparison':pin(inventory/'comparison.json'),'normalized':pin(inventory/'normalized.json'),'generator_receipt':pin(inventory/'generator-receipt.json'),'rows':120,'whole_companion_occurrences':544,'whole_object_permutations':4,'location_leaf_changes':27,'current_repository_inventory_equals_normalized':True,'qualification':'The existing actual comparison is pinned and its counts/current-file identity checked; this task did not rerun generator or independently re-audit each inventory object.'},'input_pins':[pin(B/n) for n in ['source-rows.json','fullgraph-imports.json','mode-closures.json','plan.json','freeze.json']]+[pin('/tmp/gowers-equation-aware-scoped-parser/legacy-parsers.py')],'graph_sha256_canonical':h(json.dumps(graph,sort_keys=True,separators=(',',':')).encode()),'qualifications':['All current 6,021 source hashes were read twice and parent Git blobs verified. The parent bytes match the previously frozen a879 source rows. Every changed owner had imports independently parsed before/after; unchanged owner bytes preserve the pinned graph exactly.','Source-module, closure and coverage counts are static metadata. No prior native success is attributed to the merged source.','Existing one core / 65 shared / 18 supplemental root arrays cover every affected non-facade consumer; no extra root is identified by this graph assessment.','Source-only /tmp report. No new native plan/tools, captures, generators, Lean, native checks, source edits, Git mutations or cache writes.']}
save('report.json',report);save('freeze.json',{'assets':[pin(p) for p in sorted(O.iterdir()) if p.name!='freeze.json']})
print(json.dumps({'report':pin(O/'report.json'),'freeze':pin(O/'freeze.json'),'summary':summary,'modes':{m:{k:v for k,v in r.items() if k not in ['roots','changed_owners']} for m,r in mode_rows.items()}},indent=2))
