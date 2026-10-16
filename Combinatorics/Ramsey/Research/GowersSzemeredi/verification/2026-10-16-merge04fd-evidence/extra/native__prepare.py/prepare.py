from pathlib import Path
from datetime import datetime, timezone
import subprocess,json,hashlib,re,copy,difflib
R=Path('/home/codex/.codex/worktrees/9c9b/Proofs')
O=Path('/tmp/gowers-merge04fd-native-tools')
assert not O.exists(); O.mkdir()
P=Path('/tmp/gowers-merge68ad-native-tools')
def sha_bytes(b):return hashlib.sha256(b).hexdigest()
def sha(p):return sha_bytes(Path(p).read_bytes())
def git(*args,input=None):return subprocess.check_output(['git','--no-optional-locks',*args],cwd=R,input=input)
def emit(name,data):
 p=O/name
 with p.open('x') as f: json.dump(data,f,indent=2);f.write('\n')
 return sha(p)
def imports(text):return re.findall(r'^import\s+(\S+)',text,re.M)
def key(path,base):return str(path.relative_to(base).with_suffix('')).replace('/','.')
base=git('rev-parse','cb7319ce84f72719fa92797c689591a29e547d40').decode().strip()
incoming=git('rev-parse','04fd0fb36e46ff05373664236758eff99665bded').decode().strip()
commit=git('rev-parse','HEAD').decode().strip()
assert git('status','--porcelain')==b''
assert git('show','-s','--format=%P',commit).decode().split()==[base,incoming]
paths={}; rows={}; graph={}
for prefix in ['Combinatorics/Ramsey/Lean','lib/openai-math/lean']:
 root=R/prefix
 for p in sorted(root.rglob('*.lean')):
  m=key(p,root);assert m not in graph
  b=p.read_bytes();text=b.decode();rel=str(p.relative_to(R))
  paths[rel]=m;graph[m]=imports(text)
  rows[m]={'path':rel,'sha256':sha_bytes(b),'source_lines':len(text.splitlines())}
graph=dict(sorted(graph.items()));rows=dict(sorted(rows.items()))
changed_paths=git('diff','--name-only','-z',base,'--','*.lean').decode().rstrip('\0').split('\0')
changed_paths=[p for p in changed_paths if p]
assert all(p in paths for p in changed_paths),('new/deleted/outside roots',set(changed_paths)-set(paths))
changed=sorted(paths[p] for p in changed_paths)
# Retrieve all baseline changed-owner objects in one read-only Git batch.
requests=''.join(base+':'+p+'\n' for p in changed_paths).encode()
raw=git('cat-file','--batch',input=requests);offset=0;old_text={}
for p in changed_paths:
 end=raw.index(b'\n',offset);header=raw[offset:end].split();assert header[1]==b'blob'
 n=int(header[2]);b=raw[end+1:end+1+n];assert len(b)==n
 old_text[paths[p]]=b.decode();offset=end+n+2
assert offset==len(raw)
old_graph=copy.deepcopy(graph)
for m,text in old_text.items():old_graph[m]=imports(text)
# Exact local import graph checks, including cycles and missing local providers.
def local(m):return m.split('.')[0] in ['GowersSzemeredi','OAI']
for label,g in [('before',old_graph),('current',graph)]:
 missing=sorted({d for deps in g.values() for d in deps if local(d) and d not in g});assert not missing,(label,missing)
def closure_function(g):
 memo={};active=set()
 def closure(m):
  if m in memo:return memo[m]
  assert m not in active,('cycle',m)
  active.add(m);result={m}
  for d in g[m]:
   if local(d):result.update(closure(d))
  active.remove(m);memo[m]=frozenset(result);return memo[m]
 for m in g:closure(m)
 return closure
newcl=closure_function(graph);oldcl=closure_function(old_graph)
changed_set=set(changed)
oldaffected={m for m in graph if changed_set & oldcl(m)}
newaffected={m for m in graph if changed_set & newcl(m)}
affected=oldaffected|newaffected
plan=json.loads((P/'plan.json').read_text());old_plan=copy.deepcopy(plan)
selected=set().union(*(newcl(r) for v in plan.values() for r in v['roots']))
facades={'GowersSzemeredi','GowersSzemeredi.Audit','GowersSzemeredi.PortImportAudit'}
uncovered=affected-selected-facades
extra=[]
while uncovered:
 # Choose an uncovered consumer that covers the largest remaining uncovered set.
 target=max(sorted(uncovered),key=lambda m:len(newcl(m)&uncovered))
 extra.append(target);plan['supplemental']['roots'].append(target);selected.update(newcl(target));uncovered=affected-selected-facades
cumulative=set();modes={}
for mode,spec in plan.items():
 mods=set().union(*(newcl(r) for r in spec['roots']));cumulative.update(mods)
 spec.update(module_count=len(mods),input_count=len(mods)+3,source_lines=sum(rows[m]['source_lines'] for m in mods))
 modes[mode]={'roots':spec['roots'],'modules':sorted(mods),'module_count':len(mods),'input_count':len(mods)+3,'source_lines':spec['source_lines'],'cumulative_modules':sorted(cumulative)}
assert selected==cumulative
assert changed_set<=selected and affected-selected<=facades
coverage=[]
for m in sorted(affected):
 covered_by=[mode for mode,v in modes.items() if m in v['modules']]
 coverage.append({'module':m,'changed_owner':m in changed_set,'affected_before':m in oldaffected,'affected_current':m in newaffected,'selected_modes':covered_by,'excluded_facade':m in facades and not covered_by})
owner_rows=[]
for m in changed:
 oldb=old_text[m].encode()
 owner_rows.append({'module':m,'path':rows[m]['path'],'baseline_sha256':sha_bytes(oldb),'current_sha256':rows[m]['sha256'],'source_lines_before':len(old_text[m].splitlines()),'source_lines_after':rows[m]['source_lines'],'source_lines_delta':rows[m]['source_lines']-len(old_text[m].splitlines()),'imports_before':old_graph[m],'imports_current':graph[m],'selected_modes':[k for k,v in modes.items() if m in v['modules']]})
checker='Combinatorics/Ramsey/scripts/check_gowers.py'
checker_old=git('show',base+':'+checker);assert (R/checker).read_bytes()==checker_old
checker_sha=sha_bytes(checker_old)
configs={p:sha(R/p) for p in ['Combinatorics/Ramsey/scripts/check_gowers.py','lean-toolchain','lake-manifest.json']}
for p,h in configs.items():assert h==sha_bytes(git('show',base+':'+p))
# All source reads must still match; inventory and Git commit are intentionally not frozen here.
assert all(sha(R/row['path'])==row['sha256'] for row in rows.values())
for name in ['common.py','capture.py','run.py']:
 with (O/name).open('xb') as f:f.write((P/name).read_bytes())
emit('plan.json',plan)
emit('fullgraph-imports.json',graph)
emit('baseline-fullgraph-imports.json',old_graph)
emit('source-rows.json',rows)
emit('changed-owners.json',owner_rows)
emit('consumer-coverage.json',coverage)
emit('mode-closures.json',modes)
with (O/'plan.diff').open('x') as f:f.writelines(difflib.unified_diff((P/'plan.json').read_text().splitlines(True),(O/'plan.json').read_text().splitlines(True),fromfile=str(P/'plan.json'),tofile=str(O/'plan.json')))
measurement={'schema_version':1,'status':'Prepared source-only merge validation plan; no snapshot captured and no native invocation','recorded_at':datetime.now(timezone.utc).isoformat(),'workspace':str(R),'comparison_commit':base,'incoming_commit':incoming,'merge_commit':None,'inventory_generation_pending':True,'full_local_modules':len(graph),'changed_production_owners':len(changed),'global_changed_source_lines_delta':sum(v['source_lines_delta'] for v in owner_rows),'dependent_consumers_before':len(oldaffected),'dependent_consumers_current':len(newaffected),'dependent_consumers_union':len(affected),'covered_consumers':len(affected&selected),'excluded_facades':sorted(affected-selected),'uncovered_changed_owners':sorted(changed_set-selected),'other_uncovered_consumers':sorted(affected-selected-facades),'roots_preserved':all(plan[k]['roots'][:len(old_plan[k]['roots'])]==old_plan[k]['roots'] for k in plan),'added_supplemental_roots':extra,'mode_counts':{k:{q:v[q] for q in ['module_count','input_count','source_lines']}|{'root_count':len(v['roots'])} for k,v in modes.items()},'combined_local_modules':len(selected),'protected_inputs_expected_at_capture':len(selected)+7,'helper_files_byte_identical_to_merge68ad':{name:sha(O/name)==sha(P/name) for name in ['common.py','capture.py','run.py']},'tool_sha256':{name:sha(O/name) for name in ['common.py','capture.py','run.py','plan.json']},'configuration_sha256':configs,'checker_unchanged_vs_comparison_commit':True,'source_consistency_at_finish':True,'snapshot_captured':False,'native_validation_run':False,'historical_native_retention_used':False,'limitations':['Plan measurements describe current resolved Lean sources while inventory regeneration and the merge commit are pending.','Root closures are source metadata only; no native outcome is asserted.','The prior a879 receipts do not validate merged sources. A new committed snapshot and fresh sequential core/shared/supplemental invocation chain are required.','Three aggregate facades remain protected source inputs at capture but are excluded from native selected-root coverage, matching the prior scope.','Full source and import graph records are measurements, not a committed native source snapshot.'],'evidence':{n:sha(O/n) for n in ['fullgraph-imports.json','baseline-fullgraph-imports.json','source-rows.json','changed-owners.json','consumer-coverage.json','mode-closures.json','plan.diff']}}
emit('measurement.json',measurement)
readme='Merge04fd native validation preparation\n\nThis package was prepared without running or importing native/capture/source-guard helpers.\ncommon.py, capture.py and run.py are byte-identical to the reviewed merge68ad package.\nplan.json is remeasured on the current resolved Lean sources, with source-only coverage evidence.\nNo snapshot was captured: regenerate/normalize the inventory and commit the merge first.\nThe three aggregate facades remain protected inputs but are excluded as native roots.\nThe old a879 native outcomes do not certify the merged sources.\n'
with (O/'README.txt').open('x') as f:f.write(readme)
emit('freeze.json',{p.name:sha(p) for p in sorted(O.iterdir()) if p.is_file() and p.name!='freeze.json'})
print(json.dumps({k:measurement[k] for k in ['full_local_modules','changed_production_owners','global_changed_source_lines_delta','dependent_consumers_union','covered_consumers','excluded_facades','other_uncovered_consumers','mode_counts','combined_local_modules','added_supplemental_roots','tool_sha256']},indent=2))
print('measurement_sha256',sha(O/'measurement.json'));print('freeze_sha256',sha(O/'freeze.json'))

# Finalize this new package against the committed actual merge and inventory.
import ast
tracked={x for x in git('ls-tree','-r','--name-only','-z',base,'--','Combinatorics/Ramsey/Lean','lib/openai-math/lean').decode().split('\0') if x.endswith('.lean')}
assert tracked=={row['path'] for row in rows.values()}
assert all(sha(R/row['path'])==row['sha256'] for row in rows.values())
assert git('rev-parse','HEAD').decode().strip()==commit and git('status','--porcelain')==b''
inv='Combinatorics/Ramsey/gowers-proof-status.json'; invsha='d705215fb1fe2edb737ff21e464913e0823d6c5b682de168eddbc6146d0ffadd'
assert sha(R/inv)==invsha
comparison=Path('/tmp/gowers-merge04fd-inventory-actual/comparison.json')
assert sha(comparison)=='42d4e89374878db9728bdf4f43e1ba98195a5fa98250106d82ff4cd40636d432'
for name in ['common.py','capture.py','run.py']: ast.parse((O/name).read_text())
measurement['status']='Prepared committed actual merge validation plan; source-only, no snapshot or native run'
measurement['finalized_at']=datetime.now(timezone.utc).isoformat(); measurement['merge_commit']=commit; measurement['inventory_generation_pending']=False
measurement['baseline_tracked_module_keyset_verified']=len(rows); measurement['current_all_source_hashes_rechecked_after_commit']=len(rows)
measurement['current_inventory']={'path':inv,'sha256':invsha,'comparison':{'path':str(comparison),'sha256':sha(comparison)}}
measurement['limitations'][0]='Measurements describe committed actual merge '+commit+'; all configured source bytes rechecked after commit and actual inventory generation.'
(O/'measurement.json').write_text(json.dumps(measurement,indent=2)+'\n')
(O/'README.txt').write_text('Merge04fd native validation preparation\n\nCommitted source: '+commit+'\nThis package contains source-only measurements. No snapshot or native run yet.\nThe native helper files are byte-identical to the previously validated merge68ad tools.\nPrior a879 receipts do not certify the current merged source.\nThree aggregate facades remain protected inputs, excluded as native roots.\n')
(O/'prepare.py').write_text(Path(__file__).read_text())
(O/'freeze.json').write_text(json.dumps({p.name:sha(p) for p in sorted(O.iterdir()) if p.is_file() and p.name!='freeze.json'},indent=2)+'\n')
print('FINAL',json.dumps({'merge_commit':commit,'measurement_sha256':sha(O/'measurement.json'),'freeze_sha256':sha(O/'freeze.json'),'plan_sha256':sha(O/'plan.json')}))
for p in O.iterdir():
 if p.is_file(): p.chmod(0o444)
