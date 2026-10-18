"""Read/hash existing root-owned proof records only. Never execute proof/guard code."""
from pathlib import Path
import hashlib,json,re
B=Path('/tmp/zfc-routing245-lean/coverage-pilots')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
desc=lambda p:dict(path=str(p),sha256=sha(p))
plan=json.loads((B/'pilot-plan.json').read_text());units={u['site_index']:u for u in plan['pilots']}
first=B/'leaf1704-run1/case1704/verification.json';assert sha(first)=='659ccf67b43f136e932125ad6f7ed5d1b3575d0769b94e0c95d64347ed0d8bc4'
batchfile=B/'remaining6-run1/batch.json';batch=json.loads(batchfile.read_text());assert batch['status']=='PASS_SELECTED_PILOTS' and batch['prepare_only']is False
assert batch['failed_leaf'] is None and batch['selected_leaf_indices']==[1609,1703,1705,1720,4730,6324]
records={1704:desc(first)}
for u in batch['completed_units']:
 assert u['status']=='PASS';p=Path(u['record']['path']);assert sha(p)==u['record']['sha256'];records[u['leaf_index']]=u['record']
assert set(records)==set(units)
allinputs={};rows=[];probes=callers=guardcases=0;before_checks=0;actual_checks=0
for i in [1704,1609,1703,1705,1720,4730,6324]:
 p=Path(records[i]['path']);d=json.loads(p.read_text());u=units[i]
 assert d['status']=='PASS' and d['prepare_only'] is False and d['before']==d['after'] and len(d['before'])==91
 assert d['all_input_provider_postchecks'] and d['all_fresh_objects_unchanged_after_audit'] and d['only_standard_axioms']
 assert d['source_object_recorded_before_audit'] and d['project_module_count']==22 and d['exact_project_import_closure']
 assert d['leaf_index']==i and d['path_bits']==u['path'] and (d['depth'],d['opcode'],d['operand'],d['guard_cases'])==(u['depth'],u['opcode'],u['operand'],u['guards'])
 assert d['site_fuel']==4000 and d['margin']==64 and d['limits']==dict(threads=1,memory_mebibytes=4096,shared_wall_seconds=120,proof_limits='Lean defaults')
 assert d['compiler_version_query_performed']is False and d['dependency_build']is False and d['downloads']is False
 assert d['source_overridden']is False and d['audit_overridden']is False
 assert [x['label']for x in d['commands']]==['source','audit']
 assert sum(x['seconds']for x in d['commands'])<120
 for x in d['commands']:
  assert x['exit_code']==0 and x['timed_out']is False and x['command'][1:3]==['-j1','-M4096']
  assert Path(x['log']).read_text()==x['output'] and 'sorryAx'not in x['output']
 assert d['warnings']==dict(source=0,audit=0)
 for f,h in d['before'].items():
  assert sha(f)==h
  if f in allinputs:assert allinputs[f]==h
  allinputs[f]=h;before_checks+=1
 for role in ['source','audit']:
  assert d[role]['sha256']==u[role]['sha256']==sha(d[role]['path'])==sha(d[role]['snapshot'])
  assert Path(d[role]['path']).resolve()==Path(u[role]['path']).resolve()
 candidates={x['module']:x for x in d['reused_modules']};actual={x['module']:x for x in d['actual_first_providers']}
 assert len(candidates)==len(actual)==22
 for m,x in candidates.items():
  a=actual[m];assert Path(a['actual_first']).resolve()==Path(a['resolved']).resolve()==Path(x['object']).resolve()
  assert sha(a['actual_first'])==a['sha256']==x['object_sha256'];actual_checks+=1
 for x in d['toolchain_providers']:
  assert Path(x['actual_first']).resolve()==Path(x['object']).resolve() and sha(x['actual_first'])==x['object_sha256'];actual_checks+=1
 assert {x['module']for x in d['toolchain_providers']}=={'Init','Lean.Elab.Tactic.Omega'}
 assert len(d['fresh_modules'])==1;f=d['fresh_modules'][0];sf=d['source_pass_object'];a=d['fresh_first_provider_before_audit']
 assert all(f[k]==sf[k]for k in ['module','path','sha256','source_sha256']) and sf['source_command_index']==0
 assert f['module']==u['module'] and f['source_sha256']==d['source']['sha256']
 assert Path(f['path']).is_file()and not Path(f['path']).is_symlink()and sha(f['path'])==f['sha256']
 assert Path(a['actual_first']).resolve()==Path(a['resolved']).resolve()==Path(f['path']).resolve()and a['sha256']==f['sha256']
 assert Path(d['commands'][0]['command'][d['commands'][0]['command'].index('-o')+1]).resolve()==Path(f['path']).resolve()
 assert [x['label']for x in d['parent_summaries']]==['site','program']
 assert [x['module']for x in d['parent_summaries']]==['BusyBeaver.ZFC.SiteRouting245','BusyBeaver.ZFC.ProgramRouting245']
 for x in d['provider_evidence']:assert sha(x['path'])==x['sha256']
 actual_reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",d['commands'][1]['output'],re.S)
 parsed=[dict(name=n,axioms=[x.strip()for x in block.split(',')if x.strip()])for n,block in actual_reports]
 assert parsed==d['actual_axiom_sets'] and all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'}for x in parsed)
 assert [x['name']for x in parsed]==['SetTheory.BusyBeaver.ZFC.'+u['module'].rsplit('.',1)[1]+'.'+n for n in ['actual_leaf','site_checked']]
 assert (d['named_axiom_probes'],d['callers'])==(u['probes'],u['callers'])
 probes+=d['named_axiom_probes'];callers+=d['callers'];guardcases+=u['guards']
 rows.append(dict(leaf_index=i,record=records[i],source_seconds=d['commands'][0]['seconds'],audit_seconds=d['commands'][1]['seconds'],
                  fresh_object=f,probes=d['named_axiom_probes'],callers=d['callers'],axiom_sets=parsed,guard_cases=u['guards'],warnings=d['warnings']))
assert (len(rows),probes,callers,guardcases)==(7,14,25,9)
r=dict(status='PASS_SELECTED_LEAF_EXISTING_EVIDENCE_REVIEW',reviewer_role='Pilot source/guard author; separate static review of root-produced evidence, not an independent-source-author claim.',
       reviewer=desc(Path(__file__)),manifest=desc(B/'pilot-plan.json'),guard=desc(B/'check-pilots.py'),remaining_batch=desc(batchfile),records=rows,
       totals=dict(leaves=7,guards=9,axiom_probes=14,typed_callers=25,warnings=0,current_input_comparisons=before_checks,distinct_current_inputs=len(allinputs),actual_provider_comparisons=actual_checks,project_providers_per_leaf=22),
       current_inputs=allinputs,source_audit_snapshots_exact=True,fresh_source_saved_before_audit_and_still_exact=True,
       site_fuel=4000,margin=64,default_proof_limits=True,no_new_execution=True,findings=[],
       scope='Seven exact-tree-linked accepted leaves only. Both guards of two decrement leaves included. These measurements do not establish any subtree or full8391 coverage and do not freeze a production schedule.')
p=B/'leaf-evidence-review.json';p.write_text(json.dumps(r,indent=2)+'\n');print(sha(p));print(json.dumps(r['totals']))
