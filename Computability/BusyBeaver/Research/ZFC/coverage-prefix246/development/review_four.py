"""Read-only static review of the frozen four-cut coverage candidate and old PASS evidence.
No generated guard, runner, compiler, toolchain version or proof evaluation call.
"""
from pathlib import Path
from collections import Counter
import ast,hashlib,json,re
B=Path('/tmp/zfc-prefix246-lean/coverage');P=B/'plan-four';G=B/'guards-four'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
p=json.loads((P/'generation.json').read_text());m=json.loads((G/'pipeline-manifest.json').read_text());s=json.loads((B/'plan-single/generation.json').read_text());reps=json.loads((B/'representatives/generation.json').read_text())
assert m['full_plan'] and m['status']=='GUARDS_FROZEN_READY' and sha(m['plan'])==m['plan_sha256']
assert sha(m['site_evidence'])==m['site_evidence_sha256']=='ed4586b081e531b08e17827f04e0ad31730a8a73c19426cf5d927e207f4714cd'
assert p['max_cuts_per_module']==4 and p['max_batch_guards']==128 and p['max_guards_per_cut']==64 and p['joins_per_module']==16
assert p['chunks']==233 and p['joins']==232 and p['selected_units']==len(m['units'])==102
keys=['index','path','nodes','leaves','guards','depth','theorem']
assert [{k:c[k]for k in keys}for c in p['cut_frontier']]==[{k:c[k]for k in keys}for c in s['cut_frontier']]
assert sum(c['leaves']for c in p['cut_frontier'])==6460 and sum(c['guards']for c in p['cut_frontier'])==8391
units={u['module']:u for u in p['units']};seen=set();closure={};ns='SetTheory.BusyBeaver.ZFC.SitesPrefix246.'
def bits(b):return '['+', '.join('true'if v else'false'for v in b)+']'
def goal(b):return 'allSites SitePrefix246.checkSite '+bits(b[::-1])+'\n      (descend ActualTree254.tree '+bits(b)+') = true'
cut_refs=[];join_refs=[];forbidden=r'\b(?:sorry|admit|native_decide|axiom)\b|set_option\s+max(?:Heartbeats|RecDepth)'
for u in m['units']:
 assert u['module'] in units
 for k in units[u['module']]:assert u[k]==units[u['module']][k]
 for a,b in [('source_path','source_sha256'),('audit_path','audit_sha256'),('guard','guard_sha256')]:assert sha(u[a])==u[b]
 src=Path(u['source_path']).read_text();aud=Path(u['audit_path']).read_text();guard=Path(u['guard']).read_text();ast.parse(guard)
 assert not re.search(forbidden,src+aud)
 assert re.findall(r'^import (\S+)',src,re.M)==u['imports']
 assert re.findall(r'^import (\S+)',aud,re.M)==[u['module']]
 assert re.findall(r'^#print axioms (\S+)',aud,re.M)==[ns+n for n in u['probe_names']]
 assert len(re.findall(r'^example\b',aud,re.M))==u['callers']==u['probes']
 assert re.findall(r'^theorem (\w+)',src,re.M)==u['probe_names']
 deps=[n for n in u['imports']if n in units];assert deps==u['generated_direct_dependencies'] and set(deps)<=seen
 ancestors=set(deps)
 for d in deps:ancestors|=closure[d]
 assert sorted(ancestors)==u['generated_transitive_dependencies'] and u['expected_provider_count']==24+len(ancestors)
 closure[u['module']]=ancestors;seen.add(u['module'])
 for k,v in [('MODULE',u['module']),('SOURCE_SHA',u['source_sha256']),('AUDIT_SHA',u['audit_sha256'])]:assert f'{k}={v!r}'in guard
 assert f"PROBES={u['probe_names']!r}"in guard and f"CALLERS={u['callers']}"in guard and 'TIMEOUT=120'in guard
 assert "'-j1', '-M4096'"in guard and 'deadline = time.monotonic() + TIMEOUT'in guard
 assert "compiler_version_query_performed=False"in guard and 'dependency_build=False'in guard
 assert m['site_evidence_sha256']in guard and 'PENDING_'not in guard
 assert 'len(closure) == '+str(u['expected_provider_count'])in guard
 assignment=next(n for n in ast.parse(guard).body if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='DEPENDENCY_PINS'for t in n.targets))
 pins=ast.literal_eval(assignment.value)
 assert pins=={d:{'source_sha256':units[d]['source_sha256'],'audit_sha256':units[d]['audit_sha256']}for d in deps}
 if u['kind']=='closed_cuts':
  assert len(u['cuts'])<=4 and u['guards']<=128 and len(u['cuts'])==u['probes'];cut_refs+=u['cuts']
  assert u['guards']==sum(p['cut_frontier'][i]['guards']for i in u['cuts'])
  for i in u['cuts']:
   c=p['cut_frontier'][i];g=goal(c['path']);assert f"theorem block_{i} :\n    {g} := by decide +kernel"in src
   assert f"example : {g} := block_{i}"in aud
 else:
  assert 'decide' not in src.replace('decoder','')
  if u['kind']=='binary_composition':
   js=[j for j in p['join_plan']if j['module']==u['module'].split('.')[-1]];assert len(js)==u['join_count']<=16
   for j in js:
    join_refs.append(j['index']);children=[]
    for side,b in [('left',False),('right',True)]:
     tag,i=j[side];c=(p['cut_frontier']if tag=='cut'else p['join_plan'])[i];assert c['path']==j['path']+[b];children.append(c)
    b=j['path'];expected=f"theorem {j['theorem']} :\n    {goal(b)} :=\n  allSites_join SitePrefix246.checkSite {bits(b[::-1])}\n    (descend ActualTree254.tree {bits(b+[False])})\n    (descend ActualTree254.tree {bits(b+[True])})\n    {children[0]['theorem']} {children[1]['theorem']}"
    assert expected in src
assert cut_refs==list(range(233)) and join_refs==list(range(232))
assert all(v==1 for v in Counter(tuple(c['path'])for c in p['cut_frontier']).values())
for i,c in enumerate(p['cut_frontier']):
 for j,d in enumerate(p['cut_frontier']):
  if i!=j:assert c['path']!=d['path'][:len(c['path'])]
uses=Counter(tuple(j[side])for j in p['join_plan']for side in ['left','right'])
assert all(uses['cut',i]==1 for i in range(233)) and all(uses['join',i]==1 for i in range(231)) and uses['join',231]==0
assert p['join_plan'][-1]['path']==[]
last=m['units'][-1];assert last['module']=='BusyBeaver.ZFC.SitesPrefix246'and last['probe_names']==['all_sites','actual_walk_checked','actual_walk_exists']and last['probes']==last['callers']==3
assert last['source_sha256']==s['units'][-1]['source_sha256']and last['audit_sha256']==s['units'][-1]['audit_sha256']
reuse=[];records=[]
recordpins={0:'862381728b14725c8069afd301df28949b220f76af908150a4c76ef97c822fdc',42:'db073c989b2f9ad27c48918149875e68a08a8c5071d7015034831af2eba269e2',210:'0583dc55970be326a3f4c0354668477be2af83af1f86456c11e295df3136a924'}
for u in reps['units']:
 z=units[u['module']];assert z['source_sha256']==u['source_sha256']and z['audit_sha256']==u['audit_sha256']
 i=z['cuts'][0];path=B/f'cut{i:03d}-run1/verification.json';assert sha(path)==recordpins[i];r=json.loads(path.read_text())
 assert r['status']=='PASS'and r['named_axiom_probes']==r['callers']==1 and r['only_standard_axioms']
 assert r['all_input_provider_postchecks']and r['all_fresh_objects_unchanged_after_audit']and r['source_object_recorded_before_audit']
 assert r['source']['sha256']==z['source_sha256']and r['audit']['sha256']==z['audit_sha256']and r['before']==r['after']
 for q,h in r['before'].items():assert sha(q)==h
 assert sha(r['compiler']['path'])==r['compiler']['sha256']
 f=r['fresh_modules'][0];assert len(r['fresh_modules'])==1 and r['source_pass_object']==f and f['module']==u['module']and sha(f['path'])==f['sha256']
 for k in ['source','audit']:assert sha(r[k]['path'])==sha(r[k]['snapshot'])==r[k]['sha256']
 assert [c['label']for c in r['commands']]==['source','audit']and all(c['exit_code']==0 for c in r['commands'])and all(v==0 for v in r['warnings'].values())
 for q in r['actual_first_providers']:assert Path(q['actual_first']).resolve()==Path(q['resolved']).resolve()and sha(q['actual_first'])==q['sha256']
 reuse.append(str(path));records.append(dict(path=str(path),sha256=sha(path),module=u['module'],input_hashes_checked=len(r['before']),source_seconds=r['commands'][0]['seconds'],audit_seconds=r['commands'][1]['seconds'],fresh_object_sha256=f['sha256']))
reuse_path=B/'representatives-reuse.json';assert not reuse_path.exists();reuse_path.write_text(json.dumps(reuse,indent=2)+'\n')
next_unit=next(u for u in m['units']if u['module']not in {r['module']for r in records})
report=dict(status='STATIC_GROUPED_SOURCE_AND_PRIOR_EVIDENCE_REVIEW_ONLY',manifest=str(G/'pipeline-manifest.json'),manifest_sha256=sha(G/'pipeline-manifest.json'),generation_sha256=sha(P/'generation.json'),source_generator_sha256=sha(B/'generate_sites_prefix246.py'),guard_generator_sha256=sha(B/'prepare_plan_guards.py'),runner_sha256=sha(B/'run_pipeline.py'),units=len(m['units']),unit_kinds=dict(Counter(u['kind']for u in m['units'])),cut_file_guard_range=[min(u['guards']for u in m['units']if u['kind']=='closed_cuts'),max(u['guards']for u in m['units']if u['kind']=='closed_cuts')],cuts=233,joins=232,leaves=6460,guard_cases=8391,all_cut_statements_independently_reconstructed=True,all_join_statements_independently_reconstructed=True,actual_child_paths_checked=True,frontier_identical_single_plan=True,representative_source_audit_bytes_unchanged=True,final_source_audit_bytes_unchanged=True,final_audit=dict(probes=3,typed_callers=3),all102_guard_hashes_and_ast_metadata_checked=True,all204_source_audit_files_checked=True,closure_policy='24 exact project prerequisites plus exact generated transitive ancestors',per_unit_shared_seconds=120,compiler_threads=1,memory_mebibytes=4096,proof_limits='Lean defaults',reused_records=records,reuse_list=dict(path=str(reuse_path),sha256=sha(reuse_path)),first_new_unit={k:next_unit[k]for k in ['module','source_sha256','audit_sha256','guard_sha256','cuts','guards','leaves','probes','callers']},commands_executed_here='Pure Python source generation and read-only static source/evidence review only',guard_invoked=False,runner_invoked=False,compiler_invoked=False,version_queried=False,scope_limit='No grouped unit compiled; only the three separate representative PASS records were checked as existing evidence. No complete coverage theorem yet.')
(B/'grouped-four-static-review.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
