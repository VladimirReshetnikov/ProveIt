"""Read and preserve existing interrupted-run evidence only. No replay/guard/compiler."""
from pathlib import Path
import hashlib,json,re,shutil,datetime
B=Path('/tmp/zfc-prefix246-lean/coverage');D=Path(__file__).parent;W=B/'grouped-four-remaining068';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def dump(p,x):assert not p.exists();p.write_text(json.dumps(x,indent=2)+'\n')
M=B/'guards-four/pipeline-manifest.json';assert sha(M)=='9ee21ec2c106e88f01b1613588dc65b0cdd1f12e04abcd13abc8fbaabb151b09';manifest=json.loads(M.read_text());units=manifest['units'];by={u['module']:u for u in units};P=W/'pipeline.json';ph=sha(P);pipeline=json.loads(P.read_text());assert ph=='94f2b1e84464f7b07455c4654ba1a1ade3647d287cbb4ec76cb38d040497d23a'
assert pipeline['status']=='RUNNING'and len(pipeline['attempts'])==16 and len(pipeline['completed'])==15
prior=B/'grouped-four-reuse-034.json';assert sha(prior)=='eb24cf5a6f27f16f762530dd4fd948c556d82b48b930f8ba4e9dbbd704c3eda3';refs=list(map(Path,json.loads(prior.read_text())));assert len(refs)==34
new=list(sorted(W.glob('*/verification.json')));assert len(new)==16;refs+=new
seen={};all_inputs={};selected={};new_stats=[]
for p in refs:
 d=json.loads(p.read_text());assert d['status']=='PASS'and d['only_standard_axioms']and d['all_input_provider_postchecks']and d['all_fresh_objects_unchanged_after_audit'];assert d['source_object_recorded_before_audit']and d['before']==d['after'];assert len(d['fresh_modules'])==1
 f=d['fresh_modules'][0];m=f['module'];u=by[m];assert m not in selected
 assert d['source']['sha256']==u['source_sha256']and d['audit']['sha256']==u['audit_sha256'];assert(d['named_axiom_probes'],d['callers'])==(u['probes'],u['callers']);assert d['source_pass_object']==f
 assert[d['label']for d in d['commands']]==['source','audit']and all(c['exit_code']==0 and not c.get('timed_out',False)for c in d['commands'])
 for k in('source','audit'):assert sha(d[k]['path'])==sha(d[k]['snapshot'])==d[k]['sha256']
 assert sha(f['path'])==f['sha256']and f['source_sha256']==u['source_sha256']
 assert d['compiler']['sha256']==pipeline['compiler']['sha256']and d['compiler']['version']==pipeline['compiler']['version']
 for q,h in d['before'].items():
  if q in all_inputs:assert all_inputs[q]==h
  else:all_inputs[q]=h
 for q in d['actual_first_providers']:assert Path(q['actual_first']).resolve()==Path(q['resolved']).resolve()and sha(q['actual_first'])==q['sha256']
 for c in d['commands']:
  log=p.parent/(c['label']+'.log');assert log.read_text()==c['output']
 reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",d['commands'][1]['output'],re.S)
 assert[n for n,_ in reports]==['SetTheory.BusyBeaver.ZFC.SitesPrefix246.'+n for n in u['probe_names']]
 assert all({x.strip()for x in ax.split(',')if x.strip()}<={'propext','Classical.choice','Quot.sound'}for _,ax in reports)
 selected[m]=dict(path=str(p),sha256=sha(p),fresh=f,source_sha256=u['source_sha256'],audit_sha256=u['audit_sha256'],warnings=d['warnings'])
 if p in new:
  attempt=next(x for x in pipeline['attempts']if x['module']==m);assert attempt['source_sha256']==u['source_sha256']and attempt['audit_sha256']==u['audit_sha256']and attempt['guard_sha256']==u['guard_sha256'];assert sha(u['guard'])==u['guard_sha256'];assert u['guard']in d['before']and d['before'][u['guard']]==u['guard_sha256']
  if attempt['status']=='PASS':assert attempt['record']['sha256']==sha(p)and attempt['exit_code']==0 and sha(attempt['log'])==attempt['log_sha256']
  else:assert m=='BusyBeaver.ZFC.SitesPrefix246Batch048'and attempt['status']=='RUNNING'
  new_stats.append(dict(module=m,record=selected[m],source_seconds=d['commands'][0]['seconds'],audit_seconds=d['commands'][1]['seconds'],runner_attempt_status=attempt['status'],driver_log_exists=(W/(m.split('.')[-1]+'.driver.log')).exists()))
for p,h in all_inputs.items():assert sha(p)==h,p
assert len(selected)==50 and sha(P)==ph
# Recheck every remaining frozen source/audit/guard and the exact topological plan.
pending=[];available=set(selected)
for u in units:
 for pk,hk in [('source_path','source_sha256'),('audit_path','audit_sha256'),('guard','guard_sha256')]:assert sha(u[pk])==u[hk]
 if u['module']not in selected:
  assert set(u['generated_direct_dependencies'])<=available;pending.append(u)
 available.add(u['module'])
assert len(pending)==52 and pending[0]['module']=='BusyBeaver.ZFC.SitesPrefix246Batch049'and pending[-1]['module']=='BusyBeaver.ZFC.SitesPrefix246'
ordered=[selected[u['module']]['path']for u in units if u['module']in selected]
reuse=B/'grouped-four-reuse-050.json';dump(reuse,ordered)
# Preserve precisely the interrupted coordinator's recorded state. Do not rewrite it as terminal.
history=D/'preserved';history.mkdir();shutil.copyfile(P,history/'pipeline-stale-running.json')
last=W/'SitesPrefix246Batch048';last_files=[]
for name in['verification.json','source.log','audit.log']:
 p=last/name;q=history/('Batch048-'+name);shutil.copyfile(p,q);last_files.append(dict(original=str(p),preserved=str(q),sha256=sha(p)))
for kind in['source','audit']:
 d=json.loads((last/'verification.json').read_text());p=Path(d[kind]['snapshot']);q=history/('Batch048-'+kind+'.lean');shutil.copyfile(p,q);last_files.append(dict(original=str(p),preserved=str(q),sha256=sha(p)))
q=history/'Batch048-executed-check.py';shutil.copyfile(by['BusyBeaver.ZFC.SitesPrefix246Batch048']['guard'],q);last_files.append(dict(original=by['BusyBeaver.ZFC.SitesPrefix246Batch048']['guard'],preserved=str(q),sha256=sha(q)))
report=dict(status='EXISTING_PASS_RECOVERY_REVIEW_NO_EXECUTION',session=79413,root_report=dict(exit_code=143,stdout='empty',source='Parent message; no direct session transcript inspected by this author',termination_cause='Undetermined from persisted proof records; OS-process inspection remains root-owned'),pipeline=dict(path=str(P),sha256=ph,preserved=str(history/'pipeline-stale-running.json'),raw_status='RUNNING',recorded_completed=15,recorded_attempts=16),verified_prior=34,verified_new=16,verified_total=50,remaining=52,reuse_list=dict(path=str(reuse),sha256=sha(reuse)),deduplicated_current_input_paths=len(all_inputs),new_records=new_stats,last_unit_scope='Batch048 has an independent complete source/audit PASS with all postchecks despite stale RUNNING coordinator entry. No guard driver exit code or driver log exists for it; no such exit is inferred. It is eligible for the existing runner verified_record reuse contract.',preserved_last_unit_files=last_files,remaining_selection=dict(path=str(D/'remaining052-selection.json')),old_run_directory_left_untouched=True,source_or_guard_mutations=False,compiler_invoked=False,guard_invoked=False,version_queried=False)
selection=dict(status='SOURCE_ONLY_RECOVERY_SELECTION',manifest=dict(path=str(M),sha256=sha(M)),reuse_list=report['reuse_list'],count=52,units=pending,prior_static_source_review=dict(path=str(B/'grouped-four-remaining068-source-review.json'),sha256=sha(B/'grouped-four-remaining068-source-review.json')),recommended_first_batch=dict(max_units=10,wall_seconds=1400,output=str(B/'grouped-four-recovery050-next010')),note='No cause is inferred for session143. Short bounded sessions reduce exposure to another coordinator interruption; they do not change proofs, guards, limits or grouping. Root chooses run budget after OS-process check.')
dump(D/'remaining052-selection.json',selection);report['remaining_selection']['sha256']=sha(D/'remaining052-selection.json');dump(D/'recovery-review.json',report)
print(json.dumps(dict(verified=50,new=16,pending=52,reuse_sha256=sha(reuse),review_sha256=sha(D/'recovery-review.json'),selection_sha256=sha(D/'remaining052-selection.json'),current_input_paths=len(all_inputs),warnings_new=sum(sum(s['record']['warnings'].values())for s in new_stats)),indent=2))
