"""Existing coverage-record inspection only; no guard, compiler or proof execution."""
from pathlib import Path
import hashlib,json,re
B=Path('/tmp/zfc-prefix246-lean/coverage');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
M=B/'guards-four/pipeline-manifest.json';assert sha(M)=='9ee21ec2c106e88f01b1613588dc65b0cdd1f12e04abcd13abc8fbaabb151b09';plan=json.loads(M.read_text());by={u['module']:u for u in plan['units']}
P=B/'grouped-four-next010-after050/pipeline.json';ph=sha(P);d=json.loads(P.read_text());assert d['status']=='PARTIAL_UNIT_LIMIT'and len(d['attempts'])==len(d['completed'])==10 and len(d['reused'])==50 and len(d['available_records'])==60 and len(d['pending'])==42 and not d['endpoint_established']
inputs={};records={};new=[]
for m,ref in d['available_records'].items():
 p=Path(ref['path']);assert sha(p)==ref['sha256'];v=json.loads(p.read_text());u=by[m]
 assert v['status']=='PASS'and v['only_standard_axioms']and v['all_input_provider_postchecks']and v['all_fresh_objects_unchanged_after_audit']and v['source_object_recorded_before_audit']and v['before']==v['after']
 assert len(v['fresh_modules'])==1;f=v['fresh_modules'][0];assert f==ref['fresh']==v['source_pass_object']and f['module']==m and f['source_sha256']==u['source_sha256'];assert sha(f['path'])==f['sha256']
 for kind in ['source','audit']:assert v[kind]['sha256']==u[kind+'_sha256']==sha(v[kind]['path'])==sha(v[kind]['snapshot'])
 assert(v['named_axiom_probes'],v['callers'])==(u['probes'],u['callers']);assert[c['label']for c in v['commands']]==['source','audit']and all(c['exit_code']==0 and not c.get('timed_out',False)for c in v['commands'])
 for c in v['commands']:assert(p.parent/(c['label']+'.log')).read_text()==c['output']
 reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",v['commands'][1]['output'],re.S)
 assert[n for n,_ in reports]==['SetTheory.BusyBeaver.ZFC.SitesPrefix246.'+n for n in u['probe_names']]
 assert all({x.strip()for x in ax.split(',')if x.strip()}<={'propext','Classical.choice','Quot.sound'}for _,ax in reports)
 for q,h in v['before'].items():
  if q in inputs:assert inputs[q]==h
  else:inputs[q]=h
 for q in v['actual_first_providers']:assert Path(q['actual_first']).resolve()==Path(q['resolved']).resolve()and sha(q['actual_first'])==q['sha256']
 assert v['compiler']['sha256']==d['compiler']['sha256']and v['compiler']['version']==d['compiler']['version']
 for pk,hk in [('source_path','source_sha256'),('audit_path','audit_sha256'),('guard','guard_sha256')]:assert sha(u[pk])==u[hk]
 records[m]=dict(path=str(p),sha256=sha(p),fresh=f,source_sha256=u['source_sha256'],audit_sha256=u['audit_sha256'])
 if m in d['completed']:
  attempt=next(a for a in d['attempts']if a['module']==m);assert attempt['status']=='PASS'and attempt['exit_code']==0 and not attempt['timed_out']and attempt['record']['sha256']==sha(p)
  assert attempt['guard_sha256']==u['guard_sha256']==v['before'][u['guard']];assert sha(attempt['log'])==attempt['log_sha256']
  new.append(dict(module=m,record=records[m],warnings=v['warnings'],source_seconds=v['commands'][0]['seconds'],audit_seconds=v['commands'][1]['seconds']))
for p,h in inputs.items():assert sha(p)==h,p
assert sha(P)==ph
reuse=B/'grouped-four-reuse-060.json';assert not reuse.exists();reuse.write_text(json.dumps([records[u['module']]['path']for u in plan['units']if u['module']in records],indent=2)+'\n')
pending=[u for u in plan['units']if u['module']not in records];assert len(pending)==42 and pending[0]['module']=='BusyBeaver.ZFC.SitesPrefix246Batch059'
r=dict(status='EXISTING_RECORDS_VALIDATED_NO_REPLAY_PROVISIONAL60_OF102',pipeline=dict(path=str(P),sha256=ph,status=d['status']),previous_reuse=dict(path=str(B/'grouped-four-reuse-050.json'),sha256=sha(B/'grouped-four-reuse-050.json')),reuse=dict(path=str(reuse),sha256=sha(reuse)),verified_total=60,verified_new=10,remaining=42,deduplicated_current_input_paths=len(inputs),new_records=new,next_module=pending[0]['module'],endpoint_established=False,interrupted_previous_run_preserved=True,compiler_invoked=False,guard_invoked=False,version_queried=False)
p=B/'grouped-four-reuse060-review.json';assert not p.exists();p.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(dict(reuse_sha256=sha(reuse),review_sha256=sha(p),pipeline_sha256=ph,current_input_paths=len(inputs),new_warnings=sum(sum(x['warnings'].values())for x in new),next_module=pending[0]['module']),indent=2))
