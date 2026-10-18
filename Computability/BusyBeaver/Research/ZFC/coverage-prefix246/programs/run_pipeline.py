#!/usr/bin/env python3
"""Root-run, serial, bounded exact246 coverage pipeline.

This runner never builds imported dependencies or changes proof limits. It runs
only reviewed per-unit guards whose exact hashes are frozen in the supplied
manifest. Each guard has a shared120s source/audit limit and -j1 -M4096. Total
runner wall time and number of newly checked units are explicit bounds. A failed
unit stops the pipeline and retains every attempt; changing group sizes requires
a fresh generated plan/output and a new root review. No compiler/version query
or guard invocation occurs with --prepare-only.
"""
from pathlib import Path
import argparse,hashlib,json,os,signal,subprocess,sys,time

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(c,msg):
 if not c:raise RuntimeError(msg)
def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--repo',type=Path,required=True);p.add_argument('--manifest',type=Path,required=True);p.add_argument('--manifest-sha',required=True)
 p.add_argument('--output',type=Path,required=True);p.add_argument('--reuse-record',type=Path,action='append',default=[])
 p.add_argument('--reuse-list',type=Path);p.add_argument('--max-units',type=int,default=1);p.add_argument('--wall-seconds',type=int,default=180)
 p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
 need(__debug__,'Python assertions must remain enabled.');need(1<=a.max_units<=512 and 1<=a.wall_seconds<=3600,'Explicit finite unit and wall bounds required.')
 R=a.repo.resolve();M=a.manifest.resolve();W=a.output.resolve();need(not W.is_relative_to(R),'Use external scratch output.');need(not W.exists()or not any(W.iterdir()),'Use new or empty output.')
 need(sha(M)==a.manifest_sha,'Manifest hash changed.');plan=json.loads(M.read_text());need(plan['status']=='GUARDS_FROZEN_READY','Site PASS must be frozen before pipeline preparation.')
 need(sha(plan['plan'])==plan['plan_sha256'],'Generation manifest changed.');need(sha(plan['site_evidence'])==plan['site_evidence_sha256'],'Site PASS pin changed.')
 site=json.loads(Path(plan['site_evidence']).read_text());need(site['status']=='PASS','Site parent is not PASS.');compiler=site['compiler'];need(sha(compiler['path'])==compiler['sha256'],'Compiler binary changed.')
 units=plan['units'];by_module={u['module']:u for u in units};need(len(by_module)==len(units),'Duplicate unit module.')
 for u in units:
  for path_key,hash_key in [('source_path','source_sha256'),('audit_path','audit_sha256'),('guard','guard_sha256')]:need(sha(u[path_key])==u[hash_key],'Frozen '+path_key+' changed: '+u['module'])
 known={};seen=set()
 for u in units:
  need(set(u['generated_direct_dependencies'])<=seen,'Dependency ordering changed.');seen.add(u['module'])
 def verified_record(path):
  path=path.resolve();d=json.loads(path.read_text())
  need(d['status']=='PASS' and d['only_standard_axioms'] and d['all_input_provider_postchecks'] and d['all_fresh_objects_unchanged_after_audit'],'Incomplete successful record: '+str(path))
  need(d['source_object_recorded_before_audit'] and len(d['fresh_modules'])==1,'Fresh source not recorded before audit.')
  f=d['fresh_modules'][0];m=f['module'];need(m in by_module,'Reused record is outside exact selected plan.');u=by_module[m]
  need(d['source']['sha256']==u['source_sha256'] and d['audit']['sha256']==u['audit_sha256'],'Reused proof bytes differ from selected unit.')
  need(d['compiler']['sha256']==compiler['sha256'] and d['compiler']['version']==compiler['version'],'Compiler identity mismatch.')
  need([q['label']for q in d['commands']]==['source','audit'] and all(q['exit_code']==0 for q in d['commands']),'Missing successful source/audit commands.')
  need(d['named_axiom_probes']==u['probes'] and d['callers']==u['callers'],'Audit census differs.')
  need(d['before']==d['after'],'Input postcheck differs.')
  for q,h in d['before'].items():need(sha(q)==h,'Recorded live input/provider changed: '+q)
  for key in ['source','audit']:need(sha(d[key]['path'])==sha(d[key]['snapshot'])==d[key]['sha256'],'Snapshot mismatch: '+key)
  need(sha(f['path'])==f['sha256'] and f['source_sha256']==u['source_sha256'] and d['source_pass_object']==f,'Fresh object mismatch.')
  for q in d['actual_first_providers']:need(Path(q['actual_first']).resolve()==Path(q['resolved']).resolve() and sha(q['actual_first'])==q['sha256'],'First provider changed.')
  return m,dict(path=str(path),sha256=sha(path),fresh=f)
 refs=list(a.reuse_record)
 if a.reuse_list:
  raw=json.loads(a.reuse_list.read_text());need(isinstance(raw,list) and all(isinstance(x,str)for x in raw),'Reuse list must contain record paths only.');refs.extend(Path(x)for x in raw)
 for path in refs:
  m,ref=verified_record(path);need(m not in known,'Duplicate reuse module.');known[m]=ref
 W.mkdir(parents=True,exist_ok=True)
 state=dict(status='PREPARED_NO_EXECUTION'if a.prepare_only else'RUNNING',manifest=dict(path=str(M),sha256=sha(M)),plan_sha256=plan['plan_sha256'],compiler=compiler,compiler_version_query_performed=False,limits=dict(max_new_units=a.max_units,total_wall_seconds=a.wall_seconds,per_unit_guard_wall_seconds=120,termination_grace_seconds=3,threads=1,memory_mebibytes=4096,proof_limits='Lean defaults'),reused=known.copy(),attempts=[],completed={},no_dependency_build=True,full_plan=plan['full_plan'],endpoint_established=False)
 def save():(W/'pipeline.json').write_text(json.dumps(state,indent=2)+'\n')
 def finish(status):
  state['status']=status;state['available_records']=known.copy();state['pending']=[u['module']for u in units if u['module']not in known]
  state['endpoint_established']=bool(plan['full_plan'] and not state['pending'] and 'BusyBeaver.ZFC.SitesPrefix246'in known)
  save();print(json.dumps(dict(status=status,new_attempts=len(state['attempts']),remaining=len(state['pending']),endpoint_established=state['endpoint_established'],record=str(W/'pipeline.json'))))
 save()
 if a.prepare_only:finish('PREPARED_NO_EXECUTION');return
 deadline=time.monotonic()+a.wall_seconds
 for u in units:
  m=u['module']
  if m in known:continue
  if len(state['attempts'])>=a.max_units:finish('PARTIAL_UNIT_LIMIT');return
  if deadline-time.monotonic()<1:finish('PARTIAL_WALL_LIMIT');return
  need(set(u['generated_direct_dependencies'])<=set(known),'Required dependency record missing before unit.')
  short=m.split('.')[-1];dest=W/short
  deps={k:dict(path=known[k]['path'],sha256=known[k]['sha256'])for k in u['generated_direct_dependencies']}
  cmd=[sys.executable,'-B',u['guard'],'--repo',str(R),'--site-evidence',plan['site_evidence'],'--output',str(dest)]
  if deps:
   dp=W/(short+'.dependencies.json');dp.write_text(json.dumps(deps,indent=2)+'\n');cmd+=['--dependencies',str(dp)]
  attempt=dict(module=m,source_sha256=u['source_sha256'],audit_sha256=u['audit_sha256'],guard_sha256=u['guard_sha256'],command=cmd,output=str(dest),status='RUNNING');state['attempts'].append(attempt);save()
  began=time.monotonic();env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1');env.pop('PYTHONOPTIMIZE',None)
  proc=subprocess.Popen(cmd,cwd=R,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,start_new_session=True)
  timed_out=False
  try:output,_=proc.communicate(timeout=max(0.01,deadline-time.monotonic()))
  except subprocess.TimeoutExpired:
   timed_out=True;os.killpg(proc.pid,signal.SIGTERM)
   try:output,_=proc.communicate(timeout=3)
   except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);output,_=proc.communicate()
  log=W/(short+'.driver.log');log.write_text(output)
  attempt.update(exit_code=proc.returncode,seconds=time.monotonic()-began,timed_out=timed_out,log=str(log),log_sha256=sha(log))
  if timed_out or proc.returncode!=0:
   attempt['status']='TIMEOUT'if timed_out else'FAIL';finish('STOPPED_UNIT_FAILURE');return
  try:module,ref=verified_record(dest/'verification.json');need(module==m,'Unexpected successful module.')
  except Exception as error:attempt.update(status='EVIDENCE_REJECTED',error=str(error));finish('STOPPED_EVIDENCE_REJECTION');return
  known[m]=ref;state['completed'][m]=ref;attempt.update(status='PASS',record=ref);save()
 finish('PASS_COMPLETE_PLAN'if plan['full_plan']else'PASS_SELECTED_UNITS')
if __name__=='__main__':main()
