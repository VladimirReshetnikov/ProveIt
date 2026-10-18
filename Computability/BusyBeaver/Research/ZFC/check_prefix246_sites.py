#!/usr/bin/env python3
"""Stage the exact published coverage plan and perform bounded serial replay/preparation.
--stage-only runs no child programs. --prepare-only runs102 Python guards in
preparation mode, with no Lean/version/dependency calls. Default replay calls
the exact published serial runner with explicit finite unit and wall limits.
Historical source/object cache prerequisites remain explicit and unchanged.
"""
from pathlib import Path
import argparse,ast,copy,difflib,hashlib,json,os,subprocess,sys,time
HERE=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(c,m):
 if not c:raise RuntimeError(m)
def dump(p,x):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(x,indent=2)+'\n')
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--repo',type=Path,default=HERE.parents[3]);ap.add_argument('--manifest-sha',required=True);ap.add_argument('--output',type=Path,required=True)
 mode=ap.add_mutually_exclusive_group();mode.add_argument('--stage-only',action='store_true');mode.add_argument('--prepare-only',action='store_true')
 ap.add_argument('--reuse-list',type=Path);ap.add_argument('--max-units',type=int,default=10);ap.add_argument('--wall-seconds',type=int,default=1400);a=ap.parse_args()
 need(__debug__,'Assertions must remain enabled.');R=a.repo.resolve();W=a.output.resolve();need(not W.exists()and not W.is_relative_to(R),'New external output required.')
 need(1<=a.max_units<=512 and 1<=a.wall_seconds<=3600,'Finite bounds required.')
 need(not(a.stage_only or a.prepare_only)or a.reuse_list is None,'Preparation uses historical parents; no reuse override.')
 Z=R/'Computability/BusyBeaver/Research/ZFC';M=Z/'coverage-prefix246/manifest.json';need(sha(M)==a.manifest_sha,'Publication manifest pin changed.');manifest=json.loads(M.read_text())
 need(manifest['status']=='EXACT_COMPLETED_COVERAGE_EVIDENCE_PACKET'and manifest['module_count']==102,'Complete publication required.')
 def published(binding):
  rel=Path(binding['path']);need(not rel.is_absolute()and '..'not in rel.parts,'Unsafe published path.');p=R/rel;need(sha(p)==binding['sha256'],'Published artifact changed: '+str(p));return p
 for h,row in manifest['content_registry'].items():
  for name in row['published_paths']:published(dict(path=name,sha256=h))
 need(published(manifest['programs']['coordinator']).resolve()==Path(__file__).resolve(),'Unexpected installed coordinator.')
 units=manifest['units'];need(len(units)==len({u['module']for u in units})==102,'Module census differs.');by={u['module']:u for u in units}
 raw_manifest=published(manifest['plans']['pipeline']);raw=json.loads(raw_manifest.read_text());need(raw['full_plan']and raw['status']=='GUARDS_FROZEN_READY','Raw plan is incomplete.')
 need([u['module']for u in raw['units']]==[u['module']for u in units],'Publication order differs.')
 site=published(manifest['site_parent']);need(sha(site)==raw['site_evidence_sha256'],'Site pin differs.')
 generation=published(manifest['plans']['generation']);need(sha(generation)==raw['plan_sha256'],'Generation changed.')
 runner=published(manifest['programs']['run_pipeline.py'])
 W.mkdir();record=dict(status='STAGING',prepare_only=a.prepare_only,stage_only=a.stage_only,manifest=dict(path=str(M),sha256=sha(M)),coordinator_sha256=sha(Path(__file__)),source_audit_bytes_changed=False,compiler_version_query_performed=False,dependency_build=False,commands=[],units=[],limits=dict(max_new_units=a.max_units,total_wall_seconds=a.wall_seconds,shared_source_audit_seconds=120,threads=1,memory_mebibytes=4096,proof_limits='Lean defaults'))
 def save():dump(W/'coordination.json',record)
 save();portable=copy.deepcopy(raw);portable.update(plan=str(generation),site_evidence=str(site));staged=[]
 for unit,u in zip(units,portable['units']):
  art=unit['artifacts'];source=published(art['source']);audit=published(art['audit']);guard=published(art['planned_guard']);text=guard.read_text();modified=text
  for old,new in[(unit['planned_source_path'],str(source)),(unit['planned_audit_path'],str(audit))]:
   needle='Path('+repr(old)+')';need(modified.count(needle)==1,'Expected one default path occurrence.');modified=modified.replace(needle,'Path('+repr(new)+')')
  class Normalize(ast.NodeTransformer):
   def visit_Constant(self,node):
    if isinstance(node.value,str):
     node.value={str(source):unit['planned_source_path'],str(audit):unit['planned_audit_path']}.get(node.value,node.value)
    return node
  need(ast.dump(Normalize().visit(ast.parse(modified)),include_attributes=False)==ast.dump(ast.parse(text),include_attributes=False),'Portable guard changed beyond defaults.')
  short=unit['module'].split('.')[-1];stage=W/'guards'/(short+'.check.py');stage.parent.mkdir(exist_ok=True);stage.write_text(modified);delta=stage.with_suffix('.diff');delta.write_text(''.join(difflib.unified_diff(text.splitlines(True),modified.splitlines(True),fromfile=str(guard),tofile=str(stage))))
  u.update(source_path=str(source),audit_path=str(audit),guard=str(stage),guard_sha256=sha(stage));staged.append((unit,stage))
  record['units'].append(dict(module=unit['module'],source_sha256=sha(source),audit_sha256=sha(audit),raw_guard_sha256=sha(guard),staged_guard=str(stage),staged_guard_sha256=sha(stage),defaults_only_diff=str(delta),defaults_only_diff_sha256=sha(delta)))
 PM=W/'pipeline-manifest.json';dump(PM,portable);record.update(portable_manifest=dict(path=str(PM),sha256=sha(PM)));save()
 if a.stage_only:record.update(status='STAGED_NO_EXECUTION',compiler_invoked=False);save();print(W/'coordination.json');return
 env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1');env.pop('PYTHONOPTIMIZE',None)
 if a.prepare_only:
  record['status']='PREPARING';save();deadline=time.monotonic()+a.wall_seconds
  for(unit,guard),note in zip(staged,record['units']):
   short=unit['module'].split('.')[-1];dest=W/'prepared'/short;deps={m:dict(path=str(published(by[m]['artifacts']['verification'])),sha256=by[m]['artifacts']['verification']['sha256'])for m in unit['generated_direct_dependencies']}
   cmd=[sys.executable,'-B',str(guard),'--repo',str(R),'--site-evidence',str(site),'--output',str(dest),'--prepare-only']
   if deps:
    dp=W/'dependencies'/(short+'.json');dump(dp,deps);cmd+=['--dependencies',str(dp)]
   remaining=deadline-time.monotonic();need(remaining>0,'Preparation wall bound exhausted.');began=time.monotonic()
   try:cp=subprocess.run(cmd,cwd=R,env=env,capture_output=True,text=True,timeout=remaining)
   except subprocess.TimeoutExpired as ex:
    dec=lambda x:x.decode(errors='replace')if isinstance(x,bytes)else(x or'');log=W/(short+'.preparation.log');log.write_text(dec(ex.stdout)+dec(ex.stderr));record['commands'].append(dict(module=unit['module'],command=cmd,status='TIMEOUT',log=str(log),log_sha256=sha(log)));record['status']='STOPPED_PREPARATION_TIMEOUT';save();raise
   log=W/(short+'.preparation.log');log.write_text(cp.stdout+cp.stderr);record['commands'].append(dict(module=unit['module'],command=cmd,exit_code=cp.returncode,seconds=time.monotonic()-began,log=str(log),log_sha256=sha(log)));save()
   if cp.returncode!=0:record['status']='STOPPED_PREPARATION_FAILURE';save();raise RuntimeError('Preparation failed: '+short)
   vr=dest/'verification.json';d=json.loads(vr.read_text());need(d['status']=='PREPARED_NOT_BUILT'and d['commands']==[]and d['fresh_modules']==[],'Preparation emitted proof evidence.')
   need(d['compiler']['compiler_version_query_performed']is False and d['dependency_build']is False,'Preparation queried/built dependencies.')
   need(not d['source_overridden']and not d['audit_overridden'],'Expected maintained defaults.')
   need(d['source']['path']==str(published(unit['artifacts']['source']))and d['audit']['path']==str(published(unit['artifacts']['audit'])),'Prepared default paths differ.')
   need(d['source']['sha256']==note['source_sha256']and d['audit']['sha256']==note['audit_sha256']and d['before']==d['after']and d['all_input_provider_postchecks'],'Preparation binding differs.')
   note.update(preparation=dict(path=str(vr),sha256=sha(vr)));save()
  record.update(status='PREPARED_NOT_BUILT',compiler_invoked=False,guard_preparations=102);save();print(W/'coordination.json');return
 # The unchanged runner owns serial execution, process-group timeouts and reuse validation.
 cmd=[sys.executable,'-B',str(runner),'--repo',str(R),'--manifest',str(PM),'--manifest-sha',sha(PM),'--output',str(W/'replay'),'--max-units',str(a.max_units),'--wall-seconds',str(a.wall_seconds)]
 if a.reuse_list:cmd+=['--reuse-list',str(a.reuse_list.resolve())]
 record['status']='RUNNING';record['commands'].append(dict(command=cmd,status='RUNNING'));save()
 log=W/'runner.log'
 with log.open('w')as stream:cp=subprocess.run(cmd,cwd=R,env=env,stdout=stream,stderr=subprocess.STDOUT)
 record['commands'][-1].update(exit_code=cp.returncode,log=str(log),log_sha256=sha(log))
 pr=W/'replay/pipeline.json'
 if cp.returncode!=0 or not pr.exists():record.update(status='STOPPED_RUNNER_FAILURE');save();raise RuntimeError('Runner did not complete normally.')
 d=json.loads(pr.read_text());record.update(status=d['status'],pipeline=dict(path=str(pr),sha256=sha(pr)),endpoint_established=d['endpoint_established']);save()
 need(d['status']in ['PASS_COMPLETE_PLAN','PARTIAL_UNIT_LIMIT','PARTIAL_WALL_LIMIT'],'Runner stopped with a failed unit/evidence check.');print(W/'coordination.json')
if __name__=='__main__':main()
