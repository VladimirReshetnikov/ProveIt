#!/usr/bin/env python3
"""Read-only phase20 actual-result audit. Never imports a runner or invokes Lean."""
import argparse,hashlib,json,re
from pathlib import Path
LEAN='/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'
LEAN_SHA='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
HELPER_SHA='a3cf7cc38004bca5e2a2df10c607fe5353896c0454069b4ff24d6b5176c32fbd'
STD={'Classical.choice','Quot.sound','propext'}
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
def profiles(t):return [[n,sorted(set(x.strip() for x in a.split(',') if x.strip()))] for n,a in re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",t)]
def warnings(t):return [[a.strip(),b.strip()] for a,b in re.findall(r'warning: ([^\n]+)\n(?:[ \t]+([^\n]+))?',t)]
def pin(p):p=Path(p);return {'path':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def accepted(directory,pinned,count):
 assert sha(directory/'result.json')==pinned
 result=read(directory/'result.json');inventory=read(directory/'inventory.json');done=read(directory/'completed.json')
 assert result['status']=='PASS' and len(done)==len(inventory['modules'])==count
 assert sha(directory/'inventory.json')==result['inventory_sha256'] and sha(directory/'completed.json')==result['completed_sha256']
 return result,inventory,done

def main():
 p=argparse.ArgumentParser()
 for n in ['check','plan','runner','basis','outer','stdout','stderr','freeze','output']:p.add_argument('--'+n,type=Path,required=True)
 p.add_argument('--basis-sha',required=True);a=p.parse_args()
 assert not a.output.exists(),'Use a new output path; prior evidence is immutable.'
 assert sha(a.runner)=='5560cc1e7f6529d620819f959d1c06f57c43341c527431ef95a11c393a1f2570'
 q=read(a.plan);res,inv,done=accepted(a.check,sha(a.check/'result.json'),227);br,bi,bd=accepted(a.basis,a.basis_sha,226)
 rows={r['module']:r for r in q['modules']};old={r['module']:r for r in bi['modules']};assert len(rows)==227 and len(old)==226 and set(rows)==set(done)==set(old)|{'BusyBeaver.ZFC.AXWord'} and set(old)==set(bd)
 assert inv=={'modules':q['modules'],'targets':q['targets'],'external_imports':['Init']}
 assert res['map_sha256']==sha(a.plan) and res['runner_sha256']==sha(a.runner) and res['basis_result_sha256']==a.basis_sha
 assert res['targets']==q['targets'] and res['provider_count']==227 and res['source_transitive_reuse_only'] and res['all_source_object_dependency_log_toolchain_inputs_postchecked']
 assert q['basis_directory']==str(a.basis.resolve()) and q['basis_result_sha256']==a.basis_sha
 assert len(br['fresh_modules'])==16 and len(br['reused_modules'])==210 and len(br['audits'])==2
 freeze=read(a.freeze);outer=read(a.outer)
 assert freeze['runner']==str(a.runner) and freeze['plan']==str(a.plan)
 for path,h in freeze['files'].items():assert sha(path)==h,path
 assert freeze['files'][str(a.runner)]==sha(a.runner) and freeze['files'][str(a.plan)]==sha(a.plan)
 assert outer['status']=='PASS_EXIT_ZERO' and outer['exit_code']==0 and outer['freeze_sha256']==sha(a.freeze)
 assert outer['stdout_sha256']==sha(a.stdout) and outer['stderr_sha256']==sha(a.stderr)
 assert outer['argv']==['python3','-B',str(a.runner),'--map',str(a.plan),'--out',str(a.check)]
 assert a.stderr.read_text()==''
 before=read(a.check/'before.json');assert before['runner_sha256']==sha(a.runner) and before['plan_sha256']==sha(a.plan) and before['targets']==q['targets']
 for path,h in before['inputs'].items():assert sha(path)==h,path
 assert before['absent_inputs']==q['absent_inputs']
 for path in q['absent_inputs']:assert not Path(path).exists() and not Path(path).is_symlink(),path
 for path,h in q['present_inputs'].items():assert sha(path)==h and before['inputs'][path]==h,path
 tc=read(a.check/'toolchain.json');assert tc==read(a.basis/'toolchain.json')
 for key in ['lean','lake','Init.olean','project_toolchain']:assert sha(tc[key]['path'])==tc[key]['sha256']
 assert tc['lean']['path']==LEAN and tc['lean']['sha256']==LEAN_SHA
 changed={m for m,r in rows.items() if m not in old or (r['source_sha256'],r['imports'])!=(old[m]['source_sha256'],old[m]['imports'])};forced=set(changed)
 while True:
  more=forced|{m for m,r in rows.items() if set(r['imports'])&forced}
  if more==forced:break
  forced=more
 assert len(changed)==8 and len(forced)==14
 assert sorted(changed)==q['expected']['changed_sources']==res['changed_sources']==before['changed_sources']
 assert sorted(forced)==q['expected']['fresh_by_source_transitivity']==res['force_basis_rebuild']==before['force_basis_rebuild']
 assert set(res['fresh_modules'])==forced and set(res['reused_modules'])==set(rows)-forced
 assert not any('KSites215Batch' in m or 'KSource215FwdCheck' in m for m in forced)
 clients=[m for m in rows if not m.startswith(('BusyBeaver.','FirstOrder.','ZF.','BoundedZFCConsistency.'))];assert len(clients)==15
 assert sum(len(rows[m]['expected_reports']) for m in clients)==93 and len(rows['BusyBeaver.ZFC.WFTheory']['expected_reports'])==5
 evidence=[];raw_present=raw_absent=raw_without_object_hash=0;all_objects={m:r['object_sha256'] for m,r in done.items()};fresh_warning_modules=[]
 # Bind accepted basis source bytes to its checked workspace, never changed old canonical paths.
 for m,r in rows.items():
  rec=done[m];prior=bd.get(m);rel=m.replace('.','/');source=a.check/'workspace'/(rel+'.lean');obj=a.check/'objects'/(rel+'.olean')
  oldsource=a.basis/'workspace'/(rel+'.lean');oldobj=a.basis/'objects'/(rel+'.olean')
  if prior is not None:
   assert sha(oldsource)==old[m]['source_sha256']==prior['source_sha256'] and sha(oldobj)==prior['object_sha256']
   assert sha(prior['log'])==prior['log_sha256']
   assert prior['status']=='PASS' and prior.get('exit_code',0)==0 and not prior.get('timed_out',False)
   assert prior['dependencies']=={d:bd[d]['object_sha256'] for d in old[m]['imports'] if d!='Init'}
  else:assert m=='BusyBeaver.ZFC.AXWord'
  assert sha(r['source'])==sha(source)==r['source_sha256']==rec['source_sha256']
  assert rec['module']==m and rec['status']=='PASS' and rec.get('exit_code',0)==0 and not rec.get('timed_out',False)
  assert rec['dependencies']=={d:all_objects[d] for d in r['imports'] if d!='Init'}
  assert sha(obj)==rec['object_sha256'] and sha(rec['log'])==rec['log_sha256']
  text=Path(rec['log']).read_text();assert 'error:' not in text and 'sorryAx' not in text
  assert profiles(text)==r['expected_reports']==(profiles(Path(prior['log']).read_text()) if prior is not None else [])
  assert all(set(ax)<=STD for _,ax in profiles(text))
  if r.get('warnings_forbidden'):assert 'warning:' not in text
  if m in clients:assert 'warning:' not in text
  raw=Path(rec['log']).with_name('record.json')
  if raw.is_file():
   receipt=read(raw);raw_present+=1
   for k in ['module','source_sha256','dependencies','log_sha256','status']:assert receipt[k]==rec[k],(m,k)
   for k in ['command','exit_code','timed_out']:
    if k in rec:assert receipt[k]==rec[k],(m,k)
   assert receipt['exit_code']==0 and not receipt['timed_out']
   if 'object_sha256' in receipt:assert receipt['object_sha256']==rec['object_sha256']
   else:raw_without_object_hash+=1
   evidence.append(pin(raw))
  else:raw_absent+=1;assert m not in forced
  if m in forced:
   assert rec['origin']=='candidate_fresh' and raw.is_file() and read(raw)==rec and not obj.is_symlink()
   assert rec['command']==[LEAN,'-j1','-M12288','--root='+str(a.check/'workspace'),'-o',str(obj),str(source)]
   assert rec['compiler_sha256']==LEAN_SHA and rec['helper_sha256']==HELPER_SHA and rec['memory_mebibytes']==12288 and rec['timeout_seconds']==120
   assert sha(raw.parent/source.name)==r['source_sha256']
   if 'warning:' in text:fresh_warning_modules.append(m)
   assert 'warning:' not in text
  else:
   assert {k:v for k,v in rec.items() if k!='origin'}=={k:v for k,v in prior.items() if k!='origin'}
   assert rec['origin']=='phase19_checked' and obj.is_symlink() and obj.resolve()==oldobj.resolve()
  if m=='BusyBeaver.ZFC.L2Control219':assert 'warning:' not in text
  evidence.extend([pin(source),pin(obj),pin(Path(rec['log']))])
 assert fresh_warning_modules==[]
 assert {str(p.relative_to(a.check/'objects')) for p in (a.check/'objects').rglob('*.olean')}=={m.replace('.','/')+'.olean' for m in rows}
 for m in q['retired_modules']:
  path=a.check/'objects'/(m.replace('.','/')+'.olean');assert not path.exists() and not path.is_symlink()
 audits=res['audits'];assert len(audits)==len(q['audits'])==2;assert sum(len(r['expected_reports']) for r in q['audits'])==10
 for spec,rec in zip(q['audits'],audits):
  m=spec['module'];directory=a.check/('audit-'+m);source=directory/(m+'.lean');obj=directory/(m+'.olean');log=directory/'compiler.log';raw=directory/'record.json'
  assert read(raw)==rec and rec['module']==m and rec['origin']=='candidate_fresh_audit'
  assert rec['status']=='PASS' and rec['exit_code']==0 and not rec['timed_out']
  assert sha(spec['source'])==sha(source)==spec['source_sha256']==rec['source_sha256'] and sha(obj)==rec['object_sha256'] and sha(log)==rec['log_sha256']
  assert rec['command']==[LEAN,'-j1','-M12288','--root='+str(directory),'-o',str(obj),str(source)] and rec['dependencies']==all_objects
  assert rec['compiler_sha256']==LEAN_SHA and rec['helper_sha256']==HELPER_SHA and rec['timeout_seconds']==120 and rec['memory_mebibytes']==12288
  text=log.read_text();assert 'error:' not in text and 'sorryAx' not in text and 'warning:' not in text and profiles(text)==spec['expected_reports']
  evidence.extend(pin(x) for x in [source,obj,log,raw])
 stdout=a.stdout.read_text();assert re.findall(r'^CHECK (\S+)$',stdout,re.M)==[m for m in rows if m in forced]
 assert re.findall(r'^REUSE (\S+) phase19_checked$',stdout,re.M)==[m for m in rows if m not in forced]
 assert re.findall(r'^AUDIT (\S+)$',stdout,re.M)==[r['module'] for r in q['audits']] and stdout.endswith('COMPLETE 227 2 audits\n')
 assert all(rows[m].get('warnings_forbidden',False) for m in changed)
 assert res['new_module_actual_profiles']=={'BusyBeaver.ZFC.AXWord':[]}
 assert sum('KSites215Batch' in m for m in rows)==9
 # Final reread prevents a mutable artifact changing during this readback.
 for item in evidence:assert sha(item['path'])==item['sha256']
 for path,h in before['inputs'].items():assert sha(path)==h,path
 report={'status':'PASS_INDEPENDENT_ACTUAL_CANDIDATE_READBACK','auditor':pin(__file__),'check_directory':str(a.check),'result':pin(a.check/'result.json'),'basis_result':pin(a.basis/'result.json'),'plan':pin(a.plan),'runner':pin(a.runner),'outer':pin(a.outer),'freeze':pin(a.freeze),'providers':227,'projects':212,'typed_clients':15,'changed_Lean_sources':8,'fresh':14,'reuses':213,'audits':2,'client_reports':93,'WFTheory_reports':5,'audit_reports':10,'exact_profiles_preserved':True,'fresh_provider_warnings':0,'Control219_warnings':0,'fresh_client_audit_warnings':0,'reused_provider_warnings':sum(Path(done[m]['log']).read_text().count('warning:') for m in rows if m not in forced),'raw_records_present':raw_present,'raw_records_absent_inherited':raw_absent,'raw_records_without_object_hash_inherited':raw_without_object_hash,'all_source_object_dependency_log_toolchain_bindings_checked':True,'owner_inputs_checked':len(before['inputs']),'present_inputs_checked':len(q['present_inputs']),'absences_checked':len(q['absent_inputs']),'no_site_or_forward_certificate_batch_recompiled':True,'scope':'Exact phase20 selected 215 closure plus maintained native/222/219/Dom compatibility roots and 15 typed clients. New AXWord module is checked fresh; all eight changed sources and their dependents rebuild. The internal PA endpoint remains open. Historical basis source bytes bind checked workspace; missing inherited raw records remain an accepted aggregate boundary. No compiler or supplied code executed by this audit.'}
 a.output.write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'status':report['status'],'report':pin(a.output)},indent=2))
if __name__=='__main__':main()
