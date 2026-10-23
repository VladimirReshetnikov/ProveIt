#!/usr/bin/env python3
"""Read-only phase23 actual-result audit. Never imports a runner or invokes Lean."""
import argparse,hashlib,json,re
from pathlib import Path
LEAN='/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'
LEAN_SHA='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
HELPER_SHA='a3cf7cc38004bca5e2a2df10c607fe5353896c0454069b4ff24d6b5176c32fbd'
BASIS_SHA='cd966bd654b04a3c2becbafc00ba1f13f2866fcbab64b5b6715cf6449461dc66'
BASIS_PLAN=Path('/tmp/k215-phase22-check-v3/candidate-plan.json')
R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
LEAF=['README.md','capture-config.json','capture.json','capture.py','check-plan.json','check.py','evidence.tar.gz','index.json','result-review.json','result.json','review_actual.py']
STD={'Classical.choice','Quot.sound','propext'}
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
def profiles(t):return [[n,sorted(set(x.strip() for x in a.split(',') if x.strip()))] for n,a in re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",t)]
def norm(rows):
 result=[]
 for n,ax in rows:
  assert isinstance(n,str) and isinstance(ax,(str,list))
  values=ax.split(',') if isinstance(ax,str) else ax
  assert all(isinstance(x,str) for x in values)
  result.append([n,sorted({x.strip() for x in values if x.strip()})])
 return result
def recorded_profiles(rec,text):
 # Old accepted reports use both comma-separated strings and lists; logs decide exact profiles.
 if 'reports' in rec:assert norm(rec['reports'])==profiles(text)
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
 assert sha(a.runner)==P23_RUNNER_SHA and a.basis_sha==BASIS_SHA
 q=read(a.plan)
 for path,h in P23_RUNTIME_INPUTS.items():assert q['present_inputs'][path]==h==sha(path)
 count=q['expected']['provider_count'];res,inv,done=accepted(a.check,sha(a.check/'result.json'),count);br,bi,bd=accepted(a.basis,a.basis_sha,226)
 assert sha(BASIS_PLAN)==br['map_sha256'];bq=read(BASIS_PLAN)
 assert q['mode']=='phase23-candidate' and q['status']=='SOURCE_DERIVED_READY_FOR_ROOT_REVIEW' and q['base_commit']=='017861249e7da624c007e0dd6d170e32433be549'
 rows={r['module']:r for r in q['modules']};old={r['module']:r for r in bi['modules']};retired={r['module'] for r in q['newly_retired_module_sources']}
 assert len(rows)==len(q['modules'])==count and len(old)==226 and set(rows)==set(done) and set(old)==set(bd)
 assert q['unselected_old_modules']==sorted(set(old)-set(rows)) and retired<=set(old)-set(rows)
 assert set(q['retired_modules'])==set(bq['retired_modules'])|retired and not set(q['retired_modules'])&set(rows)
 assert q['targets']==bq['targets'] and q['audits']==bq['audits']
 assert q['absent_inputs'][:len(bq['absent_inputs'])]==bq['absent_inputs'] and len(q['absent_inputs'])==len(set(q['absent_inputs']))==len(bq['absent_inputs'])+len(q['newly_retired_module_sources'])+len(q['newly_retired_producers'])
 packet=R/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase22/lean'
 assert {p.name for p in packet.iterdir()}==set(LEAF)
 for name in LEAF:assert q['present_inputs'][str(packet/name)]==sha(packet/name)
 assert sha(packet/'result.json')==BASIS_SHA
 for suffix in ['candidate-k215/k215.tm','candidate-k215/k215.native.tm','candidate-k215/sites215.json','k225-formal/generate_l2dom.py']:
  path=str(R/'Computability/BusyBeaver/Research/ZFC'/suffix);assert q['present_inputs'][path]==bq['present_inputs'][path]==sha(path)
 for r in q['newly_retired_module_sources']+q['newly_retired_producers']:
  assert not Path(r['canonical']).exists() and not Path(r['canonical']).is_symlink() and r['canonical'] in q['absent_inputs']
  assert sha(r['snapshot'])==r['sha256']==q['present_inputs'][r['snapshot']]
 for r in q['newly_retired_module_sources']:assert r['sha256']==old[r['module']]['source_sha256']
 assert inv=={'modules':q['modules'],'targets':q['targets'],'external_imports':['Init']}
 assert res['map_sha256']==sha(a.plan) and res['runner_sha256']==sha(a.runner) and res['basis_result_sha256']==a.basis_sha
 assert res['targets']==q['targets'] and res['provider_count']==count and res['source_transitive_reuse_only'] and res['all_source_object_dependency_log_toolchain_inputs_postchecked']
 assert q['basis_directory']==str(a.basis.resolve()) and q['basis_result_sha256']==a.basis_sha
 assert sorted(br['fresh_modules']+br['reused_modules'])==sorted(bd) and len(br['audits'])==len(bq['audits'])==2
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
 assert changed=={r['module'] for r in q['source_overlay']}
 assert sorted(changed)==q['expected']['changed_sources']==res['changed_sources']==before['changed_sources']
 assert sorted(forced)==q['expected']['fresh_by_source_transitivity']==res['force_basis_rebuild']==before['force_basis_rebuild']
 assert set(res['fresh_modules'])==forced and set(res['reused_modules'])==set(rows)-forced
 assert all(rows[m].get('warnings_forbidden',False) for m in forced)
 clients=[m for m in rows if not m.startswith(('BusyBeaver.','FirstOrder.','ZF.','BoundedZFCConsistency.'))];assert len(clients)==15
 assert set(clients)=={m for m in old if not m.startswith(('BusyBeaver.','FirstOrder.','ZF.','BoundedZFCConsistency.'))}
 assert sorted(set(clients)&forced)==q['expected']['affected_typed_clients']
 assert (q['expected']['project_count'],q['expected']['typed_client_count'])==(count-len(clients),len(clients))
 assert sum(len(rows[m]['expected_reports']) for m in clients)==93 and len(rows['BusyBeaver.ZFC.WFTheory']['expected_reports'])==5
 evidence=[];raw_present=raw_absent=raw_without_object_hash=0;all_objects={m:r['object_sha256'] for m,r in done.items()};fresh_warning_modules=[]
 # Bind every accepted phase22 provider to its checked workspace; preserve missing raw records.
 basis_raw_absent=set()
 for m,prior in bd.items():
  rel=m.replace('.','/');oldsource=a.basis/'workspace'/(rel+'.lean');oldobj=a.basis/'objects'/(rel+'.olean')
  assert sha(oldsource)==old[m]['source_sha256']==prior['source_sha256'] and sha(oldobj)==prior['object_sha256']
  assert sha(prior['log'])==prior['log_sha256']
  text=Path(prior['log']).read_text();assert 'error:' not in text and 'sorryAx' not in text
  assert profiles(text)==old[m]['expected_reports'] and all(set(ax)<=STD for _,ax in profiles(text));recorded_profiles(prior,text)
  assert prior['status']=='PASS' and prior.get('exit_code',0)==0 and not prior.get('timed_out',False)
  assert prior['dependencies']=={d:bd[d]['object_sha256'] for d in old[m]['imports'] if d!='Init'}
  raw=Path(prior['log']).with_name('record.json')
  if not raw.is_file():basis_raw_absent.add(m)
  else:
   receipt=read(raw)
   for k in ['module','source_sha256','dependencies','log_sha256','status']:assert receipt[k]==prior[k],(m,k)
   for k in ['command','exit_code','timed_out','object_sha256']:
    if k in prior and k in receipt:assert receipt[k]==prior[k],(m,k)
   assert receipt['exit_code']==0 and not receipt['timed_out'] and receipt['command'][:3]==[LEAN,'-j1','-M12288']
   recorded_profiles(receipt,text);evidence.append(pin(raw))
  evidence.extend(pin(x) for x in [oldsource,oldobj,Path(prior['log'])])
 assert len(basis_raw_absent)==31
 for m,r in rows.items():
  rec=done[m];prior=bd.get(m);rel=m.replace('.','/');source=a.check/'workspace'/(rel+'.lean');obj=a.check/'objects'/(rel+'.olean');oldobj=a.basis/'objects'/(rel+'.olean')
  assert sha(r['source'])==sha(source)==r['source_sha256']==rec['source_sha256']
  assert rec['module']==m and rec['status']=='PASS' and rec.get('exit_code',0)==0 and not rec.get('timed_out',False)
  assert rec['dependencies']=={d:all_objects[d] for d in r['imports'] if d!='Init'}
  assert sha(obj)==rec['object_sha256'] and sha(rec['log'])==rec['log_sha256']
  text=Path(rec['log']).read_text();assert 'error:' not in text and 'sorryAx' not in text
  assert profiles(text)==r['expected_reports'];recorded_profiles(rec,text)
  if prior is not None:assert profiles(text)==profiles(Path(prior['log']).read_text())
  else:assert profiles(text)==[]
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
   recorded_profiles(receipt,text);evidence.append(pin(raw))
  else:raw_absent+=1;assert m not in forced and m in basis_raw_absent
  if m in forced:
   assert rec['origin']=='candidate_fresh' and raw.is_file() and read(raw)==rec and not obj.is_symlink()
   assert rec['command']==[LEAN,'-j1','-M12288','--root='+str(a.check/'workspace'),'-o',str(obj),str(source)]
   assert rec['compiler_sha256']==LEAN_SHA and rec['helper_sha256']==HELPER_SHA and rec['memory_mebibytes']==12288 and rec['timeout_seconds']==(900 if 'KSites215Batch' in m or 'KSource215FwdCheck' in m else 120)
   assert sha(raw.parent/source.name)==r['source_sha256']
   if 'warning:' in text:fresh_warning_modules.append(m)
   assert 'warning:' not in text
  else:
   assert prior is not None
   assert {k:v for k,v in rec.items() if k!='origin'}=={k:v for k,v in prior.items() if k!='origin'}
   assert rec['origin']=='phase22_checked' and obj.is_symlink() and obj.resolve()==oldobj.resolve()
  if m=='BusyBeaver.ZFC.L2Control219':assert 'warning:' not in text
  evidence.extend([pin(source),pin(obj),pin(Path(rec['log']))])
 assert fresh_warning_modules==[] and raw_absent==len((basis_raw_absent&set(rows))-forced)
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
  recorded_profiles(rec,text);assert all(set(ax)<=STD for _,ax in profiles(text))
  evidence.extend(pin(x) for x in [source,obj,log,raw])
 stdout=a.stdout.read_text();assert re.findall(r'^CHECK (\S+)$',stdout,re.M)==[m for m in rows if m in forced]
 assert re.findall(r'^REUSE (\S+) phase22_checked$',stdout,re.M)==[m for m in rows if m not in forced]
 assert re.findall(r'^AUDIT (\S+)$',stdout,re.M)==[r['module'] for r in q['audits']] and stdout.endswith(f'COMPLETE {count} {len(q["audits"])} audits\n')
 assert all(rows[m].get('warnings_forbidden',False) for m in forced)
 assert res['new_module_actual_profiles']=={m:profiles(Path(done[m]['log']).read_text()) for m in rows if m not in old}
 assert sum('KSites215Batch' in m for m in rows)==sum('KSites215Batch' in m for m in old)==9
 # Final reread prevents a mutable artifact changing during this readback.
 for item in evidence:assert sha(item['path'])==item['sha256']
 for path,h in before['inputs'].items():assert sha(path)==h,path
 for path in q['absent_inputs']:assert not Path(path).exists() and not Path(path).is_symlink(),path
 report={'status':'PASS_INDEPENDENT_ACTUAL_CANDIDATE_READBACK','auditor':pin(__file__),'check_directory':str(a.check),'result':pin(a.check/'result.json'),'basis_result':pin(a.basis/'result.json'),'plan':pin(a.plan),'runner':pin(a.runner),'outer':pin(a.outer),'freeze':pin(a.freeze),'providers':count,'projects':count-len(clients),'typed_clients':len(clients),'changed_Lean_sources':len(changed),'fresh':len(forced),'reuses':count-len(forced),'audits':len(audits),'client_reports':93,'WFTheory_reports':5,'audit_reports':10,'exact_profiles_preserved':True,'fresh_provider_warnings':0,'Control219_warnings':0,'fresh_client_audit_warnings':0,'reused_provider_warnings':sum(Path(done[m]['log']).read_text().count('warning:') for m in rows if m not in forced),'fresh_typed_clients':sorted(set(clients)&forced),'newly_retired_Lean_modules':sorted(retired),'newly_retired_producers':len(q['newly_retired_producers']),'basis_raw_records_absent_inherited':len(basis_raw_absent),'raw_records_present':raw_present,'raw_records_absent_inherited':raw_absent,'raw_records_without_object_hash_inherited':raw_without_object_hash,'historical_report_forms':'Comma-separated string and list axiom fields normalized only for exact comparison with compiler-log profiles; original records unchanged.','all_source_object_dependency_log_toolchain_bindings_checked':True,'owner_inputs_checked':len(before['inputs']),'present_inputs_checked':len(q['present_inputs']),'absences_checked':len(q['absent_inputs']),'fresh_site_or_forward_certificate_batches':[m for m in rows if m in forced and ('KSites215Batch' in m or 'KSource215FwdCheck' in m)],'scope':'Exact phase23 source-transitive selected closure of all accepted phase22 roots and fifteen maintained typed clients. Dynamic changed/fresh/reuse counts derive from the frozen source map; every fresh provider and audit has zero warnings. Historical basis source bytes bind checked workspace; 31 missing inherited basis raw records remain an accepted aggregate boundary, and no records are fabricated. Internal PA endpoint and minimum-state theorem remain open. No compiler or supplied code executed by this audit.'}
 a.output.write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'status':report['status'],'report':pin(a.output)},indent=2))
if __name__=='__main__':main()
