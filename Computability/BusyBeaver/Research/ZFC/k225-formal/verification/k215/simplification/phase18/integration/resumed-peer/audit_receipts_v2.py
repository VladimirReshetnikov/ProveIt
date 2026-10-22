"""Independent read-only terminal receipt audit; no compiler, generator or helper execution."""
from pathlib import Path
from collections import Counter
import hashlib,json,re,copy
O=Path('/tmp/k215-phase18-resumed-peer');C=Path('/tmp/k215-phase18-check');D=C/'build-run1';T=Path('/tmp/k215-phase18-budget-transition');P=Path('/tmp/k215-phase17-check/build-run1');I=Path('/tmp/k215-phase18-session-interruption')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();rd=lambda p:json.loads(Path(p).read_bytes())
RUNNER='71bd42b1cad2f485581620bb9b8c7d196e30447a101546077767642d065e0c1a';PLAN='df0dbde51be55370f466af3a61f777f81ecda2748b319396a3270f8ff1026977';OLD_RUNNER='6d36aefb6bfffe718ae244dd954de5a9c6e9e67d738daff2436eb0a2428f9a19';STD={'propext','Classical.choice','Quot.sound'}
# Deliberate first gate: this file is not a running-build monitor.
outer=rd(C/'resume2-outer.json');assert outer['status']=='PASS_EXIT_ZERO'and outer['exit_code']==0
assert outer['argv']==['python3','-B',str(C/'build-forward-budget.py'),'--map',str(C/'plan.json'),'--out',str(D)]
assert sha(C/'build-forward-budget.py')==RUNNER and sha(C/'plan.json')==PLAN and sha(C/'build.py')==OLD_RUNNER
assert outer['stdout_sha256']==sha(C/'resume2.stdout')and outer['stderr_sha256']==sha(C/'resume2.stderr')and not(C/'resume2.stderr').read_bytes()
assert outer['freeze_sha256']==sha(C/'resume2-freeze.json')and outer['launcher_sha256']==sha('/tmp/k215-phase18-integration/run_detached_resume.py')and outer['interruption_sha256']==sha(I/'interruption.json')
freeze=rd(C/'resume2-freeze.json')
for p,h in freeze['files'].items():assert sha(p)==h,p
transition=rd(T/'transition.json');assert transition['status']=='RESOURCE_ONLY_OWNER_MIGRATION'and sha(T/'transition.json')=='eeecb22d1b01c2b1ef8ada73ae902fb3ebebc724149d5f4d87521a9428e80ede'
for p,row in transition['snapshots'].items():assert sha(row['snapshot'])==row['sha256']

assert sha(I/'interruption.json')=='85d5000b71ec39a0f07612f695a5a6b55014fd9603df17e336542e3435fe381f'
interruption=rd(I/'interruption.json');middle=rd(I/'original/build-run1/completed.json')
assert interruption['observed_executor_exit_code']==143 and interruption['compiler_exit_status_known']is False and not(C/'resume-outer.json').exists()
assert len(middle)==153 and Counter(r['origin']for r in middle.values())=={'candidate_fresh':69,'phase17_checked':84}
for p,row in interruption['snapshots'].items():assert sha(row['snapshot'])==row['sha256']
assert sha(D/'before.json')==interruption['before_sha256']and sha(I/'original/build-run1/completed.json')==interruption['completed_sha256']
partial=rd(I/'original/build-run1/attempts/071-BusyBeaver.ZFC.KSites215Batch002/record.json')
assert partial['status']=='COMPILING'and 'exit_code'not in partial and 'object_sha256'not in partial and not Path(partial['log']).read_bytes()
assert interruption['physical_unaccepted_object']=={'present':True,'sha256':'bde2c88e3d361922a1caac548d75b68dfe81e97c4b18d320363460b29ab79ea6','accepted':False}
assert rd(C/'resume2-launcher.stdout')==outer and not(C/'resume2-launcher.stderr').read_bytes()
oldbefore=rd(T/'original/build-run1/before.json');before=rd(D/'before.json');expected=copy.deepcopy(oldbefore);expected['runner_sha256']=RUNNER
assert expected['inputs'].pop(str(C/'build.py'))==OLD_RUNNER;expected['inputs'][str(C/'build-forward-budget.py')]=RUNNER;assert expected==before
oldsource=(C/'build.py').read_text();newsource=(C/'build-forward-budget.py').read_text();assert oldsource.replace("timeout=900 if 'KSites215Batch' in m else 120","timeout=900 if 'KSites215Batch' in m or 'KSource215FwdCheck' in m else 120",1)==newsource
plan=rd(C/'plan.json');inventory=rd(D/'inventory.json');result=rd(D/'result.json');done=rd(D/'completed.json');rows=plan['modules'];selected={r['module']:r for r in rows};initial=rd(T/'original/build-run1/completed.json')
assert result['status']=='PASS'and result['runner_sha256']==RUNNER and result['map_sha256']==PLAN
assert result['inventory_sha256']==sha(D/'inventory.json')and result['completed_sha256']==sha(D/'completed.json')
assert result['source_transitive_reuse_only']and result['all_source_object_dependency_log_toolchain_inputs_postchecked']
assert inventory=={'modules':rows,'targets':plan['targets'],'external_imports':['Init']}and len(done)==len(rows)==len(selected)==214 and set(done)==set(selected)
assert len(initial)==23 and Counter(r['origin']for r in initial.values())=={'candidate_fresh':18,'phase17_checked':5}
assert all(done[m]==r for m,r in initial.items())and all(done[m]==r for m,r in middle.items())
assert sha(P/'result.json')=='0ece73d070ab23aee17cf6067d9b9850bd657f1c63523c0567c1fe4ced66f1ee'
oldinv=rd(P/'inventory.json');oldrows={r['module']:r for r in oldinv['modules']};old=rd(P/'completed.json');assert len(old)==len(oldrows)==213
assert set(selected)==set(old)|{'MacroSharing18Api'}and result['targets']==before['targets']==plan['targets']
assert rd(D/'toolchain.json')==rd(P/'toolchain.json')
for tool in rd(D/'toolchain.json').values():
 if isinstance(tool,dict)and 'path'in tool and 'sha256'in tool:assert sha(tool['path'])==tool['sha256']
profiles=lambda s:[[n,sorted({v.strip()for v in ax.split(',')if v.strip()})]for n,ax in re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",s)]
fresh=[];reused=[];warnings=[];clients=[];allreports={};fresh_details=[]
roots=[Path('/home/codex/.codex/worktrees/ec20/Proofs')/r for r in ['Computability/BusyBeaver/Lean','Logic/FirstOrder/Lean','SetTheory/ZF/Lean','SetTheory/BoundedConsistency/Lean']]
for row in rows:
 m=row['module'];rec=done[m];workspace=D/'workspace'/(m.replace('.','/')+'.lean');obj=D/'objects'/(m.replace('.','/')+'.olean');text=Path(rec['log']).read_text();actual=profiles(text)
 assert rec['status']=='PASS'and rec.get('exit_code',0)==0 and not rec.get('timed_out',False)
 assert sha(row['source'])==sha(workspace)==row['source_sha256']==rec['source_sha256']and sha(obj)==rec['object_sha256']and sha(rec['log'])==rec['log_sha256']
 assert rec['dependencies']=={dep:done[dep]['object_sha256']for dep in row['imports']if dep!='Init'}
 assert actual==row['expected_reports']and all(set(a)<=STD for _,a in actual)and 'sorryAx'not in text and 'error('not in text and 'error:'not in text
 allreports[m]=actual
 if m in old:
  assert actual==profiles(Path(old[m]['log']).read_text())
  oldworkspace=P/'workspace'/(m.replace('.','/')+'.lean');oldobj=P/'objects'/(m.replace('.','/')+'.olean')
  assert sha(oldworkspace)==oldrows[m]['source_sha256']==old[m]['source_sha256']and sha(oldobj)==old[m]['object_sha256']and sha(old[m]['log'])==old[m]['log_sha256']
 canonical=[r/(m.replace('.','/')+'.lean')for r in roots if(r/(m.replace('.','/')+'.lean')).exists()]
 if canonical:assert len(canonical)==1 and canonical[0]==Path(row['source'])
 else:
  clients.append(m);assert row['warnings_forbidden']and 'warning:'not in text
  if m in old:assert row['source_sha256']==oldrows[m]['source_sha256']
 messages=[s.split('warning:',1)[1].strip()for s in text.splitlines()if'warning:'in s];assert len(messages)==rec.get('warnings',len(messages))
 if messages:warnings.append({'module':m,'origin':rec['origin'],'count':len(messages),'headlines':messages,'all_preexisted_in_same_module':m in old and all(s in Path(old[m]['log']).read_text()for s in messages),'log_sha256':rec['log_sha256']})
 if rec['origin']=='candidate_fresh':
  fresh.append(m);raw=Path(rec['log']).with_name('record.json');assert rd(raw)==rec and not obj.is_symlink()and rec['reports']==actual
  assert sha(raw.parent/workspace.name)==row['source_sha256']and rec['candidate']==row['source']
  assert rec['command']==[str(Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')),'-j1','-M12288','--root='+str(D/'workspace'),'-o',str(obj),str(workspace)]
  expected_budget=120 if m in initial else(900 if'KSites215Batch'in m or'KSource215FwdCheck'in m else 120)
  assert rec['timeout_seconds']==expected_budget and rec['memory_mebibytes']==12288
  assert rec['compiler_sha256']=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'and rec['helper_sha256']=='a3cf7cc38004bca5e2a2df10c607fe5353896c0454069b4ff24d6b5176c32fbd'
  fresh_details.append({'module':m,'attempt':raw.parent.name,'budget':rec['timeout_seconds'],'seconds':rec['seconds'],'source_sha256':rec['source_sha256'],'log_sha256':rec['log_sha256']})
 else:
  reused.append(m);assert m in old and rec=={**old[m],'origin':'phase17_checked'}and obj.is_symlink()and obj.resolve()==(P/'objects'/(m.replace('.','/')+'.olean')).resolve()
assert len(fresh)==107 and len(reused)==107 and result['fresh_modules']==fresh and result['reused_modules']==reused and len(clients)==15
assert set(fresh)==set(plan['expected']['fresh_by_source_transitivity'])
assert 'MacroNamespace18Probe'not in selected and 'MacroSharing18Api'in clients
oldclients=set(clients)-{'MacroSharing18Api'};assert len(oldclients)==14 and sum(len(allreports[m])for m in oldclients)==83
baseline=rd('/tmp/k215-phase18-clients/baseline-run3/MacroSharing18Api/record.json');assert baseline['status']=='PASS'and allreports['MacroSharing18Api']==profiles(Path(baseline['log']).read_text())and selected['MacroSharing18Api']['source_sha256']==baseline['source_sha256']
assert len(allreports['MacroSharing18Api'])==10 and len(allreports['BusyBeaver.ZFC.WFTheory'])==5
assert result['new_module_actual_profiles']=={'MacroSharing18Api':allreports['MacroSharing18Api']}
assert len(result['audits'])==2;auditreports=[]
for row,rec in zip(plan['audits'],result['audits']):
 name=row['module'];directory=D/('audit-'+name);source=directory/(name+'.lean');text=Path(rec['log']).read_text();actual=profiles(text)
 assert rec['module']==name and rec['status']=='PASS'and rec['exit_code']==0 and not rec['timed_out']and rec['warnings']==0 and 'warning:'not in text and 'sorryAx'not in text
 assert rd(directory/'record.json')==rec and sha(row['source'])==sha(source)==row['source_sha256']==rec['source_sha256']and sha(source.with_suffix('.olean'))==rec['object_sha256']and sha(rec['log'])==rec['log_sha256']
 assert rec['dependencies']=={m:r['object_sha256']for m,r in done.items()}and actual==row['expected_reports']==rec['reports'];auditreports.extend(actual)
 assert rec['command']==['/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-j1','-M12288','--root='+str(directory),'-o',str(source.with_suffix('.olean')),str(source)]
 assert rec['origin']=='candidate_fresh_audit'and rec['timeout_seconds']==120 and rec['memory_mebibytes']==12288
 assert rec['compiler_sha256']=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'and rec['helper_sha256']=='a3cf7cc38004bca5e2a2df10c607fe5353896c0454069b4ff24d6b5176c32fbd'
assert len(auditreports)==10
failedname='019-BusyBeaver.ZFC.KSource215FwdCheck12';failed=rd(D/'attempts'/failedname/'record.json');assert failed==rd(T/'original/build-run1/attempts'/failedname/'record.json')
assert failed['status']=='FAIL'and failed['exit_code']==-9 and failed['timed_out']and failed['object_sha256']is None and not Path(failed['log']).read_bytes()
retry=done[failed['module']];assert Path(retry['log']).parent.name=='020-BusyBeaver.ZFC.KSource215FwdCheck12'and retry['status']=='PASS'and retry['timeout_seconds']==900
for key in ['source_sha256','candidate','dependencies','command']:assert failed[key]==retry[key]
partialname='071-BusyBeaver.ZFC.KSites215Batch002';assert rd(D/'attempts'/partialname/'record.json')==partial
retry2=done[partial['module']];assert Path(retry2['log']).parent.name=='072-BusyBeaver.ZFC.KSites215Batch002'and retry2['status']=='PASS'
for key in ['source_sha256','candidate','dependencies','command','timeout_seconds']:assert partial[key]==retry2[key]
attempts=sorted((D/'attempts').iterdir());assert len(attempts)==109 and {p.name for p in attempts if rd(p/'record.json')['status']!='PASS'}=={failedname,partialname}
assert {int(p.name.split('-',1)[0])for p in attempts}==set(range(1,110))
assert {str(Path(done[m]['log']).parent)for m in fresh}=={str(p)for p in attempts if p.name not in{failedname,partialname}}
initialstdout=(C/'build.stdout').read_text();middlestdout=(C/'resume.stdout').read_text();resumestdout=(C/'resume2.stdout').read_text()
assert len(re.findall(r'(?m)^CHECK ',initialstdout))==19 and len(re.findall(r'(?m)^REUSE ',initialstdout))==5
assert len(re.findall(r'(?m)^CHECK ',middlestdout))==52 and len(re.findall(r'(?m)^PASS ',middlestdout))==51 and len(re.findall(r'(?m)^REUSE ',middlestdout))==79
assert len(re.findall(r'(?m)^CHECK ',resumestdout))==38 and len(re.findall(r'(?m)^REUSE ',resumestdout))==23 and resumestdout.rstrip().endswith('COMPLETE 214 2 audits')
checks=lambda s:re.findall(r'(?m)^CHECK (\S+)$',s)
reuses=lambda s:re.findall(r'(?m)^REUSE (\S+) ',s)
assert checks(initialstdout)[:-1]+checks(middlestdout)[:-1]+checks(resumestdout)==fresh
assert reuses(initialstdout)+reuses(middlestdout)+reuses(resumestdout)==reused
assert len(before['inputs'])==1084 and len(plan['present_inputs'])==39 and len(plan['absent_inputs'])==8
for p,h in before['inputs'].items():assert sha(p)==h,p
for p in plan['absent_inputs']:assert not Path(p).exists()and not Path(p).is_symlink()
site=[r for r in fresh_details if'KSites215Batch'in r['module']];assert len(site)==9
summary={'status':'PASS_INDEPENDENT_TERMINAL_TWICE_RESUMED_ACTUAL_READBACK','result_sha256':sha(D/'result.json'),'outer_sha256':sha(C/'resume2-outer.json'),'runner_sha256':RUNNER,'plan_sha256':PLAN,'transition_sha256':sha(T/'transition.json'),'resource_resume_freeze_sha256':sha(C/'resume-freeze.json'),'resume2_freeze_sha256':sha(C/'resume2-freeze.json'),'interruption_sha256':sha(I/'interruption.json'),'providers':214,'project_modules':199,'typed_clients':15,'fresh_providers':107,'reuses':107,'retained_provider_records':23,'provider_compiler_invocations':109,'failed_invocations':1,'interrupted_compiler_invocations_unknown_exit':1,'retained_before_detached':153,'interrupted_executor_exit_code':143,'unaccepted_partial_object_preserved_as_metadata_only':True,'audit_invocations':2,'old_client_reports':83,'macro_reports':10,'WFTheory_reports':5,'endpoint_audit_reports':auditreports,'site_batches':site,'warning_occurrences':sum(r['count']for r in warnings),'fresh_warning_occurrences':sum(r['count']for r in warnings if r['origin']=='candidate_fresh'),'reused_warning_occurrences':sum(r['count']for r in warnings if r['origin']!='candidate_fresh'),'all_fresh_warning_headlines_preexisted':all(r['all_preexisted_in_same_module']for r in warnings if r['origin']=='candidate_fresh'),'warnings':warnings,'client_and_audit_warnings':0,'detached_resume_seconds':outer['seconds'],'own_helper_sha256':sha(__file__),'fresh_receipts':fresh_details,'actual_auditor_executed_by_peer':False,'compiler_generator_captured_helper_or_supplied_code_executed':False,'canonical_or_frozen_writes':False,'scope':'Exact current 215 selected sources and 15 required clients; optional namespace failure remains excluded and disclosed. No other-variant full-stack, PA or minimum-state claim.'}
(O/'actual-readback-v2.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps({k:v for k,v in summary.items()if k not in ['fresh_receipts','warnings','site_batches','endpoint_audit_reports']},indent=2))
