"""Read only the eleven phase21 contexts already reported terminal FAIL by root."""
import hashlib,json
from pathlib import Path
D=Path('/tmp/k215-phase21-actual-peer');out=D/'failed-contexts-read-v7.json'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
pin=lambda p:{'path':str(p),'sha256':sha(p),'bytes':Path(p).stat().st_size}
assert not out.exists()
rows=[]
for n in range(1,12):
 parent=Path('/tmp/k215-phase21-check'+('' if n==1 else f'-v{n}'));check=parent/'candidate-build-run1'
 outer=parent/'candidate-build-outer.json';o=json.loads(outer.read_text());freeze=parent/'freeze.json';plan=parent/'candidate-plan.json'
 assert o['status']=='FAIL' and o['exit_code']==1 and o['freeze_sha256']==sha(freeze)
 assert o['stdout_sha256']==sha(parent/'candidate-build.stdout') and o['stderr_sha256']==sha(parent/'candidate-build.stderr')
 assert not (check/'result.json').exists()
 f=json.loads(freeze.read_text());assert f['files'][str(plan)]==sha(plan)
 raw=[]
 for p in check.rglob('record.json'):
  r=json.loads(p.read_text());assert r['timed_out']==(n==6 and r['status']=='FAIL')
  if r['status']!='PASS':
   assert r['status']=='FAIL' and r['exit_code']==(-9 if n==6 else 1) and r['module']==('BusyBeaver.ZFC.AXWord' if n==1 else 'BusyBeaver.ZFC.L2Axioms254' if n in [8,9,10,11] else 'BusyBeaver.ZFC.L2Root254')
   log=Path(r['log']);text=log.read_text();assert sha(log)==r['log_sha256']
   if n==6:assert r['object_sha256'] is None and not (check/'objects/BusyBeaver/ZFC/L2Root254.olean').exists() and text==''
   raw.append({'timed_out':r['timed_out'],'exit_code':r['exit_code'],'seconds':r['seconds'],'record':pin(p),'log':pin(log),'module':r['module'],'errors':[x for x in text.splitlines() if 'error:' in x],'warning_count':text.count('warning:')})
 assert len(raw)==1
 rows.append({'attempt':n,'outer':pin(outer),'freeze':pin(freeze),'plan':pin(plan),'failed_provider':raw[0]})
assert [x['failed_provider']['warning_count'] for x in rows]==[0,7,7,0,0,0,7,0,0,0,0]
report={'status':'PASS_TERMINAL_FAILURE_CONTEXTS_PRESERVED','reader':pin(__file__),'contexts':rows,'all_exit_one':True,'provider_timeouts':[6],'timeout_seconds':120,'timeout_had_no_object':True,'no_accepted_result_in_any_failed_context':True,'scope':'Only historical attempts 1 through 11 that root had already reported terminal FAIL were read. No current/nonterminal output, compiler, supplied code, or canonical file was executed or changed.'}
with out.open('x') as f:json.dump(report,f,indent=2);f.write('\n')
print(json.dumps({'status':report['status'],'report':pin(out)},indent=2))
