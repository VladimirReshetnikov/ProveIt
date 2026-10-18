from pathlib import Path
import os,sys,shutil,subprocess,time,signal,json,hashlib
origin=Path('/tmp/zfc244-248bc05936-inspection/zfc244-compensated-routing-20261018')
root=Path(__file__).resolve().parent
mode=sys.argv[1]; assert mode in ('portable','full-runtime')
out=root/mode;out.mkdir(exist_ok=False); package=out/'package';shutil.copytree(origin,package)
# Omit only the integrity manifest in the disposable copy; intake excludes manifest checking.
manifest=package/'SHA256SUMS'
if manifest.exists(): manifest.unlink()
assert not manifest.exists()
if mode=='portable': command=[sys.executable,'-B','verify.py','--output',str(out/'verification.json')]
else: command=[sys.executable,'-B','runtime/code/full_symbolic_parametric.py','--table','runtime/candidate_1_244_old.tm','--all-values','--sites','runtime/certificate/sites_physical.json','--output',str(out/'verification.json')]
env=os.environ.copy();env.pop('PYTHONOPTIMIZE',None);env.pop('PYTHONPATH',None);env['PYTHONDONTWRITEBYTECODE']='1'
started=time.monotonic();timeout=180 if mode=='portable' else 600
with (out/'stdout.log').open('wb') as stdout,(out/'stderr.log').open('wb') as stderr:
 process=subprocess.Popen(command,cwd=package,env=env,stdout=stdout,stderr=stderr,start_new_session=True)
 try: code=process.wait(timeout=timeout);timedout=False
 except subprocess.TimeoutExpired:
  os.killpg(process.pid,signal.SIGKILL);code=process.wait();timedout=True
rec={'mode':mode,'command':command,'cwd':str(package),'returncode':code,'timed_out':timedout,'wall_seconds':time.monotonic()-started,'process_group_limit_seconds':timeout,'manifest_omitted_in_disposable_copy':True,'supplied_sources_unchanged':True,'proof_compiler_invoked':False,'stdout':str(out/'stdout.log'),'stderr':str(out/'stderr.log')}
if code==0:
 result=json.loads((out/'verification.json').read_text())
 if mode=='portable':
  assert result['status']=='PASS_PORTABLE_244_CONSTRUCTION' and result['working_states']==244 and result['binary_rows']==488
  assert result['direct_local_proof_replayed'] and result['independent_local_proof_replayed'] and result['blank_steps']==407951
  assert not result['full_runtime_replayed_in_this_invocation'] and result['runtime_dependency_smoke_cases']==1
 else:
  archived=json.loads((origin/'runtime/candidate_1_full_symbolic.json').read_text())
  assert {k:v for k,v in result.items() if k!='seconds'}=={k:v for k,v in archived.items() if k!='seconds'}
  assert result['status']=='PASS' and result['complete'] and result['counts']=={'cases':8391,'symbolic_rules':2315075}
  assert len(result['rows'])==488 and result['minimum_steps']==13 and result['positive_progress_checked']
 rec['semantic_postchecks']='PASS';rec['result_sha256']=hashlib.sha256((out/'verification.json').read_bytes()).hexdigest()
(out/'execution.json').write_text(json.dumps(rec,indent=2)+'\n')
print(json.dumps(rec),flush=True)
assert code==0 and not timedout
