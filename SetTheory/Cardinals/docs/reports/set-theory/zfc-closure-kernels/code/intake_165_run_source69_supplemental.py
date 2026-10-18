from pathlib import Path
import json,os,shutil,signal,subprocess,time
plan=json.loads(Path('/tmp/zfc-intake-165-planning/execution-plan.json').read_text());S=Path(plan['package']);W=Path('/tmp/zfc-intake-165-source69-supplemental-run1');assert not W.exists();W.mkdir();records=[]
env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1');env.pop('PYTHONOPTIMIZE',None);env.pop('PYTHONPATH',None)
for job in plan['commands'][1:]:
 J=W/job['key'];J.mkdir();P=J/'package';shutil.copytree(S,P);cwd=P/job['cwd_relative_to_copy'];start=time.monotonic();timed_out=False
 with (J/'stdout.log').open('w') as out,(J/'stderr.log').open('w') as err:
  proc=subprocess.Popen(job['argv'],cwd=cwd,env=env,stdout=out,stderr=err,start_new_session=True)
  try:code=proc.wait(timeout=job['process_group_timeout_seconds'])
  except subprocess.TimeoutExpired:
   timed_out=True;os.killpg(proc.pid,signal.SIGTERM)
   try:code=proc.wait(timeout=5)
   except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);code=proc.wait()
 r=dict(key=job['key'],status='PASS' if code==0 and not timed_out else 'FAIL',copy=str(P),command=job['argv'],cwd=str(cwd),seconds=time.monotonic()-start,exit_code=code,timed_out=timed_out,timeout_seconds=job['process_group_timeout_seconds'],scope=job['scope'],stdout=str(J/'stdout.log'),stderr=str(J/'stderr.log'),postchecks=[])
 try:
  if r['status']=='PASS' and job['postcheck']:
   for path,expected in job['postcheck'].items():
    if path=='byte_equal_pairs':
     for a,b in expected:
      assert (cwd/a).read_bytes()==(cwd/b).read_bytes(),(a,b);r['postchecks'].append(dict(byte_equal=[a,b]))
    else:
     actual=json.loads((P/path).read_text())
     for k,v in expected.items():assert actual[k]==v,(k,actual[k],v)
     r['postchecks'].append(dict(path=path,fields=expected))
 except Exception as e:r['status']='FAIL';r['postcheck_error']=repr(e)
 (J/'execution.json').write_text(json.dumps(r,indent=2)+'\n');records.append(r)
 (W/'execution.json').write_text(json.dumps(dict(status='RUNNING',records=records),indent=2)+'\n');print(r['key'],r['status'],round(r['seconds'],3),flush=True)
 if r['status']!='PASS':break
status='PASS' if len(records)==8 and all(x['status']=='PASS' for x in records) else 'FAIL'
(W/'execution.json').write_text(json.dumps(dict(status=status,records=records,scope='Eight supplementary functional checks on independent disposable copies. No delivery-checksum audit, proof compilation, discovery search or TeX build.'),indent=2)+'\n');print(status,flush=True);raise SystemExit(0 if status=='PASS' else 1)
