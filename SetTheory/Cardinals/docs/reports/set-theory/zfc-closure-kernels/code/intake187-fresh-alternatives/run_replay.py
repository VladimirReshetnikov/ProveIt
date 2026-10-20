from pathlib import Path
import argparse,hashlib,json,os,signal,subprocess,sys,time,traceback
ap=argparse.ArgumentParser(description='Run the prepared14 direct Source141 jobs serially, preserving raw logs and failures.')
ap.add_argument('--workdir',type=Path,required=True);args=ap.parse_args()
E=args.workdir.resolve();plan=json.loads((E/'plan.json').read_text())
assert not (E/'result.json').exists()
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for p,h in plan['inputs'].items():assert sha(p)==h,p
receipt=dict(status='RUNNING',plan_sha256=sha(E/'plan.json'),jobs=[],python=sys.version,scope=plan['scope'])
def save():
 temp=E/'result.tmp';temp.write_text(json.dumps(receipt,indent=2)+'\n');temp.replace(E/'result.json')
save()
env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1','TMPDIR':str(E/'scratch')};env.pop('PYTHONOPTIMIZE',None);env.pop('PYTHONPATH',None)
try:
 for j in plan['jobs']:
  name=j['name'];print('START',name,flush=True);start=time.monotonic();out=E/'logs'/(name+'.stdout.log');err=E/'logs'/(name+'.stderr.log');timed=False
  with out.open('xb') as so,err.open('xb') as se:
   p=subprocess.Popen(j['argv'],cwd=j['cwd'],env=env,stdout=so,stderr=se,start_new_session=True)
   try:code=p.wait(timeout=j['timeout_seconds'])
   except subprocess.TimeoutExpired:
    timed=True;os.killpg(p.pid,signal.SIGKILL);code=p.wait()
  rec={**j,'returncode':code,'timed_out':timed,'seconds':time.monotonic()-start,'stdout':str(out),'stdout_sha256':sha(out),'stderr':str(err),'stderr_sha256':sha(err)}
  receipt['jobs'].append(rec);save();print('END',name,code,round(rec['seconds'],3),flush=True)
  assert code==0 and not timed,name
 for p,h in plan['inputs'].items():assert sha(p)==h,p
 C=Path(plan['packet']);O=E/'output';comparisons=[]
 for n in ('zero_terminal','retagged','composed'):
  for f in ('k219.native.tm','k219.tm','k219.upstream-labels.tm','sites.json','canonicalization.json'):
   a=O/'machine'/n/f;b=C/'machine'/n/f;assert a.read_bytes()==b.read_bytes(),(n,f);comparisons.append({'variant':n,'file':f,'sha256':sha(a)})
  fresh=O/'certificates'/n;delivered=C/'certificates'/n
  for f in ('source.json','startup.json','cases.json','canonical.tm'):
   assert (fresh/f).read_bytes()==(delivered/f).read_bytes(),(n,f);comparisons.append({'variant':n,'file':f,'sha256':sha(fresh/f)})
  a=json.loads((fresh/'runtime.json').read_text());b=json.loads((delivered/'runtime.json').read_text());a.pop('seconds');b.pop('seconds');assert a==b,(n,'runtime except seconds')
 receipt.update(status='FRESH_DIRECT_LEAVES_PASS',input_pins_after_unchanged=True,exact_delivered_comparisons=comparisons,runtime_records_equal_except_elapsed_seconds=True)
except BaseException as exc:
 receipt.update(status='FAILED',error=repr(exc),traceback=traceback.format_exc());save();raise
save();print(receipt['status'],len(receipt['jobs']),flush=True)
