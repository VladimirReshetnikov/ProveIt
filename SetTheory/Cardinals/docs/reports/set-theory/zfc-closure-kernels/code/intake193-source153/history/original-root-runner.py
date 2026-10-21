from pathlib import Path
import shutil,json,hashlib,subprocess,sys,time,os
P=Path(__file__).resolve().parent;plan=json.loads(Path('/tmp/zfc-intake193/small/replay-plan.json').read_text());COPY=P/'packet';OUT=P/'outputs';BASE=P/'baseline219';shutil.copytree(plan['jobs'][0]['package'],COPY);OUT.mkdir();BASE.mkdir();(P/'logs').mkdir()
for x in plan['baseline_inputs']:
 src=Path(x['host_file']);assert hashlib.sha256(src.read_bytes()).hexdigest()==x['sha256'];dst=BASE/x['relative_target'];dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst)
def expand(s):return s.replace('{COPY}',str(COPY)).replace('{OUT}',str(OUT)).replace('{BASE219}',str(BASE))
res={'status':'RUNNING','selected_names':[j['name']for j in plan['jobs']],'scope':'Six reviewed cheap selected leaves, no optional jobs, runtime, manifest or ancestor wrapper.','jobs':[]};env=dict(os.environ);env.pop('PYTHONOPTIMIZE',None);env['PYTHONDONTWRITEBYTECODE']='1'
for j in plan['jobs']:
 name=j['name'];cmd=[expand(s)for s in j['argv']];cmd[0]=sys.executable;cwd=expand(j['cwd']);start=time.monotonic()
 with(P/'logs'/(name+'.stdout')).open('w')as o,(P/'logs'/(name+'.stderr')).open('w')as e:
  try:r=subprocess.run(cmd,cwd=cwd,stdout=o,stderr=e,env=env,timeout=j['timeout']);rc=r.returncode;limit=False
  except subprocess.TimeoutExpired:rc=None;limit=True
 rec={'name':name,'argv':cmd,'cwd':cwd,'exit_code':rc,'timeout':limit,'timeout_seconds':j['timeout'],'seconds':time.monotonic()-start,'expected':j['expected']};res['jobs'].append(rec);res['status']='RUNNING'if rc==0 else'FAIL';(P/'actual.json').write_text(json.dumps(res,indent=2)+'\n');print(name,rc,flush=True)
 if rc!=0:break
else:res['status']='SIX_SELECTED_PROCESSES_EXIT_ZERO_PENDING_RESULT_AUDIT'
(P/'actual.json').write_text(json.dumps(res,indent=2)+'\n')
