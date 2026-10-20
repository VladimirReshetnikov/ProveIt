from pathlib import Path
import json,subprocess,sys,time
ROOT=Path(__file__).resolve().parent
comparison=json.loads((ROOT/'comparison.json').read_text());runs=[]
for n,r in comparison['variants'].items():
 for suffix,p in [('',r['original_path']),('-row157',r['row157_stack_path'])]:
  name=n+suffix;out=ROOT/('shifted-'+name);cmd=[sys.executable,'-B',str(ROOT/'search_shifted.py'),'--name',name,'--table',p,'--output',str(out),'--seconds','110'];start=time.monotonic()
  with(ROOT/('shifted-'+name+'.log')).open('w')as log:
   try:rc=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT,timeout=120).returncode;timeout=False
   except subprocess.TimeoutExpired:rc=None;timeout=True
  entry={'name':name,'command':cmd,'exit_code':rc,'timeout':timeout,'seconds':time.monotonic()-start};runs.append(entry);(ROOT/'shifted-executions.json').write_text(json.dumps(runs,indent=2)+'\n')
  print(json.dumps(entry),flush=True)
  if rc!=0:break
  result=json.loads((out/'result.json').read_text())
  if any(x['exit_code']==0 for x in result['survivors']):print('CERTIFIED_SURVIVOR_STOP',name,flush=True);break
