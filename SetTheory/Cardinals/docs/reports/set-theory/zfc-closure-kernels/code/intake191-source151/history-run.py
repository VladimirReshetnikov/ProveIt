from pathlib import Path
import subprocess,json,time,concurrent.futures,sys
P=Path(__file__).resolve().parent;R=P/'packet';jobs=[('omit-runtime',[sys.executable,'-B','code/replay_runtime.py','omit-zero','--output',str(P/'omit-runtime')]),('dmn-runtime',[sys.executable,'-B','code/replay_runtime.py','dmn','--output',str(P/'dmn-runtime')])]
def run(item):
 name,cmd=item;start=time.monotonic()
 with (P/(name+'.stdout')).open('w')as o,(P/(name+'.stderr')).open('w')as e:
  try:r=subprocess.run(cmd,cwd=R,stdout=o,stderr=e,timeout=360);rc=r.returncode;limit=False
  except subprocess.TimeoutExpired:rc=None;limit=True
 out={'job':name,'argv':cmd,'cwd':str(R),'returncode':rc,'timeout':limit,'seconds':time.monotonic()-start}
 (P/(name+'.execution.json')).write_text(json.dumps(out,indent=2)+'\n');return out
with concurrent.futures.ThreadPoolExecutor(max_workers=2)as pool:
 result=list(pool.map(run,jobs))
(P/'executions.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
