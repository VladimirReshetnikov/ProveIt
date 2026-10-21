from pathlib import Path
import json,subprocess,time,concurrent.futures,sys
P=Path(__file__).resolve().parent;COPY=P/'packet';OUT=P/'outputs';OUT.mkdir()
plan=json.loads(Path('/tmp/zfc-intake191-review-investigation/replay-plan.json').read_text())
jobs=[j for j in plan['jobs']if j['name']!='core-quick']
def expand(s):return s.replace('{COPY}',str(COPY)).replace('{OUT}',str(OUT))
def run(j):
 name=j['name'];cmd=[expand(s)for s in j['argv']];cmd[0]=sys.executable;cwd=expand(j['cwd']);start=time.monotonic()
 with (P/(name+'.stdout')).open('w')as o,(P/(name+'.stderr')).open('w')as e:
  try:r=subprocess.run(cmd,cwd=cwd,stdout=o,stderr=e,timeout=j['timeout']);rc=r.returncode;limit=False
  except subprocess.TimeoutExpired:rc=None;limit=True
 rec={'name':name,'argv':cmd,'cwd':cwd,'returncode':rc,'timeout':limit,'seconds':time.monotonic()-start,'expected':j['expected']};(P/(name+'.execution.json')).write_text(json.dumps(rec,indent=2)+'\n');return rec
with concurrent.futures.ThreadPoolExecutor(max_workers=2)as pool:result=list(pool.map(run,jobs))
(P/'executions.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
