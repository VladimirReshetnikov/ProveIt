from pathlib import Path
import subprocess,sys,time,json
P=Path(__file__).resolve().parent;cmd=[sys.executable,'-B',str(P/'search.py'),'--seed',str(P.parent/'run2/candidate.native.tm'),'--output',str(P/'run1'),'--seconds','110'];start=time.monotonic()
with(P/'run1.stdout').open('w')as o,(P/'run1.stderr').open('w')as e:
 try:r=subprocess.run(cmd,stdout=o,stderr=e,timeout=120);rc=r.returncode;limit=False
 except subprocess.TimeoutExpired:rc=None;limit=True
x={'argv':cmd,'exit_code':rc,'timeout':limit,'seconds':time.monotonic()-start,'external_seconds':120};(P/'execution.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x))
