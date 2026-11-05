#!/usr/bin/env python3
"""Install one successful private stage output in the coherent overlay; does not invoke Lean."""
import sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
import hashlib,json,shutil,os
from pathlib import Path
HERE=Path(__file__).resolve().parent;TASK=HERE.parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
    if not b:raise RuntimeError(m)
need(len(sys.argv)==3 and sys.argv[1] in ('1','2','3','4','5') and sys.argv[2].isdigit(),'need stage and actual observed session id')
n=int(sys.argv[1]);sid=int(sys.argv[2]);d=json.loads((HERE/'survey-result-snapshot.json').read_text());name=d['minimal_extra_order'][n];short=name.split('.')[-1]
root=Path(f'/tmp/current2011-ordinary94-stage{n:02d}-check02' if n==5 else f'/tmp/current2011-ordinary94-stage{n:02d}-check01');receipt=root/'result.json';r=json.loads(receipt.read_text())
need(r['status']=='PASS' and r['exit']==0 and r['guards_stable'] and r['stop_reason'] is None,'stage not PASS')
obj=root/(short+'.olean');need(obj.is_file() and sha(obj)==r['object_sha256'],'object mismatch')
target=Path('/tmp/current2011-ordinary94-six-overlay-20261105/lib')/(name.replace('.','/')+'.olean')
need(not os.path.lexists(target),'target exists')
with obj.open('rb') as i,target.open('xb') as o:shutil.copyfileobj(i,o)
need(sha(target)==sha(obj),'install mismatch')
out=HERE/f'attempt{n:02d}';out.mkdir(exist_ok=False)
shutil.copyfile(receipt,out/'result.json');shutil.copyfile(root/'compile.log',out/'compile.log')
record={'session_id':sid,'observed_outer_exit':0,'observation':'functions.write_stdin terminal result','module':name,'installed_sha256':sha(target),'installed_path':str(target)}
(out/'outer-observation.json').write_text(json.dumps(record,indent=2,sort_keys=True)+'\n')
print(json.dumps(record,sort_keys=True))
