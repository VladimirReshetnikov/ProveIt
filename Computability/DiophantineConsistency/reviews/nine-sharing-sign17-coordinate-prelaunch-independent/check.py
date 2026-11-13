#!/usr/bin/env python3
"""Review conditional signed-coordinate source and staged provider routes."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';p=research/'nine-sharing-sign17-coordinate-check';draft=research/'nine-sharing-sign17-coordinate-draft';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();src=p/'src/DiophantineConsistency/Sign17Coordinate.lean';e,=json.loads((p/'source-manifest.json').read_text())['rows'];s=src.read_text();assert e['module']=='DiophantineConsistency.Sign17Coordinate' and sha(src)==sha(draft/src.name)==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports']==['DiophantineConsistency.SharingSign17Squares','DiophantineConsistency.SharingSign18Squares']
lift=s.split('def lift ',1)[1].split('![',1)[1].split(']',1)[0];drop=s.split('def drop ',1)[1].split('![',1)[1].split(']',1)[0];assert [x.strip() for x in lift.split(',')]==[f'v {i}' for i in range(18)]+['gap'] and [x.strip() for x in drop.split(',')]==[f'v {i}' for i in range(18)]
assert '((SharingSeed18Degree94.remainingResiduals p).drop 5).head? = some (oldD p)' in s and '(hg : ι gap = (ι (v 13) + 1) * (ι (v 13) + 1) - ι (v 17) * ι (v 17))' in s and all('theorem '+n in s for n in ('old_d_row','d_zero','old_gap','lift_drop'))
old=json.loads((research/'nine-sharing-sign18-degree94-root-candidate/seed.json').read_text())['residuals'];assert old[6]['gate']=='V2minusY2' and old[6]['expr']==['sub',['var',18],['sub',['mul',['add',['var',13],['num',1]],['add',['var',13],['num',1]]],['mul',['var',17],['var',17]]]]
assert not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit)\b',s)
runner=p/'run.py';assert sha(runner)=='bf605d34889338d66346d90f3355c61266541edc78393764a2fe94ae797ae988';r=runner.read_text();assert "if local=='SharingSign17Squares':" in r and "elif local in observed['observed']:" in r and "for name,rec in observed['observed'].items():" in r and "'-M2800'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
for review in ('nine-sharing-sign17-staged-syntax-terminal-independent','nine-sharing-sign18-staged-syntax-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/review/'check.py')],check=True,capture_output=True,timeout=120)
x=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(runner),'scope':'conditional signed-coordinate source; gap representative existence is an explicit hypothesis and not proved here'},indent=2,sort_keys=True))
