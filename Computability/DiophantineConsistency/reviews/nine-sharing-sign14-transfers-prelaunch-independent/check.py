#!/usr/bin/env python3
"""Review seven sign14 supplied-gap transfer stages, without Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-transfers-check';draft=root/'research/nine-sharing-sign14-transfers-draft';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();run=p/'run.py';m=p/'source-manifest.json';assert sha(run)=='f6376c2be886405ca0939c5681cedcc522225599afe70e71dbcc009b6a518e1d' and sha(m)=='33d1e56e7842aeeffd4813250254db5880b5a5fbae701b3f8079ff92d03ddb46';rows=json.loads(m.read_text())['rows'];names=[f'Sign14Transfer{i:02}' for i in range(5)];assert [r['module'].split('.')[-1] for r in rows]==names
for i,(row,name) in enumerate(zip(rows,names)):
 src=p/'src/DiophantineConsistency'/(name+'.lean');s=src.read_text();assert sha(src)==sha(draft/(name+'.lean'))==row['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==row['imports']==['DiophantineConsistency.Sign14Coordinate'] and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit)\b',s)
 old=[0,2,3,4,5][i];assert f'SharingSeed15Degree124.row{old:02} p' in s and f'SharingSeed14Degree124.row{i:02} p' in s and '(hg : ι gap =' in s and 'Sign14Coordinate.lift v gap' in s
 if i==0:assert 'SharingSeed14Degree124.firstResidual p' in s and 'SharingSeed14Degree124.firstResidual p' in s
 else:assert f'(SharingSeed15Degree124.remainingResiduals p).drop {old-1}' in s and f'(SharingSeed14Degree124.remainingResiduals p).drop {i-1}' in s
r=run.read_text();assert "matches=[x for x in base['rows'] if x['module']==local]" in r and "'-M2800'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
check=root/'reviews/nine-sharing-sign14-coordinate-terminal-independent/check.py';assert sha(check)=='ee9182709cf07e2bbff7a63fd31866ebad1b8646273102353831d8492d9b3ee3';subprocess.run([sys.executable,'-I','-S','-B',str(check)],capture_output=True,check=True,timeout=120)
x=subprocess.run([sys.executable,'-I','-S','-B',str(run),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':5,'old_rows':[0,2,3,4,5],'new_rows':list(range(5)),'runner_sha256':sha(run),'scope':'five supplied-gap evaluation transfers; no Lean transfer/zero equivalence yet'},indent=2,sort_keys=True))
