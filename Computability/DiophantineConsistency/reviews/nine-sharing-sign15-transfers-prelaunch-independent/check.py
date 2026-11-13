#!/usr/bin/env python3
"""Review seven sign15 supplied-gap transfer stages, without Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign15-transfers-check';draft=root/'research/nine-sharing-sign15-transfers-draft';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();run=p/'run.py';m=p/'source-manifest.json';assert sha(run)=='d196205ca3ec27e108315fd2e2288966dd650c656ef113f7a174771914036a0c' and sha(m)=='c62146a1e56cbd20ad1cba16857289210ce830c69442885be58348d79cfc552c';rows=json.loads(m.read_text())['rows'];names=[f'Sign15Transfer{i:02}' for i in range(6)];assert [r['module'].split('.')[-1] for r in rows]==names
for i,(row,name) in enumerate(zip(rows,names)):
 src=p/'src/DiophantineConsistency'/(name+'.lean');s=src.read_text();assert sha(src)==sha(draft/(name+'.lean'))==row['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==row['imports']==['DiophantineConsistency.Sign15Coordinate'] and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit)\b',s)
 old=[0,1,2,3,5,6][i];assert f'SharingSeed16Degree112.row{old:02} p' in s and f'SharingSeed15Degree124.row{i:02} p' in s and '(hg : ι gap =' in s and 'Sign15Coordinate.lift v gap' in s
 if i==0:assert 'SharingSeed15Degree124.firstResidual p' in s and 'SharingSeed15Degree124.firstResidual p' in s
 else:assert f'(SharingSeed16Degree112.remainingResiduals p).drop {old-1}' in s and f'(SharingSeed15Degree124.remainingResiduals p).drop {i-1}' in s
r=run.read_text();assert "matches=[x for x in base['rows'] if x['module']==local]" in r and "'-M2800'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
check=root/'reviews/nine-sharing-sign15-coordinate-terminal-independent/check.py';assert sha(check)=='f406a76ea60ae3269e0e1f8b6b02561b7eb33acec8cd885128646af5f5280a76';subprocess.run([sys.executable,'-I','-S','-B',str(check)],capture_output=True,check=True,timeout=120)
x=subprocess.run([sys.executable,'-I','-S','-B',str(run),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':6,'old_rows':[0,1,2,3,5,6],'new_rows':list(range(6)),'runner_sha256':sha(run),'scope':'six supplied-gap evaluation transfers; no Lean transfer/zero equivalence yet'},indent=2,sort_keys=True))
