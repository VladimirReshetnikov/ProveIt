#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2]; repo=root.parents[1]; p=root/'research/nine-sharing-sign14-zero-assembly-retry03-check'; old=root/'research/nine-sharing-sign14-zero-assembly-retry02-check'; sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='2f2eeefa4e66ece2a2bb90a8e9cbe21ad5cbef2c7acfc6b71bf44b93c84ea9ee'
assert sha(p/'source-manifest.json')=='7e1ce42cdbb69e2ec2658bd481522778e423e7e367c7ae557e4fddfc65a81e02'
rows=json.loads((p/'source-manifest.json').read_text())['rows']; oldrows=json.loads((old/'source-manifest.json').read_text())['rows']; assert len(rows)==len(oldrows)==2
for row,prev,name in zip(rows,oldrows,['Sign14ForwardBridge','Sign14ReverseBridge']):
 assert row['module']==prev['module']=='DiophantineConsistency.'+name and row['imports']==prev['imports']
 src=p/'src/DiophantineConsistency'/(name+'.lean'); source=src.read_text(); prior=(old/'src/DiophantineConsistency'/(name+'.lean')).read_text()
 before='SharingSign14Squares.seed_zero_iff_residuals p (Sign14Coordinate.lift v gap)' if name=='Sign14ForwardBridge' else 'SharingSign14Squares.seed_zero_iff_residuals p\n    (Sign14Coordinate.lift (Sign14Coordinate.drop v) (v 15))'; after=before.replace('SharingSign14Squares','SharingSign15Squares'); assert prior.count(before)==1 and prior.replace(before,after)==source; assert source.count('SharingSign14Squares.seed_zero_iff_residuals')==1 and source.count('SharingSign15Squares.seed_zero_iff_residuals')==1
 assert sha(src)==sha(repo/row['source'])==row['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',source,re.M)==row['imports']
 assert not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b',source)
r=(p/'run.py').read_text(); assert "'-M2800'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
assert all(s in r for s in ('failed state pin','failed outer pin','failed log pin','retry failure state pin','retry failure outer pin','second retry failure log pin'))
check=root/'reviews/nine-sharing-sign14-zero-assembly-retry02-terminal-independent/check.py'; assert sha(check)=='f7a243d764d0c5b8587562aecca2882561363f94f93571f33db3d5d8b78ff943'; subprocess.run([sys.executable,'-I','-S','-B',str(check)],capture_output=True,check=True,timeout=120)
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180); assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':2,'scope':'conditional pointwise forward/reverse zero assembly; existential iff separate'},indent=2))
