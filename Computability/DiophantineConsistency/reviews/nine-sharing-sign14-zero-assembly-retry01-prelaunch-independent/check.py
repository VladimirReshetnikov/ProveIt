#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2]; repo=root.parents[1]; p=root/'research/nine-sharing-sign14-zero-assembly-retry01-check'; old=root/'research/nine-sharing-sign14-zero-assembly-check'; sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='c62733c0ee1f4b2a3a8db5f78c563bb072ea525a5df9aa7e39f353166fb2a430'
assert sha(p/'source-manifest.json')=='75fed7e92926a518721fd5d14fdbb1e7e00eabb735dc4f1515500a569458d40f'
rows=json.loads((p/'source-manifest.json').read_text())['rows']; oldrows=json.loads((old/'source-manifest.json').read_text())['rows']; assert len(rows)==len(oldrows)==2
for row,prev,name in zip(rows,oldrows,['Sign14ForwardBridge','Sign14ReverseBridge']):
 assert row['module']==prev['module']=='DiophantineConsistency.'+name and row['imports']==prev['imports']
 src=p/'src/DiophantineConsistency'/(name+'.lean'); source=src.read_text(); prior=(old/'src/DiophantineConsistency'/(name+'.lean')).read_text()
 assert prior.replace('set_option autoImplicit false\n','set_option autoImplicit false\nset_option maxHeartbeats 4000000\n')==source
 assert sha(src)==sha(repo/row['source'])==row['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',source,re.M)==row['imports']
 assert not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b',source)
r=(p/'run.py').read_text(); assert "'-M2800'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
assert all(s in r for s in ('failed state pin','failed outer pin','failed log pin'))
check=root/'reviews/nine-sharing-sign14-zero-assembly-terminal-independent/check.py'; assert sha(check)=='142c2f07e99adcce4ab8c1abd067c57b7bfaf94a0878e91cc514b70ff76c2424'; subprocess.run([sys.executable,'-I','-S','-B',str(check)],capture_output=True,check=True,timeout=120)
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180); assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':2,'scope':'conditional pointwise forward/reverse zero assembly; existential iff separate'},indent=2))
