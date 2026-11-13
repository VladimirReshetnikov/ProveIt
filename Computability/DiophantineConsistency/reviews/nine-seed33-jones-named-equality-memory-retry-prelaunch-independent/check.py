#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-seed33-jones-named-equality-memory-retry-check';old=root/'research/nine-seed33-jones-named-equality-resume-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='742c4e8bb3da0a4bdc94b4d555d38056c4d0ecaa93e10ec9c4a81b9659ada87c' and sha(p/'source-manifest.json')=='6dea7b1ac4671d36c0dd3d1440355e6e4cb7e9bce583e0ac35edc01bde5ef18b' and sha(p/'provider-survey.py')==sha(old/'provider-survey.py')=='c89fe6d6d02beb285362261a1c25b2f49e453794e9c4b530b9d0db560c53ac9d'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];prior=json.loads((old/'source-manifest.json').read_text())['rows'];assert len(rows)==len(prior)==2
for e,q in zip(rows,prior):
 assert e['module']==q['module'] and e['imports']==q['imports'] and e['source_sha256']==q['source_sha256'];n=e['module'].split('.')[-1]+'.lean';assert sha(p/'src/DiophantineConsistency'/n)==sha(old/'src/DiophantineConsistency'/n)==e['source_sha256']
a=(old/'run.py').read_text();b=(p/'run.py').read_text();assert a.replace('named-equality-resume-check-20261110','named-equality-memory-retry-check-20261110').replace('b88bda7ca8d36fdd0cc12be758ac044e5e7656865f77ed39cf91f01d42df641c','6dea7b1ac4671d36c0dd3d1440355e6e4cb7e9bce583e0ac35edc01bde5ef18b').replace("'-M2800'","'-M3600'")==b
failure=root/'reviews/nine-seed33-jones-named-equality-resume-terminal-independent/check.py';assert sha(failure)=='1bfafdb1439b4d365495e2a82e2109d6456a24b90f2fbe7581f79da66b3fedba';subprocess.run([sys.executable,'-I','-S','-B',str(failure)],capture_output=True,check=True,timeout=120)
assert 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in b
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=360);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':2,'scope':'unchanged named equality sources; scoped -M3600 retry under unchanged external guards'},indent=2))
