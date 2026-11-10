#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-byte-binding-retry-check';old=root/'research/nine-sharing-sign17-k-byte-binding-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='2ce70e7624b9be65b6d29378d8ccaab6b25f887fb1ed4a81967c620ebd728629' and sha(p/'source-manifest.json')=='72c56552983dd059b01caafc037800783ca7a497262f0775c4f9463d91600318'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign17KByteBinding';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();imports=[f'DiophantineConsistency.Sign17KStreamCompare{i:02}' for i in range(8)];assert e['module']=='DiophantineConsistency.'+n and e['imports']==imports and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==imports and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
previous=(old/'src/DiophantineConsistency'/(n+'.lean')).read_text();needle='      rw [Sign17KStreamExplicit.digits_explicit]\n';assert previous.count(needle)==1 and s==previous.replace(needle,needle+'      rfl\n')
for f in ('nine-sharing-sign17-k-byte-binding-failure-independent','nine-sharing-sign17-k-stream-compare-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "need('Init' in deps" in r and "env['LEAN_NUM_THREADS']='1'" in r and "str(candidates[0])==rec['path']" in r and "rec['realpath']==provider_init['realpath'] and rec['sha256']==provider_init['sha256']" in r and "'-M3600'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed symbolic K equality to in-Lean byte-list decoding; no external file theorem'},indent=2))
