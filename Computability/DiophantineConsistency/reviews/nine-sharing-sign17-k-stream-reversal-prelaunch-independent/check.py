#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-stream-reversal-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='f5c3838f61fc2322c837079c843f1d591dada678c6a05d64109d8a5ed0d107c0' and sha(p/'source-manifest.json')=='b62a9410d9cd0419fa9e43f8a170491c4a5dbf28095e4590dc57411b1e0acef7'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];q=p/'src/DiophantineConsistency/Sign17KStreamReversal.lean';s=q.read_text();assert e['module']=='DiophantineConsistency.Sign17KStreamReversal' and e['imports']==['DiophantineConsistency.Sign17KCanonicalDigits'] and sha(q)==sha(repo/e['source'])==e['source_sha256']=='5d96dd45293968643819dcfc80789376fb1e350d8d99437281d5d1e0e54ae655' and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
assert 'theorem ofFn_rev {α : Type} (n : ℕ) (v : Fin n → α)' in s and 'List.ofFn (fun i => v i.rev) = (List.ofFn v).reverse' in s
for n in range(40):
 v=list(range(n));assert [v[n-1-i] for i in range(n)]==v[::-1]
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign17-k-canonical-digits-retry02-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
prior=json.loads((root/'research/nine-sharing-sign17-k-canonical-digits-retry02-check/attempt01/state.json').read_text());assert prior['status']=='PASS';obj=Path('/tmp/nine-sharing-sign17-k-canonical-digits-retry02-20261110/lib/DiophantineConsistency/Sign17KCanonicalDigits.olean');assert sha(obj)==prior['rows'][0]['object_sha256']
r=(p/'run.py').read_text();assert "need('Init' in deps" in r and "env['LEAN_NUM_THREADS']='1'" in r and "str(candidates[0])==rec['path']" in r and "rec['realpath']==provider_init['realpath'] and rec['sha256']==provider_init['sha256']" in r and "'-M3600'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'generic finite-vector reversal only; no concrete K stream, byte or external file theorem'},indent=2))
