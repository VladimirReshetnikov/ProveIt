#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-digit-bound-blocks-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='ed98d128d4643890443bfc2146a9dc9c2602229cf5c188e5a16f49caeefec359' and sha(p/'source-manifest.json')=='e8acd48a17c736bfeb3c8537b8b2a17ec384fb565d45f07bf35399801dde4ea9'
entries=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(entries)==14
for i,e in enumerate(entries,1):
 name=f'Sign17KDigitBoundBlock{i:02}';q=p/'src/DiophantineConsistency'/(name+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+name and e['imports']==['DiophantineConsistency.Sign17KRadixStreamCurrent'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
 for x in ('theorem bound (i : Fin 64)',f'Sign17KTileCoefficients{i:02}.literal i + 1 < CurrentKernel2011.radix',f'#print axioms DiophantineConsistency.{name}.bound'):assert x in s
assert list(range(32,928))==[32+64*i+j for i in range(14) for j in range(64)]
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign17-k-radix-stream-current-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
prior=json.loads((root/'research/nine-sharing-sign17-k-radix-stream-current-check/attempt01/state.json').read_text());assert prior['status']=='PASS';obj=Path('/tmp/nine-sharing-sign17-k-radix-stream-current-20261110/lib/DiophantineConsistency/Sign17KRadixStreamCurrent.olean');assert sha(obj)==prior['rows'][0]['object_sha256']
r=(p/'run.py').read_text();assert "need('Init' in deps" in r and "env['LEAN_NUM_THREADS']='1'" in r and "str(candidates[0])==rec['path']" in r and "rec['realpath']==provider_init['realpath'] and rec['sha256']==provider_init['sha256']" in r and "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'14 Fin64 blocks cover 896 coefficients; assembly and external file theorem separate'},indent=2))
