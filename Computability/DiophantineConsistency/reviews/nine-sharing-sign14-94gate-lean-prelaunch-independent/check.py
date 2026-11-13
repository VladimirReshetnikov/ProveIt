#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-94gate-lean-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='4c166fc4d403988a01d3b1cddd9ff45501e4beeee48c2270c1f2b8774319fffa' and sha(p/'source-manifest.json')=='fb7e59c5d278f2914e7a3f7b937bd2d229517b47b49bb0e146e613817bea0736'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];q=p/'src/DiophantineConsistency/Sign14Optimized94.lean';s=q.read_text();assert e['module']=='DiophantineConsistency.Sign14Optimized94' and e['imports']==['DiophantineConsistency.Sign14Optimized95'] and sha(q)==sha(repo/e['source'])==e['source_sha256']=='ce02afce038ddf7b681e2bd894bc841ddaba7999333cdfcaa3e585cfdc56976f' and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for t in ('variable {R : Type*} [CommRing R]','theorem shared41_eval','theorem seed_eval','(seed p).evalRing v = (Sign14Optimized95.seed p).evalRing v','#print axioms DiophantineConsistency.Sign14Optimized94.seed_eval'):assert t in s
for f in ('nine-sharing-sign14-94gate-candidate-independent','nine-sharing-sign14-94gate-lean-draft-independent','nine-sharing-sign14-95gate-lean-retry01-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
base=Path('/tmp/nine-sharing-sign14-95gate-lean-retry01-check-20261110');st=json.loads((root/'research/nine-sharing-sign14-95gate-lean-retry01-check/attempt01/state.json').read_text());assert st['status']=='PASS';row,=st['rows'];obj=base/'lib/DiophantineConsistency/Sign14Optimized95.olean';assert sha(obj)==row['object_sha256']
for mod,d in row['dependencies'].items():
 if mod=='Init':continue
 z=base/'lib'/(mod.replace('.','/')+'.olean');assert z.is_file() and str(z.resolve())==d['realpath'] and sha(z)==d['sha256'] and st['overlay_links'][str(z)]==d['realpath']
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed generic CommRing 94/95 seed equality; no Lean result or JSON/PDF/file/degree/iPRA theorem'},indent=2))
