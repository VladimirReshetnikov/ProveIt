#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-93gate-lean-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='d0e76ee0849004a7cd4d9eb0cf62b2a0ed42006867f0c4fde4f10ba30f08beff' and sha(p/'source-manifest.json')=='1d16d36404e71b023077d28d53e0ca3a6ef978778bbb20bbecfa2ad7a2e490a6'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];q=p/'src/DiophantineConsistency/Sign14Optimized93.lean';s=q.read_text();assert e['module']=='DiophantineConsistency.Sign14Optimized93' and e['imports']==['DiophantineConsistency.Sign14Optimized94'] and sha(q)==sha(repo/e['source'])==e['source_sha256']=='4f717d88e562ac71bf69c444cc5cdfeb11b41b6bcaa2308c4517ac1dd9c653a2' and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for t in ('variable {R : Type*} [CommRing R]','theorem shared14_eval','theorem seed_eval','(seed p).evalRing v = (Sign14Optimized94.seed p).evalRing v','#print axioms DiophantineConsistency.Sign14Optimized93.seed_eval'):assert t in s
for f in ('nine-sharing-sign14-93gate-candidate-independent','nine-sharing-sign14-93gate-lean-draft-independent','nine-sharing-sign14-94gate-lean-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
base=Path('/tmp/nine-sharing-sign14-94gate-lean-check-20261110');st=json.loads((root/'research/nine-sharing-sign14-94gate-lean-check/attempt01/state.json').read_text());assert st['status']=='PASS';row,=st['rows'];obj=base/'lib/DiophantineConsistency/Sign14Optimized94.olean';assert sha(obj)==row['object_sha256']
for mod,d in row['dependencies'].items():
 if mod=='Init':continue
 z=base/'lib'/(mod.replace('.','/')+'.olean');assert z.is_file() and str(z.resolve())==d['realpath'] and sha(z)==d['sha256'] and st['overlay_links'][str(z)]==d['realpath']
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed generic CommRing 93/94 seed equality; no Lean result or JSON/PDF/file/degree/iPRA theorem'},indent=2))
