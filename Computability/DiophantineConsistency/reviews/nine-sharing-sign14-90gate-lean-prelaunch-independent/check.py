#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-90gate-lean-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='56f602c1bedde30d3b1cfacde1a46df8d4efdfaec373685cd67998b2c2789c23' and sha(p/'source-manifest.json')=='2df474f53c134e6cb1226da77ba7bcab800f1226001914329559a5e0cec4fc6b'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];q=p/'src/DiophantineConsistency/Sign14Optimized90.lean';s=q.read_text();assert e['module']=='DiophantineConsistency.Sign14Optimized90' and e['imports']==['DiophantineConsistency.Sign14Optimized92'] and sha(q)==sha(repo/e['source'])==e['source_sha256']=='78910b0c44cd63d84a4936bf830a743745588fc52aaa45e37c589c40b8e04584' and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for t in ('variable {R : Type*} [CommRing R]','theorem shared27_eval','theorem seed_eval','(seed p).evalRing v = (Sign14Optimized92.seed p).evalRing v','#print axioms DiophantineConsistency.Sign14Optimized90.seed_eval'):assert t in s
for f in ('nine-sharing-sign14-90gate-candidate-independent','nine-sharing-sign14-90gate-lean-draft-independent','nine-sharing-sign14-92gate-lean-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
base=Path('/tmp/nine-sharing-sign14-92gate-lean-check-20261110');st=json.loads((root/'research/nine-sharing-sign14-92gate-lean-check/attempt01/state.json').read_text());assert st['status']=='PASS';row,=st['rows'];obj=base/'lib/DiophantineConsistency/Sign14Optimized92.olean';assert sha(obj)==row['object_sha256']
for mod,d in row['dependencies'].items():
 if mod=='Init':continue
 z=base/'lib'/(mod.replace('.','/')+'.olean');assert z.is_file() and str(z.resolve())==d['realpath'] and sha(z)==d['sha256'] and st['overlay_links'][str(z)]==d['realpath']
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed generic CommRing 90/92 seed equality; no Lean result or JSON/PDF/file/degree/iPRA theorem'},indent=2))
