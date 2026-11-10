#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-86gate-lean-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='3032d9ed6bdd8020cb930617f398ad36aa674c63a145984cfbcbc386bdbdcf2e' and sha(p/'source-manifest.json')=='b9950a77f4d24490614388434f192dcadd9b3a135cc419af143a69c6a0522e98'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];q=p/'src/DiophantineConsistency/Sign14Optimized86.lean';s=q.read_text();assert e['module']=='DiophantineConsistency.Sign14Optimized86' and e['imports']==['DiophantineConsistency.Sign14Optimized90'] and sha(q)==sha(repo/e['source'])==e['source_sha256']=='a18d16bbf5e3a97f82dcab7e5af5c36440656e8fb5d726e8bcd0aede13126977' and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for t in ('variable {R : Type*} [CommRing R]','theorem shared34_eval','theorem seed_eval','(seed p).evalRing v = (Sign14Optimized90.seed p).evalRing v','#print axioms DiophantineConsistency.Sign14Optimized86.seed_eval'):assert t in s
for f in ('nine-sharing-sign14-86gate-candidate-independent','nine-sharing-sign14-86gate-lean-draft-independent','nine-sharing-sign14-90gate-lean-retry01-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
base=Path('/tmp/nine-sharing-sign14-90gate-lean-retry01-check-20261110');st=json.loads((root/'research/nine-sharing-sign14-90gate-lean-retry01-check/attempt01/state.json').read_text());assert st['status']=='PASS';row,=st['rows'];obj=base/'lib/DiophantineConsistency/Sign14Optimized90.olean';assert sha(obj)==row['object_sha256']
for mod,d in row['dependencies'].items():
 if mod=='Init':continue
 z=base/'lib'/(mod.replace('.','/')+'.olean');assert z.is_file() and str(z.resolve())==d['realpath'] and sha(z)==d['sha256'] and st['overlay_links'][str(z)]==d['realpath']
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed generic CommRing 86/90 seed equality; no Lean result or JSON/PDF/file/degree/iPRA theorem'},indent=2))
