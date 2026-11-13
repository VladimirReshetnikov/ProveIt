#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-90gate-lean-retry01-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='adb14ae200ad0ba2732f1ea8f3e8a789e3bd4229146d201d15d639b74860c67b' and sha(p/'source-manifest.json')=='f7b3530c16f79440ac939f0b35674d1ed816a8b52053c51266b80863646b0b50'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];q=p/'src/DiophantineConsistency/Sign14Optimized90.lean';s=q.read_text();assert e['module']=='DiophantineConsistency.Sign14Optimized90' and e['imports']==['DiophantineConsistency.Sign14Optimized92'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
old=(root/'research/nine-sharing-sign14-90gate-lean-check/src/DiophantineConsistency/Sign14Optimized90.lean').read_text();assert old.replace("[shared25', Sign14Optimized93.shared25', Expr.evalRing_add]", "[shared25', shared14', Sign14Optimized93.shared25', Expr.evalRing_add]").replace("[shared30', Sign14Optimized93.shared30', Expr.evalRing_add]", "[shared30', shared14', Sign14Optimized93.shared30', Expr.evalRing_add]")==s
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-90gate-lean-failure-independent/check.py')],capture_output=True,check=True,timeout=180)
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
