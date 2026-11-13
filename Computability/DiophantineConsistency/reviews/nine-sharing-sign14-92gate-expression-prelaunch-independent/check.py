#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-92gate-expression-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='fcf717915dc0833697fa3440c3352419709250de7e480563ef0f12aa21471934' and sha(p/'source-manifest.json')=='e4524e73ae08175e207385c28b1c2ab79218d2f6376d68e4e87715ffbc818208'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];q=p/'src/DiophantineConsistency/Sign14Optimized92Expression.lean';s=q.read_text();assert e['module']=='DiophantineConsistency.Sign14Optimized92Expression' and e['imports']==['DiophantineConsistency.Sign14Optimized92'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for t in ('Sign32GenericRemoveInput.removeInput (Sign14Optimized92.seed p)','theorem eval_expression {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R)','(Sign32GenericRemoveInput.removeInput (Sign14Optimized93.seed p)).evalRing v','Sign32GenericRemoveInput.eval_removeInput','Sign14Optimized92.seed_eval p _','theorem polynomial_eq (p : Fin 4 → ℤ)','(expression p).toPolynomial = (Sign32GenericRemoveInput.removeInput (Sign14Optimized93.seed p)).toPolynomial','eval_expression p (MvPolynomial.X : Fin 14 → MvPolynomial (Fin 14) ℤ)','Expr.evalRing_X'):assert ' '.join(t.split()) in ' '.join(s.split())
for f in ('nine-sharing-sign14-92gate-lean-terminal-independent','nine-sharing-sign14-92gate-lean-draft-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
base=Path('/tmp/nine-sharing-sign14-92gate-lean-check-20261110');prior=json.loads((root/'research/nine-sharing-sign14-92gate-lean-check/attempt01/state.json').read_text());assert prior['status']=='PASS';r,=prior['rows'];assert sha(base/'lib/DiophantineConsistency/Sign14Optimized92.olean')==r['object_sha256']
for mod,d in r['dependencies'].items():
 if mod=='Init':continue
 z=base/'lib'/(mod.replace('.','/')+'.olean');assert z.is_file() and str(z.resolve())==d['realpath'] and sha(z)==d['sha256'] and prior['overlay_links'][str(z)]==d['realpath']
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'arbitrary-port generic evaluation and polynomial equality conditional on Lean; degree/iPRA/JSON/PDF separate'},indent=2))
