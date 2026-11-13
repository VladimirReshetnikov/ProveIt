#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-86gate-expression-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='f8fbb9d36a43a87b44add9106c3e8520c87272251428633f5ee0945ea40bbb28' and sha(p/'source-manifest.json')=='a60ef43e537630e1016b7cfabef1bb4bfe975b7bef685914acdfed0066937bfe'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];q=p/'src/DiophantineConsistency/Sign14Optimized86Expression.lean';s=q.read_text();assert e['module']=='DiophantineConsistency.Sign14Optimized86Expression' and e['imports']==['DiophantineConsistency.Sign14Optimized86'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for t in ('Sign32GenericRemoveInput.removeInput (Sign14Optimized86.seed p)','theorem eval_expression {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R)','(Sign32GenericRemoveInput.removeInput (Sign14Optimized90.seed p)).evalRing v','Sign32GenericRemoveInput.eval_removeInput','Sign14Optimized86.seed_eval p _','theorem polynomial_eq (p : Fin 4 → ℤ)','(expression p).toPolynomial = (Sign32GenericRemoveInput.removeInput (Sign14Optimized90.seed p)).toPolynomial','eval_expression p (MvPolynomial.X : Fin 14 → MvPolynomial (Fin 14) ℤ)','Expr.evalRing_X'):assert ' '.join(t.split()) in ' '.join(s.split())
for f in ('nine-sharing-sign14-86gate-lean-terminal-independent','nine-sharing-sign14-86gate-lean-draft-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
base=Path('/tmp/nine-sharing-sign14-86gate-lean-check-20261110');prior=json.loads((root/'research/nine-sharing-sign14-86gate-lean-check/attempt01/state.json').read_text());assert prior['status']=='PASS';r,=prior['rows'];assert sha(base/'lib/DiophantineConsistency/Sign14Optimized86.olean')==r['object_sha256']
for mod,d in r['dependencies'].items():
 if mod=='Init':continue
 z=base/'lib'/(mod.replace('.','/')+'.olean');assert z.is_file() and str(z.resolve())==d['realpath'] and sha(z)==d['sha256'] and prior['overlay_links'][str(z)]==d['realpath']
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'arbitrary-port generic evaluation and polynomial equality conditional on Lean; degree/iPRA/JSON/PDF separate'},indent=2))
