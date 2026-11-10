#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-95gate-expression-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='8aff6dfe8b0c5032c3ed7ffd4050d172f08a9d015a8d1c07b424bccab35602bb' and sha(p/'source-manifest.json')=='6286547a8806e71ccaa9fe6dd399d4d2cc5df2939b631ec812868c0e2a108b07'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];q=p/'src/DiophantineConsistency/Sign14Optimized95Expression.lean';s=q.read_text();assert e['module']=='DiophantineConsistency.Sign14Optimized95Expression' and e['imports']==['DiophantineConsistency.Sign14Optimized95'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for t in ('Sign32GenericRemoveInput.removeInput (Sign14Optimized95.seed p)','theorem eval_expression {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R)','(Sign14AbstractExpression.expression p).evalRing v','Sign32GenericRemoveInput.eval_removeInput','Sign14Optimized95.seed_eval p _','theorem polynomial_eq (p : Fin 4 → ℤ)','(expression p).toPolynomial = (Sign14AbstractExpression.expression p).toPolynomial','eval_expression p (MvPolynomial.X : Fin 14 → MvPolynomial (Fin 14) ℤ)','Expr.evalRing_X'):assert t in s
for f in ('nine-sharing-sign14-95gate-lean-retry01-terminal-independent','nine-sharing-sign14-95gate-lean-draft-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'arbitrary-port generic evaluation and polynomial equality conditional on Lean; degree/iPRA/JSON/PDF separate'},indent=2))
