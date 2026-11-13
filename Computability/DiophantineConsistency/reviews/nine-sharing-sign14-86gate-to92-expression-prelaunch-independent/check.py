#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-86gate-to92-expression-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();assert sha(p/'run.py')=='6ed3c7d094227c83f4eaebc4db3b97cee0416540ef3d93eb46c35e37232782d2' and sha(p/'framework-survey.py')=='8ceb6ccfb6725f153f89416ffce6e06471627854999343735dca3c2d55e69d83' and sha(p/'source-manifest.json')=='fbf367e8642c5b2e19fabe19a28035362cb807880611a2583dce114dd1c9eb58';e,=json.loads((p/'source-manifest.json').read_text())['rows'];q=p/'src/DiophantineConsistency/Sign14Optimized86To92.lean';s=q.read_text();assert e['module']=='DiophantineConsistency.Sign14Optimized86To92' and e['imports']==['DiophantineConsistency.Sign14Optimized86Expression'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for x in ('theorem eval_expression {R : Type*} [CommRing R]', 'Sign14Optimized86Expression.expression p', 'Sign32GenericRemoveInput.removeInput (Sign14Optimized90.seed p)', 'Sign32GenericRemoveInput.removeInput (Sign14Optimized92.seed p)', 'Sign14Optimized86Expression.eval_expression p v','Sign14Optimized90.seed_eval p _','theorem polynomial_eq','MvPolynomial.X : Fin 14 → MvPolynomial (Fin 14) ℤ','Expr.evalRing_X'):assert x in s
for f in ('nine-sharing-sign14-86gate-expression-terminal-independent','nine-sharing-sign14-86gate-lean-terminal-independent','nine-sharing-sign14-90gate-lean-retry01-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
base=Path('/tmp/nine-sharing-sign14-86gate-expression-check-20261110/lib');states=['nine-sharing-sign14-86gate-expression-check','nine-sharing-sign14-86gate-lean-check','nine-sharing-sign14-90gate-lean-retry01-check'];edges=[]
for stem in states:
 st=json.loads((root/'research'/stem/'attempt01/state.json').read_text());assert st['status']=='PASS'
 for row in st['rows']:
  for mod,d in row['dependencies'].items():
   if mod=='Init':continue
   z=base/(mod.replace('.','/')+'.olean');assert z.is_file() and str(z.resolve())==d['realpath'] and sha(z)==d['sha256'],(row['module'],mod);edges.append((row['module'],mod))
assert any(a=='Sign14Optimized86' and b.endswith('Sign14Optimized90') for a,b in edges)
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'framework-survey.py')],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS'
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','captured_direct_edges':len(edges),'scope':'proposed 86 to 92 fixed-input generic eval/polynomial equality; no Lean/JSON/PDF/file theorem'},indent=2))
