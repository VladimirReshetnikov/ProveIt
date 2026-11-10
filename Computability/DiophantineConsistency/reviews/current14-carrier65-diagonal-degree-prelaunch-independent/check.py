#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/current14-carrier65-diagonal-degree-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='d70a68b4eb348f64ecc23fa4aa4df45526347ba1c6ded384e0c4201b9bc950d4' and sha(p/'source-manifest.json')=='5404980f93f554b22c38f58d36301bc709a1413c46aba1de760b4968c63bc833'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Current14Carrier65DiagonalDegree';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign17UnivariateDegreeProbe'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('def diagonalVars (_ : Fin 14) : MvPolynomial (Fin 1) ℤ := X 0','MvPolynomial.eval₂ MvPolynomial.C diagonalVars p','(diagonal p).totalDegree ≤ p.totalDegree','diagonal e.toPolynomial = e.evalRing diagonalVars','(e.evalRing (fun _ => Polynomial.X)).natDegree ≤ e.toPolynomial.totalDegree','mapped_degree_le (diagonal e.toPolynomial)','diagonal_totalDegree_le e.toPolynomial'):assert z in s
for f in ('current14-carrier65-q-actual-retry-terminal-independent',):subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "env['LEAN_NUM_THREADS']='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need('Init' in deps" in r and 'first-candidate route' in r and 'Sign17UnivariateDegreeProbe' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'generic all-equal Fin14 diagonal degree-nonincreasing transport; actual degree unproved'},indent=2))
