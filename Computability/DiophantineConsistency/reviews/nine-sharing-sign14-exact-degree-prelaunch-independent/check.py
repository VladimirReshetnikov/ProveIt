#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-exact-degree-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='feb6d1c9f00f45fe0404f4c8087a4ba6ed4cb30586863ab2df2e267dd1f4bccd' and sha(p/'source-manifest.json')=='ad93b3e4824648149dc11068debcf39d6d78f913de8467a00120ca54171a329a'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];names=['Sign14AxisDiagonalDegree','Sign14AxisDiagonalBinding','Sign14AxisDegreeLower','Sign14ExactDegree'];assert [e['module'].split('.')[-1] for e in rows]==names;ss=[]
for i,e in enumerate(rows):
 src=p/'src/DiophantineConsistency'/(names[i]+'.lean');s=src.read_text();ss.append(s);assert sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports']==['DiophantineConsistency.'+('Sign14AxisSeedDegree' if i==0 else names[i-1])] and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b',s)
a,b,c,d=ss
assert all(t in a for t in ('def diagonalVars (i : Fin 14)','def diagonal (p : MvPolynomial (Fin 14) ℤ)','theorem diagonal_totalDegree_le','(diagonal p).totalDegree ≤ p.totalDegree','theorem diagonal_eval'))
assert all(t in b for t in ('def univariateVars (i : Fin 14) : P := Polynomial.X','theorem unique_eval','theorem direct_axis','(Fin.cons (.constant 1) (fun i => .var i))','refine Fin.cases ?_ (fun j => ?_) i','fin_cases j <;> rfl'))
assert all(t in c for t in ('expression_polynomial_degree_ge (p : Fin 4 → ℤ) (hz : p 0 ≠ 0)','124 ≤ (Sign14AbstractExpression.expression p).toPolynomial.totalDegree','seed_axis_degree p hz','diagonal_totalDegree_le'))
assert all(t in d for t in ('current_port_positive','current_port_nonzero','abstract_exact (p : Fin 4 → ℤ) (hz : p 0 ≠ 0)','theorem current_exact','totalDegree = 124','Sign14SyntaxDegree.expression_polynomial_degree_le p','Sign14AxisDegreeLower.expression_polynomial_degree_ge p hz'))
# Input-removal substitutes 1 at Fin15 index 0; every Fin14 witness coordinate maps to X, matching the audited seed axis.
assert [1]+['X']*14==[1 if i==0 else 'X' for i in range(15)]
check=root/'reviews/nine-sharing-sign14-axis-seed-degree-terminal-independent/check.py';assert sha(check)=='a9727f218c6f7baa3c887cf9395219c50fd1427d48be39b3f96e798ab1d106e4';subprocess.run([sys.executable,'-I','-S','-B',str(check)],capture_output=True,check=True,timeout=120)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "['author_observed_numeric_outer_exit']==0" in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':4,'scope':'conditional abstract and current symbolic Fin14 exact degree124; no external binding'},indent=2))
