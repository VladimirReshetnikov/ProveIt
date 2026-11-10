#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/current14-carrier65-q-degree-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='0c067a1d47c1afbfa950dab6e04fd6ba63c82c236e3d41db02d95ac4c590cc0a' and sha(p/'source-manifest.json')=='fec31d3d5b80c2d7a09db6a101694561f85755ff5a29bd3c1a2a12b23d333475'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Current14Carrier65QDegree';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.WeightedExpressionDegree','Mathlib.Data.Fin.VecNotation'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('let X : Expr (Fin 5) := .var 0','let a : Expr (Fin 5) := .var 1','let c : Expr (Fin 5) := .var 2','let H : Expr (Fin 5) := .var 3','let gamma : Expr (Fin 5) := .var 4','(X + gamma * H) ^ 2 + 2 * a * c * (X + gamma * H) - H * c ^ 2','![2, 6, 5, 6, 1]','(hv : ∀ j, (v j).totalDegree ≤ qWeights j)','Expr.degree_evalRing_le qSyntax qWeights v hv'):assert z in s
x,a,c,h,g=2,6,5,6,1;inner=max(x,g+h);assert (2*inner, a+c+inner,h+2*c)==(14,18,16) and max(2*inner,a+c+inner,h+2*c)==18
wd=(root/'Lean/DiophantineConsistency/WeightedExpressionDegree.lean').read_text();assert '(hv : ∀ i,(v i).totalDegree ≤ w i)' in wd and '(e.evalRing v).totalDegree ≤ e.weightedDegree w' in wd
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-carrier65-dag-value-congr-diagnostic-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "env['LEAN_NUM_THREADS']='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need('Init' in deps" in r and 'first-candidate route' in r and '948b4e01db000ecf59395fc5555f51bf4b249f8922c40f40bbd6585b190b5772' in r
z=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not z.stderr and json.loads(z.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','branch_weights':[14,18,16],'scope':'conditional generic five-input Q bound; actual input bounds/whole degree separate'},indent=2))
