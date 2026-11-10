#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-model-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='53c949aefaf68cbf8383ab86132b15c1beb1c6e09d7d046419dd1ab862bbf16f' and sha(p/'source-manifest.json')=='1e97ff8f7cd73c99f437619547c1eebed9abdb7995453be90aa6e55efda37020'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74Model';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ExpressionBridge'] and sha(q)==sha(repo/e['source'])==e['source_sha256']=='9d19a7ce74ab42bfb72fb6308b5b41c6db23c806e3a6b73113b5b72506ec7822' and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('[ORingStructure V]','V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁','InternalZero (positiveShift (Sign14Positive74.expression p)) w','InternalZero (Sign14Optimized86Expression.expression p) w','internalZero_positiveShift, internalZero_iff, internalZero_iff','map_add, map_one','Sign14Positive74ExpressionBridge.eval_shift p (fun i => ι (w i))','exact exists_congr (zero_iff p)'):assert z in s
syntax=(root/'Lean/DiophantineConsistency/CurrentEquationSyntax2011.lean').read_text();assert 'e.subst (fun i => Expr.var i + Expr.constant 1)' in syntax and 'InternalZero (positiveShift e) v ↔ InternalZero e (fun i => v i + 1)' in syntax
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-expression-bridge-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'IΣ₁ model zero iff for shifted positive expression and natural 86, not direct positive-witness bijection or external file theorem'},indent=2))
