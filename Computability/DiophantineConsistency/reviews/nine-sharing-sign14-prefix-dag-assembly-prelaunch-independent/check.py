#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-prefix-dag-assembly-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='f39092d50bfcd79a0bb6dd9d9452e7d409b2621ac72203037e97c0081f48a6e8' and sha(p/'source-manifest.json')=='3851be7426b6be0ab962bbcc71cde60230a3d5719cb6f6d09564e338da614a25'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];q=p/'src/DiophantineConsistency/Sign14PrefixDagAssembly.lean';s=q.read_text();assert e['module']=='DiophantineConsistency.Sign14PrefixDagAssembly' and e['imports']==['DiophantineConsistency.Sign14PrefixDagDecode04','DiophantineConsistency.Sign14AbstractExpressionDef'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for i in range(5):
 for t in (f'def row{i:02} (p : Fin 4 → ℤ) : Expr (Fin 15) := decoded p row{i:02}Bytes',f'theorem row{i:02}_eq (p : Fin 4 → ℤ) : row{i:02} p = SharingSeed14Degree124.row{i:02} p',f'rw [row{i:02}_decode]'):assert t in s
for t in ('row00 p * row00 p +','([row01 p, row02 p, row03 p, row04 p].map fun e => e * e)','theorem seed_eq (p : Fin 4 → ℤ) : seed p = SharingSeed14Degree124.seed p','Sign32GenericRemoveInput.removeInput (seed p)','expression p = Sign14AbstractExpression.expression p','[expression, Sign14AbstractExpression.expression, seed_eq]'):assert t in s
for f in ('nine-sharing-sign14-prefix-dag-decode-terminal-independent','nine-sharing-sign14-expression-eval-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider-survey.py')],capture_output=True,text=True,check=True,timeout=180);v=json.loads(x.stdout);assert not x.stderr and v['status']=='PASS' and v['overlap_count']==1073 and len(v['extra'])==1
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','rows':5,'overlaps':1073,'extra':1,'scope':'embedded DAG parsed expression equals symbolic Fin14 expression conditional on Lean; external file/JSON/PDF separate'},indent=2))
