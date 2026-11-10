#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-expression-bridge-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='e686ae2a6281af7e7a8f17e3ab1cf6bcab0e54eae44352ce4f6b9dc316d4aa4f' and sha(p/'source-manifest.json')=='a5301f26dd89f50d8b6910a41ea0a96c713e0081330de6e67a9284c4a7e33d57'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ExpressionBridge';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74RowsInner'] and sha(q)==sha(repo/e['source'])==e['source_sha256']=='24fe6842bb408557b4aca85ccf657ed7ebf71186777667d213b7b9f1b5a477c7' and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
assert '(Sign14Positive74.expression p).evalRing (fun i => v i + 1)' in s and '(Sign14Optimized86Expression.expression p).evalRing v' in s and 'Sign32GenericRemoveInput.eval_removeInput' in s
for z in ('Sign14Positive74RowsOuter.row00_eval','Sign14Positive74RowsInner.row01_eval','Sign14Positive74Row02.row_eval','Sign14Positive74RowsInner.row03_eval','Sign14Positive74RowsOuter.row04_eval'):assert z in s
pos=(root/'research/nine-sharing-sign14-positive74-lean-draft/Sign14Positive74Expression.lean').read_text();old=(root/'research/nine-sharing-sign14-86gate-lean-draft/Sign14Optimized86.lean').read_text();expr=(root/'research/nine-sharing-sign14-86gate-expression-draft/Sign14Optimized86Expression.lean').read_text();rm=(root/'research/nine-sharing-sign32-direct-ipra-retry01/src/DiophantineConsistency/Sign32GenericRemoveInput.lean').read_text()
for i in range(5):assert f'row{i:02} p * row{i:02} p' in pos
assert "Sign14Optimized94.row00'' p * Sign14Optimized94.row00'' p" in old and "[row01' p, row02' p, row03' p,\n      Sign14Optimized94.row04'' p].map fun e => e * e" in old and 'removeInput (Sign14Optimized86.seed p)' in expr and '(removeInput e).evalRing a = e.evalRing (Fin.cons 1 a)' in rm
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-rows-inner-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'generic ring expression evaluation under coordinate shift only; positive-model existence/degree/file separate'},indent=2))
