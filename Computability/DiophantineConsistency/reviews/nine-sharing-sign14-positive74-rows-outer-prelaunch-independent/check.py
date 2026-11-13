#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-rows-outer-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='05a64d6080c99a35dc28505d70504231312db359d5a022c7f2bcd1b86747a843' and sha(p/'source-manifest.json')=='45a8d3f192a71baa3b45c970ddde3ea2753d71bf747b188f7980928d7693028d'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74RowsOuter';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74SharedC'] and sha(q)==sha(repo/e['source'])==e['source_sha256']=='b38a09cec2348269ed7eab467065de37d302e3c06abba6e6baa5bb7b70366cd4' and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for name,new,old in (('row00','row00',"row00''"),('scale_square','g51',"shared43''"),('row04','row04',"row04''")):
 assert f'theorem {name}_eval : ({new} p).evalRing (fun i => v i + 1)' in s and f'(Sign14Optimized94.{old} p).evalRing (Fin.cons 1 v)' in s
for i in (5,6):assert f'Fin.cases (1 : R) v ({i} : Fin 15) = v {i-1} := by rfl' in s
new='\n'.join((root/f'research/nine-sharing-sign14-positive74-lean-draft/Sign14Positive74Nodes{i:02}.lean').read_text() for i in (2,6,7,8));new+=(root/'research/nine-sharing-sign14-positive74-lean-draft/Sign14Positive74Expression.lean').read_text();old=(root/'research/nine-sharing-sign14-94gate-lean-draft/Sign14Optimized94.lean').read_text()
for z in ('(g10 p) * (g10 p)','(g20 p) * (g21 p)','(g18 p) - (g22 p)','(Expr.var 5) * (g18 p)','(g50 p) * (g50 p)','(Expr.var 4) * (Expr.var 4)','(g20 p) * (g52 p)','(g62 p) - (g51 p)','(g63 p) - (g20 p)','def row00 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g23 p)','def row04 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g64 p)'):assert z in new
for z in ("(Expr.var 6 + Expr.constant 1) * shared41'' p", "shared42'' p * shared42'' p", "shared41'' p - shared40 p * (shared17 p * shared17 p)", "(shared40 p * ((Expr.var 5 + Expr.constant 1) * (Expr.var 5 + Expr.constant 1)) - shared43'' p) - shared40 p"):assert z in old
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-shared-c-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'row00,row04 and scale-square generic equalities only; remaining rows/model/file separate'},indent=2))
