#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-coordinate-probe-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='2d032f396c3b9276ee6537e6ddd2eaac0ac2ed5f66ac721eaaefa431ce3bf191' and sha(p/'source-manifest.json')=='f9102cad09d26239fe5adbfd596daa919f06e41b408d874894a2bdbcb8dcdad1'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];q=p/'src/DiophantineConsistency/Sign14Positive74CoordinateProbe.lean';s=q.read_text();assert e['module']=='DiophantineConsistency.Sign14Positive74CoordinateProbe' and e['imports']==['DiophantineConsistency.Sign14Positive74Expression'] and sha(q)==sha(repo/e['source'])==e['source_sha256']=='35e7b08db362e7fd62c084f9ddf0f6ee51b12c3ad0b5b54886bd98a67106909b' and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for t in ('Expr.constant (p 0) * (Expr.var 1 + Expr.constant 1)','(g00 p).evalRing (fun i => v i + 1)','(oldB p).evalRing (Fin.cons 1 v)','(g01 p).evalRing (fun i => v i + 1)','(oldB p + Expr.constant 1).evalRing (Fin.cons 1 v)','(g26 p).evalRing (fun i => v i + 1)','(oldB p - Expr.var 2).evalRing (Fin.cons 1 v)'):assert t in s
nodes=(root/'research/nine-sharing-sign14-positive74-lean-draft/Sign14Positive74Nodes00.lean').read_text();nodes3=(root/'research/nine-sharing-sign14-positive74-lean-draft/Sign14Positive74Nodes03.lean').read_text();assert 'def g00 (p : Fin 4 → ℤ) : Expr (Fin 14) := (Expr.constant (p 0)) * (Expr.var 0)' in nodes and 'def g01 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g00 p) + (Expr.constant 1)' in nodes and 'def g26 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g01 p) - (Expr.var 1)' in nodes3
for b in range(-3,4):
 for v0 in range(-3,4):
  for v1 in range(-3,4):
   old=b*(v0+1);assert b*(v0+1)==old and b*(v0+1)+1==old+1 and b*(v0+1)+1-(v1+1)==old-v1
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-syntax-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
base=Path('/tmp/nine-sharing-sign14-positive74-syntax-check-20261110');st=json.loads((root/'research/nine-sharing-sign14-positive74-syntax-check/attempt01/state.json').read_text());assert st['status']=='PASS' and len(st['rows'])==10
for row in st['rows']:
 n=row['module'];assert sha(base/'lib/DiophantineConsistency'/(n+'.olean'))==row['object_sha256']
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'three proposed generic ring node identities, no row/model/file theorem'},indent=2))
