#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-shared-a-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='76e7fbc9822aa1fb8ab826e124261012ce69f6e07a49d0fe4e708f7e9d822410' and sha(p/'source-manifest.json')=='1bd1fee0826ced463c9372f1a607fafd137d09d63ed5cd9bd90c90425dd3bb76'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74SharedA';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74Row02'] and sha(q)==sha(repo/e['source'])==e['source_sha256']=='80b9620360c3258eea9a74ca9b4f661415f0b67e25995c1465e413bf7b7a98eb' and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for new,old in ((2,5),(3,8),(4,12)):
 assert f'theorem shared{old:02}_eval : (g{new:02} p).evalRing (fun i => v i + 1)' in s and f'(shared{old:02} p).evalRing (Fin.cons 1 v)' in s
for i in (1,9):assert f'Fin.cases (1 : R) v ({i} : Fin 15) = v {i-1} := by rfl' in s
new=(root/'research/nine-sharing-sign14-positive74-lean-draft/Sign14Positive74Nodes00.lean').read_text();assert all(x in new for x in ('(Expr.var 8) * (g01 p)','(g01 p) * (g01 p)','(g03 p) * (g01 p)'))
a=(root/'research/nine-sharing-sign14-staged-syntax-check/src/DiophantineConsistency/SharingSeed14Shared01.lean').read_text();b=(root/'research/nine-sharing-sign14-staged-syntax-check/src/DiophantineConsistency/SharingSeed14Shared02.lean').read_text();assert 'def shared05' in a and '(Expr.var 9)' in a and 'def shared08' in a and 'def shared12' in b and '((shared08 p) *' in b
for beta in range(-3,4):
 for v0,v8 in ((0,0),(1,2),(-2,3)):
  t=beta*(v0+1)+1;assert (v8+1)*t==(v8+1)*t and t*t==t**2 and (t*t)*t==t**3
for f in ('nine-sharing-sign14-positive74-lean-draft-independent','nine-sharing-sign14-positive74-row02-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'three generic shared-node eval identities only; full rows/model/file separate'},indent=2))
