#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-shared-b-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='33b85c3a2990f4fc2ec392d463ec9757dc60aaaa7847b005cdcc9e6fff51f8bc' and sha(p/'source-manifest.json')=='4cf9c942560f95813d6beb0af44a1a7b7504c39872e922d015576d50efcd7acd'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74SharedB';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74SharedA'] and sha(q)==sha(repo/e['source'])==e['source_sha256']=='4ed2a11c2582bf4f5fdb4763fd0318dc2fa814a94645917ef26064756b81dadc' and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for new,old in ((5,13),(6,18),(7,23),(9,16),(10,17)):
 assert f'theorem shared{old:02}_eval : (g{new:02} p).evalRing (fun i => v i + 1)' in s and f'(shared{old:02} p).evalRing (Fin.cons 1 v)' in s
for i in (8,11,12):assert f'Fin.cases (1 : R) v ({i} : Fin 15) = v {i-1} := by rfl' in s
new='\n'.join((root/f'research/nine-sharing-sign14-positive74-lean-draft/Sign14Positive74Nodes{i:02}.lean').read_text() for i in (0,1));old='\n'.join((root/f'research/nine-sharing-sign14-staged-syntax-check/src/DiophantineConsistency/SharingSeed14Shared{i:02}.lean').read_text() for i in (2,3,4))
for z in ('(Expr.var 7) * (g04 p)','(g02 p) * (g05 p)','(g06 p) + (g05 p)','(Expr.var 10) + (Expr.var 11)','(g08 p) * (g05 p)','(g09 p) + (Expr.var 10)'):assert z in new
for z in ('((shared05 p) * (shared13 p))','((shared18 p) + (shared13 p))','(Expr.var 8) + (Expr.constant (1 : ℤ))','(Expr.var 11) + (Expr.constant (1 : ℤ))','(Expr.var 12) + (Expr.constant (1 : ℤ))','((shared16 p) +'):assert z in old
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-shared-a-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'five generic shared-node eval identities only; full rows/model/file separate'},indent=2))
