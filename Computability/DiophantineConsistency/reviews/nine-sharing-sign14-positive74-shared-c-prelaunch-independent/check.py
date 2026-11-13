#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-shared-c-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='f2fae282e3317ba0ce96a5d342984f2050202128e917b2cebe0cd1e3deb9ce55' and sha(p/'source-manifest.json')=='a2d0f208686838a41cd0bb4054ec7b7697805f20cfdf7a04ef1f0133cadcd859'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74SharedC';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74SharedB'] and sha(q)==sha(repo/e['source'])==e['source_sha256']=='e0b008794b96543af115613bef926b556c6e032f43c9fdb670fd22c904e7c84c' and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for name,g,old in (('shared31',11,'shared31'),('shared26',14,'shared26'),('shared28',15,'shared28'),('center',16,'Sign14Optimized94.center'),('square_offset',18,"Sign14Optimized94.shared41''"),('shared40',20,'shared40')):
 assert f'theorem {name}_eval : (g{g:02} p).evalRing (fun i => v i + 1)' in s and f'({old} p).evalRing (Fin.cons 1 v)' in s
assert 'Fin.cases (1 : R) v (14 : Fin 15) = v 13 := by rfl' in s
new='\n'.join((root/f'research/nine-sharing-sign14-positive74-lean-draft/Sign14Positive74Nodes{i:02}.lean').read_text() for i in (1,2));old='\n'.join((root/f'research/nine-sharing-sign14-staged-syntax-check/src/DiophantineConsistency/SharingSeed14Shared{i:02}.lean').read_text() for i in (4,5,6,8));opt=(root/'research/nine-sharing-sign14-94gate-lean-draft/Sign14Optimized94.lean').read_text()
for z in ('(g07 p) * (g10 p)','(g02 p) + (g11 p)','(Expr.constant 4) * (g07 p)','(g13 p) + (Expr.constant 3)','(Expr.var 13) * (g14 p)','(g12 p) + (g15 p)','(g16 p) * (g16 p)','(g17 p) - (Expr.constant 1)','(g07 p) * (g07 p)','(g19 p) + (g14 p)'):assert z in new
for z in ('((shared23 p) * (shared17 p))','((Expr.constant (4 : ℤ)) * (shared23 p))','((shared24 p) + (Expr.constant (3 : ℤ)))','(Expr.var 14) + (Expr.constant (1 : ℤ))','((shared23 p) * (shared23 p))','((shared33 p) + (shared26 p))'):assert z in old
for z in ('(shared05 p + shared31 p) + shared28 p','center p * center p - Expr.constant 1'):assert z in opt
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-shared-b-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'six central shared-node identities only; remaining rows/model/file separate'},indent=2))
