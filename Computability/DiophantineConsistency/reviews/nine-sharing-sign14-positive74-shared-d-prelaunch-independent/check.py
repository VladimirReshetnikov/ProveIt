#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-shared-d-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='12cbc81f7f1c7054aa4e6cc0933e022831283b944b33ed37a666bc7db1311ad9' and sha(p/'source-manifest.json')=='b957ff50413ddc8bbea301e261d4719445602f054430b19c1bc87408434b82ef'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74SharedD';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74RowsOuter'] and sha(q)==sha(repo/e['source'])==e['source_sha256']=='f517166583367735c752b629a7c41383522edabad673ea8eae8f7f56b1b87de1' and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for name,g,old in (('rank',28,"Sign14Optimized90.shared14'"),('shared09',32,'shared09'),('shared27',33,"Sign14Optimized90.shared27'"),('difference',34,'Sign14Optimized86.sharedDiff')):
 assert f'theorem {name}_eval : (g{g:02} p).evalRing (fun i => v i + 1)' in s and f'({old} p).evalRing (Fin.cons 1 v)' in s
for i in (1,2,3):assert f'Fin.cases (1 : R) v ({i} : Fin 15) = v {i-1} := by rfl' in s
new='\n'.join((root/f'research/nine-sharing-sign14-positive74-lean-draft/Sign14Positive74Nodes{i:02}.lean').read_text() for i in (3,4));old90=(root/'research/nine-sharing-sign14-90gate-lean-draft/Sign14Optimized90.lean').read_text();old93=(root/'research/nine-sharing-sign14-93gate-lean-draft/Sign14Optimized93.lean').read_text();old86=(root/'research/nine-sharing-sign14-86gate-lean-draft/Sign14Optimized86.lean').read_text();old='\n'.join((root/f'research/nine-sharing-sign14-staged-syntax-check/src/DiophantineConsistency/SharingSeed14Shared{i:02}.lean').read_text() for i in (0,1))
for z in ('(g01 p) - (Expr.var 1)','(g00 p) * (g26 p)','(g27 p) + (Expr.var 2)','(g28 p) * (g03 p)','(g01 p) * (Expr.constant (p 3))','(Expr.constant (p 2)) + (g30 p)','(g31 p) * (Expr.var 0)','(g29 p) + (g32 p)','(g33 p) - (g28 p)'):assert z in new
for z in ("Sign14Optimized93.shared14' p", "shared14' p * shared08 p + shared09 p"):assert z in old90
assert 'b * (b - Expr.var 2) + (Expr.var 3 + Expr.constant 1)' in old93 and "Sign14Optimized90.shared27' p - Sign14Optimized90.shared14' p" in old86 and '((shared04 p) * ((Expr.var 1)' in old and '(Expr.constant (p 2)) + (shared00 p)' in old
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-rows-outer-retry01-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'rank and three shared evaluations only; remaining rows/model/file separate'},indent=2))
