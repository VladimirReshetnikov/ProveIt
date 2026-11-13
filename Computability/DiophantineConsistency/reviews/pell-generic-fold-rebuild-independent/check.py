#!/usr/bin/env python3
"""Audit three-stage retained source and receipt without invoking Lean."""
import hashlib,json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/pell-generic-fold-rebuild';o=P/'observations/attempt01';t=json.loads((o/'terminal.json').read_text());root=pathlib.Path(t['root'])
def sha(x):return hashlib.sha256(pathlib.Path(x).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(t['status']=='PASS' and sha(P/'run.py')==t['runner_sha256'],'result/runner')
for p,h in t['pins'].items():need(sha(p)==h,'pin '+p)
old={'PellFold':'/tmp/pell-all-index-fold-ad1a76zq/PellFold.lean','PellOddFold':'/tmp/pell-all-index-odd-fold-t52feqmz/PellOddFold.lean','PellRecovery':'/tmp/pell-all-index-recovery-oi9pydkd/PellRecovery.lean'}
need(sha(old['PellFold'])=='d1c55d280615310987f55d68717a671e9ce3cd917bd83697da25129d05388d34','old fold')
fold=pathlib.Path(old['PellFold']).read_bytes();need(fold.startswith(b'import Direct80Joined\n'),'old import')
need((P/'PellFold.lean').read_bytes()==fold.replace(b'import Direct80Joined\n',b'import DiophantineConsistency.ArithmeticPellHalfIndex\n',1),'single-line delta')
for n in ('PellOddFold','PellRecovery'):need((P/(n+'.lean')).read_bytes()==pathlib.Path(old[n]).read_bytes(),'unchanged '+n)
expected={'PellFold':'5a45b94a6ff3dea0ba802c852b84f83daa99aace8415ede0bf682a11100a908b','PellOddFold':'853721216a20dbf04c1babafbbb79526d92db0aee5f3a6127625d86208bc3175','PellRecovery':'0deec819d3d49c3ebfe8179175613095e6497272cfc6cc1d7723c8df6b32524a'}
need([x['name'] for x in t['stages']]==list(expected),'stage ordering');selected=[]
for stage in t['stages']:
 n=stage['name'];s=P/(n+'.lean');out=o/(n+'.stdout');err=o/(n+'.stderr')
 need(stage['exit']==0 and stage['reason'] is None and stage['object_sha256']==sha(root/(n+'.olean'))==expected[n],'stage '+n)
 need(sha(s)==sha(o/(n+'.source.txt'))==sha(root/(n+'.lean')),'source '+n)
 need(sha(out)==stage['stdout_sha256'] and sha(err)==stage['stderr_sha256'],'logs '+n)
 reports=re.findall(r'^#print axioms ([\w.]+)$',s.read_text(),re.M)
 need(out.read_text()==''.join(f"'{x}' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for x in reports) and err.read_text()=='','reports '+n)
 for m in re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M):
  rel=m.replace('.','/')+'.olean';p=next((pathlib.Path(x)/rel for x in t['lean_path'].split(':') if (pathlib.Path(x)/rel).is_file()),None)
  need(p is not None,'import '+m)
  h=expected[m] if m in expected else '6142ab8eaac6e281c3372817a6f1a8cbc14704717d4f5479c28603c754c3a4d7'
  need(sha(p)==h,'selected '+m);selected.append({'stage':n,'module':m,'path':str(p),'sha256':sha(p)})
print(json.dumps({'status':'PASS','objects':expected,'selected':selected,'lean_replayed':False},indent=2,sort_keys=True))
