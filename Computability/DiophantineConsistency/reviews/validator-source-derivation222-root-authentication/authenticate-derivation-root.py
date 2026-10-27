from pathlib import Path
import hashlib,json,re
R=Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews'
obs=[]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def pin(p,h):assert sha(p)==h,str(p);obs.append(dict(path=str(p),sha256=h))
fixed={
 'validator-source-derivation222-author.md':'5e40bdc7c7e1d4f59e9259f3e45bd31289e62e28d26ef499f6f1e1239ba2b176',
 'validator-source-derivation222-replay.json':'d688e71398add24dc4e54cdb2ba002d45524c3fbe2af324bc2d95f411f4e195c',
 'validator-source-derivation222-cache.json':'68c4efd389e168c6991282380c1aaa4c1a449c107c331fe18e3623754e1d7d6d',
 'validator-source-derivation222-peer.md':'3f69dbd65832aea4e6b7e4926b8040b0b49763f97b7b8610d31e2ec7a02402d3',
 'validator-source-derivation222-peer-replay.json':'c375939e62d66e03f0730d270b83917c0dd063f66842e8d5dbfd75c2e9166f3e'}
for p,h in fixed.items():pin(V/p,h)
for dirname,h,count in [('validator-source-derivation222-author-replay','35842d9979b8911f73b51c9c9dec8dc9a5563f4665092d80df6cb406b86a7d8d',54),('validator-source-derivation222-peer-replay','8c20a4431aa19b7ab8f8143516246e5d1dcc2540227fa9232389940c75f40908',11)]:
 b=V/dirname;pin(b/'FILES.json',h);rows=json.loads((b/'FILES.json').read_text());assert len(rows)==count
 for x in rows:pin(b/x['path'],x['sha256'])
c=json.loads((V/'validator-source-derivation222-cache.json').read_text())
assert len(c['modules'])==164 and sum(len(x['objects'])for x in c['modules'])==515 and len(c['external'])==40
assert sum(x['module'].startswith('Foundation.')for x in c['modules'])==117
for k in ['compiler','manifest','toolchain']:pin(c[k],c[k+'_sha256'])
for x in c['parent_receipts']+c['inherited_observations']:pin(x['path'],x['sha256'])
for x in c['modules']:
 pin(x['source'],x['source_sha256'])
 for o in x['objects']:pin(o['path'],o['sha256'])
for x in c['external']:pin(x['path'],x['sha256'])
a=json.loads((V/'validator-source-derivation222-replay.json').read_text())
p=json.loads((V/'validator-source-derivation222-peer-replay.json').read_text())
assert a['status']==p['status']=='PASS'and len(a['completed'])==len(p['records'])==2
for ar,pr in zip(a['completed'],p['records']):
 assert ar['module']==pr['module']and ar['object']['sha256']==pr['object']['sha256']and pr['matches_author']
 assert ar['exit_code']==pr['exit_code']==0
 for k in ['source','snapshot','log','timing']:
  pin(ar[k],ar[k+'_sha256'])
  pin(pr[k]['path'],pr[k]['sha256'])
 for row in [ar,pr]:
  pin(row['object']['path'],row['object']['sha256']);assert not Path(row['object']['path']).is_symlink()
  log=Path(row['log']if isinstance(row['log'],str)else row['log']['path']).read_text()
  assert not re.search(r'\b(?:error|warning):|sorryAx',log)
  reports=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log)
  assert len(reports)==len(row['axiom_reports'])
  for _,ax in reports:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'}
assert sum(len(x['axiom_reports'])for x in p['records'])==17
result=dict(status='PASS',scope='Root reauthentication of frozen author and independent peer evidence; no compiler invocation.',observations=obs,count=len(obs))
Path('/tmp/validator-source-derivation222-root-authentication.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(status='PASS',observations=len(obs),distinct=len({x['path']for x in obs})),indent=2))
