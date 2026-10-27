from pathlib import Path
import hashlib,json,re
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
V=R/'Computability/DiophantineConsistency/reviews'
observations=[]
def sha(f): return hashlib.sha256(Path(f).read_bytes()).hexdigest()
def pin(p,h):
 assert sha(p)==h,str(p)
 observations.append(dict(path=str(p),sha256=h))
fixed={
 'validator-source-negation222-replay.json':'cfb206112f8eb04f4a104a7313b8ef51cb566bb82509518f731d78accd81351e',
 'validator-source-negation222-author.md':'9dcf2b99736157f99d9015580dd275a5b2229d79ad672859c91b1ec9286ca025',
 'validator-source-negation222-peer.md':'0f805ca5f882b6400a77689b1f9475b00ef1ca984b6d1a390563a5064dc20ae7',
 'validator-source-negation222-peer-replay.json':'f9013d100f8e3365c7fe19e39857ad9bba3fa5f3ef084c2a576d8745159294ef',
 'validator-source-negation222-cache.json':'fb33ff9c1bf83ca829d82958beadb725e3db1a347878caac2ab1a98e55fc4fae'}
for p,h in fixed.items(): pin(V/p,h)
for dirname,h,count in [('validator-source-negation222-author-replay','70c7319c28aab8df8b6ebb065a7d3ad017a599266bd4d5dc658e64b3fba57920',27),('validator-source-negation222-peer-replay','44144ed5d421b8aba56c87b3ca1b5dacbcbeaa86910ca01cede9c9e1ea38b209',10)]:
 b=V/dirname;pin(b/'FILES.json',h);files=json.loads((b/'FILES.json').read_text());assert len(files)==count
 for x in files:pin(b/x['path'],x['sha256'])
c=json.loads((V/'validator-source-negation222-cache.json').read_text())
assert c['counts']==dict(cached=152,foundation=117,artifacts=503,boundaries=40)
for k in ['compiler','manifest','toolchain']:pin(c[k],c[k+'_sha256'])
for x in c['parent_receipts']:pin(x['path'],x['sha256'])
for x in c['modules']:
 pin(x['source'],x['source_sha256'])
 for o in x['objects']:pin(o['path'],o['sha256'])
for x in c['external']:pin(x['path'],x['sha256'])
a=json.loads((V/'validator-source-negation222-replay.json').read_text())
p=json.loads((V/'validator-source-negation222-peer-replay.json').read_text())
assert a['status']==p['status']=='PASS'
assert len(a['completed'])==len(p['commands'])==2
for ar,pr in zip(a['completed'],p['commands']):
 assert ar['module']==pr['module'] and ar['object']['sha256']==pr['object']['sha256']
 for row in [ar,pr]:
  assert row['exit_code']==0
  pin(row['source'],row['source_sha256']);pin(row['snapshot'],row['source_sha256'])
  for k in ['log','timing']:pin(row[k],row[k+'_sha256'])
  pin(row['object']['path'],row['object']['sha256'])
  assert not Path(row['object']['path']).is_symlink()
  text=Path(row['log']).read_text();assert not re.search(r'\b(?:warning|error):',text)
  reports=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text)
  assert len(reports)==len(row['axiom_reports'])
  for _,ax in reports: assert set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'}
assert sum(len(x['axiom_reports'])for x in p['commands'])==16
state=dict(status='PASS',scope='Root reauthentication of complete frozen author/independent peer evidence; no compiler invocation.',observation_count=len(observations),observations=observations)
Path('/tmp/validator-source-negation222-root-authentication.json').write_text(json.dumps(state,indent=2)+'\n')
print(json.dumps(dict(status='PASS',observations=len(observations),distinct=len({x['path']for x in observations})),indent=2))
