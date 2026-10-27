from pathlib import Path
import hashlib,json,re
R=Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews'
obs=[]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def pin(e):assert sha(e['path'])==e['sha256'],e['path'];obs.append(e)
for n,h in [('validator-seed-padding222-peer.md','307d16800ba2a14b82742b6ed3f9b61c4d16ca7a6abd979049edf61e266354f6'),('validator-seed-padding222-peer-replay.json','402b68dd80360713fc360b843819c104208ef50cfa07263644c67c23700f4a5e'),('validator-seed-padding222-replay.json','7e789439d2947be695cefef69378da3d1426c0b5298be5afd30dc86b5e45c228')]:pin(dict(path=str(V/n),sha256=h))
p=json.loads((V/'validator-seed-padding222-peer-replay.json').read_text());a=json.loads((V/'validator-seed-padding222-replay.json').read_text())
assert p['status']==a['status']=='PASS'
pin(p['inputs']);pin(p['driver']);pin(p['bundle_manifest'])
i=json.loads(Path(p['inputs']['path']).read_text())
assert i['counts']==dict(cached=160,foundation=117,artifacts=511,boundaries=40)
for e in i['pins']:pin(e)
for packet,count in [(a,31),(p,9)]:
 manifest=packet['bundle_manifest'];pin(manifest);data=json.loads(Path(manifest['path']).read_text())
 rows=data if isinstance(data,list)else data['files'];assert len(rows)==count
 for e in rows:pin(dict(path=str(Path(manifest['path']).parent/e['path']),sha256=e['sha256']))
for ar,pr in zip(a['records'],p['records']):
 assert ar['module']==pr['module']and pr['matches_author']and ar['object']['sha256']==pr['object']['sha256']
 for row in [ar,pr]:
  assert row['exit_code']==0
  for k in ['source','snapshot','log','timing','object']:pin(row[k])
  assert not Path(row['object']['path']).is_symlink()
  log=Path(row['log']['path']).read_text();assert not re.search(r'\b(?:warning|error):|sorryAx',log)
assert len(p['records'])==2 and sum(len(x['axiom_reports'])for x in p['records'])==11
out=Path('/tmp/validator-seed-padding222-root-authentication.json')
out.write_text(json.dumps(dict(status='PASS',scope='Author root reauthentication of independent peer evidence; no additional compiler invocation.',count=len(obs),observations=obs),indent=2)+'\n')
print(json.dumps(dict(status='PASS',observations=len(obs)),indent=2))
