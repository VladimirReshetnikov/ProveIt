from pathlib import Path
import hashlib,json,re
R=Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews'
obs=[]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def pin(e):assert sha(e['path'])==e['sha256'],e['path'];obs.append(dict(path=e['path'],sha256=e['sha256']))
fixed={
 'arithmetic-dag-loops-author.md':'9a704e1a252cff7e1b3189152ed76d610586b64ae38e1274ff41146ec3c342c3',
 'arithmetic-dag-loops-replay.json':'26c0ebcee1bad71b6b613a4ffeda3e4e912299bfbf71679104a79421087ee0e5',
 'arithmetic-dag-loops-peer.md':'4610e09472aa06c4e32f65d247398d7db194865843001c242c4efc10d6bffaff',
 'arithmetic-dag-loops-peer-replay.json':'3ff36b6a6d02d9420fb486517813b7f2deb3867d6f64f45406e13f7ff8616077'}
for n,h in fixed.items():pin(dict(path=str(V/n),sha256=h))
a=json.loads((V/'arithmetic-dag-loops-replay.json').read_text());p=json.loads((V/'arithmetic-dag-loops-peer-replay.json').read_text())
assert a['status']==p['status']=='PASS'
for d,count in [(a,45),(p,35)]:
 pin(d['inputs']);pin(d['bundle_manifest'])
 m=d['bundle_manifest'];rows=json.loads(Path(m['path']).read_text());assert len(rows)==count
 for e in rows:pin(dict(path=str(Path(m['path']).parent/e['path']),sha256=e['sha256']))
for k in ['verified_state','archived_verified_state','archived_inputs','original_failed_wrapper_state','verification_failure_note']:pin(p[k])
for e in p['drivers']:pin(e)
i=json.loads(Path(p['inputs']['path']).read_text())
assert i['counts']==dict(custom=136,Foundation=95,source_matching_reuse=130,reused_artifacts=415,planned_unchanged_source_refresh=6,external=39)
assert len(i['initial_observations'])==2528
for e in i['initial_observations']:pin(e)
assert len(a['records'])==len(p['records'])==8
for ar,pr in zip(a['records'],p['records']):
 assert ar['module']==pr['module']and not pr['module'].startswith('Foundation.')and pr['byte_identical']
 assert ar['source']['sha256']==pr['source']['sha256']and ar['object']['sha256']==pr['object']['sha256']
 for row in [ar,pr]:
  assert row['exit_code']==0 and row['command'][1:4]==['-M6000','-j1','-DElab.async=false']
  for k in ['source','snapshot','log','timing','object']:pin(row[k])
  assert not Path(row['object']['path']).is_symlink()
  log=Path(row['log']['path']).read_text();assert not re.search(r'\b(?:warning|error):|sorryAx',log)
  reports=[list(x)for x in re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log)]
  assert reports==row['axiom_reports']
  for _,ax in reports:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'}
assert all(Path(r['log']['path']).read_text()==''for r in p['records'][:-1])
assert sum(len(r['axiom_reports'])for r in p['records'])==8
out=Path('/tmp/arithmetic-dag-loops-root-authentication.json')
out.write_text(json.dumps(dict(status='PASS',scope='Root reauthentication of all independent eight-build evidence; no compiler rerun.',count=len(obs),observations=obs),indent=2)+'\n')
print(json.dumps(dict(status='PASS',observations=len(obs),distinct=len({x['path']for x in obs})),indent=2))
