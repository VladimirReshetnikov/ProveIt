from pathlib import Path
import hashlib,json,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews';B=V/'arithmetic-dag-macros-perm222-root-replay'
p=Path(Path('/tmp/arithmetic-dag-macros-perm222-root-latest').read_text().strip());s=json.loads((p/'ROOT.json').read_text())
if s['status']!='PASS' or B.exists():raise RuntimeError('PASS/fresh evidence required')
def rec(q):
 q=Path(q);return dict(path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size)
def save(q,o):Path(q).write_text(json.dumps(o,indent=2)+'\n')
for x in json.loads((p/'pins.json').read_text()):
 if rec(x['path'])['sha256']!=x['sha256']:raise RuntimeError('freeze hash '+x['path'])
B.mkdir()
for q in p.iterdir():
 if q.is_file():shutil.copyfile(q,B/q.name)
shutil.copyfile('/tmp/arithmetic-dag-macros-perm222-root-console.log',B/'console.log')
a=json.loads(Path('/tmp/arithmetic-dag-macros-perm222-root-attempts.json').read_text())
if len(a)!=2:raise RuntimeError('two ROOT attempts including preflight')
f=Path(a[0]);prior=json.loads((f/'ROOT.json').read_text())
if prior['status']!='FAILED' or prior['records']:raise RuntimeError('only preflight failure')
for q in f.iterdir():
 if q.is_file():
  o=B/'preflight-1'/q.name;o.parent.mkdir(exist_ok=True);shutil.copyfile(q,o)
shutil.copyfile(__file__,B/'freeze.py')
manifest=[dict(rec(q),path=str(q.relative_to(R))) for q in sorted(B.rglob('*')) if q.is_file()];save(B/'FILES.json',manifest)
packet=dict(status='PASS',scope='ROOT independent complete macro-source review and fresh two-leaf replay; no dependency refresh',state=rec(B/'ROOT.json'),manifest=rec(B/'FILES.json'),private_provider=str(p/'lib'),counts=s['counts'],observations=s['observations'],provider_artifacts=s['provider_artifacts'],records=s['records'],compiler_invocations=2,preflight_failures=1)
save(V/'arithmetic-dag-macros-perm222-root-replay.json',packet)
print(json.dumps(dict(packet=rec(V/'arithmetic-dag-macros-perm222-root-replay.json'),manifest=rec(B/'FILES.json'),files=len(manifest),observations=s['observations'],provider_artifacts=s['provider_artifacts'],seconds=[x['seconds'] for x in s['records']]),indent=2))
