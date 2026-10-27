from pathlib import Path
import hashlib,json,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews'
p=Path('/tmp/control-bisim-perm215-root-latest').read_text().strip();p=Path(p)
s=json.loads((p/'state.json').read_text())
if s['status']!='PASS':raise RuntimeError('root pair not PASS')
B=V/'arithmetic-control-bisim-perm215-root-replay'
if B.exists():raise RuntimeError('fresh evidence only')
B.mkdir()
def rec(p):
 p=Path(p);return dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
def save(p,o):Path(p).write_text(json.dumps(o,indent=2)+'\n')
for r in json.loads((p/'pins.json').read_text()):
 if rec(r['path'])['sha256']!=r['sha256']:raise RuntimeError('freeze hash '+r['path'])
for q in p.iterdir():
 if q.is_file():shutil.copyfile(q,B/q.name)
shutil.copyfile('/tmp/control-bisim-perm215-root-console.log',B/'console.log')
shutil.copyfile(__file__,B/'freeze.py')
manifest=[dict(rec(q),path=str(q.relative_to(R))) for q in sorted(B.iterdir()) if q.name!='FILES.json']
save(B/'FILES.json',manifest)
packet=dict(status='PASS',scope='ROOT independent full proof/data review and fresh pair; no prerequisite compiler',state=rec(B/'state.json'),manifest=rec(B/'FILES.json'),counts=s['counts'],observations=s['observations'],records=s['records'],private_provider=str(p/'lib'),data_audit=rec(B/'data-audit.json'),driver=rec(B/'driver.py'),compiler_invocations=2)
save(V/'arithmetic-control-bisim-perm215-root-replay.json',packet)
print(json.dumps(dict(packet=rec(V/'arithmetic-control-bisim-perm215-root-replay.json'),manifest=rec(B/'FILES.json'),files=len(manifest),observations=s['observations'],records=[dict(module=x['module'],seconds=x['seconds'],object=x['object']['sha256']) for x in s['records']]),indent=2))
