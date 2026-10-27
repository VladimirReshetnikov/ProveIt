"""Freeze only metadata for the proposed CheckerMachine client."""
from pathlib import Path
import hashlib,json,os,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs');H=Path(__file__).resolve().parent
pins={};observations=0
def rec(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
def check(x):
 global observations
 a=rec(x['path']);assert a['sha256']==x['sha256'],x
 if 'bytes'in x:assert a['bytes']==x['bytes'],x
 pins[a['path']]=a;observations+=1;return a
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
assert shutil.disk_usage('/tmp').free>=512*1024**2
assert not (H/'FILES.json').exists()
plan=H/'cache-plan.json';check(dict(path=str(plan),sha256='d46e7377a473a7c15afc40da24c0aea4f9c2f24aa2bb498999d8f818a4019ec4'))
p=json.loads(plan.read_text());assert p['status']=='READ_ONLY_NO_LEAN_OVERLAY_OR_REFRESH'
for x in p['authenticated_pins']:check(x)
assert len(p['first_providers'])==681
for x in p['first_providers']:check(x['provider'])
for x in [p['proposal'],p['readme'],p['planner'],rec(H/'RESULTS.md'),rec(__file__)]:check(x)
log=Path('/tmp/checker-machine215-plan-attempt1.log');dest=H/'planner-attempt-1.log'
assert log.is_file()and not log.is_symlink()and not dest.exists();os.link(log,dest)
check(rec(log));check(rec(dest))
save(H/'reauthentication.json',dict(status='PASS_READ_ONLY',observations=observations,unique_paths=len(pins),pins=list(pins.values()),compiler_invocations=0,overlays=0,new_lean_sources=0))
files=sorted(x for x in H.iterdir()if x.is_file())+[Path(p['proposal']['path'])]
save(H/'FILES.json',[dict(rec(x),path=str(x.relative_to(R)))for x in files])
assert shutil.disk_usage('/tmp').free>=512*1024**2
print(json.dumps(dict(plan=rec(plan),readme=rec(H/'README.md'),results=rec(H/'RESULTS.md'),manifest=rec(H/'FILES.json'),files=len(files),observations=observations,unique_paths=len(pins)),indent=2))
