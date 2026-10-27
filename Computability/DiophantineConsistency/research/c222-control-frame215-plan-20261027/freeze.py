"""Rehash the new read-only plan, then freeze its local evidence manifest."""
from pathlib import Path
import hashlib
import json
import shutil

HERE = Path(__file__).resolve().parent
R = Path('/home/codex/.codex/worktrees/46be/Proofs')


def rec(p):
    p = Path(p)
    if not p.is_absolute():
        p = R / p
    b = p.read_bytes()
    return dict(path=str(p), sha256=hashlib.sha256(b).hexdigest(), bytes=len(b))


assert shutil.disk_usage('/tmp').free >= 512*1024**2
planp = HERE/'cache-plan.json'
assert rec(planp)['sha256'] == 'd0570b2d5abda25e5d4026fa9216f4e41cbb4d80ff17c91368cce973f56e595d'
plan = json.loads(planp.read_text())
count = 0
paths = set()
for x in plan['authenticated_pins'] + [p['provider'] for p in plan['first_providers']]:
    a = rec(x['path'])
    assert a['sha256'] == x['sha256']
    if 'bytes' in x:
        assert a['bytes'] == x['bytes']
    count += 1
    paths.add(a['path'])
assert len(plan['first_providers']) == 640
report = dict(status='FROZEN_READ_ONLY_NO_COMPILER', inventory=rec(planp),
    observations=count, unique_paths=len(paths), providers=640,
    free_bytes=shutil.disk_usage('/tmp').free, reserve_bytes=512*1024**2)
(HERE/'freeze-summary.json').write_text(json.dumps(report, indent=2)+'\n')
files = sorted(p for p in HERE.iterdir() if p.is_file() and p.name != 'FILES.json')
assert all(not p.is_symlink() for p in files)
manifest = [rec(p) for p in files]
(HERE/'FILES.json').write_text(json.dumps(manifest, indent=2)+'\n')
print(json.dumps(dict(report=rec(HERE/'freeze-summary.json'), files=len(manifest),
    manifest=rec(HERE/'FILES.json')), indent=2))
