"""Freeze only this new read-only proposal packet; no compilation or overlay."""
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')


def rec(path):
    p = Path(path)
    return {'path': str(p.relative_to(ROOT)),
            'sha256': hashlib.sha256(p.read_bytes()).hexdigest(),
            'bytes': p.stat().st_size}


plan = json.loads((HERE/'cache-plan.json').read_text())
for r in plan['authenticated_pins']:
    assert hashlib.sha256(Path(r['path']).read_bytes()).hexdigest() == r['sha256'], r
old = json.loads((HERE/'cache-plan-v1.json').read_text())
assert rec(HERE/'PROPOSAL-v1.md')['sha256'] == old['proposal']['sha256']
assert rec(HERE/'PROPOSAL.md')['sha256'] == plan['proposal']['sha256']
assert rec(HERE/'planner.py')['sha256'] == plan['planner']['sha256']
files = [rec(p) for p in sorted(HERE.iterdir()) if p.is_file() and p.name != 'FILES.json']
assert len(files) == 9, [f['path'] for f in files]
(HERE/'FILES.json').write_text(json.dumps(files,indent=2)+'\n')
print(json.dumps({'pins_rechecked':len(plan['authenticated_pins']),
    'files':len(files), 'manifest':rec(HERE/'FILES.json'),
    'proposal':rec(HERE/'PROPOSAL.md'), 'plan':rec(HERE/'cache-plan.json')},indent=2))
