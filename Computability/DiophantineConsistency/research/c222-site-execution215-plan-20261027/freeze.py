"""Freeze only the read-only site proposal; never execute Lean or a provider."""
from pathlib import Path
import hashlib
import json

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
HERE = Path(__file__).resolve().parent


def rec(p):
    p = Path(p)
    b = p.read_bytes()
    return dict(path=str(p.relative_to(ROOT)),
                sha256=hashlib.sha256(b).hexdigest(), bytes=len(b))


plan = json.loads((HERE/'cache-plan.json').read_text())
assert plan['status'] == 'READ_ONLY_NO_LEAN_OVERLAY_OR_REFRESH'
provider_keys = [(x['module'], ''.join(Path(x['provider']['path']).suffixes))
                 for x in plan['first_providers']]
assert len(set(provider_keys)) == len(provider_keys) == 622
for x in plan['authenticated_pins']:
    b = Path(x['path']).read_bytes()
    assert hashlib.sha256(b).hexdigest() == x['sha256'], x
    assert len(b) == x['bytes'], x
for name in ['proposal', 'planner']:
    assert rec(Path(plan[name]['path']))['sha256'] == plan[name]['sha256']
assert (HERE/'planner-attempt01.log').read_text().endswith(
    "FileNotFoundError: [Errno 2] No such file or directory: '/home/codex/.codex/worktrees/46be/Proofs/ROOT.json'\n")
final_log = json.loads((HERE/'planner.log').read_text())
assert final_log['counts'] == plan['counts']
assert final_log['plan']['sha256'] == rec(HERE/'cache-plan.json')['sha256']
old_plan = json.loads((HERE/'cache-plan-attempt02.json').read_text())
assert old_plan['proposal']['sha256'] == rec(HERE/'PROPOSAL-attempt02.md')['sha256']
old_log = json.loads((HERE/'planner-attempt02.log').read_text())
assert old_log['plan']['sha256'] == rec(HERE/'cache-plan-attempt02.json')['sha256']
files = [rec(p) for p in sorted(HERE.iterdir()) if p.is_file() and p.name != 'FILES.json']
assert len(files) == 11, [x['path'] for x in files]
(HERE/'FILES.json').write_text(json.dumps(files, indent=2)+'\n')
print(json.dumps(dict(status='FROZEN_READ_ONLY_PLAN', pins=len(plan['authenticated_pins']),
    manifest=rec(HERE/'FILES.json'), proposal=rec(HERE/'PROPOSAL.md'),
    plan=rec(HERE/'cache-plan.json'), files=len(files)), indent=2))
