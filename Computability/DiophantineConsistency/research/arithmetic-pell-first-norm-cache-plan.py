"""Read-only extension of the accepted internal Pell cache inventory."""
from pathlib import Path
import hashlib, json

DC = Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency')
base = DC / 'research/arithmetic-pell-congruences-cache-plan.json'
peer = DC / 'reviews/arithmetic-pell-congruences-peer-replay.json'
def record(path):
    p = Path(path); b = p.read_bytes()
    return dict(path=str(p), sha256=hashlib.sha256(b).hexdigest(), bytes=len(b))
def require(ok, message):
    if not ok:
        raise RuntimeError(message)
def check(x):
    require(record(x['path'])['sha256'] == x['sha256'], x['path'])

check(dict(path=str(base),sha256='a5182706264e4a28a0ff58f2a97cf32a2860e7246ff3c04d76a163a9e83f8f99'))
check(dict(path=str(peer),sha256='a03102eb692bd0028747b72bce9eca08539af01f2dd967d496f16dc5c7b48238'))
plan = json.loads(base.read_text())
p = json.loads(peer.read_text()); main = p['records'][0]
require(main['module'] == 'DiophantineConsistency.ArithmeticPellCongruences' and
        main['exit_code'] == 0, 'accepted congruence main')
for x in [main['source'],main['object']]: check(x)
plan['modules'].append(dict(module=main['module'],source=main['source'],objects=[main['object']],
    imports=['Init','DiophantineConsistency.ArithmeticPellClassification'],
    provenance='Independently accepted congruence main, commit6809609c61'))
plan['pins'] += [record(base),record(peer),record(DC/'reviews/arithmetic-pell-congruences-root.md'),
    record(__file__),main['source'],main['object']]
plan['direct_imports'] = [main['module']]
plan['counts'] = dict(custom=98,Foundation=95,artifacts=383,external=38,
    external_companions=114,fresh_prerequisites=0)
require(len(plan['modules']) == 98 and sum(len(m['objects']) for m in plan['modules']) == 383,
        'exact98/383 scope')
for x in plan['pins']: check(x)
plan['scope'] = ('Two new internal Pell first-norm leaves only. Reuse98 cached modules; '
    'no dependency/Foundation refresh, no complete carrier or PA/HA equivalence claim.')
out = DC/'research/arithmetic-pell-first-norm-cache-plan.json'
require(not out.exists(),'fresh cache plan')
out.write_text(json.dumps(plan,indent=2)+'\n')
print(json.dumps(dict(output=record(out),counts=plan['counts'],pins=len(plan['pins']))))
