"""Read-only extension of the accepted internal Pell cache inventory."""
from pathlib import Path
import hashlib, json

DC = Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency')
base = DC / 'research/arithmetic-pell-classification-cache-plan.json'
peer = DC / 'reviews/arithmetic-pell-classification-peer-replay.json'
def record(path):
    p = Path(path); b = p.read_bytes()
    return dict(path=str(p), sha256=hashlib.sha256(b).hexdigest(), bytes=len(b))
def require(ok, message):
    if not ok:
        raise RuntimeError(message)
def check(x):
    require(record(x['path'])['sha256'] == x['sha256'], x['path'])

check(dict(path=str(base),sha256='e2ede81b0aa4ddb9f54f92eb8196e6456df15891b3dd292be4e14bcbdcbadc29'))
check(dict(path=str(peer),sha256='6794e6e051a46a6bfa737b164ed78cb029789a8438bdb428ef9ca148a440b31f'))
plan = json.loads(base.read_text())
p = json.loads(peer.read_text()); main = p['records'][0]
require(main['module'] == 'DiophantineConsistency.ArithmeticPellClassification' and
        main['exit_code'] == 0, 'accepted classification main')
for x in [main['source'],main['object']]: check(x)
plan['modules'].append(dict(module=main['module'],source=main['source'],objects=[main['object']],
    imports=['Init','DiophantineConsistency.ArithmeticPellRecurrence'],
    provenance='Independently accepted classification main, commit4d1841128e'))
plan['pins'] += [record(base),record(peer),record(DC/'reviews/arithmetic-pell-classification-root.md'),
    record(__file__),main['source'],main['object']]
plan['direct_imports'] = [main['module']]
plan['counts'] = dict(custom=97,Foundation=95,artifacts=382,external=38,
    external_companions=114,fresh_prerequisites=0)
require(len(plan['modules']) == 97 and sum(len(m['objects']) for m in plan['modules']) == 382,
        'exact97/382 scope')
for x in plan['pins']: check(x)
plan['scope'] = ('Two new internal Pell congruence leaves only. Reuse97 cached modules; '
    'no dependency/Foundation refresh, no complete carrier or PA/HA equivalence claim.')
out = DC/'research/arithmetic-pell-congruences-cache-plan.json'
require(not out.exists(),'fresh cache plan')
out.write_text(json.dumps(plan,indent=2)+'\n')
print(json.dumps(dict(output=record(out),counts=plan['counts'],pins=len(plan['pins']))))
