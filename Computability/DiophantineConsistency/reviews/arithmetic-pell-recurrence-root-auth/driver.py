from pathlib import Path
import hashlib, json, tempfile

DC = Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency')
observations = []
def check(x):
    p = Path(x['path']); b = p.read_bytes(); h = hashlib.sha256(b).hexdigest()
    if h != x['sha256'] or ('bytes' in x and len(b) != x['bytes']):
        raise RuntimeError(str(p))
    observations.append(dict(path=str(p), sha256=h, bytes=len(b)))

author = DC / 'reviews/arithmetic-pell-recurrence-replay.json'
peer = DC / 'reviews/arithmetic-pell-recurrence-peer-replay.json'
check(dict(path=str(author), sha256='022e44d19bec3bd4fe3de9e130d601ea31179bb73efcee51deb6233fe71e183d'))
check(dict(path=str(peer), sha256='b581c5220c6ccc30e5ca6e7e29417cfb3c9464442661a990643f7a242ca691f0'))
a = json.loads(author.read_text()); p = json.loads(peer.read_text())
for packet in [a,p]:
    for name in ['state','inputs','bundle_manifest']:
        check(packet[name])
    mf = Path(packet['bundle_manifest']['path'])
    for item in json.loads(mf.read_text()):
        check(dict(item,path=str(mf.parent/item['path'])))
plan = json.loads(Path(a['plan']['path']).read_text())
check(a['plan']); check(a['proposal'])
for pin in plan['pins']:
    check(pin)
for pin in json.loads(Path(p['inputs']['path']).read_text())['observations']:
    check(pin)
if len(a['records']) != 2 or len(p['records']) != 2:
    raise RuntimeError('two leaves')
for ar,pr in zip(a['records'],p['records']):
    if ar['module'] != pr['module'] or ar['source'] != pr['source']:
        raise RuntimeError('source equality')
    if ar['exit_code'] != 0 or pr['exit_code'] != 0 or ar['object']['sha256'] != pr['object']['sha256']:
        raise RuntimeError('fresh matching objects')
    if ar['axiom_reports'] != pr['axiom_reports']:
        raise RuntimeError('same reports')
    for r in [ar,pr]:
        for name in ['source','snapshot','log','timing','object']:
            check(r[name])
    if Path(ar['log']['path']).read_bytes() != Path(pr['log']['path']).read_bytes():
        raise RuntimeError('same logs')
if sum(len(r['axiom_reports']) for r in p['records']) != 9:
    raise RuntimeError('nine reports')
for pin in list(observations):
    check(pin)
out = Path(tempfile.mkdtemp(prefix='arithmetic-pell-recurrence-root-auth-'))
(out/'observations.json').write_text(json.dumps(observations,indent=2)+'\n')
(out/'driver.py').write_bytes(Path(__file__).read_bytes())
result=dict(status='PASS_NO_THIRD_COMPILATION',observations=len(observations),
    unique_paths=len({x['path'] for x in observations}),author=str(author),peer=str(peer),
    reports=9,private=str(out))
(out/'ROOT.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
