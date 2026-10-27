from pathlib import Path
import hashlib, json, tempfile
ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
D = ROOT/'Computability/DiophantineConsistency/reviews'
observations = []
def check(x):
    p = Path(x['path']); b = p.read_bytes(); h = hashlib.sha256(b).hexdigest()
    if h != x['sha256'] or ('bytes' in x and len(b) != x['bytes']):
        raise RuntimeError(str(p))
    observations.append(dict(path=str(p),sha256=h,bytes=len(b)))
def record(p):
    p=Path(p);b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
author = D/'native-adaptive-current2011-replay.json'
peer = D/'native-adaptive-current2011-peer-replay.json'
check(dict(path=str(author),sha256='9b7841844daed00727ec08fcdc81b6ab1a2952b62b68e03cffe37ba63bdb4b89'))
check(dict(path=str(peer),sha256='6661c2f42baa774e9e2844b23e4621ddff2dca161424be140c00c0b0d436db48'))
a=json.loads(author.read_text());p=json.loads(peer.read_text())
for name,expected,expected_hash in [
    ('native-adaptive-current2011-replay',17,'db4f52680f1c362cb7c987a087241fcc46d5dd8a83cd48e119f5f8b6d48bcbb9'),
    ('native-adaptive-current2011-peer-replay',13,'d7c08b0bbc1138055879d9387e67a4d59b007af5b9553e66ce0833ad372d03ae')]:
    mf=D/name/'FILES.json';items=json.loads(mf.read_text())
    if len(items)!=expected:raise RuntimeError('manifest count')
    check(dict(path=str(mf),sha256=expected_hash))
    for item in items:
        path=Path(item['path'])
        if not path.is_absolute():
            path=ROOT/path if path.parts[0]=='Computability' else mf.parent/path
        check(dict(item,path=str(path)))
for packet in [a,p]:
    check(packet['inputs'])
    inp=json.loads(Path(packet['inputs']['path']).read_text())
    for pin in inp['pins']:check(pin)
    if len(inp['selected_custom'])!=377 or len(inp['external_boundary'])!=64:
        raise RuntimeError('377/64 scope')
    if sum(len(e['artifacts']) for e in inp['external_boundary'])!=192:
        raise RuntimeError('192 boundary companions')
for row in json.loads(Path(p['inputs']['path']).read_text())['actual_providers']:
    check(row['actual']);check(row['expected'])
if a['final']['status']!='PASS' or p['final']['status']!='PASS':raise RuntimeError('final pass')
ar=a['final']['records'];pr=p['final']['records']
if len(ar)!=2 or len(pr)!=2:raise RuntimeError('two leaves')
for x,y in zip(ar,pr):
    if x['source']!=y['source'] or x['module']!=y['module']:raise RuntimeError('source equality')
    if x['exit_code']!=0 or y['exit_code']!=0:raise RuntimeError('compiler success')
    if x['object']['sha256']!=y['object']['sha256'] or x['axiom_reports']!=y['axiom_reports']:
        raise RuntimeError('object/report equality')
    for row in [x,y]:
        for key in ['source','snapshot','object','log','timing']:check(row[key])
    if Path(x['log']['path']).read_bytes()!=Path(y['log']['path']).read_bytes():
        raise RuntimeError('log equality')
if sum(len(x['axiom_reports']) for x in ar)!=10:raise RuntimeError('ten reports')
for pin in list(observations):check(pin)
out=Path(tempfile.mkdtemp(prefix='native-adaptive-current2011-root-auth-'))
(out/'observations.json').write_text(json.dumps(observations,indent=2)+'\n')
(out/'driver.py').write_bytes(Path(__file__).read_bytes())
result=dict(status='PASS_NO_THIRD_COMPILATION',observations=len(observations),
    unique_paths=len({x['path'] for x in observations}),reports=10,private=str(out),
    author=record(author),peer=record(peer))
(out/'ROOT.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
