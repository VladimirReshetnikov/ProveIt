from pathlib import Path
import hashlib, json, tempfile
D=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/reviews')
observations=[]
def check(x):
    p=Path(x['path']);b=p.read_bytes();h=hashlib.sha256(b).hexdigest()
    if h!=x['sha256'] or ('bytes' in x and len(b)!=x['bytes']):raise RuntimeError(str(p))
    observations.append(dict(path=str(p),sha256=h,bytes=len(b)))
author=D/'validator-full-seed-theory222-replay.json'
peer=D/'validator-full-seed-theory222-peer-replay.json'
check(dict(path=str(author),sha256='a43514a4122ddf304a805511b4ef444b30418c7408eb217882a8d8233f7e0502'))
check(dict(path=str(peer),sha256='4c0307c365be10c8680d27ed33b60caff41914bc390014a25955ea9fd5152a56'))
a=json.loads(author.read_text());p=json.loads(peer.read_text())
for name,expected,sha in [
    ('validator-full-seed-theory222-author-replay',47,'4f20507b3bafbd9e9158605bf6e162bdbc7bc64ab25d06c50145c5f30fce723b'),
    ('validator-full-seed-theory222-peer-replay',13,'4b13e63a46a0cb1cc31f964effb03e4c99edf77cdc09c1e6846dda5c9891ac18')]:
    mf=D/name/'FILES.json';check(dict(path=str(mf),sha256=sha))
    files=json.loads(mf.read_text())
    if len(files)!=expected:raise RuntimeError('manifest count')
    for x in files:check(dict(x,path=str(mf.parent/x['path'])))
data=a['inputs']
if data['counts']!=dict(cached_modules=191,foundation=136,artifacts=599,external_boundaries=45):
    raise RuntimeError('exact191/136/599/45')
for key in ['compiler','manifest','toolchain']:
    check(dict(path=data[key],sha256=data[key+'_sha256']))
for x in [*data['parent_receipts'],*data['inherited_observations']]:check(x)
for m in data['modules']:
    check(dict(path=m['source'],sha256=m['source_sha256']))
    for x in m['objects']:check(x)
for x in data['external']:check(x)
for key in ['state','driver','inputs','providers','pins','author_packet','author_manifest','manifest']:
    check(p[key])
if json.loads(Path(p['inputs']['path']).read_text())!=data:raise RuntimeError('same exact inputs')
for x in json.loads(Path(p['pins']['path']).read_text()):check(x)
for x in json.loads(Path(p['providers']['path']).read_text()):
    check(dict(path=x['provider'],sha256=x['sha256']))
if len(a['completed'])!=2 or len(p['records'])!=2:raise RuntimeError('two leaves')
for x,y in zip(a['completed'],p['records']):
    if x['module']!=y['module'] or x['source']!=y['source']['path'] or x['source_sha256']!=y['source']['sha256']:
        raise RuntimeError('source identity')
    if x['exit_code']!=0 or y['exit_code']!=0:raise RuntimeError('successful builds')
    if x['object']['sha256']!=y['object']['sha256'] or x['axiom_reports']!=y['axiom_reports']:
        raise RuntimeError('object/report equality')
    for key in ['source','snapshot','log','timing']:
        check(dict(path=x[key],sha256=x[key+'_sha256']));check(y[key])
    check(x['object']);check(y['object'])
    if Path(x['log']).read_bytes()!=Path(y['log']['path']).read_bytes():raise RuntimeError('full log equality')
if sum(len(x['axiom_reports']) for x in p['records'])!=13:raise RuntimeError('13 reports')
for x in list(observations):check(x)
out=Path(tempfile.mkdtemp(prefix='validator-full-seed-theory222-root-auth-'))
(out/'observations.json').write_text(json.dumps(observations,indent=2)+'\n')
(out/'driver.py').write_bytes(Path(__file__).read_bytes())
result=dict(status='PASS_NO_THIRD_COMPILATION',observations=len(observations),
    unique_paths=len({x['path'] for x in observations}),reports=13,private=str(out),
    trace_bundles=p['trace_bundles'],author=str(author),peer=str(peer))
(out/'ROOT.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
