from pathlib import Path
import hashlib, json, shutil

R=Path('/home/codex/.codex/worktrees/46be/Proofs')
D=R/'Computability/DiophantineConsistency'; V=D/'reviews'
P=Path('/tmp/arithmetic-pell-residue-classes-root-er_y8ywe')
B=V/'arithmetic-pell-residue-classes-root-replay'


def need(ok,message):
    if not ok: raise RuntimeError(message)


def rec(p):
    p=Path(p); b=p.read_bytes()
    return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))


def check(x):
    a=rec(x['path']); need(a['sha256']==x['sha256'],'hash '+x['path'])
    if 'bytes' in x: need(a['bytes']==x['bytes'],'bytes '+x['path'])
    return a


def read(p): return json.loads(Path(p).read_text())


def save(p,x): Path(p).write_text(json.dumps(x,indent=2)+'\n')


state=read(P/'state.json'); need(state['status']=='PASS','ROOT PASS')
author=read(V/'arithmetic-pell-residue-classes-replay.json')
snapshots={}
for attempt in author['attempts']:
    check(attempt['state']); s=read(attempt['state']['path'])
    need(s['status']==attempt['status'],'historical status')
    for row in s['records']:
        for k in ['snapshot','log','timing']: check(row[k])
        need(row['snapshot']['sha256']==row['source']['sha256'],'historical source binding')
        snapshots[row['source']['sha256']]=row['snapshot']
        need(row['command'][1:4]==['-M6000','-j1','-DElab.async=false'],'historical caps')
        if 'object' in row: check(row['object'])
for attempt in author['attempts']:
    private=Path(attempt['private']); old=read(private/'inputs.json')
    s=read(private/'state.json')
    need(rec(private/'driver.py')['sha256']==s['driver']['sha256'],'historical driver snapshot')
    for x in old['sources']: need(x['sha256'] in snapshots,'all historical source bytes')
need([x['status'] for x in author['attempts']]==['FAILED','FAILED','PASS'],'three attempt chronology')
for row,ar in zip(state['records'],author['records'],strict=True):
    need(row['author_object_and_full_log_equal'],'pair equality flag')
    for k in ['source','snapshot','log','timing','object']: check(row[k])
    for k in ['source','snapshot','log','object']:
        need(row[k]['sha256']==ar[k]['sha256'],'independent equality '+k)
for x in read(P/'authentication.json'): check(x)
need(not B.exists(),'fresh bundle'); B.mkdir()
for name in ['driver.py','plan.json','proposal.md','inputs.json','providers.json','authentication.json','state.json']:
    shutil.copyfile(P/name,B/name)
for row in state['records']:
    for k in ['snapshot','log','timing']:
        p=Path(row[k]['path']); shutil.copyfile(p,B/p.name)
shutil.copyfile(__file__,B/'freeze.py')
packet=dict(status='PASS',scope='ROOT full final-source and author-driver review plus independent fresh two-leaf replay. Internal IΣ1 Pell residue classes and signed doubled step only; no carrier index, strong integrality, cofinality or PA/HA endpoint.',
    counts=read(P/'inputs.json')['counts'],private_provider=str(P/'lib'),state=rec(P/'state.json'),
    durable_state=rec(B/'state.json'),records=state['records'],
    author_packet=rec(V/'arithmetic-pell-residue-classes-replay.json'),
    author_manifest=rec(V/'arithmetic-pell-residue-classes-author-replay/FILES.json'),
    observations=state['observations'],comparisons=state['comparisons'],artifact_providers=498,
    compiler_invocations=2,all_fifteen_standard_reports=True,
    historical_attempts_authenticated=True,driver=rec(B/'driver.py'))
packet_path=V/'arithmetic-pell-residue-classes-root-replay.json'
need(not packet_path.exists(),'fresh packet'); save(packet_path,packet)
files=[dict(rec(p),path=str(p.relative_to(R))) for p in sorted(B.iterdir())]
files.extend(dict(rec(p),path=str(p.relative_to(R))) for p in [packet_path,V/'arithmetic-pell-residue-classes-root.md'])
save(B/'FILES.json',files)
print(json.dumps(dict(packet=rec(packet_path),manifest=rec(B/'FILES.json'),files=len(files)),indent=2))
