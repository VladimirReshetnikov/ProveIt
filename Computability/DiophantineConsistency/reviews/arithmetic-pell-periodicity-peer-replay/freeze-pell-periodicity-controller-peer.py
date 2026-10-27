from pathlib import Path
import hashlib, json, shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
REV=R/'Computability/DiophantineConsistency/reviews'
P=Path('/tmp/arithmetic-pell-periodicity-controller-peer-hepovkab')
def rec(p):
    p=Path(p)
    return dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
def save(p,v):Path(p).write_text(json.dumps(v,indent=2)+'\n')
def check(r):assert rec(r['path'])['sha256']==r['sha256'],r['path']
s=json.loads((P/'PEER.json').read_text())
assert s['status']=='PASS' and len(s['records'])==2
for row in s['records']:
    assert row['exit_code']==0 and row['object_byte_identical'] and row['log_byte_identical'] and row['reports_identical']
    for key in ['source','snapshot','object','log','timing']:check(row[key])
    assert not Path(row['object']['path']).is_symlink()
obs=json.loads((P/'observations.json').read_text())
unique={r['path']:r for r in obs}
for r in unique.values():check(r)
inputs=json.loads((P/'inputs.json').read_text())
for provider in inputs['providers']:check(provider['actual'])
out=REV/'arithmetic-pell-periodicity-peer-replay';assert not out.exists();out.mkdir()
for name in ['PEER.json','inputs.json','observations.json','driver.py']:
    shutil.copyfile(P/name,out/name)
for row in s['records']:
    for key in ['snapshot','object','log','timing']:
        path=Path(row[key]['path']);shutil.copyfile(path,out/path.name)
shutil.copyfile(__file__,out/Path(__file__).name)
marker=Path('/tmp/arithmetic-pell-periodicity-controller-peer-attempts.json')
assert json.loads(marker.read_text())==[str(P)]
shutil.copyfile(marker,out/marker.name)
packet=dict(status='PASS',scope='Independent full mathematical/source/provenance review and fresh private two-leaf replay of root-authored internal Pell periodicity. No prerequisite rebuild or full PA/HA claim.',
    counts=s['counts'],records=s['records'],private_provider=str(P/'lib'),
    state=rec(out/'PEER.json'),inputs=rec(out/'inputs.json'),authentication=rec(out/'observations.json'),
    driver=rec(out/'driver.py'),observations=s['observations'],distinct_paths=s['distinct_paths'],
    author_packet=inputs['author'],author_receipt=inputs['receipt'],author_manifest=inputs['manifest'],
    plan=inputs['plan'],compiler=inputs['compiler'],LEAN_PATH=inputs['LEAN_PATH'],
    final_unique_pin_reauthentication=len(unique),final_provider_reauthentication=len(inputs['providers']))
packetpath=REV/'arithmetic-pell-periodicity-peer-replay.json';assert not packetpath.exists();save(packetpath,packet)
manifest=[dict(path=str(p.relative_to(R)),sha256=rec(p)['sha256'],bytes=p.stat().st_size) for p in sorted(out.rglob('*')) if p.is_file()]
save(out/'FILES.json',manifest)
for p in [packetpath,out/'FILES.json']:print(rec(p)['sha256'],p)
print('files',len(manifest),'pins',len(unique),'providers',len(inputs['providers']))
