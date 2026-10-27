from pathlib import Path
import hashlib, json, shutil
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
REV=ROOT/'Computability/DiophantineConsistency/reviews'
private=Path('/tmp/arithmetic-pell-first-norm-peer-latest').read_text().strip()
P=Path(private)
B=REV/'arithmetic-pell-first-norm-peer-replay'

def require(ok,message):
    if not ok: raise RuntimeError(message)

def rec(p):
    p=Path(p); raw=p.read_bytes()
    return dict(path=str(p),sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw))

def save(p,o): Path(p).write_text(json.dumps(o,indent=2)+'\n')

def check(pin):
    got=rec(pin['path'])
    require(got['sha256']==pin['sha256'],'pin '+pin['path'])
    if 'bytes' in pin: require(got['bytes']==pin['bytes'],'size '+pin['path'])

require(not B.exists(),'fresh evidence directory')
state=json.loads((P/'state.json').read_text())
inputs=json.loads((P/'inputs.json').read_text())
require(state['status']=='PASS' and len(state['records'])==2,'two PASS leaves')
require(sum(len(r['axiom_reports']) for r in state['records'])==11,'eleven reports')
for pin in inputs['observations']: check(pin)
for pin in (state['driver'],state['inputs'],inputs['author_packet'],inputs['plan'],inputs['providers']):check(pin)
for row in state['records']:
    require(row['exit_code']==0 and row['matches_author'],'exact successful replay')
    for key in ('source','snapshot','log','timing','object'):check(row[key])
    require(not Path(row['object']['path']).is_symlink(),'regular new object')
require(shutil.disk_usage('/tmp').free>=512*1024**2,'reserve')
B.mkdir()
for p in sorted(P.rglob('*')):
    if p.is_file() and 'lib' not in p.relative_to(P).parts:
        target=B/p.relative_to(P);target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(p,target)
shutil.copyfile('/tmp/arithmetic-pell-first-norm-peer-console.log',B/'console.log')
shutil.copyfile(__file__,B/'freeze.py')
packet=dict(status='PASS',scope='Independent two-leaf review/replay of actual internal first norm; no dependency builds or final HA claim',
    private=private,counts=inputs['counts'],records=state['records'],state=rec(B/'state.json'),
    inputs=rec(B/'inputs.json'),providers=rec(B/'providers.json'),driver=rec(B/'driver.py'),
    author_packet=inputs['author_packet'],author_manifest=inputs['author_manifest'],
    authenticated_distinct_paths=len(inputs['observations']),compiler=inputs['compiler'],
    LEAN_PATH=inputs['LEAN_PATH'],free_bytes=shutil.disk_usage('/tmp').free)
save(REV/'arithmetic-pell-first-norm-peer-replay.json',packet)
manifest=[dict(rec(p),path=str(p.relative_to(ROOT))) for p in sorted(B.rglob('*')) if p.is_file()]
save(B/'FILES.json',manifest)
print(json.dumps(dict(packet=rec(REV/'arithmetic-pell-first-norm-peer-replay.json'),
    manifest=rec(B/'FILES.json'),files=len(manifest),observations=len(inputs['observations']),
    records=[dict(module=r['module'],seconds=r['seconds'],object=r['object']['sha256']) for r in state['records']]),indent=2))
