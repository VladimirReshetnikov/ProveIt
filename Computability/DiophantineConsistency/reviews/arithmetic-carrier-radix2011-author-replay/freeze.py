from pathlib import Path
import hashlib, json, os, re, shutil

ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
DC=ROOT/'Computability/DiophantineConsistency'
RUNS=Path('/tmp/arithmetic-carrier-radix2011-author-runs.txt')
BUNDLE=DC/'reviews/arithmetic-carrier-radix2011-author-replay'
PACKET=DC/'reviews/arithmetic-carrier-radix2011-replay.json'
observations={}; comparisons=0

def need(ok,msg):
    if not ok: raise RuntimeError(msg)
def record(p):
    p=Path(p); b=p.read_bytes()
    return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
def check(p):
    global comparisons
    a=record(p['path']); need(a['sha256']==p['sha256'],'hash '+p['path'])
    need('bytes' not in p or a['bytes']==p['bytes'],'size '+p['path'])
    observations[a['path']]=a; comparisons+=1; return a
def save(p,j): p.write_text(json.dumps(j,indent=2)+'\n')
def link(p,q):
    need(p.is_file() and not p.is_symlink(),'regular evidence '+str(p))
    q.parent.mkdir(parents=True,exist_ok=True); os.link(p,q)
    need(record(p)['sha256']==record(q)['sha256'],'hardlink equality')

need(not BUNDLE.exists() and not PACKET.exists(),'fresh bundle')
need(shutil.disk_usage('/tmp').free>=512*1024**2,'reserve')
paths=[Path(s) for s in RUNS.read_text().splitlines()]
need(len(paths)==1,'one final first-pass attempt')
private=paths[-1]; state=json.loads((private/'state.json').read_text())
need(state['status']=='PASS' and len(state['records'])==2,'final pair')
inputs=json.loads(Path(check(state['inputs'])['path']).read_text())
plan=json.loads(Path(check(inputs['plan'])['path']).read_text())
check(inputs['proposal']); check(inputs['compiler']); check(state['driver'])
need(plan['counts']['actual_first_providers']==573 and
     plan['counts']['fresh_prerequisites']==0,'scope')
for p in plan['pins']: check(p)
for p in inputs['sources']: check(p)
auth=json.loads(Path(check(inputs['authentication'])['path']).read_text())
for p in auth['pins']: check(p)
providers=json.loads(Path(check(inputs['providers'])['path']).read_text())
need(len(providers)==573,'all providers')
for pair in providers:
    check(pair['expected']); check(pair['actual'])
    need(pair['expected']['sha256']==pair['actual']['sha256'],'provider match')
for row in state['records']:
    need(row['exit_code']==0,'exit')
    for k in ['source','snapshot','object','log','timing']: check(row[k])
    need(row['source']['sha256']==row['snapshot']['sha256'],'snapshot source')
    obj=Path(row['object']['path'])
    need(obj.is_file() and not obj.is_symlink(),'regular fresh object')
    need(row['command'][1:4]==['-M6000','-j1','-DElab.async=false'],'caps')
    for name,axioms in row['axiom_reports']:
        need(set(re.findall('[A-Za-z][A-Za-z.]*',axioms))<=
             {'propext','Classical.choice','Quot.sound'},'axioms '+name)
need(len(state['records'][1]['axiom_reports'])==8,'eight reports')
need(Path(state['records'][0]['log']['path']).read_text()=='','empty main')
BUNDLE.mkdir()
for name in ['driver.py','inputs.json','providers.json','authentication.json','state.json']:
    link(private/name,BUNDLE/'attempt-1'/name)
for p in sorted((private/'logs').iterdir()): link(p,BUNDLE/'attempt-1/logs'/p.name)
link(RUNS,BUNDLE/'runs.txt')
link(Path(__file__),BUNDLE/'freeze.py')
for p in sorted(BUNDLE.rglob('*')):
    if p.is_file(): check(record(p))
for p in list(observations.values()): check(p)
need(shutil.disk_usage('/tmp').free>=512*1024**2,'final reserve')
freeze=dict(status='PASS',comparisons=comparisons,unique_paths=len(observations),
    pins=list(observations.values()),free_bytes=shutil.disk_usage('/tmp').free)
save(BUNDLE/'freeze-authentication.json',freeze)
manifest=[record(p) for p in sorted(BUNDLE.rglob('*')) if p.is_file()]
save(BUNDLE/'FILES.json',manifest)
packet=dict(status='PASS',role='Author implementation and first capped private replay',
    scope='Same actual maintained positive or once-shifted natural split zero derives power and width94517 radix; distinct recovered block count and zero residual exponent preserved. No word/carry/tableau/converse/HA claim.',
    counts=plan['counts'],private_provider=str(private/'lib'),records=state['records'],
    plan=inputs['plan'],proposal=inputs['proposal'],driver=record(state['driver']['path']),
    state=record(private/'state.json'),durable_state=record(BUNDLE/'attempt-1/state.json'),
    inputs=record(state['inputs']['path']),providers=inputs['providers'],
    attempts=[dict(private=str(private),status='PASS',state=record(private/'state.json'))],
    freeze_authentication=record(BUNDLE/'freeze-authentication.json'),
    manifest=record(BUNDLE/'FILES.json'),freeze_driver=record(__file__),
    comparisons=comparisons,unique_paths=len(observations),
    evidence='Immutable terminal snapshots/logs/metadata retained as regular hardlinks; no copied cache objects, shared-object mutation, prerequisite refresh or unreported attempts. Outer packet and author receipt are outside FILES to avoid cyclic hashes.')
save(PACKET,packet)
print(json.dumps(dict(packet=record(PACKET),manifest=record(BUNDLE/'FILES.json'),
    files=len(manifest),sources=[r['source'] for r in state['records']],
    objects=[r['object'] for r in state['records']],comparisons=comparisons,
    paths=len(observations),free_bytes=shutil.disk_usage('/tmp').free),indent=2))
