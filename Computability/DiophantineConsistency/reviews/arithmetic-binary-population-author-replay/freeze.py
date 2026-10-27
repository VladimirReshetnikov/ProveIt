from pathlib import Path
import hashlib,json,os,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency'
O=D/'reviews/arithmetic-binary-population-author-replay';F=D/'reviews/arithmetic-binary-population-replay.json'
pins={};comparisons=0
def need(c,m):
 if not c:raise RuntimeError(m)
def rec(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
def check(x):
 global comparisons
 a=rec(x['path']);need(a['sha256']==x['sha256'],'hash '+x['path'])
 if 'bytes'in x:need(a['bytes']==x['bytes'],'size')
 pins[a['path']]=a;comparisons+=1;return a
def read(p):return json.loads(Path(p).read_text())
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
need(not O.exists()and not F.exists(),'fresh author evidence')
need(shutil.disk_usage('/tmp').free>=512*1024**2,'reserve')
paths=read('/tmp/binary-population-root-author-attempts.json');need(len(paths)==3,'all three attempts')
attempts=[]
for number,path in enumerate(paths,1):
 p=Path(path);s=read(p/'AUTHOR.json');need(s['status']in['FAILED','PASS'],'terminal attempt')
 check(rec(p/'AUTHOR.json'));check(s['driver']);check(s['inputs']);i=read(s['inputs']['path'])
 for x in i['pins']:check(x)
 for x in i['actual_providers']:check(x['actual']);check(x['expected'])
 for x in i['sources']:
  check(x['snapshot']);need(x['sha256']==x['snapshot']['sha256'],'historical source snapshot')
 for row in s['records']:
  need(row['command'][1:4]==['-M6000','-j1','-DElab.async=false'],'caps')
  check(row['snapshot']);check(row['log']);check(row['timing'])
  need(row['source']['sha256']==row['snapshot']['sha256'],'record source binding')
  if 'object'in row:check(row['object'])
 attempts.append(dict(number=number,private=str(p),status=s['status'],state=rec(p/'AUTHOR.json'),records=s['records']))
last=attempts[-1];need([x['status']for x in attempts]==['FAILED','FAILED','PASS'],'complete attempt statuses')
P=Path(last['private']);state=read(P/'AUTHOR.json');inputs=read(state['inputs']['path'])
need(len(state['records'])==2,'final pair')
for row,wanted in zip(state['records'],[0,14],strict=True):
 need(row['exit_code']==0 and len(row['axiom_reports'])==wanted,'clean final reports')
 check(row['source']);check(row['snapshot']);check(row['object'])
 need(Path(row['object']['path']).is_file()and not Path(row['object']['path']).is_symlink(),'regular object')
for x in list(pins.values()):check(x)
check(rec(__file__))
O.mkdir()
for attempt in attempts:
 p=Path(attempt['private']);folder=O/('attempt-%02d'%attempt['number']);folder.mkdir()
 for q in sorted(p.iterdir()):
  if q.is_file()and not q.is_symlink():os.link(q,folder/q.name)
 attempt['durable_state']=rec(folder/'AUTHOR.json')
auth=O/'freeze-authentication.json'
save(auth,dict(status='PASS',comparisons=comparisons,unique_paths=len(pins),pins=list(pins.values()),
 qualification='All three capped author attempts, historical snapshots, complete logs/timings, all494providers and final standard-only pair authenticated. No independent proof acceptance.'))
shutil.copyfile(__file__,O/'freeze.py')
packet=dict(status='PASS',role='ROOT_AUTHOR_AWAITING_INDEPENDENT_REPLAY',
 scope='Actual total represented binary population in every IΣ1 model; internal binary recurrence, arbitrary-length concatenation and complement identities. No carry/binomial/mask/tableau or full HA claim.',
 counts=state['counts'],private_provider=str(P/'lib'),records=state['records'],attempts=attempts,
 plan=check(inputs['plan']),plan_manifest=check(inputs['manifest']),inputs=rec(O/'attempt-03/inputs.json'),
 state=rec(P/'AUTHOR.json'),durable_state=rec(O/'attempt-03/AUTHOR.json'),driver=rec(O/'attempt-03/driver.py'),
 freeze_authentication=rec(auth),freeze_driver=rec(O/'freeze.py'),comparisons=comparisons,unique_paths=len(pins),
 independent_plan_receipt=check(rec(D/'reviews/arithmetic-binary-population-plan-peer.md')))
save(F,packet)
files=sorted(q for q in O.rglob('*')if q.is_file())
save(O/'FILES.json',[dict(rec(q),path=str(q.relative_to(R)))for q in files])
need(shutil.disk_usage('/tmp').free>=512*1024**2,'final reserve')
print(json.dumps(dict(packet=rec(F),manifest=rec(O/'FILES.json'),files=len(files),comparisons=comparisons,unique_paths=len(pins),provider=str(P/'lib'),free_bytes=shutil.disk_usage('/tmp').free),indent=2))
