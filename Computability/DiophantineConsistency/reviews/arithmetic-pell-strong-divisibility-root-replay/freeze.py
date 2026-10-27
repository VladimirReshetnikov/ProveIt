from pathlib import Path
import hashlib,json,re,shutil,sys
R=Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews'
kind=sys.argv[1];assert kind in ['strong','tape']
if kind=='strong':
    stem='arithmetic-pell-strong-divisibility';P=Path('/tmp/arithmetic-pell-strong-divisibility-root-mljfsamm')
    expected='c85cf2c33f09b8aef36719430cffefcc8a1c4d51a19f3aabd8feaae1457dc4c7'
    numreports=7;numproviders=496;statuses=['FAILED','PASS'];statefile='state.json'
else:
    stem='arithmetic-machine-tape215';P=Path('/tmp/machine-tape215-root-bbarbz31')
    expected='c0c88f0c2d9d3e260710bf022bb050460dc3ddce0d41218caa05f419de678b2e'
    numreports=13;numproviders=594;statuses=['FAILED']*4+['PASS'];statefile='ROOT.json'
B=V/(stem+'-root-replay');OBS=[]
def need(ok,msg):
    if not ok:raise RuntimeError(msg)
def rec(p):
    p=Path(p);data=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
def pin(x,actual=None):
    a=rec(actual or x['path']);need(a['sha256']==x['sha256'],'hash '+x['path'])
    if 'bytes'in x:need(a['bytes']==x['bytes'],'size '+x['path'])
    OBS.append(dict(expected=x,actual=a));return a
def read(p):return json.loads(Path(p).read_text())
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
need(not B.exists(),'fresh ROOT evidence')
ap=V/(stem+'-replay.json');pin(dict(path=str(ap),sha256=expected));a=read(ap);s=read(P/statefile)
need(s['status']==a['status']=='PASS','both successful pairs')
ars=a['records']if kind=='strong'else a['final']['records']
need(len(ars)==len(s['records'])==2,'both leaves')
actual_statuses=[]
for attempt in a['attempts']:
    pin(attempt['durable']);st=read(attempt['durable']['path'])
    if kind=='strong':pin(attempt['state']);need(st==read(attempt['state']['path']),'durable author state')
    else:need(st==attempt['state'],'durable author state')
    actual_statuses.append(st['status']);private=Path(st['private']);inp=read(private/'inputs.json')
    pin(st['inputs']);pin(st['driver'],private/'driver.py')
    for x in inp['sources']:
        snapshot=private/'logs'/Path(x['path']).name if kind=='strong'else Path(x['snapshot']['path'])
        pin(x,snapshot)
    for row in st['records']:
        need(row['command'][1:4]==['-M6000','-j1','-DElab.async=false'],'historical caps')
        for key in ['snapshot','log','timing']:pin(row[key])
        if 'object'in row:pin(row['object'])
need(actual_statuses==statuses,'author chronology')
total=0
for ar,rr in zip(ars,s['records'],strict=True):
    need(ar['module']==rr['module']and ar['exit_code']==rr['exit_code']==0,'same successful leaf')
    need(rr['author_object_and_full_log_equal'],'runner equality')
    for key in ['source','snapshot','log','timing','object']:pin(ar[key]);pin(rr[key])
    for key in ['source','snapshot','log','object']:need(ar[key]['sha256']==rr[key]['sha256'],'matching '+key)
    need(ar['axiom_reports']==rr['axiom_reports'],'full report equality')
    text=Path(rr['log']['path']).read_text();need(not re.search(r'\b(?:warning|error|sorryAx)\b',text),'clean logs')
    reports=[list(x)for x in re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text)]
    need(reports==rr['axiom_reports'],'actual reports');total+=len(reports)
    for _,ax in reports:need(set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'},'standard axioms')
need(total==numreports,'all reports')
inp=read(P/'inputs.json')
auth=read(P/'authentication.json')['pins']if kind=='strong'else inp['pins']
for row in auth:pin(row)
providers=read(P/'providers.json')if kind=='strong'else inp['actual_providers']
need(len(providers)==numproviders,'all first providers')
for row in providers:pin(row['expected']);pin(row['actual'])
B.mkdir()
for p in sorted(P.iterdir()):
    if p.is_file()and not p.is_symlink():shutil.copyfile(p,B/p.name)
if kind=='strong':
    for p in sorted((P/'logs').iterdir()):
        if p.is_file():shutil.copyfile(p,B/p.name)
shutil.copyfile(__file__,B/'freeze.py')
save(B/'final-authentication.json',dict(observations=OBS,count=len(OBS),distinct_paths=len({x['actual']['path']for x in OBS})))
out=V/(stem+'-root-replay.json');need(not out.exists(),'fresh ROOT packet')
save(out,dict(status='PASS',scope='ROOT complete final proof/Checks and author-driver review plus independent fresh private pair. No final HA equation theorem.',
    author=rec(ap),private_provider=str(P/'lib'),state=rec(P/statefile),durable_state=rec(B/statefile),
    counts=inp['counts']if kind=='strong'else s['counts'],records=s['records'],compiler_invocations=2,
    artifact_providers=numproviders,reports=numreports,driver=rec(B/'driver.py'),
    final_authentication=rec(B/'final-authentication.json'),historical_attempts=len(a['attempts']),
    freeze_command=['python',str(Path(__file__).absolute()),kind]))
paths=[p for p in sorted(B.iterdir())if p.is_file()]+[out,V/(stem+'-root.md')]
save(B/'FILES.json',[dict(rec(p),path=str(p.relative_to(R)))for p in paths])
print(json.dumps(dict(packet=rec(out),manifest=rec(B/'FILES.json'),files=len(paths),authentication=len(OBS),distinct_paths=len({x['actual']['path']for x in OBS})),indent=2))
