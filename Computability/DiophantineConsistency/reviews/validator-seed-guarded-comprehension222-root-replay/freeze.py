from pathlib import Path
import hashlib,json,re,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews'
stem='validator-seed-guarded-comprehension222';P=Path('/tmp/validator-seed-guarded-comprehension222-root-mrsef1jx')
expected='262bf7fc06ed6524e95fa609368016d2a51dbc96f918c36896d0311ac52e72a6';numreports=22;numproviders=655
B=V/(stem+'-root-replay');OBS=[]
def need(ok,msg):
    if not ok:raise RuntimeError(msg)
def rec(p):
    p=Path(p);b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
def pin(x,actual=None):
    a=rec(actual or x['path']);need(a['sha256']==x['sha256'],'hash '+x['path']);OBS.append(dict(expected=x,actual=a));return a
def read(p):return json.loads(Path(p).read_text())
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
def norm(row):
    if isinstance(row['source'],dict):return row
    return dict(module=row['module'],exit_code=row['exit_code'],object=row['object'],axiom_reports=row['axiom_reports'],
        **{k:dict(path=row[k],sha256=row[k+'_sha256'])for k in ['source','snapshot','log','timing']})
need(not B.exists(),'fresh ROOT evidence')
ap=V/(stem+'-replay.json');pin(dict(path=str(ap),sha256=expected));a=read(ap);s=read(P/'state.json')
need(s['status']==a['status']=='PASS','successful pair')
ars=a['completed']
need(len(ars)==len(s['records'])==2,'both leaves')
bundle=Path(a['bundle']);need(len(a['attempts'])==6,'six author attempts')
for t in a['attempts']:
    p=bundle/'attempts'/Path(t['path']).name;pin(dict(path=str(p/'state.json'),sha256=t['state_sha256']))
    st=read(p/'state.json');need(st['status']==t['status'],'historical status')
    planned=read(p/'plan.json');need(len(planned)==2,'all historical inputs')
    for row in planned:pin(dict(path=row['source'],sha256=row['source_sha256']),p/Path(row['snapshot']).name)
    for row in st['completed']:
        for k in ['snapshot','log','timing']:pin(dict(path=row[k],sha256=row[k+'_sha256']),p/Path(row[k]).name)
        need(row['command'][1:4]==['-M6000','-j1','-DElab.async=false'],'historical caps')
need([t['status']for t in a['attempts']]==['FAIL']*5+['PASS'],'author chronology')
auth=read(P/'authentication.json')
total=0
for ar,rr in zip(ars,s['records'],strict=True):
    ar=norm(ar);need(ar['module']==rr['module']and ar['exit_code']==rr['exit_code']==0,'same successful leaf')
    for k in ['source','snapshot','log','timing','object']:pin(ar[k]);pin(rr[k])
    for k in ['source','snapshot','log','object']:need(ar[k]['sha256']==rr[k]['sha256'],'matching '+k)
    need(ar['axiom_reports']==rr['axiom_reports'],'full report equality')
    text=Path(rr['log']['path']).read_text();need(not re.search(r'\b(?:warning|error|sorryAx)\b',text),'clean logs')
    rs=[list(x)for x in re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text)]
    need(rs==rr['axiom_reports'],'actual reports');total+=len(rs)
    for _,ax in rs:need(set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'},'standard axioms')
need(total==numreports,'all reports')
for x in auth:pin(x)
providers=read(P/'providers.json');need(len(providers)==numproviders,'all first providers')
for row in providers:pin(row['expected']);pin(row['actual'])
B.mkdir()
for p in sorted(P.iterdir()):
    if p.is_file()and not p.is_symlink():shutil.copyfile(p,B/p.name)
for p in sorted((P/'logs').iterdir()):
    if p.is_file():shutil.copyfile(p,B/p.name)
shutil.copyfile(__file__,B/'freeze.py')
save(B/'final-authentication.json',dict(observations=OBS,count=len(OBS),distinct_paths=len({x['actual']['path']for x in OBS})))
inp=read(P/'inputs.json')
out=V/(stem+'-root-replay.json');need(not out.exists(),'fresh ROOT packet')
save(out,dict(status='PASS',scope='ROOT complete final proof/Checks and author-driver review plus independent fresh private pair. No final HA equation theorem.',
    author=rec(ap),private_provider=str(P/'lib'),state=rec(P/'state.json'),durable_state=rec(B/'state.json'),
    counts=inp['counts'],records=s['records'],compiler_invocations=2,artifact_providers=numproviders,reports=numreports,
    driver=rec(B/'driver.py'),final_authentication=rec(B/'final-authentication.json'),historical_attempts=len(a['attempts'])))
paths=[p for p in sorted(B.iterdir())if p.is_file()]+[out,V/(stem+'-root.md')]
save(B/'FILES.json',[dict(rec(p),path=str(p.relative_to(R)))for p in paths])
print(json.dumps(dict(packet=rec(out),manifest=rec(B/'FILES.json'),files=len(paths),authentication=len(OBS),distinct_paths=len({x['actual']['path']for x in OBS})),indent=2))
