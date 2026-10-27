from pathlib import Path
import hashlib,json,re,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
V=R/'Computability/DiophantineConsistency/reviews'
P=Path('/tmp/arithmetic-pell-first-index-root-obnhr4v8')
stem='arithmetic-pell-first-index';B=V/(stem+'-root-replay');OBS=[]
def need(ok,msg):
    if not ok:raise RuntimeError(msg)
def rec(p):
    p=Path(p);b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
def pin(x,actual=None):
    a=rec(actual or x['path']);need(a['sha256']==x['sha256'],'hash '+x['path'])
    if 'bytes'in x:need(a['bytes']==x['bytes'],'size '+x['path'])
    OBS.append(dict(expected=x,actual=a));return a
def read(p):return json.loads(Path(p).read_text())
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
need(not B.exists(),'fresh ROOT evidence')
need(shutil.disk_usage('/tmp').free>=512*1024**2,'512MiB reserve')
ap=V/(stem+'-replay.json')
pin(dict(path=str(ap),sha256='5fedfc6a25af2ed24729fc5e07ddc5145d582f69cfdb912b0ee91ce633235e00'))
a=read(ap);s=read(P/'state.json');need(s['status']==a['status']=='PASS','successful pairs')
need(len(a['records'])==len(s['records'])==2,'both leaves')
need([t['status']for t in a['attempts']]==['FAILED','FAILED','FAILED','PASS'],'author chronology')
for i,t in enumerate(a['attempts'],1):
    pin(t['state']);pin(t['durable']);st=read(t['durable']['path'])
    need(st==read(t['state']['path']),'durable author state')
    private=Path(t['private']);inp=read(private/'inputs.json')
    pin(st['inputs']);pin(st['driver'],private/'driver.py')
    for x in inp['sources']:pin(x,private/'logs'/Path(x['path']).name)
    for row in st['records']:
        need(row['command'][1:4]==['-M6000','-j1','-DElab.async=false'],'historical caps')
        for key in ['snapshot','log','timing']:pin(row[key])
        if 'object'in row:pin(row['object'])
total=0
for ar,rr in zip(a['records'],s['records'],strict=True):
    need(ar['module']==rr['module']and ar['exit_code']==rr['exit_code']==0,'same successful leaf')
    need(rr['author_object_and_full_log_equal'],'runner equality')
    for key in ['source','snapshot','log','timing','object']:pin(ar[key]);pin(rr[key])
    for key in ['source','snapshot','log','object']:need(ar[key]['sha256']==rr[key]['sha256'],'matching '+key)
    need(ar['axiom_reports']==rr['axiom_reports'],'full report equality')
    text=Path(rr['log']['path']).read_text()
    need(not re.search(r'\b(?:warning|error|sorryAx)\b',text),'clean logs')
    rs=[list(x)for x in re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text)]
    need(rs==rr['axiom_reports'],'actual reports');total+=len(rs)
    for _,ax in rs:need(set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'},'standard axioms')
need(total==5,'all five reports')
for x in read(P/'authentication.json')['pins']:pin(x)
providers=read(P/'providers.json');need(len(providers)==507,'all first providers')
for row in providers:pin(row['expected']);pin(row['actual'])
B.mkdir()
for p in sorted(P.iterdir()):
    if p.is_file()and not p.is_symlink():shutil.copyfile(p,B/p.name)
for p in sorted((P/'logs').iterdir()):
    if p.is_file():shutil.copyfile(p,B/p.name)
shutil.copyfile(__file__,B/'freeze.py')
save(B/'final-authentication.json',dict(observations=OBS,count=len(OBS),distinct_paths=len({x['actual']['path']for x in OBS})))
inp=read(P/'inputs.json');out=V/(stem+'-root-replay.json');need(not out.exists(),'fresh ROOT packet')
save(out,dict(status='PASS',scope='ROOT complete final proof/Checks and independent executed-driver review plus independent fresh private pair. No final HA equation theorem.',
    author=rec(ap),private_provider=str(P/'lib'),state=rec(P/'state.json'),durable_state=rec(B/'state.json'),
    counts=inp['counts'],records=s['records'],compiler_invocations=2,artifact_providers=507,reports=5,
    driver=rec(B/'driver.py'),final_authentication=rec(B/'final-authentication.json'),historical_attempts=4))
paths=[p for p in sorted(B.iterdir())if p.is_file()]+[out,V/(stem+'-root.md')]
save(B/'FILES.json',[dict(rec(p),path=str(p.relative_to(R)))for p in paths])
print(json.dumps(dict(packet=rec(out),manifest=rec(B/'FILES.json'),files=len(paths),authentication=len(OBS),distinct_paths=len({x['actual']['path']for x in OBS})),indent=2))
