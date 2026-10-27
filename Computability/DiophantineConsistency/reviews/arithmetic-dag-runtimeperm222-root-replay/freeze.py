from pathlib import Path
import hashlib,json,re,shutil,sys
R=Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews'
kind=sys.argv[1]
assert kind in ['known-unit','runtimeperm222']
if kind=='known-unit':
    stem='arithmetic-pell-known-unit';private=Path('/tmp/arithmetic-pell-known-unit-root-rha8oka_')
    statefile='state.json';author_sha='faf3ab49a1a56710f95cfac4e8a317012d96c2f0c48984719911dcdda8716c87'
    attempts=3;leaves=2;reports=4;providers=496
else:
    stem='arithmetic-dag-runtimeperm222';private=Path('/tmp/dag-runtimeperm222-root-lxpl7_mz')
    statefile='AUTHOR.json';author_sha='0a214c73daa754812658979554a9dd163400519c258dbf3400a504095cde1135'
    attempts=4;leaves=3;reports=11;providers=592
B=V/(stem+'-root-replay');observations=[]
def need(ok,msg):
    if not ok:raise RuntimeError(msg)
def rec(p):
    p=Path(p);p=p if p.is_absolute()else R/p;b=p.read_bytes()
    return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
def pin(x,actual=None):
    a=rec(actual or x['path']);need(a['sha256']==x['sha256'],'hash '+x['path'])
    if 'bytes'in x:need(a['bytes']==x['bytes'],'bytes '+x['path'])
    observations.append(dict(expected=x,actual=a));return a
def read(p):return json.loads(Path(p).read_text())
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')

need(not B.exists(),'fresh ROOT bundle')
ap=V/(stem+'-replay.json');pin(dict(path=str(ap),sha256=author_sha));author=read(ap)
state=read(private/statefile);need(state['status']==author['status']=='PASS','PASS states')
ars=author['records']if kind=='known-unit'else author['final']['records']
need(len(state['records'])==len(ars)==leaves,'all fresh leaves')
need(len(author['attempts'])==attempts,'all historical attempts')
for t in author['attempts']:
    if kind=='known-unit':
        pin(t['state']);pin(t['durable']);old=read(t['durable']['path']);oldprivate=Path(t['private'])
        need(old==read(t['state']['path']),'durable state identity')
    else:
        pin(t['durable']);old=read(t['durable']['path']);need(old==t['state'],'durable state identity');oldprivate=Path(old['private'])
    inp=read(oldprivate/'inputs.json');pin(old['inputs']);pin(old['driver'],oldprivate/'driver.py')
    for src in inp['sources']:
        snap=src.get('snapshot')
        actual=snap['path']if snap else oldprivate/'logs'/Path(src['path']).name
        pin(src,actual)
    for row in old['records']:
        for k in ['snapshot','log','timing']:pin(row[k])
        need(row['snapshot']['sha256']==row['source']['sha256'],'executed source binding')
        need(row['command'][1:4]==['-M6000','-j1','-DElab.async=false'],'historical caps')
        if 'object'in row:pin(row['object'])
total=0
for ar,rr in zip(ars,state['records'],strict=True):
    need(ar['module']==rr['module']and ar['exit_code']==rr['exit_code']==0,'matching successful leaves')
    for k in ['source','snapshot','log','timing','object']:pin(ar[k]);pin(rr[k])
    for k in ['source','snapshot','log','object']:need(ar[k]['sha256']==rr[k]['sha256'],'byte equality '+k)
    need(ar['axiom_reports']==rr['axiom_reports'],'complete report equality')
    text=Path(rr['log']['path']).read_text();need(not re.search(r'\b(?:warning|error|sorryAx)\b',text),'clean logs')
    actual=[list(x)for x in re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text)]
    need(actual==rr['axiom_reports'],'actual reports');total+=len(actual)
    for _,ax in actual:need(set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'},'standard axioms')
need(total==reports,'all reports')
inp=read(private/'inputs.json')
if kind=='known-unit':
    for x in read(private/'authentication.json')['pins']:pin(x)
    ps=read(private/'providers.json')
else:
    for x in inp['pins']:pin(x)
    ps=inp['actual_providers']
need(len(ps)==providers,'all artifact providers')
for row in ps:pin(row['expected']);pin(row['actual'])
B.mkdir()
for p in sorted(private.iterdir()):
    if p.is_file()and not p.is_symlink():shutil.copyfile(p,B/p.name)
if (private/'logs').exists():
    for p in sorted((private/'logs').iterdir()):
        if p.is_file():shutil.copyfile(p,B/p.name)
shutil.copyfile(__file__,B/'freeze.py')
save(B/'final-authentication.json',dict(observations=observations,count=len(observations),distinct_paths=len({x['actual']['path']for x in observations})))
packet=dict(status='PASS',scope='ROOT full final source/Checks and driver review with independent fresh replay; all objects and complete logs match author. No final equation/HA endpoint.',
    author=rec(ap),private_provider=str(private/'lib'),state=rec(private/statefile),durable_state=rec(B/statefile),
    records=state['records'],counts=inp.get('counts',inp.get('profile',{}).get('counts')),
    driver=rec(B/'driver.py'),compiler_invocations=leaves,artifact_providers=providers,
    reports=reports,historical_attempts=attempts,final_authentication=rec(B/'final-authentication.json'),
    qualifications='The ROOT runner is derived from the reviewed author driver, with frozen-source pins and explicit object/full-log/report comparisons. All prerequisite provenance limitations are retained.')
out=V/(stem+'-root-replay.json');need(not out.exists(),'fresh ROOT packet');save(out,packet)
paths=[p for p in sorted(B.iterdir())if p.is_file()]+[out,V/(stem+'-root.md')]
save(B/'FILES.json',[dict(rec(p),path=str(p.relative_to(R)))for p in paths])
print(json.dumps(dict(packet=rec(out),manifest=rec(B/'FILES.json'),files=len(paths),authentication=len(observations),distinct_paths=len({x['actual']['path']for x in observations})),indent=2))
