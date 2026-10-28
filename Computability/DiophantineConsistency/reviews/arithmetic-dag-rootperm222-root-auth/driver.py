from pathlib import Path
import hashlib,json,re,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews'
B=V/'arithmetic-dag-rootperm222-root-auth';observations=[]

def need(ok,msg):
    if not ok:raise RuntimeError(msg)
def rec(p):
    p=Path(p);p=p if p.is_absolute() else R/p
    b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
def pin(x):
    a=rec(x['path']);need(a['sha256']==x['sha256'],'hash '+x['path'])
    if 'bytes' in x:need(a['bytes']==x['bytes'],'bytes '+x['path'])
    observations.append(a);return a
def read(p,h=None):
    if h:pin(dict(path=str(p),sha256=h))
    return json.loads(Path(p).read_text())
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')

need(not B.exists(),'fresh ROOT evidence')
a=read(V/'arithmetic-dag-rootperm222-replay.json','47136eefb13b4fedd512e160a3538ba7fb96b5d456ebbe47d37805f41680e65a')
p=read(V/'arithmetic-dag-rootperm222-peer-replay.json','8fac1519929603a2bd9eb52c5bd5ed74b00e8308684c5da66636b153600e1690')
need(a['status']==p['status']==a['final']['status']=='PASS','PASS packets')
need(p['failed_peer_attempts']==0 and len(a['attempts'])==2,'attempt counts')
for mf,n in [(a['evidence_manifest'],17),(p['manifest'],12)]:
    pin(mf);rows=read(mf['path']);need(len(rows)==n,'manifest size')
    for x in rows:pin(x)
for k in ['author','author_receipt','plan','state','inputs','authentication','driver']:pin(p[k])
peerstate=read(p['state']['path'])
need(peerstate['status']=='PASS' and peerstate['records']==[
    {k:v for k,v in row.items()if k!='peak_rss_kib'}for row in p['records']],'durable peer state')
pin(a['inputs']);ai=read(a['inputs']['path']);pi=read(p['inputs']['path'])
plan=read(p['plan']['path']);need(ai['profile']==plan,'author profile identity')
need(plan['counts']==p['counts']==dict(custom=149,Foundation=95,artifacts=434,external=39,boundary_companion_observations=117,refresh=0),'scope')
for x in ai['pins']+pi['pins']+plan['selected_authentication']:pin(x)
for x in pi['foundation_traces']:pin(x['trace'])
need(len(pi['foundation_traces'])==95,'Foundation current trace observations')
snapshots={}
for t in a['attempts']:
    pin(t['durable']);s=read(t['durable']['path']);need(s==t['state'],'author durable state')
    private=Path(s['private']);need(rec(private/'driver.py')['sha256']==s['driver']['sha256'],'historical driver')
    for row in s['records']:
        for k in ['snapshot','log','timing']:pin(row[k])
        need(row['snapshot']['sha256']==row['source']['sha256'],'historical source')
        snapshots[row['source']['sha256']]=row['snapshot']
        need(row['command'][1:4]==['-M6000','-j1','-DElab.async=false'],'historical caps')
        if 'object'in row:pin(row['object'])
unexecuted=[]
for t in a['attempts']:
    s=t['state'];old=read(Path(s['private'])/'inputs.json')
    ran={row['module']for row in s['records']}
    for src in old['sources']:
        if src['module']in ran:need(src['sha256'] in snapshots,'executed input snapshot')
        elif src['sha256']not in snapshots:unexecuted.append(src)
need([t['state']['status']for t in a['attempts']]==['FAILED','PASS'],'author chronology')
reports=0
for ar,pr in zip(a['final']['records'],p['records'],strict=True):
    need(ar['module']==pr['module']and ar['exit_code']==pr['exit_code']==0,'successful same leaf')
    for k in ['source','snapshot','log','timing','object']:pin(ar[k]);pin(pr[k])
    for k in ['source','snapshot','log','object']:need(ar[k]['sha256']==pr[k]['sha256'],'byte equality '+k)
    rss=re.search(r'Maximum resident set size \(kbytes\): (\d+)',Path(pr['timing']['path']).read_text())
    need(rss is not None and int(rss.group(1))==pr['peak_rss_kib'],'derived peak RSS')
    need(ar['axiom_reports']==pr['axiom_reports'],'complete reports')
    text=Path(pr['log']['path']).read_text();need(not re.search(r'\b(?:warning|error|sorryAx)\b',text),'clean diagnostics')
    actual=[list(x)for x in re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text)]
    need(actual==pr['axiom_reports'],'actual reports')
    for _,axs in actual:need(set(re.findall(r'[A-Za-z][A-Za-z.]*',axs))<={'propext','Classical.choice','Quot.sound'},'standard axioms')
    reports+=len(actual)
need(reports==13,'thirteen reports')
providers=[]
for row in plan['modules']+plan['external']:
    expected=row['objects']if'objects'in row else[row if'path'in row else row['object'],*row['companion_observations']]
    for ob in expected:
        rel=Path(*row['module'].split('.')[:-1])/Path(ob['path']).name
        first=next((Path(q)/rel for q in pi['LEAN_PATH']if(Path(q)/rel).is_file()),None)
        need(first is not None,'first artifact '+str(rel))
        actual=pin(dict(ob,path=str(first)))
        providers.append(dict(module=row['module'],expected=ob,actual=actual))
need(len(providers)==590,'all first artifact providers')
need([x['actual']['sha256']for x in providers]==[x['actual']['sha256']for x in pi['providers']],'peer provider order/bytes')
for x in list(observations):pin(x)
state=dict(status='PASS',scope='ROOT complete final source/Checks and both executed-driver review; frozen author/peer and all historical attempts authenticated; no third compiler',counts=plan['counts'],
    records=p['records'],private_provider=p['private_provider'],compiler_invocations=0,
    observations=len(observations),distinct_paths=len({x['path']for x in observations}),artifact_providers=590,reports=reports,
    author=rec(V/'arithmetic-dag-rootperm222-replay.json'),peer=rec(V/'arithmetic-dag-rootperm222-peer-replay.json'),
    unexecuted_historical_input_hash_only=unexecuted)
B.mkdir();save(B/'state.json',state);save(B/'observations.json',observations);save(B/'providers.json',providers);shutil.copyfile(__file__,B/'driver.py')
save(B/'FILES.json',[dict(rec(q),path=str(q.relative_to(R)))for q in sorted(B.iterdir())])
print(json.dumps({k:v for k,v in state.items()if k!='records'},indent=2));print('manifest',rec(B/'FILES.json'))
