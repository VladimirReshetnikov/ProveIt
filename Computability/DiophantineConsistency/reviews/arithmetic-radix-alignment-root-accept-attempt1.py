from pathlib import Path
import hashlib,json,re,stat
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency';pins={};observations=0
def need(c,m):
 if not c:raise RuntimeError(m)
def rec(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
def check(x):
 global observations
 a=rec(x['path']);need(a['sha256']==x['sha256'],'hash '+x['path']);pins[a['path']]=a;observations+=1;return a
def load(p,h=None):
 a=check(dict(path=str(p),sha256=h))if h else check(rec(p));return json.loads(Path(a['path']).read_text())
a=load(D/'reviews/arithmetic-radix-alignment-replay.json','d7992406dc9e9a44e95622e0d0fe4eee36186e7b9e8c10b6428dc9ccaf70407b')
p=load(D/'reviews/arithmetic-radix-alignment-peer-replay.json','d2ecc9d7e9890a16cd5b72fe99aba6433f49a6179ca7db7de8830816dc93058e')
check(dict(path=str(D/'reviews/arithmetic-radix-alignment-peer.md'),sha256='778560140d6ce58a9f0f59e564593b51548f91e1b262510c3e58d13ef8442064'))
check(rec(D/'reviews/arithmetic-radix-alignment-author.md'))
for stem,h,count in [('arithmetic-radix-alignment-author-replay','914ed3da00f6f2f7f5817d7561cb1208c0a6e4401038254116b389cfe3bb5b87',23),('arithmetic-radix-alignment-peer-replay','38fce832944dd3a855b3d5649fdc4c0b354d5dbf4aefc96f35e6b8f7a8129172',14)]:
 rows=load(D/'reviews'/stem/'FILES.json',h);need(len(rows)==count,'manifest size')
 for x in rows:check(dict(x,path=str(R/x['path'])))
need(a['status']==p['status']=='PASS','roles/status')
for key in ['inputs','driver','state','plan','compiler','freeze_authentication','freeze_driver']:check(p[key])
auth=load(p['freeze_authentication']['path']);need(auth['status']=='PASS','peerfreeze')
for x in auth.get('pins',auth.get('observed',[])):check(x)
inputs=load(p['inputs']['path']);check(inputs['providers']);providers=load(inputs['providers']['path']);need(len(providers)==474,'all providers')
for x in providers:check(x['actual']);check(x['expected'])
for ar,pr,n in zip(a['final']['records'],p['records'],[0,8],strict=True):
 need(ar['module']==pr['module']and pr['exit_code']==0 and pr['matches_author'],'peer records')
 for key in ['source','snapshot','object','log','timing']:check(pr[key])
 for key in ['source','object','log']:need(ar[key]['sha256']==pr[key]['sha256'],'author peer equality')
 need(pr['axiom_reports']==ar['axiom_reports']and len(pr['axiom_reports'])==n,'reports')
 for _,ax in pr['axiom_reports']:need(set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'},'standard axioms')
 log=Path(pr['log']['path']).read_text();need(not re.search(r'\b(?:warning|error|sorryAx)\b',log),'diagnostics')
 ap=Path(ar['object']['path']);pp=Path(pr['object']['path']);need(stat.S_ISREG(pp.lstat().st_mode)and pp.stat().st_ino!=ap.stat().st_ino,'independent regular object')
for x in list(pins.values()):check(x)
out=D/'reviews/arithmetic-radix-alignment-root-acceptance.json';need(not out.exists(),'fresh acceptance')
result=dict(status='PASS',role='Controller authored; complemented independently reviewed/replayed; ROOT read sources and authenticated peer result',author=rec(D/'reviews/arithmetic-radix-alignment-replay.json'),peer_packet=rec(D/'reviews/arithmetic-radix-alignment-peer-replay.json'),observations=observations,unique_paths=len(pins),pins=list(pins.values()),driver=rec(__file__),provider=p['private_provider'])
out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k!='pins'},indent=2))
