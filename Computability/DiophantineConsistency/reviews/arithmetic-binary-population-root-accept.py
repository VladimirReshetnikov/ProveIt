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
a=load(D/'reviews/arithmetic-binary-population-replay.json','ee47d164549eb378ed52ca616cc121ff50fc90f9e812f11f4419cd6616416677')
p=load(D/'reviews/arithmetic-binary-population-peer-replay.json','808afd07ae24a76f2c8e86754e6d0b7d118362913da54c97a3f8aac78dfaea23')
check(dict(path=str(D/'reviews/arithmetic-binary-population-peer.md'),sha256='d202a8c5699469d3719422ee52769738c3f8405d5af8256b2998d5e630391138'))
check(dict(path=str(D/'reviews/arithmetic-binary-population-author.md'),sha256='77c2473a8b515006c7e64aa04cde1d463327192262f7c85a4b189dde9962e35d'))
for stem,h,count in [('arithmetic-binary-population-author-replay','a7599395145ec4cbbe10aa7249aeb112e46cd12f0d60889ac5c2a07df17a0d1f',25),('arithmetic-binary-population-peer-replay','356a675a62a9c0eca25754271200a7e2ea735554373c4b23e37f020034c0706d',14)]:
 rows=load(D/'reviews'/stem/'FILES.json',h);need(len(rows)==count,'manifest size')
 for x in rows:check(dict(x,path=str(R/x['path'])))
need(a['status']==p['status']=='PASS','roles/status')
for key in ['inputs','driver','state','plan','compiler','freeze_authentication','freeze_driver']:check(p[key])
auth=load(p['freeze_authentication']['path']);need(auth['comparisons']==3651 and auth['unique_paths']==2656 and len(auth['pins'])==2656,'peer freeze counts')
for x in auth.get('pins',auth.get('observed',[])):check(x)
inputs=load(p['inputs']['path']);check(inputs['providers']);providers=load(inputs['providers']['path']);need(len(providers)==494,'all providers')
for x in providers:check(x['actual']);check(x['expected'])
for ar,pr,n in zip(a['records'],p['records'],[0,14],strict=True):
 need(ar['module']==pr['module']and pr['exit_code']==0 and pr['matches_author'],'peer records')
 for key in ['source','snapshot','object','log','timing']:check(pr[key])
 for key in ['source','object','log']:need(ar[key]['sha256']==pr[key]['sha256'],'author peer equality')
 need(pr['axiom_reports']==ar['axiom_reports']and len(pr['axiom_reports'])==n,'reports')
 for _,ax in pr['axiom_reports']:need(set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'},'standard axioms')
 log=Path(pr['log']['path']).read_text();need(not re.search(r'\b(?:warning|error|sorryAx)\b',log),'diagnostics')
 ap=Path(ar['object']['path']);pp=Path(pr['object']['path']);need(stat.S_ISREG(pp.lstat().st_mode)and pp.stat().st_ino!=ap.stat().st_ino,'independent regular object')
for x in list(pins.values()):check(x)
out=D/'reviews/arithmetic-binary-population-root-acceptance.json';need(not out.exists(),'fresh acceptance')
result=dict(status='PASS',role='ROOT authored; complemented independently reviewed/replayed; ROOT fully read peer driver/receipt and reauthenticated the independent result without third compilation',author=rec(D/'reviews/arithmetic-binary-population-replay.json'),peer_packet=rec(D/'reviews/arithmetic-binary-population-peer-replay.json'),observations=observations,unique_paths=len(pins),pins=list(pins.values()),driver=rec(__file__),provider=p['private_provider'])
out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k!='pins'},indent=2))
