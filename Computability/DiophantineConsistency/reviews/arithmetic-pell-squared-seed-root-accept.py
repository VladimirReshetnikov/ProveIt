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
a=load(D/'reviews/arithmetic-pell-squared-seed-replay.json','7c0e54bd7a003d21fe54dc66216e025e549e410e90547ab1f33e48ad69618f40')
p=load(D/'reviews/arithmetic-pell-squared-seed-peer-replay.json','66bfbe0b9ff07cb382df5ce764b315fad9b1f3177d1cecd2cceb46ca9cf2ced3')
check(dict(path=str(D/'reviews/arithmetic-pell-squared-seed-peer.md'),sha256='5aa716bd5d42167678dfa63b28a176db659088b66c09bf566106209b43d2c6af'))
check(rec(D/'reviews/arithmetic-pell-squared-seed-author.md'))
for stem,h,count in [('arithmetic-pell-squared-seed-author-replay','a72448ab814f6eeb1fc06cb8dece3771311e1ab0628da40bf336203b89ddf1eb',25),('arithmetic-pell-squared-seed-peer-replay','9df5af2e84f89ae4aafcbfb29c1c9ac61d6734cdd4e52be66ecb0f0c89b6f6cf',17)]:
 rows=load(D/'reviews'/stem/'FILES.json',h);need(len(rows)==count,'manifest size')
 for x in rows:check(dict(x,path=str(R/x['path'])))
need(a['status']==p['status']=='PASS'and a['author']=='ROOT'and p['author']=='ROOT','roles/status')
for key in ['inputs','driver','final_state','plan','compiler','freeze_authentication','freeze']:check(p[key])
auth=load(p['freeze_authentication']['path']);need(auth['status']=='PASS','peerfreeze')
for x in auth['pins']:check(x)
inputs=load(p['inputs']['path']);check(inputs['providers']);providers=load(inputs['providers']['path']);need(len(providers)==498,'all providers')
for x in providers:check(x['actual']);check(x['expected'])
for ar,pr,n in zip(a['records'],p['records'],[0,4],strict=True):
 need(ar['module']==pr['module']and pr['exit_code']==0 and pr['object_byte_identical']and pr['full_log_identical'],'peer records')
 for key in ['source','snapshot','object','log','timing']:check(pr[key])
 for key in ['source','object','log']:need(ar[key]['sha256']==pr[key]['sha256'],'author peer equality')
 need(pr['axiom_reports']==ar['axiom_reports']and len(pr['axiom_reports'])==n,'reports')
 for _,ax in pr['axiom_reports']:need(set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'},'standard axioms')
 log=Path(pr['log']['path']).read_text();need(not re.search(r'\b(?:warning|error|sorryAx)\b',log),'diagnostics')
 ap=Path(ar['object']['path']);pp=Path(pr['object']['path']);need(stat.S_ISREG(pp.lstat().st_mode)and pp.stat().st_ino!=ap.stat().st_ino,'independent regular object')
for x in list(pins.values()):check(x)
out=D/'reviews/arithmetic-pell-squared-seed-root-acceptance.json';need(not out.exists(),'fresh acceptance')
result=dict(status='PASS',role='ROOT authored; controller independently source-reviewed and replayed',author=a['manifest'],peer_packet=rec(D/'reviews/arithmetic-pell-squared-seed-peer-replay.json'),observations=observations,unique_paths=len(pins),pins=list(pins.values()),driver=rec(__file__),provider=p['private_provider'])
out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k!='pins'},indent=2))
