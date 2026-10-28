from pathlib import Path
import hashlib,json,os,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency'
P=Path('/tmp/arithmetic-carrier-soundness2011-root-d5casc3p');O=D/'reviews/arithmetic-carrier-soundness2011-root-replay';F=D/'reviews/arithmetic-carrier-soundness2011-root-replay.json'
pins={};observations=0
def need(c,m):
 if not c:raise RuntimeError(m)
def rec(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
def check(x):
 global observations
 a=rec(x['path']);need(a['sha256']==x['sha256'],'hash '+x['path']);pins[a['path']]=a;observations+=1;return a
def read(p):return json.loads(Path(p).read_text())
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
need(not O.exists()and not F.exists(),'fresh durable evidence');need(shutil.disk_usage('/tmp').free>=512*1024**2,'reserve')
s=read(P/'ROOT.json');need(s['status']=='PASS','terminal ROOT result');i=read(P/'inputs.json')
a=check(dict(path=str(D/'reviews/arithmetic-carrier-soundness2011-replay.json'),sha256='bf96127c58c05bfab6356c8adadf823712b47d80b14b7d8b52889fff83bd34bc'));author=read(a['path'])
for x in read(i['authentication']['path'])['pins']:check(x)
providers=read(i['providers']['path']);need(len(providers)==570,'all providers')
for x in providers:check(x['actual']);check(x['expected'])
for row,ar in zip(s['records'],author['records'],strict=True):
 need(row['exit_code']==0 and row['author_object_and_full_log_equal'],'successful independent pair')
 for key in ['source','snapshot','log','timing','object']:check(row[key])
 for key in ['source','object','log']:need(row[key]['sha256']==ar[key]['sha256'],'author matching '+key)
 need(row['axiom_reports']==ar['axiom_reports'],'all reports match')
for x in list(pins.values()):check(x)
check(rec(P/'ROOT.json'));check(rec(P/'inputs.json'));check(rec(P/'driver.py'));check(i['authentication']);check(i['providers'])
auth=P/'final-authentication.json';need(not auth.exists(),'new authentication')
save(auth,dict(status='PASS',observations=observations,unique_paths=len(pins),pins=list(pins.values()),scope='Actual literal current zero to five additive equations. Both fresh objects/full logs/all5reports and570providers reauthenticated; all101authorfiles and10attempts checked by independent driver.'))
O.mkdir()
for q in [*sorted((P/'logs').iterdir()),*[P/n for n in ['ROOT.json','inputs.json','driver.py','authentication.json','providers.json','final-authentication.json']]]:
 need(q.is_file()and not q.is_symlink(),'immutable regular metadata');os.link(q,O/q.name)
shutil.copyfile(__file__,O/'freeze.py')
packet=dict(status='PASS',scope='Actual maintained splitNatural zero to five additive equations in every IΣ1 model; exact current bounds and one natural shift. No product/norm/transport/port oracle; complete polynomial/native encoding/cofinal/HA remain open.',counts=i['counts'],records=s['records'],author=a,private=str(P),provider=str(P/'lib'),state=rec(P/'ROOT.json'),durable_state=rec(O/'ROOT.json'),inputs=rec(O/'inputs.json'),driver=rec(O/'driver.py'),final_authentication=rec(O/'final-authentication.json'),observations=observations,unique_paths=len(pins))
save(F,packet)
files=[*sorted(O.iterdir()),F,D/'reviews/arithmetic-carrier-soundness2011-root.md'];save(O/'FILES.json',[dict(rec(q),path=str(q.relative_to(R)))for q in files])
print(json.dumps(dict(packet=rec(F),manifest=rec(O/'FILES.json'),files=len(files),observations=observations,unique_paths=len(pins)),indent=2))
