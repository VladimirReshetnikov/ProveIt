from pathlib import Path
import hashlib,json,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
D=R/'Computability/DiophantineConsistency'
P=Path('/tmp/symbolic-core215-root-d4b0mp1m')
O=D/'reviews/arithmetic-symbolic-core215-root-replay'
F=D/'reviews/arithmetic-symbolic-core215-root-replay.json'
def rec(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
def need(x,m):
 if not x:raise RuntimeError(m)
pins={};observations=0
def check(x):
 global observations
 a=rec(x['path']);need(a['sha256']==x['sha256'],'hash '+x['path']);pins[a['path']]=a;observations+=1;return a
need(not O.exists()and not F.exists(),'fresh durable evidence')
need(shutil.disk_usage('/tmp').free>=512*1024**2,'512MiB reserve')
s=json.loads((P/'ROOT.json').read_text());need(s['status']=='PASS','terminal ROOT success')
a=check(dict(path=str(D/'reviews/arithmetic-symbolic-core215-replay.json'),sha256='89f2dbb6efcca6b80625f958abf112a338f21b432b914f666169e97f37670776'))
author=json.loads(Path(a['path']).read_text())
inputs=json.loads((P/'inputs.json').read_text())
for x in inputs['pins']:check(x)
for x in inputs['actual_providers']:check(x['actual']);check(x['expected'])
for row,expected in zip(s['records'],author['final']['records']):
 need(row['exit_code']==0 and row['author_object_and_full_log_equal'],'accepted independent result')
 for k in ['source','snapshot','object','log','timing']:check(row[k])
 for k in ['source','object','log']:need(row[k]['sha256']==expected[k]['sha256'],'author equality '+k)
 need(row['axiom_reports']==expected['axiom_reports'],'every report equal')
for x in list(pins.values()):check(x)
auth=P/'final-authentication.json';need(not auth.exists(),'new authentication')
save(auth,dict(status='PASS',observations=observations,unique_paths=len(pins),pins=list(pins.values()),scope='ROOT selected current inputs,597 first providers,two fresh sources/objects/full logs and all15 reports reauthenticated. Author58 durable files and seven attempts were checked by the independently executed driver.'))
O.mkdir()
for row in s['records']:
 for k in ['snapshot','log','timing']:
  source=Path(row[k]['path']);shutil.copyfile(source,O/source.name)
for name in ['ROOT.json','inputs.json','driver.py','final-authentication.json']:shutil.copyfile(P/name,O/name)
shutil.copyfile(__file__,O/'freeze.py')
packet=dict(status='PASS',scope='Independent ROOT pair; actual215 symbolic execution, no final PA/HA endpoint.',counts=s['counts'],records=s['records'],author=a,
 state=check(rec(P/'ROOT.json')),durable_state=rec(O/'ROOT.json'),driver=rec(O/'driver.py'),inputs=rec(O/'inputs.json'),final_authentication=rec(O/'final-authentication.json'),
 observations=observations,unique_paths=len(pins),private=str(P),provider=str(P/'lib'))
save(F,packet)
files=sorted(O.iterdir())+[F,D/'reviews/arithmetic-symbolic-core215-root.md']
manifest=[dict(rec(p),path=str(p.relative_to(R)))for p in files]
save(O/'FILES.json',manifest)
print(json.dumps(dict(packet=rec(F),manifest=rec(O/'FILES.json'),files=len(manifest),observations=observations,unique_paths=len(pins)),indent=2))
