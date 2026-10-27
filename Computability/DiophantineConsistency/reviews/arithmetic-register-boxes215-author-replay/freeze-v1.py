from pathlib import Path
import hashlib,json,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
D=R/'Computability/DiophantineConsistency'
Q=D/'reviews/arithmetic-register-boxes215-author-replay'
MARK=Path('/tmp/register-boxes215-controller-author-attempts.json')

def rec(p):
 p=Path(p);return dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
pins={};count=0
def check(x):
 global count
 y=rec(x['path']);assert y['sha256']==x['sha256'],x['path'];pins[y['path']]=y;count+=1;return y
def copy(p,d):
 assert not d.exists(),str(d)
 shutil.copyfile(p,d);assert rec(p)['sha256']==rec(d)['sha256'];return rec(d)
assert shutil.disk_usage('/tmp').free>=512*1024**2
assert not Q.exists();Q.mkdir()
paths=json.loads(MARK.read_text());assert len(paths)==9
attempts=[]
for i,p in enumerate(paths,1):
 p=Path(p);s=json.loads((p/'AUTHOR.json').read_text());inp=json.loads((p/'inputs.json').read_text())
 check(s['inputs']);check(s['driver'])
 for x in inp['pins']:check(x)
 for x in inp['actual_providers']:check(x['actual']);check(x['expected'])
 for x in inp['sources']:check(x['snapshot']);assert x['snapshot']['sha256']==x['sha256']
 for x in s['records']:
  check(x['log']);check(x['timing']);check(x['snapshot'])
  if 'object'in x:check(x['object'])
 out=Q/f'attempt-{i:02}';out.mkdir();copies=[]
 for f in sorted(p.iterdir()):
  if f.is_file()and f.suffix in {'.json','.py','.lean','.log','.time'}:copies.append(copy(f,out/f.name))
 attempts.append(dict(number=i,private=str(p),state=rec(p/'AUTHOR.json'),status=s['status'],records=s['records'],copies=copies))
final=attempts[-1];assert final['status']=='PASS'
s=json.loads(Path(final['state']['path']).read_text());assert len(s['records'])==3
for x in s['records']:check(x['source']);assert x['source']['sha256']==x['snapshot']['sha256']
assert len(s['records'][2]['axiom_reports'])==14
assert Path(s['records'][0]['log']['path']).stat().st_size==0
assert Path(s['records'][1]['log']['path']).stat().st_size==0
copy(MARK,Q/'attempts.json');copy(__file__,Q/'freeze.py')
save(Q/'reauthentication.json',dict(status='PASS',observations=count,unique_paths=len(pins),pins=list(pins.values())))
packet=dict(status='PASS',scope='Author construction and bounded private replay, not independent review',counts=s['counts'],final=final,attempts=attempts,reauthentication=rec(Q/'reauthentication.json'),freeze=rec(Q/'freeze.py'),plan=rec(D/'research/c222-site215-plan-20261027/cache-plan.json'),final_sources=[x['source']for x in s['records']],final_objects=[x['object']for x in s['records']],final_reports=s['records'][2]['axiom_reports'])
packetpath=D/'reviews/arithmetic-register-boxes215-replay.json';assert not packetpath.exists();save(packetpath,packet)
files=[rec(p)for p in sorted(Q.rglob('*'))if p.is_file()]+[rec(packetpath)]
for x in files:x['path']=str(Path(x['path']).relative_to(R))
save(Q/'FILES.json',files)
assert shutil.disk_usage('/tmp').free>=512*1024**2
print('PACKET',rec(packetpath));print('MANIFEST',rec(Q/'FILES.json'));print('FILES',len(files),'OBSERVATIONS',count,'PATHS',len(pins))
