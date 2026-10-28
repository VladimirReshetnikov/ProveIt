from pathlib import Path
import hashlib,json,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency'
OLD=D/'reviews/arithmetic-register-boxes215-replay.json'
OLDMF=D/'reviews/arithmetic-register-boxes215-author-replay/FILES.json'
Q=D/'reviews/arithmetic-register-boxes215-final-replay'
P=Path('/tmp/register-boxes215-controller-author-1kdy5c1a')
def rec(p):
 p=Path(p);return dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
pins={};observations=0
def check(x):
 global observations
 y=rec(x['path']);assert y['sha256']==x['sha256'],x['path'];pins[y['path']]=y;observations+=1;return y
def copy(p,d):
 assert not d.exists();shutil.copyfile(p,d);assert rec(p)['sha256']==rec(d)['sha256'];return rec(d)
assert shutil.disk_usage('/tmp').free>=512*1024**2
check(dict(path=str(OLD),sha256='6b18110388c842980e4c6862f184793d01c360ad5b4779014c4599334bb67e55'))
check(dict(path=str(OLDMF),sha256='b6a5e7a2987f134f7b5959738997fbfe30f26e69411f84ae30da611bf13b9302'))
for x in json.loads(OLDMF.read_text()):check({**x,'path':str(R/x['path'])})
old=json.loads(OLD.read_text());s=json.loads((P/'AUTHOR.json').read_text());inp=json.loads((P/'inputs.json').read_text())
assert s['status']=='PASS' and len(s['records'])==3
main=s['records'][1]['source']['path'];check(s['inputs']);check(s['driver'])
historical=[]
for x in json.loads(Path(old['reauthentication']['path']).read_text())['pins']:
 if x['path']==main and x['sha256']!=rec(main)['sha256']:
  historical.append(dict(historical=x,current=rec(main),reason='ROOT-authorized single omit annotation on values_split; attempt9 snapshot preserved.'))
 else:check(x)
assert len(historical)==1
for x in inp['pins']:check(x)
for x in inp['actual_providers']:check(x['actual']);check(x['expected'])
assert len(inp['actual_providers'])==595
for x in s['records']:
 for field in ['source','snapshot','object','log','timing']:check(x[field])
 assert x['source']['sha256']==x['snapshot']['sha256']
 assert x['exit_code']==0 and not Path(x['object']['path']).is_symlink()
assert Path(s['records'][0]['log']['path']).stat().st_size==0
assert Path(s['records'][1]['log']['path']).stat().st_size==0
assert len(s['records'][2]['axiom_reports'])==14
assert 'warning:'not in Path(s['records'][2]['log']['path']).read_text()
assert not Q.exists();Q.mkdir();copies=[]
for f in sorted(P.iterdir()):
 if f.is_file()and f.suffix in {'.json','.py','.lean','.log','.time'}:copies.append(copy(f,Q/f.name))
copy(__file__,Q/'freeze.py')
final=dict(number=10,private=str(P),state=rec(P/'AUTHOR.json'),status='PASS',records=s['records'],copies=copies)
save(Q/'reauthentication.json',dict(status='PASS',observations=observations,unique_paths=len(pins),pins=list(pins.values()),historical_source_change=historical))
packet=dict(status='PASS',scope='Author construction; independent review pending',counts=s['counts'],final=final,attempts=old['attempts']+[final],pre_final_packet=rec(OLD),pre_final_manifest=rec(OLDMF),historical_source_change=historical,reauthentication=rec(Q/'reauthentication.json'),freeze=rec(Q/'freeze.py'),plan=old['plan'],final_sources=[x['source']for x in s['records']],final_objects=[x['object']for x in s['records']],final_reports=s['records'][2]['axiom_reports'])
OUT=D/'reviews/arithmetic-register-boxes215-final-replay.json';assert not OUT.exists();save(OUT,packet)
files=[rec(p)for p in sorted(Q.rglob('*'))if p.is_file()]+[rec(OUT),rec(OLDMF)]
for x in files:x['path']=str(Path(x['path']).relative_to(R))
save(Q/'FILES.json',files)
assert shutil.disk_usage('/tmp').free>=512*1024**2
print('PACKET',rec(OUT));print('MANIFEST',rec(Q/'FILES.json'));print('FILES',len(files),'OBSERVATIONS',observations,'PATHS',len(pins))
