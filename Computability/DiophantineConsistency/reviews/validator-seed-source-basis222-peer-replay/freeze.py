from pathlib import Path
import hashlib,json,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs');REV=R/'Computability/DiophantineConsistency/reviews'
P=Path('/tmp/validator-seed-source-basis222-controller-peer-81rcdk9o')
E=REV/'validator-seed-source-basis222-peer-replay'
def rec(p):
 p=Path(p);return dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
def req(x,s):
 if not x:raise RuntimeError(s)
req(not E.exists(),'new freeze directory');req(shutil.disk_usage('/tmp').free>=512*1024**2,'512MiB reserve')
S=json.loads((P/'PEER.json').read_text());req(S['status']=='PASS'and len(S['records'])==2,'successful pair')
obs=json.loads((P/'observations.json').read_text())
for r in obs:req(rec(r['path'])['sha256']==r['sha256'],'final pin '+r['path'])
for r in S['records']:
 for k in ['source','snapshot','object','log','timing']:req(rec(r[k]['path'])['sha256']==r[k]['sha256'],'final artifact '+k)
 req(r['object_byte_identical']and r['log_byte_identical'],'exact author reproduction')
E.mkdir();copies=[]
for p in sorted(P.iterdir()):
 if p.is_file()and not p.is_symlink():
  q=E/p.name;shutil.copyfile(p,q);copies.append(dict(original=rec(p),saved=rec(q)))
shutil.copyfile(__file__,E/'freeze.py')
save(E/'freeze-authentication.json',dict(status='PASS',observations=len(obs),unique_paths=len({r['path']for r in obs}),copies=copies))
files=[dict(rec(p),path=str(p.relative_to(E)))for p in sorted(E.iterdir())if p.is_file()]
save(E/'FILES.json',files)
packet=dict(status='PASS',reviewer='controller_certificate',author='circuit_reduction',
 scope='Independent complete final-source mathematical review and fresh isolated two-leaf replay; no dependency refresh or downstream CP/GIC/HA inference.',
 author_packet=dict(path=str(REV/'validator-seed-source-basis222-replay.json'),sha256='c19fcc42ee10f3c48c1d0cc6fed1fb2838ad08538820466516a6c6b37a0c78fa'),
 private=str(P),state=S,durable_state=rec(E/'PEER.json'),inputs=rec(E/'inputs.json'),manifest=rec(E/'FILES.json'),files=len(files))
out=REV/'validator-seed-source-basis222-peer-replay.json';save(out,packet)
print(json.dumps(dict(packet=rec(out),manifest=rec(E/'FILES.json'),files=len(files),observations=len(obs)),indent=2))
