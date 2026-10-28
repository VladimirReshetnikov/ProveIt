from pathlib import Path
import json,hashlib,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs');REV=R/'Computability/DiophantineConsistency/reviews'
P=Path('/tmp/native-adaptive-current2011-controller-peer-n5cwjt2a')
def rec(p):
 p=Path(p);return dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
def check(r):assert rec(r['path'])['sha256']==r['sha256'],r['path']
def save(p,j):p.write_text(json.dumps(j,indent=2)+'\n')
s=json.loads((P/'PEER.json').read_text());assert s['status']=='PASS'
i=json.loads((P/'INPUTS.json').read_text())
for r in i['pins']:check(r)
for r in s['records']:
 for key in ['source','snapshot','object','log','timing']:check(r[key])
 assert r['object_byte_identical'] and r['log_byte_identical']
out=REV/'native-adaptive-current2011-peer-replay';assert not out.exists();out.mkdir()
for name in ['PEER.json','INPUTS.json','driver.py','author-driver.py']:shutil.copyfile(P/name,out/name)
for r in s['records']:
 for key in ['snapshot','object','log','timing']:
  path=Path(r[key]['path']);shutil.copyfile(path,out/path.name)
shutil.copyfile(__file__,out/'freeze.py')
j=dict(status='PASS',reviewer='controller_certificate',author='complemented47_review',
 scope='Independent complete source/contract/provenance review and fresh two-leaf replay; accepted prerequisites reused, no dependency rebuild or HA/metric endpoint claim.',
 final=s,author_packet=i['author_packet'],author_manifest=i['author_manifest'],author_receipt=i['author_receipt'],
 inputs=rec(out/'INPUTS.json'),executed_peer_driver=rec(out/'driver.py'),durable_state=rec(out/'PEER.json'))
packet=REV/'native-adaptive-current2011-peer-replay.json';assert not packet.exists();save(packet,j)
files=[dict(path=str(p.relative_to(R)),**{k:v for k,v in rec(p).items()if k!='path'}) for p in sorted(out.iterdir())if p.is_file()]
save(out/'FILES.json',files)
for p in [packet,out/'FILES.json']:print(rec(p))
print('files',len(files))
