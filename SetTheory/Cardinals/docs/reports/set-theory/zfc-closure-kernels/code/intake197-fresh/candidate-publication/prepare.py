"""Own publication copier; exact input artifacts plus explicit JSON serialization.

Writes only this scratch directory. Does not execute submitted code or touch
the maintained tree. The root controls final installation.
"""
from pathlib import Path
import hashlib,json,shutil

HERE=Path(__file__).resolve().parent
P=Path('/tmp/zfc-intake197/extracted/K216_Permuted_Commands_2026-10-21')
DEST='Computability/BusyBeaver/Research/ZFC/candidate-k216/alternatives/permuted'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
copies={
 'machine/k216.native.tm':'k216.native.tm','machine/k216.tm':'k216.tm',
 'machine/sites216.json':'sites216.json','machine/canonicalization.json':'canonicalization.json',
 'secondary/k216-120.native.tm':'secondary/k216-120.native.tm',
 'secondary/k216-120.tm':'secondary/k216-120.tm',
 'secondary/sites120.json':'secondary/sites120.json',
 'secondary/canonicalization.json':'secondary/canonicalization.json'}
for p in (P/'licenses').iterdir():
 if p.is_file():copies[str(p.relative_to(P))]=str(p.relative_to(P))
for name in ['ATTRIBUTION.md','PREDECESSOR_ATTRIBUTION.md','K218_NOTICE.md','inputs.json','transition_recipe210.json','transition_recipe120.json']:
 copies['provenance/'+name]='provenance/'+name
maps=[]
for src,dst in copies.items():
 q=HERE/dst;q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert q.read_bytes()==(P/src).read_bytes()
 else:shutil.copyfile(P/src,q)
 maps.append(dict(source=str(q),destination=DEST+'/'+dst,sha256=sha(q),origin=str(P/src),role='byte-exact submission artifact'))
for src,dst in [('sites216.json','sites216.compact.json'),('secondary/sites120.json','secondary/sites120.compact.json')]:
 q=HERE/dst;data=(json.dumps(json.loads((HERE/src).read_text()),separators=(',',':'))+'\n').encode()
 if q.exists():assert q.read_bytes()==data
 else:q.write_bytes(data)
 assert json.loads(q.read_text())==json.loads((HERE/src).read_text())
 maps.append(dict(source=str(q),destination=DEST+'/'+dst,sha256=sha(q),origin=str(HERE/src),role='own compact serialization; parsed data equal'))
for name in ['README.md','proof.md','NOTICE.md','provenance.json']:
 q=HERE/name;maps.append(dict(source=str(q),destination=DEST+'/'+name,sha256=sha(q),role='own publication exposition'))
(HERE/'copy-map.json').write_text(json.dumps({'status':'SCRATCH_CANDIDATE_PUBLICATION_READY','files':maps,'writer_sha256':sha(Path(__file__))},indent=2)+'\n')
print(json.dumps({'file_count':len(maps),'copy_map_sha256':sha(HERE/'copy-map.json')}))
