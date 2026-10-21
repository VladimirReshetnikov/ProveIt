"""Read-only archive integrity check; never run archived code or proof compilers."""
from pathlib import Path,PurePosixPath
import hashlib,json,tarfile
P=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((P/'result.json').read_text());idx=json.loads((P/'index.json').read_text())
assert sha((P/'index.json').read_bytes())==r['index_sha256']
assert sha((P/'evidence.tar.gz').read_bytes())==r['archive_sha256']
with tarfile.open(P/'evidence.tar.gz','r:gz') as t:
 ms=t.getmembers();assert len(ms)==len(idx)==r['members'] and len({m.name for m in ms})==len(ms)
 for m in ms:
  p=PurePosixPath(m.name);assert not p.is_absolute() and '..' not in p.parts and m.isfile()
  assert not any(x in m.name for x in ['.olean','.ilean','.pyc'])
  b=t.extractfile(m).read();assert len(b)==idx[m.name]['size'] and sha(b)==idx[m.name]['sha256']
print(json.dumps({'status':'PASS_ARCHIVE_BYTES_ONLY','members':len(idx),'compiled_objects':False}))
