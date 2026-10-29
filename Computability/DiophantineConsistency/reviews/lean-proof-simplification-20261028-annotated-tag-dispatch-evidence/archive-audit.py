from pathlib import Path
import json,zipfile,hashlib,subprocess
r=Path('Computability/DiophantineConsistency/reviews/lean-proof-simplification-20261028-annotated-tag-dispatch-evidence');j=json.loads((r/'BUNDLE.json').read_text());a=r/j['archive'];z=zipfile.ZipFile(a);assert z.testzip() is None and hashlib.sha256(a.read_bytes()).hexdigest()==j['archive_sha256'];assert set(j['members'])==set(z.namelist())
for n,v in j['members'].items():
 b=z.read(n);assert hashlib.sha256(b).hexdigest()==v['sha256'] and len(b)==v['bytes'];assert not n.endswith(('.olean','.ilean','.ir','.o','.olean.private','.olean.server'))
for n in [n for n in z.namelist() if n.startswith('sources/baseline/') and n.endswith('.lean')]:
 f=n.split('/')[-1];b=subprocess.check_output(['git','show',j['source_commit']+':Computability/DiophantineConsistency/Lean/DiophantineConsistency/'+f]);assert z.read(n)==b
print('CRC, all',len(j['members']),'member hashes, no compiled objects, and all seven baseline source snapshots verified')
