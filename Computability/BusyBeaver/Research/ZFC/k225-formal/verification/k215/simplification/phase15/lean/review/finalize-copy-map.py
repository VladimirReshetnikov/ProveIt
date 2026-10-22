"""Produce an allowlisted byte-copy map after terminal capture and owner saved check."""
from pathlib import Path
import json,hashlib
S=Path('/tmp/k215-phase15-published/lean');E=Path(__file__).resolve().parent/'run2';OUT=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text())
assert read(E/'capture-actual.json')['exit_code']==0 and read(E/'saved-actual.json')['exit_code']==0
summary=read(S/'result.json');saved=read(E/'saved-review.json');assert summary['status']=='PASS_COLLECTED_PHASE15'and saved['status']=='PASS_SAVED_PHASE15'and saved['current_sources_checked']
assert summary['archive_sha256']==saved['archive_sha256']==sha(S/'execution.tar.gz')
core=['README.md','basis.py','basis-reference.json','packet.py','review_saved.py','result.json','index.json','execution.tar.gz'];assert set(p.name for p in S.iterdir())==set(core)
prefix='Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase15/lean/'
files=[]
def add(p,target):
 p=Path(p);assert p.is_file()and not p.is_symlink();files.append({'source':str(p),'target':prefix+target,'sha256':sha(p),'bytes':p.stat().st_size})
for n in core:add(S/n,n)
add(OUT/'core-hashes.json','review/core-hashes.json')
add(__file__,'review/finalize-copy-map.py')
for n in ['run.py','capture-actual.json','capture.stdout.log','capture.stderr.log','saved-actual.json','saved-review.json','saved.stdout.log','saved.stderr.log']:
 add(E/n,'review/owner/'+n.replace('.log','.txt'))
for p in sorted(Path('/tmp/k215-phase15-publication-peer').iterdir()):
 if p.is_file()and p.suffix in {'.json','.md','.py'}:add(p,'review/source-peer/'+p.name)
record={'status':'EXACT_COMPLETED_PHASE15_PACKET_COPY_MAP','core_files':8,'files':files,'total_bytes':sum(r['bytes']for r in files),'archive_sha256':summary['archive_sha256'],'owner_saved_sha256':sha(E/'saved-review.json'),'scope':'Exact bytes only; no canonical writes, compiled objects or ancestor archives. Historical raw statuses remain unchanged.'}
(OUT/'copy-map.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps({'files':len(files),'bytes':record['total_bytes'],'map_sha256':sha(OUT/'copy-map.json')}))
