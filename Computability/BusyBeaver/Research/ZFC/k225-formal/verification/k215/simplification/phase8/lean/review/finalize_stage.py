"""Add exact peer/root/control receipts and emit a tight publication copy map."""
from pathlib import Path
import hashlib,json,shutil
P=Path(__file__).resolve().parent;S=P/'staged-lean'
DEST='Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase8/lean/'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
assert read(P/'live-review-run1.json')['status']=='PASS_LIVE_POST_AUDIT_REVIEW'
assert read(P/'saved-review-run1.json')['status']=='PASS_SAVED_EVIDENCE_REVIEW'
assert read(S/'result.json')['status']=='PASS'
outer=Path('/tmp/k215-proof-phase8/outer-execution-observation.json');root=Path('/tmp/k215-proof-phase8/root-actual-review.json')
assert read(outer)['exit_code']==0 and read(outer)['root_review_sha256']==sha(root)
assert read(root)['result_sha256']==read(outer)['result_sha256']==read(P/'saved-review-run1.json')['result_sha256']
base=['README.md','basis-reference.json','basis_reference.py','evidence.py','review_saved.py','execution.tar.gz','index.json','result.json','live-review.json']
extra={
 'review/saved-review.json':P/'saved-review-run1.json',
 'review/root-actual-review.json':root,
 'review/root_readonly_review.py':Path('/tmp/k215-proof-phase8/root_readonly_review.py'),
 'review/outer-execution-observation.json':outer,
 'review/source-peer.json':Path('/tmp/k215-proof-phase8-publication-peer/review.json'),
 'review/source-peer.md':Path('/tmp/k215-proof-phase8-publication-peer/review.md'),
 'review/source-freeze-v1.json':P/'source-freeze-v1.json',
 **{'review/peer-'+n:Path('/tmp/k215-proof-phase8-publication-peer')/n for n in ('controls.py','controls-result.json','controls.stdout.log','controls.stderr.log')},
 'review/controls.py':P/'controls.py','review/controls-result.json':P/'controls-result.json',
 'review/controls.stdout.log':P/'controls.stdout.log','review/controls.stderr.log':P/'controls.stderr.log',
 'review/README.prepared.md':P/'README.prepared.md','review/preparation-history.json':P/'preparation-history.json',
 'review/live.stdout.log':P/'live.stdout.log','review/live.stderr.log':P/'live.stderr.log',
 'review/publish.stdout.log':P/'publish.stdout.log','review/publish.stderr.log':P/'publish.stderr.log',
 'review/saved.stdout.log':P/'saved.stdout.log','review/saved.stderr.log':P/'saved.stderr.log',
 'review/finalize_stage.py':Path(__file__)}
assert sha(extra['review/root_readonly_review.py'])==read(root)['reviewer_sha256']
for name,src in extra.items():
 dst=S/name;assert not dst.exists();assert src.is_file() and not src.is_symlink()
 dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst)
allowed=base+list(extra)
assert len(allowed)==len(set(allowed))
rows=[]
for name in allowed:
 path=S/name
 assert path.is_file() and not path.is_symlink()
 assert '__pycache__'not in path.parts and not any(x in {'.olean','.ilean','.pyo','.pyc','.o','.so','.vo','.vos','.vok'}for x in path.suffixes)
 rows.append({'source':str(path),'destination':DEST+name,'sha256':sha(path),'bytes':path.stat().st_size})
map={'status':'HELD_STAGED_PACKET_FOR_ROOT_COPY','files':rows,'file_count':len(rows),'bytes':sum(r['bytes']for r in rows),'scope':'Exact nine primary packet files and additive review/control/root observation receipts; no canonical mutation or proof execution.'}
with(P/'copy-map.json').open('x')as f:json.dump(map,f,indent=2);f.write('\n')
print(json.dumps({k:v for k,v in map.items()if k!='files'},indent=2))
