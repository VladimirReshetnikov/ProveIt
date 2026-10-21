"""Own explicit publication of Source159 evidence and accepted alternative files.

No submitted executable is imported or invoked. No Git mutation or placement
map rewrite. Original saved auditor and root runners are copied byte-for-byte.
"""
from pathlib import Path
import gzip,hashlib,json,shutil

REPO=Path('/home/codex/.codex/worktrees/ec20/Proofs')
HOST=REPO/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels'
BASE=Path('/tmp/zfc-intake197');FRESH=BASE/'fresh'
DATA=HOST/'data/intake197-fresh';CODE=HOST/'code/intake197-fresh'
DATA.mkdir(parents=True,exist_ok=False);CODE.mkdir(parents=True,exist_ok=True)
changed=[]
def digest(b):return hashlib.sha256(b).hexdigest()
def put(dst,data):
 dst.parent.mkdir(parents=True,exist_ok=True)
 if dst.exists():assert dst.read_bytes()==data,str(dst)
 else:dst.write_bytes(data)
 changed.append(str(dst.relative_to(REPO)))
def copy(src,dst):put(dst,src.read_bytes())
actual=json.loads((FRESH/'actual.json').read_text())
review=json.loads((BASE/'reflection-review/actual-review.json').read_text())
assert actual['status']=='TEN_SELECTED_LEAVES_PASS' and len(actual['jobs'])==10
assert review['status']=='PASS_INDEPENDENT_SAVED_OUTPUT_AUDIT' and review['actual_sha256']==digest((FRESH/'actual.json').read_bytes())
index=[]
def saved(src,stored,restore):
 raw=src.read_bytes();encoded=raw;encoding='identity'
 if src.suffix=='.json' and len(raw)>100000:
  encoded=gzip.compress(raw,compresslevel=9,mtime=0);stored+='.gz';encoding='gzip'
 put(DATA/stored,encoded)
 index.append({'stored':stored,'restore':restore,'encoding':encoding,'sha256':digest(raw),'stored_sha256':digest(encoded),'bytes':len(raw),'original':str(src)})
for p in sorted(FRESH.rglob('*')):
 if not p.is_file():continue
 rel=p.relative_to(FRESH)
 if rel.parts[0] in ('packet','parents'):continue
 saved(p,rel.as_posix(),rel.as_posix())
# Preserve only the selected actual inputs consumed by the saved auditor.
selected=['packet/'+p for p in review['selected_pristine_inputs']]
selected += ['parents/K218_Dominated_Rho8_2026-10-20/binary/code/'+p for p in review['runtime_inputs']]
selected += ['parents/K217_Dominated_Continuation_2026-10-20/code/vendor/source_language.py']
for rel in selected:saved(FRESH/rel,'saved-inputs/'+rel,rel)
assert len({x['restore'] for x in index})==len(index)
put(DATA/'archive-index.json',(json.dumps({'status':'EXACT_SAVED_OUTPUTS_AND_SELECTED_CURRENT_INPUTS','files':index,'scope':'All new outputs/raw logs retained. Selected current actual inputs are snapshotted; no historical before/after map claimed. Large JSON gzip encoding is reversible and separately pinned.'},indent=2)+'\n').encode())
copy(BASE/'run.py',CODE/'run.py');copy(BASE/'secondary_blank.py',CODE/'secondary_blank.py')
copy(BASE/'reflection-review/review_saved.py',CODE/'review_saved.py')
copy(BASE/'reflection-review/actual-review.json',DATA/'actual-review.json')
copy(BASE/'reflection-review/actual-review-freeze.json',DATA/'actual-review-freeze.json')
for group,path in [('math',BASE/'drop-review'),('literal',BASE/'reflection-review')]:
 for p in sorted(path.rglob('*')):
  if not p.is_file():continue
  rel=p.relative_to(path)
  if group=='literal' and p.name in ('review_saved.py','actual-review.json','actual-review-freeze.json'):continue
  target=(CODE if p.suffix=='.py' else DATA)/'reviews'/group/rel
  copy(p,target)
DRAFT=Path('/tmp/zfc-intake197-candidate-draft')
mapping=json.loads((DRAFT/'copy-map.json').read_text())
for row in mapping['files']:
 p=Path(row['source']);assert digest(p.read_bytes())==row['sha256'];copy(p,REPO/row['destination'])
for name in ['copy-map.json','publication-review.json']:
 copy(DRAFT/name,DATA/'candidate-publication'/name)
for p in sorted((DRAFT/'history').rglob('*')):
 if p.is_file():copy(p,DATA/'candidate-publication/history'/p.relative_to(DRAFT/'history'))
for name in ['prepare.py','audit_publication.py']:
 copy(DRAFT/name,CODE/'candidate-publication'/name)
copy(Path(__file__),CODE/'publication-writer.py')
receipt=Path('/tmp/zfc-intake196/prose-peer/review.json')
copy(receipt,HOST/'data/intake196-placement-history/prose-peer.json')
out={'status':'ACCEPTED_ALTERNATIVES_AND_FRESH_EVIDENCE_INSTALLED','candidate_files':len(mapping['files']),
 'saved_audit_files':len(index),'actual_sha256':digest((FRESH/'actual.json').read_bytes()),
 'actual_review_sha256':digest((BASE/'reflection-review/actual-review.json').read_bytes()),
 'archive_index_sha256':digest((DATA/'archive-index.json').read_bytes()),
 'candidate_copy_map_sha256':digest((DRAFT/'copy-map.json').read_bytes()),
 'writer_sha256':digest(Path(__file__).read_bytes()),
 'changed_files':changed,'scope':'Publication copies/data compression only. No submitted execution or Git mutation. Placement map untouched.'}
put(DATA/'publication.json',(json.dumps(out,indent=2)+'\n').encode())
(BASE/'installed-paths.json').write_text(json.dumps(changed,indent=2)+'\n')
print(json.dumps({'candidate_files':len(mapping['files']),'saved_audit_files':len(index),'total_written':len(changed),'publication_sha256':digest((DATA/'publication.json').read_bytes())}))
