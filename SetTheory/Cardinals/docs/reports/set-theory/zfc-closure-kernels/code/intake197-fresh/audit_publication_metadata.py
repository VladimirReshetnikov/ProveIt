"""Own bounded publication audit: bytes, links, compression and saved statuses.

No candidate/recovery replay and no Git operation. A concurrent root-owned K215
publication may supply its one explicitly planned README link after this check.
"""
from pathlib import Path
import gzip,hashlib,json,re

HERE=Path(__file__).resolve().parent;H=HERE.parents[1];R=H.parents[5]
D=H/'data/intake197-fresh';C=R/'Computability/BusyBeaver/Research/ZFC/candidate-k216/alternatives/permuted'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
index=json.loads((D/'archive-index.json').read_text())
for f in index['files']:
 p=D/f['stored'];assert sha(p)==f['stored_sha256']
 b=p.read_bytes();b=gzip.decompress(b) if f['encoding']=='gzip' else b
 assert hashlib.sha256(b).hexdigest()==f['sha256'] and len(b)==f['bytes']
review=json.loads((D/'actual-review.json').read_text());actual=json.loads((D/'actual.json').read_text())
assert actual['status']=='TEN_SELECTED_LEAVES_PASS' and len(actual['jobs'])==10
assert review['actual_sha256']==sha(D/'actual.json') and review['status']=='PASS_INDEPENDENT_SAVED_OUTPUT_AUDIT'
assert (D/'portable-check/actual-review.json').read_bytes()==(D/'actual-review.json').read_bytes()
recovered=json.loads((D/'portable-check/recovery.json').read_text());prepared=json.loads((D/'portable-check/audit-view-preparation.json').read_text())
assert recovered['members']==72 and prepared['files']==len(index['files'])==81
assert prepared['archive_index_sha256']==sha(D/'archive-index.json')
mapping=json.loads((D/'candidate-publication/current-copy-map.json').read_text())
assert len(mapping['files'])==25
for f in mapping['files']:assert sha(R/f['destination'])==f['sha256']
pages=[H/'intake-197.md',H/'intake-197-reproduction.md',HERE/'README.md',C/'README.md',C/'proof.md',C/'NOTICE.md']
planned=R/'Computability/BusyBeaver/Research/ZFC/candidate-k215/README.md';links=[]
for page in pages:
 for target in re.findall(r'\]\(([^)]+)\)',page.read_text()):
  if target.startswith(('http','mailto:','#')):continue
  p=(page.parent/target.split('#')[0]).resolve()
  status='exists' if p.exists() else 'root-owned K215 publication pending' if p==planned else 'BROKEN'
  assert status!='BROKEN',(page,target)
  links.append({'page':str(page.relative_to(R)),'target':target,'status':status})
owned=[H/'intake-197.md',H/'intake-197-reproduction.md',H/'code/recover-intake197.py']
for base in [HERE,D,C]:owned.extend(p for p in base.rglob('*') if p.is_file() and p.name not in ('publication-final-review.json','changed-paths.json'))
owned.append(H/'data/intake196-placement-history/prose-peer.json')
owned=sorted(set(owned));assert H/'data/intake197-placement.json' not in owned
pinlist=[{'path':str(p.relative_to(R)),'sha256':sha(p),'bytes':p.stat().st_size} for p in owned]
(D/'changed-paths.json').write_text(json.dumps(pinlist,indent=2)+'\n')
out={'status':'PUBLICATION_METADATA_AND_PROSE_REVIEW_PASS','reviewer':'drop_contract; author of publication prose and copier',
 'files':len(pinlist),'bytes':sum(x['bytes'] for x in pinlist),'saved_view_files':81,'candidate_files':25,'links':links,
 'actual_sha256':sha(D/'actual.json'),'independent_saved_review_sha256':sha(D/'actual-review.json'),
 'current_candidate_map_sha256':sha(D/'candidate-publication/current-copy-map.json'),
 'pages':{str(p.relative_to(R)):sha(p) for p in pages},'script_sha256':sha(Path(__file__)),
 'portable_checks':'Own recovery and decompression preparer ran; unchanged record auditor returned PASS with byte-identical result. No candidate rerun.',
 'scope':'Full own prose read; exact saved compression/byte and candidate-copy checks plus local link audit. Not a second full runtime-case re-audit.',
 'unchanged_ownership':['placement map','root/host/catalogue/incoming files','Git index and commits'],
 'notes':['Historical initial candidate map/review remain preserved; the after215-context diff and current map bind the later README status correction.','Empty stderr files and all20 logs must be included by the root Git writer even if ignored.']}
(D/'publication-final-review.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':out['status'],'files':len(pinlist),'bytes':out['bytes'],'links':len(links),'planned_links':sum(x['status']!='exists' for x in links),'review_sha256':sha(D/'publication-final-review.json')}))
