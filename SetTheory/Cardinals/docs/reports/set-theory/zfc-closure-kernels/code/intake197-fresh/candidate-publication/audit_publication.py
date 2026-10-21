"""Own metadata-only candidate publication audit; no candidate execution."""
from pathlib import Path
import hashlib,json,re,posixpath
HERE=Path(__file__).resolve().parent
REPO=Path('/home/codex/.codex/worktrees/ec20/Proofs')
DEST='Computability/BusyBeaver/Research/ZFC/candidate-k216/alternatives/permuted'
HOST='SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
record=Path('/tmp/zfc-intake197/fresh/actual.json')
actual=json.loads(record.read_text())
review_path=Path('/tmp/zfc-intake197/reflection-review/actual-review.json')
review=json.loads(review_path.read_text())
assert actual['status']=='TEN_SELECTED_LEAVES_PASS' and len(actual['jobs'])==10
assert all(x['accepted'] and x['exit_code']==0 and not x['timed_out'] for x in actual['jobs'])
assert review['status']=='PASS_INDEPENDENT_SAVED_OUTPUT_AUDIT' and review['actual_sha256']==sha(record)
for key,steps,rules,minimum in [('210',95674,1605450,6),('120',96244,1605505,9)]:
 r=review['runtime'][key]
 assert (r['cases'],r['rows'],r['startup_steps'],r['symbolic_rules'],r['min_positive_constant'],r['one_cells'],r['gap'])==(6176,432,steps,rules,minimum,95,1)
provenance={'status':'ACCEPTED_ORDINARY_PROOF_ALTERNATIVES_AFTER_TEN_FRESH_PASSES',
 'source_number':159,'arrival_commit_prefix':'d59b441882','primary_candidate_unchanged':'candidate-k216 partial-selector',
 'actual_sha256':sha(record),'saved_output_review_sha256':sha(review_path),
 'ordinary_source_review_sha256':sha(Path('/tmp/zfc-intake197/drop-review/review.json')),
 'source_dossier_sha256':sha(Path('/tmp/zfc-intake197/drop-review/dossier.md')),
 'root_runner_sha256':sha(Path('/tmp/zfc-intake197/run.py')),
 'root_secondary_blank_driver_sha256':sha(Path('/tmp/zfc-intake197/secondary_blank.py')),
 'actual_destination':HOST+'/data/intake197-fresh/actual.json',
 'actual_review_destination':HOST+'/data/intake197-fresh/actual-review.json',
 'claims':['ordinary ZFC-provable blank nonhalting equivalence with Con(ZFC)','two distinct216-state alternatives; no lower bound'],
 'limits':['no exact-table Lean/Rocq/internal-PA endpoint','no historical before/after hash map invented','C++ receipts delivered only; no fresh compilation','no further215-state saving proved'],
 'authorship':{'submission':'ChatGPT-assisted Source159 contribution for ProveIt; inherited notices retained','drop_contract':'independent full math/selected-source review, publication exposition and own metadata audit','review_upstream_reflection':'independent literal comparison and saved-output audit','root':'fresh execution and publication'}}
(HERE/'provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
maps=json.loads((HERE/'copy-map.json').read_text())['files'] if (HERE/'copy-map.json').exists() else []
# This first pass creates provenance; run prepare.py, then call again to audit it.
if not any(x['destination']==DEST+'/provenance.json' for x in maps):
 print('PROVENANCE_READY; rerun prepare then this audit');raise SystemExit(0)
known={x['destination'] for x in maps};checks=[]
for x in maps:
 p=Path(x['source']);assert p.is_file() and sha(p)==x['sha256'];checks.append(x['destination'])
 if x['role']=='byte-exact submission artifact':assert p.read_bytes()==Path(x['origin']).read_bytes()
 elif x['role'].startswith('own compact'):assert json.loads(p.read_text())==json.loads(Path(x['origin']).read_text())
planned={HOST+'/intake-197.md',HOST+'/intake-197-reproduction.md',HOST+'/data/intake197-fresh/actual.json',HOST+'/data/intake197-fresh/actual-review.json'}
links=[]
for name in ['README.md','proof.md','NOTICE.md']:
 text=(HERE/name).read_text();assert 'Fresh verification pending' not in text
 for target in re.findall(r'\]\(([^)]+)\)',text):
  assert not target.startswith(('http','file:'))
  rel=posixpath.normpath(posixpath.join(DEST,target.split('#')[0]))
  status='mapped' if rel in known or any(q.startswith(rel+'/') for q in known) else 'existing' if (REPO/rel).exists() else 'planned host' if rel in planned else 'BROKEN'
  assert status!='BROKEN',(name,target,rel)
  links.append({'file':name,'target':target,'resolved':rel,'status':status})
for name in ['README.md','proof.md','NOTICE.md']:
 for h in re.findall(r'`([0-9a-f]{64})`',(HERE/name).read_text()):
  assert h in {x['sha256'] for x in maps} or h in {'4aa33f0c4844043d243fb7d01ef316d4b72de641864e5317525f7cfac7f5c809','080b4fe855c109ab77588c01c9e012d9572afa7721682306370ccb2eb22cbea9'},(name,h)
out={'status':'OWN_PUBLICATION_METADATA_AND_PROSE_REVIEW_PASS','reviewer':'drop_contract; author of this exposition',
 'copy_map_sha256':sha(HERE/'copy-map.json'),'files':len(maps),'links':links,
 'actual_sha256':sha(record),'independent_saved_review_sha256':sha(review_path),
 'scope':'Full own prose reread and exact copied bytes/compact equality/printed pins/planned links plus terminal summary correspondence. No candidate replay or duplicate full case audit.',
 'script_sha256':sha(Path(__file__))}
(HERE/'publication-review.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':out['status'],'files':len(maps),'links':len(links),'review_sha256':sha(HERE/'publication-review.json')}))
