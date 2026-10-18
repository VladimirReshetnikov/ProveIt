#!/usr/bin/env python3
"""Own source-fidelity, path and metadata review only; no supplied program invocation."""
from pathlib import Path
import hashlib,json,re,ast
B=Path(__file__).parent;R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
d=lambda p:dict(path=str(p),sha256=sha(p));load=lambda p:json.loads(Path(p).read_text())
checks=[]
def check(x,s):
 assert x,s
 checks.append(s)
p=load(B/'write-inputs.json');check((p['batch'],p['host_source'],p['collection_reports'])==(166,70,290),'batch/source/report census')
check(len(p['files'])==75 and len({q['target'] for q in p['files']})==75,'75 distinct mapped input targets')
check(sha(R/p['base_article']['path'])==p['base_article']['sha256'],'base article remains unchanged')
check(sha(p['placement_map']['path'])==p['placement_map']['sha256'],'placement map pin');placement=load(p['placement_map']['path'])
check(len(placement['files'])==191 and sum(q['disposition']=='place_unchanged' for q in placement['files'])==170,'170 placed/21 archive-only/191 recoverable')
for q in placement['files']:
 if q['disposition']=='place_unchanged':check(sha(R/q['target'])==q['sha256'],'placed ancillary '+q['target'])
for q in p['files']:
 s=Path(q['source']);check(sha(s)==q['sha256'] and s.stat().st_size==q['bytes'],'frozen source '+q['target'])
 check(sha(R/q['target'])==q['sha256'],'installed target '+q['target'])
check(sha(R/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake-166-write-inputs.json')==sha(B/'write-inputs.json'),'76th exact provenance manifest')
links=[]
for q in p['files']:
 if q['source'] not in [str(B/'write-v2'/n) for n in ['intake-166.md','intake-166-reproduction.md','source70-dossier.md','candidate-README.md']]:continue
 for target in re.findall(r'\]\(([^)]+)\)',Path(q['source']).read_text()):
  if '://' in target or target.startswith('#'):continue
  path=(R/q['target']).parent/target.split('#')[0];check(path.exists(),'current local link '+str(path));links.append(str(path.resolve()))
# Read and parse only, never import the publication helper.
helper=B/'write_166.py';tree=ast.parse(helper.read_text())
check(not any(isinstance(n,(ast.Import,ast.ImportFrom)) and (getattr(n,'module','') or '').startswith('subprocess') for n in ast.walk(tree)),'helper no subprocess import')
# Existing replay records: distinct portable/full/retained-local scope.
e=load('/tmp/zfc244-root-replays/full-runtime/execution.json');v=load('/tmp/zfc244-root-replays/full-runtime/verification.json')
check(e['returncode']==0 and not e['timed_out'] and e['semantic_postchecks']=='PASS','full runtime terminal')
check(v['counts']==dict(cases=8391,symbolic_rules=2315075) and len(v['rows'])==488 and v['minimum_steps']==13,'full census')
l=load('/tmp/zfc244-root-replays/retained-local/execution.json');check(l['status']=='PASS_RETAINED_LOCAL_EVIDENCE' and len(l['records'])==4 and all(x['returncode']==0 and not x['timed_out'] for x in l['records']),'four retained local commands')
for x in l['records']:check(Path(x['stdout']).exists() and Path(x['stderr']).read_bytes()==b'','retained streams '+x['name'])
copy=Path('/tmp/zfc244-root-replays/retained-local/package/runtime');delivery=Path('/tmp/zfc244-248bc05936-inspection/zfc244-compensated-routing-20261018/runtime')
for new,old in l['outputs_equal_delivered_records']:check((copy/new).read_bytes()==(delivery/old).read_bytes(),'retained output exact '+new)
r=dict(status='SOURCE70_WRITE_FIDELITY_AND_INSTALLED_BYTES_REVIEW_PASS',findings=[],reviewer_source=d(__file__),write_inputs=d(B/'write-inputs.json'),writer_source=d(helper),authored_documents=[d(B/'write-v2'/n) for n in ['intake-166.md','intake-166-reproduction.md','source70-dossier.md','candidate-README.md','host-README.md']],ordinary_review=d('/tmp/zfc244-ordinary-proof-review/review.json'),portable_review=d('/tmp/zfc244-ordinary-proof-review/portable-evidence-review.json'),full_runtime_review=d('/tmp/zfc244-ordinary-proof-review/full-runtime-evidence-review.json'),reviewer_role='Independent ordinary/source and root-evidence reviewer, now reviewing authored reconciliation/writer and installed bytes; no intake writer, supplied checker, compiler or builder execution.',counts=dict(mapped_inputs=75,total_installed_with_input_manifest=76,placed_ancillaries=170,archive_only=21,delivery_members=191,local_links=len(links)),content_review=['Read all four new principal documents and the host README insertion; previous historical host sections are outside this new-content review.','Exact four-row compensated deletion, all-function-tape ordinary theorem from old95, finite-support Lean boundary, seven whole-tape blocks, completed aligned clock bounds and inherited calibration retained.','Portable smoke1 vs separate complete8391 replay vs retained-local repeat kept distinct. Discovery/supplemental variants not mislabeled fresh principal proofs.','Equational completeness remains conditional on cited Boolean basis/inherited calibration, with artificial demo and unimplemented binary control stated; no new state bound.','Frozen documents describe the intake checkpoint before the separate whole244 Lean endpoint. Later proof artifacts must update public status separately rather than silently rewrite this historical scope.','Writer reads pinned inputs, checks170 existing placements/base article, allows only explicit host README replacement, emits76 files to a fresh external directory and rechecks all input hashes. No executable verification is invoked.'],supplied_execution=False,checks=checks,check_count=len(checks))
out=B/'independent-write-fidelity-review.json';out.write_text(json.dumps(r,indent=2)+'\n');print(d(out))
