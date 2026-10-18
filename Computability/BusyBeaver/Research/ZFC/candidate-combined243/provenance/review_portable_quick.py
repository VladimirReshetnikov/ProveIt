#!/usr/bin/env python3
"""Read/hash the existing root replay only. Does not execute any replay code."""
from pathlib import Path
import hashlib,json
B=Path('/tmp/zfc243-portable-reproduction');P=Path('/tmp/combined243-portable-quick/verification.json')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
desc=lambda p:dict(path=str(p),sha256=sha(p))
assert sha(P)=='450b804a5a3d36d9ee0e1c98d1e72aad5dc1a4f2d8da618148e72edfba1d91a6'
r=json.loads(P.read_text());assert r['status']=='PASS_COMBINED243_QUICK_REPRODUCTION'
assert r['expanded_requested']is False and r['before']==r['after'] and r['all_input_postchecks']
assert r['proof_compiler_executed']is False and r['delivery_manifest_wrapper_executed']is False and r['delivery_checksum_manifests_verified']is False
for p,h in r['before'].items():assert sha(p)==h
assert [c['label']for c in r['commands']]==['blank','affine','literal']
for c in r['commands']:
 assert c['exit_code']==0 and c['timed_out']is False and c['interrupted']is None and c['timeout_seconds']==120 and c['seconds']<120
 assert c['command'][1:3]==['-I','-B']
 for k in ('stdout','stderr'):assert sha(c[k]['path'])==c[k]['sha256']
 assert Path(c['stderr']['path']).read_text()==''
for q in r['results'].values():assert sha(q['path'])==q['sha256']
blank=json.loads(Path(r['results']['blank']['path']).read_text());affine=json.loads(Path(r['results']['affine']['path']).read_text());literal=json.loads(Path(r['results']['literal']['path']).read_text())
assert r['blank_steps']==blank['blank_steps']==407967 and r['literal_steps']==literal['literal_steps']==6473394 and r['cases']==8390
assert blank['working_states']==243 and blank['transitions']==486 and blank['head']==-5 and blank['one_count']==351
assert blank['sparse_dense_exact_agreement_both_numberings'] and blank['all_other_cells_zero']
assert affine['status']=='PASS_UNIVERSAL_AFFINE_RUNTIME' and affine['complete'] and affine['counts']['cases']==8390 and len(affine['cases'])==8390
assert literal['status']=='PASS_FINITE_LITERAL_REGRESSION' and literal['cases']==8390 and literal['whole_tape_endpoints_checked']
assert 'expanded' not in r['results']
for p,h in r['before'].items():assert sha(p)==h
receipt=dict(status='EXISTING_QUICK_REPRODUCTION_METADATA_REVIEW_PASS',reviewer_role='Author of the reproduction helper and candidate adapters; this is a packaging/raw-evidence review, not an independent semantic proof.',reviewer_source=desc(Path(__file__)),verification=desc(P),checked_input_count=len(r['before']),commands=r['commands'],results=r['results'],blank_steps=407967,cases=8390,literal_steps=6473394,expanded_replayed=False,scope='Fresh external input-copy/default-path reproduction of blank/affine/finite literal checks. Previous expanded result is separate. No source-loop theorem, Lean endpoint or PA claim.',findings=[])
(B/'actual-quick-review.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(desc(B/'actual-quick-review.json')))
