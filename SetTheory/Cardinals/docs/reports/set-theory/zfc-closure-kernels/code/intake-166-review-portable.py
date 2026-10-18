#!/usr/bin/env python3
"""Read-only existing portable-run evidence review; never invokes supplied code."""
from pathlib import Path
import hashlib,json
P=Path('/tmp/zfc244-248bc05936-inspection/zfc244-compensated-routing-20261018')
B=Path('/tmp/zfc244-root-replays/portable')
OUT=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def desc(p):return {'path':str(p),'sha256':sha(p)}
def load(p):return json.loads(p.read_text())
e=load(B/'execution.json');v=load(B/'verification.json')
assert e['returncode']==0 and not e['timed_out'] and e['semantic_postchecks']=='PASS'
assert e['result_sha256']==sha(B/'verification.json')
assert e['command'][1:]==['-B','verify.py','--output',str(B/'verification.json')]
assert e['mode']=='portable' and e['process_group_limit_seconds']==180
assert not (B/'package/SHA256SUMS').exists()
pairs=[]
for p in sorted(P.rglob('*')):
    if not p.is_file() or p.name=='SHA256SUMS':continue
    q=B/'package'/p.relative_to(P)
    assert p.read_bytes()==q.read_bytes(), str(p)
    pairs.append({'original':desc(p),'executed_copy':desc(q)})
assert len(pairs)==190
assert v['status']=='PASS_PORTABLE_244_CONSTRUCTION'
for k,n in {'working_states':244,'binary_rows':488,'ordinary_checkpoint_rows':482,'exceptional_local_cases':7,'invariant_boolean_implications':7784,'blank_steps':407951,'archived_guarded_cases':8391,'archived_covered_rows':488,'runtime_dependency_smoke_cases':1}.items():assert v[k]==n
assert not v['full_runtime_replayed_in_this_invocation'] and not v['proof_assistant_endpoint_for_244_claimed']
log=(B/'stdout.log').read_text();lines=[x for x in log.splitlines() if x.startswith('PASS ')]
assert lines==['PASS rebuild_candidates.py','PASS prove_contextual_fold.py','PASS verify_local_stuttering.py','PASS check_new_boot.py','PASS '+str(B/'package/runtime/code/full_symbolic_parametric.py'),'PASS verify_backend.py','PASS equational_search.py']
assert json.loads(log[log.index('{'):])==v and (B/'stderr.log').read_bytes()==b''
result={'status':'EXISTING_PORTABLE_REPLAY_EVIDENCE_REVIEW_PASS','findings':[],
 'reviewer_role':'Independent ordinary-proof/source reviewer additionally reviewing root-executed evidence; no supplied execution by reviewer.',
 'reviewer_source':desc(Path(__file__)), 'execution':desc(B/'execution.json'),'verification':desc(B/'verification.json'),
 'stdout':desc(B/'stdout.log'),'stderr':desc(B/'stderr.log'),'root_launcher_source_read':desc(B.parent/'run_replays.py'),
 'portable_driver_source_read':desc(P/'verify.py'),'unchanged_delivery_byte_pairs':pairs,
 'summary':{'root_wall_seconds':e['wall_seconds'],'child_checks_reported':7,'ordinary_rows':482,'local_cases':7,'boolean_implications':7784,'sparse_dense_boot_steps':407951,'full_runtime_fresh':False,'full_runtime_archived_cases':8391,'fresh_symbolic_smoke_cases':1},
 'scope':['The default driver checks the exact rebuilt three variants, regenerated local proof records and sparse/dense boot against archived records, archived runtime input identities, one fresh symbolic case, and equational/backend artificial-demo checks.',
 'Child output bodies and temporary replay products are not retained separately by this driver. The raw parent log reports seven successful subprocesses; the read driver requires byte/JSON identity at its relevant gates. This receipt does not invent separate child execution records.',
 'The entire190-file delivered content excluding SHA256SUMS remains byte-identical in the executed disposable package. The omitted manifest alone is the authorized intake adaptation; no checksum-manifest loop was executed.',
 'The separate full8391 invocation and any proof-assistant endpoint are outside this receipt. No new audit/compiler execution was performed by this reviewer.']}
(OUT/'portable-evidence-review.json').write_text(json.dumps(result,indent=2)+'\n')
print(desc(OUT/'portable-evidence-review.json'))
