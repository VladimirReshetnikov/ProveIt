#!/usr/bin/env python3
"""Own existing evidence/hash comparison; never invokes supplied runtime code."""
from pathlib import Path
import hashlib,json
P=Path('/tmp/zfc244-248bc05936-inspection/zfc244-compensated-routing-20261018');B=Path('/tmp/zfc244-root-replays/full-runtime');O=Path(__file__).parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
d=lambda p:dict(path=str(p),sha256=sha(p));load=lambda p:json.loads(Path(p).read_text())
e=load(B/'execution.json');v=load(B/'verification.json');archive=P/'runtime/candidate_1_full_symbolic.json';a=load(archive)
assert e['returncode']==0 and not e['timed_out'] and e['semantic_postchecks']=='PASS' and e['process_group_limit_seconds']==600
assert e['result_sha256']==sha(B/'verification.json') and not e['proof_compiler_invoked']
assert e['command'][1:]==['-B','runtime/code/full_symbolic_parametric.py','--table','runtime/candidate_1_244_old.tm','--all-values','--sites','runtime/certificate/sites_physical.json','--output',str(B/'verification.json')]
assert {k:x for k,x in v.items() if k!='seconds'}=={k:x for k,x in a.items() if k!='seconds'}
assert v['status']=='PASS' and v['complete'] and v['positive_progress_checked']
assert v['expected_cases']==8391 and len(v['cases'])==8391 and len(v['rows'])==488 and v['minimum_steps']==13 and v['frame_padding']==64
assert v['counts']==dict(cases=8391,symbolic_rules=2315075) and v['invariant_closure_edges']==8384
pairs=[]
for p in sorted(P.rglob('*')):
 if p.is_file() and p.name!='SHA256SUMS':
  q=B/'package'/p.relative_to(P);assert p.read_bytes()==q.read_bytes();pairs.append(dict(original=d(p),executed_copy=d(q)))
assert len(pairs)==190 and not (B/'package/SHA256SUMS').exists()
for field,rel in [('source_sha256','runtime/reference/context246/sources/Prog254.v'),('table_sha256','runtime/candidate_1_244_old.tm'),('alternative_sites_sha256','runtime/certificate/sites_physical.json'),('invariant_sha256','runtime/results/interval-invariants.json')]:
 p=B/'package'/rel
 if not p.exists() and field=='invariant_sha256':
  matches=[z for z in (B/'package').rglob('*.json') if sha(z)==v[field]];assert len(matches)==1;p=matches[0]
 assert sha(p)==v[field],(field,p)
raw=(B/'stdout.log').read_text();summary,end=json.JSONDecoder().raw_decode(raw)
assert summary=={k:x for k,x in v.items() if k not in ['cases','rows']} and raw[end:].strip()=='rows 488'
assert (B/'stderr.log').read_bytes()==b''
r=dict(status='EXISTING_FULL_RUNTIME_REPLAY_EVIDENCE_REVIEW_PASS',findings=[],reviewer_source=d(__file__),reviewer_role='Independent ordinary mathematical/source review and root-executed evidence review; no supplied-code execution.',execution=d(B/'execution.json'),verification=d(B/'verification.json'),archived_verification=d(archive),stdout=d(B/'stdout.log'),stderr=d(B/'stderr.log'),unchanged_delivery_pairs=pairs,summary=dict(cases=8391,rows=488,symbolic_rules=2315075,closure_edges=8384,minimum_steps=13,frame_padding=64,root_wall_seconds=e['wall_seconds']),comparison='Every result field, case and row is identical to delivered principal all-values result except elapsed seconds.',scope=v['scope'],scope_limit='This is a fresh completed Python symbolic check of the principal table and its stated frame family, not a Lean or PA proof. Direct all-function-tape fold proof is reviewed separately. Only ignored SHA256SUMS was omitted in the disposable package.',supplied_execution=False)
p=O/'full-runtime-evidence-review.json';p.write_text(json.dumps(r,indent=2)+'\n');print(d(p))
