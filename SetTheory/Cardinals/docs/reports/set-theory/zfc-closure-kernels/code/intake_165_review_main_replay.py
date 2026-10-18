"""Own static comparison of root's completed replay; no supplied code is imported."""
from pathlib import Path
import json,hashlib
W=Path('/tmp/zfc-intake-165-planning');B=Path('/tmp/zfc-intake-165-source69-main-run1');I=json.loads((W/'inventory.json').read_text());a=I['archives'][0];P=Path(a['extraction'])/a['roots'][0];C=B/'package'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def d(p):return {'path':str(p),'sha256':sha(p)}
e=json.loads((B/'execution.json').read_text());assert e['status']=='PASS' and e['exit_code']==0 and not e['timed_out'] and e['command']==['python3','-B','code/verify_all.py'] and e['seconds']<e['timeout_seconds']==180
assert json.loads((C/'results/verification-summary.json').read_text())==e['summary'];assert len(e['summary']['jobs'])==14 and all(x['status']=='PASS' for x in e['summary']['jobs']);assert not e['summary']['new_sub246_consistency_machine'] and not e['summary']['new_kernel_endpoint'];assert (B/'stderr.log').read_bytes()==b''
assert (B/'stdout.log').read_text().count('PASS ')==14 and 'ALL SUB246 RESEARCH CHECKS PASS' in (B/'stdout.log').read_text()
def strip(x):
 if isinstance(x,dict):return {k:strip(v) for k,v in x.items() if k not in ('seconds','time_seconds','elapsed_seconds')}
 if isinstance(x,list):return [strip(v) for v in x]
 return x
changed=[];semantic=[]
for m in a['members']:
 rel=Path(m['archive_member']).relative_to(a['roots'][0]);s=P/rel;c=C/rel;assert sha(s)==m['sha256'],('pristine changed',rel);assert c.exists()
 if sha(c)!=m['sha256']:
  assert str(rel).startswith('results/') or str(rel)=='code/source-exactroot-affine-verification.json',rel
  changed.append(str(rel))
  if rel.suffix=='.json':
   old=json.loads(s.read_text());new=json.loads(c.read_text());assert strip(old)==strip(new),('semantic difference',rel);semantic.append(str(rel))
assert sha(C/'code/verify_all.py')==sha(P/'code/verify_all.py')
newfiles=sorted(str(p.relative_to(C)) for p in C.rglob('*') if p.is_file() and not (P/p.relative_to(C)).exists());assert all(p.startswith('results/') for p in newfiles),newfiles
r={'status':'ROOT_MAIN_REPLAY_EVIDENCE_REVIEW_PASS','reviewer_role':'Source/manuscript/preflight reviewer and own metadata comparison author; did not execute the supplied suite.','execution':d(B/'execution.json'),'stdout':d(B/'stdout.log'),'stderr':d(B/'stderr.log'),'summary':d(C/'results/verification-summary.json'),'pristine_members_rehashed':466,'root_jobs':14,'seconds':e['seconds'],'changed_delivered_outputs':changed,'changed_json_equal_after_removing_duration_fields':semantic,'new_output_files':newfiles,'driver_unchanged':True,'scope':'Default functional checks pass; recorded_domain_identity compares six existing result domains and does not replay the searches. The eight supplemental commands remain pending. No new machine, formal endpoint, dependency build or PA proof.','findings':[],'reviewer_source':d(Path(__file__))}
out=W/'source69-main-replay-review.json';assert not out.exists();out.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(d(out)));print('changed',len(changed),'new',len(newfiles))
