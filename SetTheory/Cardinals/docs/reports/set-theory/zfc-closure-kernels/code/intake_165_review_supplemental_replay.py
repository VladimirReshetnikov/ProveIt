"""Own existing-output comparison only; does not run or import delivery code."""
from pathlib import Path
import hashlib,json
W=Path('/tmp/zfc-intake-165-planning');E=Path('/tmp/zfc-intake-165-source69-supplemental-run1/execution.json');e=json.loads(E.read_text());p=json.loads((W/'execution-plan.json').read_text());i=json.loads((W/'inventory.json').read_text())['archives'][0];P=Path(i['extraction'])/i['roots'][0]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def d(p):return {'path':str(p),'sha256':sha(p)}
assert e['status']=='PASS' and len(e['records'])==8;out=[]
for r,j in zip(e['records'],p['commands'][1:]):
 assert r['key']==j['key'] and r['command']==j['argv'] and r['status']=='PASS' and r['exit_code']==0 and not r['timed_out'] and r['seconds']<r['timeout_seconds']==120
 C=Path(r['copy']);cwd=C/j['cwd_relative_to_copy'];assert cwd.resolve()==Path(r['cwd']).resolve();assert Path(r['stderr']).read_bytes()==b''
 # All executable input scripts are unchanged, including imported modules; changed outputs are separate evidence.
 scripts=[]
 for m in i['members']:
  rel=Path(m['archive_member']).relative_to(i['roots'][0]);src=P/rel;assert sha(src)==m['sha256'];dst=C/rel
  if src.suffix in ('.py','.v','.lean','.cpp'):
   assert sha(dst)==m['sha256'];scripts.append(str(rel))
 if j['postcheck']:
  for k,v in j['postcheck'].items():
   if k=='byte_equal_pairs':
    for x,y in v:assert (cwd/x).read_bytes()==(cwd/y).read_bytes()
   else:
    data=json.loads((C/k).read_text());assert all(data[q]==z for q,z in v.items())
 out.append({'key':r['key'],'seconds':r['seconds'],'unchanged_executable_members':len(scripts),'stdout':d(Path(r['stdout'])),'stderr':d(Path(r['stderr'])),'postchecks':r['postchecks']})
report={'status':'ROOT_SUPPLEMENTAL_REPLAY_EVIDENCE_REVIEW_PASS','findings':[],'execution':d(E),'plan':d(W/'execution-plan.json'),'jobs':out,'pristine_members_per_sweep':466,'checks_execution_status_only':False,'scope':'Eight actual root-run supplementary jobs, exact commands/cwd/status/raw logs/current executable identities and independent rebuilt table plus emitter JSON postchecks reviewed. Not a new supplied execution, checksum-manifest audit, search, proof compiler or general soundness theorem.','reviewer_source':d(Path(__file__))}
target=W/'source69-supplemental-replay-review.json';assert not target.exists();target.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(d(target)))
