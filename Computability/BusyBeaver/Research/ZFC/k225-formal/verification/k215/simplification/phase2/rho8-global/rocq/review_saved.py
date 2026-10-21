#!/usr/bin/env python3
"""Read-only saved-record audit; does not run a proof compiler or trust live objects."""
from pathlib import Path
import argparse, hashlib, json, tarfile

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--packet',type=Path,default=Path(__file__).resolve().parent)
parser.add_argument('--repo',type=Path)
parser.add_argument('--output',type=Path,required=True)
a=parser.parse_args();packet=a.packet.resolve();assert not a.output.exists()
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
summary=json.loads((packet/'result.json').read_text())
assert sha(packet/'execution.tar.gz')==summary['execution_archive_sha256']
index=json.loads((packet/'index.json').read_text());data={}
with tarfile.open(packet/'execution.tar.gz','r:gz') as tar:
 for member in tar.getmembers():
  assert member.isfile() and member.name in index and member.name not in data
  assert not Path(member.name).is_absolute() and '..' not in Path(member.name).parts
  assert not member.name.endswith(('.vo','.vos','.vok','.olean','.glob','.aux'))
  content=tar.extractfile(member).read();assert len(content)==index[member.name]['bytes']
  assert hashlib.sha256(content).hexdigest()==index[member.name]['sha256']
  data[member.name]=content
assert set(data)==set(index) and len(data)==summary['archive_members']
read=lambda name:json.loads(data[name])
plan=read('actual/plan.json');reuse=read('actual/reuse.json');actual=read('actual/result.json')
assert actual['status']=='PASS_INCREMENTAL_ENDPOINTS_FOCUSED_KERNEL'
assert len(plan['order'])==237 and set(plan['order'])==set(plan['modules'])
seen=set()
def visit(m):
 if m in seen:return
 seen.add(m)
 for d in plan['modules'][m]['dependencies']:visit(d)
visit('K215F.CorrectDense215');assert seen==set(plan['order'])
assert len(reuse)==230 and len(actual['recompiled'])==7
assert set(reuse).isdisjoint(actual['recompiled']) and set(reuse)|set(actual['recompiled'])==seen
records={m:read('actual/attempts/'+m+'/record.json') for m in actual['recompiled']}
objects={m:r['object_sha256'] for m,r in reuse.items()}|{m:r['object_sha256'] for m,r in records.items()}
closed=0
for m,r in records.items():
 assert r['status']=='PASS' and r['exit_code']==0 and r['post_inputs_unchanged'] and r['assumption_gate_passed']
 prefix='actual/attempts/'+m+'/'
 source=data[prefix+Path(r['source_snapshot']).name];log=data[prefix+'output.log']
 assert hashlib.sha256(source).hexdigest()==r['source_sha256']
 assert hashlib.sha256(log).hexdigest()==r['output_sha256']
 assert r['argv']==[r['argv'][0],*plan['flags'],'-w','-deprecated,-notation-overridden',plan['modules'][m]['target']]
 assert Path(r['argv'][0]).name=='coqc'
 expected={plan['modules'][m]['source']:r['source_sha256']}
 for d in plan['modules'][m]['dependencies']:
  expected[str(Path(plan['modules'][d]['target']).with_suffix('.vo'))]=objects[d]
 assert r['inputs']==expected
 text=log.decode();assert 'Axioms:' not in text
 if m in ['K215F.Correct215','K215F.CorrectDense215']:
  assert text.count('Closed under the global context')==2;closed+=2
assert closed==actual['endpoint_closed_reports']==summary['endpoint_closed_reports']==4
kernel=read('actual/kernel/record.json');log=data['actual/kernel/output.log']
assert kernel['exit_code']==0 and kernel['post_inputs_unchanged']
assert hashlib.sha256(log).hexdigest()==kernel['output_sha256']
assert kernel['argv']==[kernel['argv'][0],*plan['flags'],'-silent','-o','K215F.DomRho8']
assert Path(kernel['argv'][0]).name=='coqchk'
assert kernel['inputs']=={str(Path(plan['modules'][m]['target']).with_suffix('.vo')):objects[m] for m in seen}
assert '* Axioms: <none>' in log.decode()
for line in ['type-in-type: <none>','unsafe (co)fixpoints: <none>','positivity is assumed: <none>']:
 assert line in log.decode()
current=[]
if a.repo:
 formal=a.repo/'Computability/BusyBeaver/Research/ZFC/k225-formal'
 for m,r in records.items():
  path=formal/'rocq/rocq-extension/coq/215'/(m.split('.')[-1]+'.v')
  assert sha(path)==r['source_sha256'];current.append(str(path))
 for name,key in [('generate_domrho8_rocq_compact.py','renderer_sha256'),('rho8plan/plan.json','plan_sha256'),('rho8plan/replay.py','replay_sha256')]:
  assert sha(formal/name)==summary[key];current.append(str(formal/name))
result={'status':'PASS_SAVED_RECORD_AUDIT','archive_members':len(data),
 'recompiled':len(records),'reused':len(reuse),'endpoint_closed_reports':closed,
 'focused_recursive_kernel_target':'K215F.DomRho8','focused_context_axioms':[],
 'current_source_bindings':current,'compiled_objects_in_archive':False,
 'archive_sha256':summary['execution_archive_sha256'],'reviewer_sha256':sha(__file__),
 'scope':'Saved process/source/dependency/object-hash records and optional current maintained source bytes. No compiler run, no live object validation, no new full237 recursive endpoint replay.'}
a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
