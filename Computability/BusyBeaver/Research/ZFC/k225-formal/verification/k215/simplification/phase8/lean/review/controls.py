"""Prospective metadata-only reader controls; no current run capture or proof tools."""
from pathlib import Path
import copy,io,json,tarfile,tempfile
import basis_reference
import evidence as e
from review_saved import read_members
P=Path(__file__).resolve().parent;R=Path('/home/codex/.codex/worktrees/ec20/Proofs');D=Path('/tmp/k215-proof-phase8')
rows=[]
def check(name,fun,reject=False):
    try:fun()
    except (AssertionError,KeyError):assert reject,name
    else:assert not reject,name
    rows.append({'name':name,'expected':'reject'if reject else'accept','status':'PASS'})
prior,_,_=basis_reference.validate(R)
check('pinned_predecessor187_and_resolved_logs',lambda:None if len([m for m in prior if m.startswith('execution/logs/')])==187 else (_ for _ in ()).throw(AssertionError()))
ctx=(P/'context.json').read_bytes();c=json.loads(ctx)
members={'review/context.json':ctx,**{r['member']:Path(r['path']).read_bytes()for r in c['files']}}
old=json.loads(prior['execution/inventory.json']);new=json.loads((D/'prospective-inventory.json').read_bytes());registration=json.loads((D/'registered-adoption.json').read_bytes())
census=json.loads((D/'prospective-census.json').read_bytes());scope={k:census[k]for k in ('changed_sources','added_modules','unchanged_source_count','potentially_affected_modules','producer_pins')}
owner={'repo':str(R),'script_sha256':e.DRIVER_SHA256,'source_change_scope':scope,'producer_pins':scope['producer_pins'],'adoption_sha256':e.REGISTRATION_SHA256,'compiler_sha256':json.loads(prior['execution/owner.json'])['compiler_sha256'],'helper_sha256':json.loads(prior['execution/owner.json'])['helper_sha256']}
members['execution/result.json']=json.dumps({k:owner[k]for k in ('source_change_scope','producer_pins','adoption_sha256')}).encode()
members['execution/registered-adoption.json']=(D/'registered-adoption.json').read_bytes()
members['execution/toolchain.json']=prior['execution/toolchain.json']
for row in registration['files']:
 data=(R/row['destination']).read_bytes();members['execution/adopted-sources/'+row['destination']]=data
 if row['kind']=='lean':members['execution/sources/'+row['module'].replace('.','/')+'.lean']=data
check('nine_registered_files_and_isolated17_reports',lambda:e.validate_context(members,new,old,owner,None))
for path in ['context/implication/isolated-run2/DomApi.log','context/math-peer/review.json','context/seed-peer/review.json','context/driver-peer/review.json','context/raw-inputs/shortcuts.json','execution/registered-adoption.json','execution/adopted-sources/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DominatedImplication.lean','execution/adopted-sources/Computability/BusyBeaver/Research/ZFC/k225-formal/dominated_implication_templates/adapter.txt']:
 def bad(path=path):
  m=dict(members);m[path]+=b' ';e.validate_context(m,new,old,owner,None)
 check('changed_'+path,bad,True)
def changed_inventory(which):
 n=copy.deepcopy(new)
 if which=='extra_source':next(r for r in n['modules']if r['module']not in e.REGISTERED_MODULES)['source_sha256']='0'*64
 elif which=='remove_new':n['modules']=[r for r in n['modules']if r['module']!=e.NEW_MODULE]
 else:next(r for r in n['modules']if r['module']=='BusyBeaver.ZFC.KSeed222')['imports'].append('Init.Nat')
 e.validate_context(members,n,old,owner,None)
for which in ('extra_source','remove_new','seed_import'):check(which,lambda which=which:changed_inventory(which),True)
log=prior['execution/audit-001/EndpointAudit215.log'].decode()
check('exact_two_named_reports',lambda:e.named_reports(log,'EndpointAudit215'))
check('renamed_report',lambda:e.named_reports(log.replace('EndpointAudit215.','Other.'),'EndpointAudit215'),True)
check('new_axiom',lambda:e.named_reports(log.replace('propext','sorryAx'),'EndpointAudit215'),True)
def archive_case(name,kind='file'):
 stream=io.BytesIO();data=b'control'
 with tarfile.open(fileobj=stream,mode='w:gz')as t:
  info=tarfile.TarInfo(name);info.size=len(data)
  if kind=='symlink':info.type=tarfile.SYMTYPE;info.linkname='elsewhere';info.size=0
  t.addfile(info,io.BytesIO(data)if kind=='file'else None)
 with tempfile.NamedTemporaryFile(suffix='.tar.gz',dir=P) as archive:
  archive.write(stream.getvalue());archive.flush()
  return read_members(Path(archive.name),{name:{'sha256':e.digest(data),'bytes':len(data)}})
check('regular_text_archive',lambda:archive_case('record.json'))
for name,kind in [('proof.olean.private','file'),('proof.olean.server','file'),('module.pyo','file'),('../escape','file'),('alias','symlink')]:
 check('reject_archive_'+name,lambda name=name,kind=kind:archive_case(name,kind),True)
result={'status':'PASS_PROSPECTIVE_READER_CONTROLS','positive':sum(r['expected']=='accept'for r in rows),'negative':sum(r['expected']=='reject'for r in rows),'cases':rows,'scope':'Published phase7 saved evidence and source registration/isolated provenance only. Synthetic context/import/report/archive mutations. No current phase8 capture, live-provider audit, compiler or candidate execution.'}
e.save(P/'controls-result.json',result);print(json.dumps({k:v for k,v in result.items()if k!='cases'},indent=2))
