"""Prospective reader-interface controls; no phase7 capture or compiler."""
from pathlib import Path
import copy,io,json,tarfile
import basis_reference
import evidence as e
from review_saved import read_members
P=Path(__file__).resolve().parent;R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
rows=[]
def check(name,fun,reject=False):
    try:fun()
    except (AssertionError,KeyError):assert reject,name
    else:assert not reject,name
    rows.append({'name':name,'expected':'reject'if reject else'accept','status':'PASS'})
# Validate only the already published predecessor; no current run is collected.
prior,_,_=basis_reference.validate(R)
check('pinned_predecessor_complete187',lambda: (_ for _ in ()).throw(AssertionError()) if json.loads(prior['execution/result.json'])['primary_project_modules']!=187 else None)
ctx=(P/'context.json').read_bytes();c=json.loads(ctx)
members={'review/context.json':ctx,**{r['member']:Path(r['path']).read_bytes()for r in c['files']}}
inv=json.loads(prior['execution/inventory.json']);new=copy.deepcopy(inv)
next(r for r in new['modules']if r['module']==e.DOM)['source_sha256']=e.SOURCE_SHA256
scope={'changed_sources':[e.DOM],'potentially_affected_modules':sorted(e.AFFECTED)}
owner={'script_sha256':e.DRIVER_SHA256,'source_change_scope':scope,'producer_sha256':e.PRODUCER_SHA256}
members['execution/result.json']=json.dumps({'source_change_scope':scope,'producer_sha256':e.PRODUCER_SHA256}).encode()
members['execution/sources/BusyBeaver/ZFC/DomRho8.lean']=members['context/pointwise/DomRho8.lean']
members['execution/generate_domrho8_lean.py']=members['context/pointwise/generate_domrho8_lean.py']
check('exact_isolated_provenance_and_two_source_bindings',lambda:e.validate_context(members,new,inv,owner,None))
for path in ['context/pointwise/DomRho8.lean','context/pointwise/generate_domrho8_lean.py','context/math-peer/review.json','context/driver-peer/review.json','context/pointwise/run1/compiler.log','context/pointwise/generation/result.json']:
    def bad(path=path):
        m=dict(members);m[path]+=b' ';e.validate_context(m,new,inv,owner,None)
    check('changed_'+path,bad,True)
def changed_inventory(which):
    n=copy.deepcopy(new)
    if which=='extra_source':n['modules'][0]['source_sha256']='0'*64
    else:n['modules'][0]['imports'].append('Init.Nat')
    e.validate_context(members,n,inv,owner,None)
check('extra_primary_source_change',lambda:changed_inventory('extra_source'),True)
check('changed_import',lambda:changed_inventory('import'),True)
log=prior['execution/audit-001/EndpointAudit215.log'].decode()
check('exact_two_named_reports',lambda:e.named_reports(log,'EndpointAudit215'))
check('renamed_report',lambda:e.named_reports(log.replace('EndpointAudit215.','Other.'),'EndpointAudit215'),True)
check('new_axiom',lambda:e.named_reports(log.replace('propext','sorryAx'),'EndpointAudit215'),True)
# Tiny synthetic archives test the newly shared object/regular-member interface.
def archive_case(name,kind='file'):
    stream=io.BytesIO();data=b'control'
    with tarfile.open(fileobj=stream,mode='w:gz')as t:
        info=tarfile.TarInfo(name);info.size=len(data)
        if kind=='symlink':info.type=tarfile.SYMTYPE;info.linkname='elsewhere';info.size=0
        t.addfile(info,io.BytesIO(data)if kind=='file'else None)
    stream.seek(0)
    return read_members(stream,{name:{'sha256':e.digest(data),'bytes':len(data)}})
check('regular_text_archive',lambda:archive_case('record.json'))
for name,kind in [('proof.olean.private','file'),('proof.olean.server','file'),('module.pyo','file'),('../escape','file'),('alias','symlink')]:
    check('reject_archive_'+name,lambda name=name,kind=kind:archive_case(name,kind),True)
result={'status':'PASS_PROSPECTIVE_READER_CONTROLS','positive':sum(r['expected']=='accept'for r in rows),'negative':sum(r['expected']=='reject'for r in rows),'cases':rows,'scope':'Published phase6 saved validation and pointwise provenance only; synthetic mutations of context/import/report/archive interfaces. No phase7 capture, live-provider audit, compiler or candidate execution.'}
e.save(P/'controls-result.json',result);print(json.dumps({k:v for k,v in result.items()if k!='cases'},indent=2))
