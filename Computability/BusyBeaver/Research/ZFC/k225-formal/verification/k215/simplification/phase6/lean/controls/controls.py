"""Fifteen synthetic checks of new metadata interfaces; no phase6 capture/audit."""
from pathlib import Path
import io,json,tarfile,tempfile,hashlib
import basis_reference
from evidence import digest,manifest,named_reports,REPORT_NAMES
from review_saved import read_members
from review import check_providers

HERE=Path(__file__).resolve().parent
results=[]
def reject(name,fn):
    try:fn()
    except (AssertionError,KeyError,ValueError,FileNotFoundError):
        results.append({'name':name,'rejected':True})
    else:raise AssertionError('Accepted negative control: '+name)

def tar_case(path,items,index):
    with tarfile.open(path,'w:gz')as t:
        for name,data,kind in items:
            e=tarfile.TarInfo(name);e.size=len(data)
            if kind=='link':e.type=tarfile.SYMTYPE;e.linkname='elsewhere';e.size=0
            t.addfile(e,io.BytesIO(data)if kind=='file'else None)
    return read_members(path,index)

ref=basis_reference.reference()
results.append({'name':'exact pinned predecessor reference','accepted':True})
for label,key,value in [('changed reference location','repository_relative_directory','elsewhere'),('changed reference status','scope','changed')]:
    obj=dict(ref);obj[key]=value
    reject(label,lambda obj=obj:basis_reference.reference((json.dumps(obj)+'\n').encode()))
with tempfile.TemporaryDirectory(prefix='phase6-metadata-controls-')as tmp:
    tmp=Path(tmp);p=tmp/'tiny.tar.gz';data={'record.json':b'{}\n'};idx=manifest(data)
    assert tar_case(p,[('record.json',data['record.json'],'file')],idx)==data
    results.append({'name':'safe indexed text archive','accepted':True})
    cases=[('missing indexed member',[],idx),
           ('duplicate member',[('record.json',b'{}\n','file')]*2,idx),
           ('absolute member',[('/record.json',b'{}\n','file')],manifest({'/record.json':b'{}\n'})),
           ('parent traversal',[('../record.json',b'{}\n','file')],manifest({'../record.json':b'{}\n'})),
           ('archive symlink',[('record.json',b'','link')],manifest({'record.json':b''}))]
    for suffix in ['.olean.server','.olean.private','.pyo']:
        n='accidental'+suffix;cases.append(('compiled suffix '+suffix,[(n,b'bytes','file')],manifest({n:b'bytes'})))
    for label,items,index in cases:reject(label,lambda items=items,index=index:tar_case(p,items,index))
    client='EndpointAudit215';names=REPORT_NAMES[client]
    text=lambda ns:''.join("'"+n+"' depends on axioms: [propext]\n"for n in ns)
    assert len(named_reports(text(names),client))==2
    results.append({'name':'exact named typed reports','accepted':True})
    for label,bad in [('renamed theorem',[names[0]+'_other',names[1]]),('missing theorem',names[:1]),('reordered reports',names[::-1])]:
        reject(label,lambda bad=bad:named_reports(text(bad),client))
    parent,basis,run=[tmp/n for n in ['parent','basis','run']]
    rel=Path('BusyBeaver/ZFC/Toy.olean')
    for root in [parent,basis,run]:(root/'objects'/rel.parent).mkdir(parents=True)
    (parent/'objects'/rel).write_bytes(b'old');(basis/'objects'/rel).symlink_to(parent/'objects'/rel);(run/'objects'/rel).symlink_to(basis/'objects'/rel)
    old={'BusyBeaver.ZFC.Toy':{'origin':'phase4_hash_bound'}};done={'BusyBeaver.ZFC.Toy':{'origin':'phase5_hash_bound'}}
    check_providers(run,basis,done,old,parent);results.append({'name':'two-level immutable provider links','accepted':True})
    (run/'objects'/rel).unlink();(run/'objects'/rel).write_bytes(b'old')
    reject('reused current object is regular',lambda:check_providers(run,basis,done,old,parent))
    (run/'objects'/rel).unlink();(run/'objects'/rel).symlink_to(basis/'objects'/rel)
    other=tmp/'other.olean';other.write_bytes(b'old');(basis/'objects'/rel).unlink();(basis/'objects'/rel).symlink_to(other)
    reject('basis symlink has wrong provider',lambda:check_providers(run,basis,done,old,parent))
assert sum(x.get('rejected',False)for x in results)==15
out={'status':'PASS_SYNTHETIC_METADATA_CONTROLS','positive':4,'negative':15,'results':results,
     'sources':{n:digest((HERE/n).read_bytes())for n in ['basis_reference.py','evidence.py','review.py','review_saved.py','controls.py']},
     'proof_compiler_invoked':False,'phase6_execution_captured':False,'live_phase6_audit_executed':False}
p=HERE/'controls-result.json';assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
