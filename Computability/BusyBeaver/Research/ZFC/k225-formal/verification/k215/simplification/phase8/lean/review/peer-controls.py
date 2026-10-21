"""Independent pure metadata tests. No collect/validate/live/publish/compiler call."""
from pathlib import Path
import copy,hashlib,importlib.util,io,json,sys,tarfile,tempfile
sys.dont_write_bytecode=True
P=Path('/tmp/k215-proof-phase8-publication');O=Path(__file__).resolve().parent
sys.path.insert(0,str(P))
import evidence as e
from review_saved import read_members
records=[]
def check(name,f,reject=False):
 try:f()
 except (AssertionError,KeyError):assert reject,name
 else:assert not reject,name
 records.append({'name':name,'expected':'reject'if reject else'accept','status':'PASS'})
log='\n'.join("'%s' depends on axioms: [propext, Quot.sound]"%x for x in e.REPORT_NAMES['EndpointAudit215'])
check('qualified_two_report_gate',lambda:e.named_reports(log,'EndpointAudit215'))
check('wrong_namespace',lambda:e.named_reports(log.replace('EndpointAudit215.','Different.'),'EndpointAudit215'),True)
check('unapproved_axiom',lambda:e.named_reports(log.replace('Quot.sound','Untrusted'),'EndpointAudit215'),True)
check('extra_report',lambda:e.named_reports(log+"\n'extra' does not depend on any axioms",'EndpointAudit215'),True)
check('error_in_log',lambda:e.log_text((log+'\nerror: failure').encode()),True)
check('sorry_in_log',lambda:e.log_text((log+'\nsorryAx').encode()),True)
# Test virtual-reference expansion using a deliberately tiny data-only fixture.
m='M';logb=b'';rec={'log_sha256':e.digest(logb)}
prior={'execution/'+n+suffix:b'{}'for n,suffix in [('owner','.json'),('result','.json'),('completed','.json'),('inventory','.json'),('toolchain','.json'),('reviewed-driver','.py')]}
prior['execution/completed.json']=json.dumps({m:rec}).encode();prior['review/live-review.json']=b'{}';prior['execution/logs/'+m+'.log']=logb
members={'execution/completed.json':json.dumps({m:{'origin':'phase7_hash_bound'}}).encode(),'execution/reused-log-origins.json':json.dumps({m:{'basis_member':'execution/logs/M.log','sha256':e.digest(logb)}}).encode()}
check('virtual_reference_expansion',lambda:e.expand_references(members,prior))
for name in ['basis/result.json','basis/logs/M.log','execution/logs/M.log']:
 check('reject_duplicated_'+name,lambda name=name:e.expand_references({**members,name:b'x'},prior),True)
wrong={**members,'execution/reused-log-origins.json':json.dumps({m:{'basis_member':'execution/logs/M.log','sha256':'0'*64}}).encode()}
check('wrong_reused_log_pin',lambda:e.expand_references(wrong,prior),True)
# Archive member checks use only synthetic bytes and delete their temporary file.
def archive_case(name,duplicate=False):
 b=io.BytesIO();data=b'{}'
 with tarfile.open(fileobj=b,mode='w:gz')as t:
  for _ in range(2 if duplicate else 1):
   i=tarfile.TarInfo(name);i.size=len(data);t.addfile(i,io.BytesIO(data))
 with tempfile.NamedTemporaryFile(dir=O,suffix='.tar.gz')as f:
  f.write(b.getvalue());f.flush();return read_members(Path(f.name),{name:{'sha256':e.digest(data),'bytes':len(data)}})
check('regular_archive',lambda:archive_case('record.json'))
for name in ['proof.olean','proof.olean.private','proof.olean.server','module.ilean','cache.pyo','native.o','shared.so','static.a','rocq.vo','../escape','/absolute']:
 check('archive_'+name,lambda name=name:archive_case(name),True)
check('duplicate_archive_member',lambda:archive_case('record.json',True),True)
record={'status':'PASS_INDEPENDENT_PURE_METADATA_CONTROLS','positive':sum(r['expected']=='accept'for r in records),'negative':sum(r['expected']=='reject'for r in records),'cases':records,'evidence_sha256':e.sha(P/'evidence.py'),'saved_reader_sha256':e.sha(P/'review_saved.py'),'script_sha256':e.sha(Path(__file__)),'scope':'Only named report/log checks, in-memory synthetic reference expansion and tiny synthetic archive readers. No current run capture, basis validator, archived code, compiler or proof execution.'}
(O/'controls-result.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps({k:v for k,v in record.items()if k!='cases'},indent=2))
