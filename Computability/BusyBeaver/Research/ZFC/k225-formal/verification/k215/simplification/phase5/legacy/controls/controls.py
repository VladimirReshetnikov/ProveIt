"""Synthetic metadata controls only. Never invokes Lean or creates objects."""
from pathlib import Path
import copy,hashlib,importlib.util,json
import evidence as E
P=Path(__file__).resolve().parent
pack={}
def put(n,x):pack[n]=(json.dumps(x,indent=2)+'\n').encode()
prep=E.read(P/'prepared-inventory.json');pi=prep['primary'];inv=prep['union'];old={};done={};before={};fresh=[]
for n in ('build.py','LegacyAudit.lean','prepared-inventory.json','prepared.json','driver-from-phase4.diff'):
 pack['preparation/'+n]=(P/n).read_bytes();before[str(P/n)]=E.digest(pack['preparation/'+n])
helper=Path('/home/codex/.codex/worktrees/ec20/Proofs/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/lean/build.py')
pack['execution/supervisor.py']=helper.read_bytes();before[str(helper)]=E.sha(helper)
put('execution/inventory.json',inv);put('basis/inventory.json',pi)
tool={'lean':{'path':'/synthetic/lean','sha256':'a'*64}};put('basis/toolchain.json',tool);put('execution/toolchain.json',tool)
primary={r['module']for r in pi['modules']};run=Path('/synthetic/run')
for r in inv['modules']:
 mod=r['module'];before[r['source']]=r['source_sha256'];deps={d:done[d]['object_sha256']for d in r['imports']if d in done}
 rec={'status':'PASS','source_sha256':r['source_sha256'],'dependencies':deps,'object_sha256':E.digest(mod.encode())}
 if mod in primary:old[mod]=rec;done[mod]={**rec,'origin':'phase5_primary_hash_bound'};continue
 i=len(fresh)+1;base=f'execution/attempts/{i:02d}-{mod}';fresh.append((mod,base))
 source=Path(r['source']).read_bytes();pack[base+'/'+Path(r['source']).name]=source;pack[base+'/compiler.log']=b''
 root=r['source'][:-len(mod.replace('.','/')+'.lean')].rstrip('/')
 rec.update(module=mod,origin='legacy_fresh',log=str(run/Path(base).relative_to('execution')/'compiler.log'),log_sha256=E.digest(b''),
  command=['/synthetic/lean','-j1','-M12288','--root='+root,'-o',str(run/'objects'/(mod.replace('.','/')+'.olean')),r['source']],compiler_sha256='a'*64,
  exit_code=0,timed_out=False,timeout_seconds=120,memory_mebibytes=12288,source_unchanged=True,dependencies_unchanged=True,warnings=0,seconds=1)
 put(base+'/record.json',rec);done[mod]=rec
put('execution/completed.json',done);put('execution/basis-completed.json',old);put('execution/before.json',before)
basis={'status':'PASS','primary_project_modules':184,'basis_unchanged':True,'all_private_objects_logs_and_toolchain_rechecked_after_audits':True,'typed_audits':2,'axiom_reports':10,'inventory_sha256':E.digest(pack['basis/inventory.json']),'completed_sha256':E.digest(pack['execution/basis-completed.json'])}
put('execution/basis-result.json',basis);put('execution/basis-review.json',{'status':'PASS_LIVE_POST_AUDIT_REVIEW','all184_objects_rehashed_after_audits':True,'result_sha256':E.digest(pack['execution/basis-result.json'])})
pack['execution/audit/LegacyAudit.lean']=pack['preparation/LegacyAudit.lean']
log=''.join(f"'{E.CLIENT_PREFIX}{c}' depends on axioms: [propext, Quot.sound]\n"for c in E.CLIENTS).encode();pack['execution/audit/compiler.log']=log
au={'status':'PASS','warnings':0,'exit_code':0,'timed_out':False,'expected_axiom_reports':5,'source_sha256':E.digest(pack['execution/audit/LegacyAudit.lean']),'log':str(run/'audit/compiler.log'),'log_sha256':E.digest(log),'dependencies':{m:r['object_sha256']for m,r in done.items()},'compiler_sha256':'a'*64,'timeout_seconds':120,'memory_mebibytes':12288,'command':['/synthetic/lean','-j1','-M12288','--root='+str(run/'audit'),'-o',str(run/'audit/LegacyAudit.olean'),str(run/'audit/LegacyAudit.lean')],'reports':['propext, Quot.sound']*5}
put('execution/audit/record.json',au)
res={'status':'PASS','project_modules':199,'reused_primary_modules':184,'fresh_legacy_modules':15,'basis_unchanged':True,'all_inputs_objects_logs_rechecked_after_audit':True,'inventory_sha256':E.digest(pack['execution/inventory.json']),'completed_sha256':E.digest(pack['execution/completed.json']),'audit':au};put('execution/result.json',res)
results=[]
E.validate(pack);results.append({'name':'consistent_synthetic199','pass':True,'kind':'positive'})
def test(name,mutate):
 m=copy.deepcopy(pack);mutate(m)
 try:E.validate(m)
 except(AssertionError,KeyError,ValueError):results.append({'name':name,'pass':True,'kind':'negative'});return
 raise AssertionError(('not rejected',name))
def change_json(m,p,f):
 x=json.loads(m[p]);f(x);m[p]=(json.dumps(x,indent=2)+'\n').encode()
def record_change(m,f):
 mod,base=fresh[0];r=json.loads(m[base+'/record.json']);f(r);m[base+'/record.json']=(json.dumps(r,indent=2)+'\n').encode()
 change_json(m,'execution/completed.json',lambda d:d.__setitem__(mod,r));change_json(m,'execution/result.json',lambda d:d.__setitem__('completed_sha256',E.digest(m['execution/completed.json'])))
def namespace_change(m):
 m['execution/audit/compiler.log']=log.replace(E.CLIENT_PREFIX.encode(),b'Unrelated.')
 change_json(m,'execution/audit/record.json',lambda a:a.__setitem__('log_sha256',E.digest(m['execution/audit/compiler.log'])))
 change_json(m,'execution/result.json',lambda r:r.__setitem__('audit',json.loads(m['execution/audit/record.json'])))
test('wrong_full_report_namespace',namespace_change)
test('arbitrary_fresh_output_root',lambda m:record_change(m,lambda r:r['command'].__setitem__(5,r['command'][5].replace('/synthetic/run','/other'))))
test('changed_runner_snapshot',lambda m:m.__setitem__('preparation/build.py',m['preparation/build.py']+b'\n'))
test('changed_client_snapshot',lambda m:m.__setitem__('preparation/LegacyAudit.lean',m['preparation/LegacyAudit.lean']+b'\n'))
test('changed_supervisor_snapshot',lambda m:m.__setitem__('execution/supervisor.py',b'other'))
test('changed_prepared_inventory',lambda m:m.__setitem__('preparation/prepared-inventory.json',m['preparation/prepared-inventory.json']+b'\n'))
test('changed_saved_log',lambda m:m.__setitem__(fresh[0][1]+'/compiler.log',b'changed'))
test('timed_out_module',lambda m:record_change(m,lambda r:r.__setitem__('timed_out',True)))
test('changed_source_snapshot',lambda m:m.__setitem__(fresh[0][1]+'/'+Path(inv['modules'][184]['source']).name,b'changed'))
test('wrong_extra_count',lambda m:change_json(m,'execution/result.json',lambda r:r.__setitem__('fresh_legacy_modules',14)))
for name in ['x.olean.server','x.olean.private','x.ilean','x.o','x.so','x.a','x.glob','../escape','/absolute']:
 assert not E.safe(name);results.append({'name':'reject_member_'+name,'pass':True,'kind':'negative'})
r={'status':'PASS_SYNTHETIC_METADATA_CONTROLS','no_compiler':True,'no_live_proof_evidence_claim':True,'positive':sum(x['kind']=='positive'for x in results),'negative':sum(x['kind']=='negative'for x in results),'controls':results,'evidence_sha256':E.sha(P/'evidence.py'),'script_sha256':E.sha(Path(__file__))}
E.save(P/'controls.json',r);print(json.dumps(r,indent=2))
