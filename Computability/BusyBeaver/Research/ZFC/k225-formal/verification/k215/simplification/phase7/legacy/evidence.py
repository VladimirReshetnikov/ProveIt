"""Read-only phase7 legacy evidence gates. Never execute archived code."""
from pathlib import Path,PurePosixPath
import hashlib,json,re,tarfile
EXTRA={'BusyBeaver.ZFC.'+n for n in ('Enum222','L2Axioms222','L2Root222','Seed222','Dag219Equiv','L2Lib219','L2Macros219','L2Control219','L2Axioms219','L2Root219','L2Dom','EnumDom','L2AxiomsDom','L2RootDom','RMOffsetBisim')}
CLIENTS=['SetTheory.BusyBeaver.ZFC.LegacyAudit.'+n for n in ('root222','root219','rootDom','rootPerm','offset_checker')]
SUPERVISOR='a3cf7cc38004bca5e2a2df10c607fe5353896c0454069b4ff24d6b5176c32fbd'
BINARY={'.olean','.ilean','.vo','.vos','.vok','.pyc','.pyo','.o','.so','.a','.glob'}
def digest(b):return hashlib.sha256(b).hexdigest()
def sha(p):return digest(Path(p).read_bytes())
def read(p):return json.loads(Path(p).read_text())
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
def safe(n):
 p=PurePosixPath(n)
 return bool(n)and not p.is_absolute()and'..'not in p.parts and'\\'not in n and not any(s in BINARY for s in p.suffixes)
def manifest(m):return {n:{'sha256':digest(b),'bytes':len(b)}for n,b in sorted(m.items())}
def manifest_hash(m):return digest((json.dumps(manifest(m),sort_keys=True,separators=(',',':'))+'\n').encode())
def members(archive,index):
 out={}
 with tarfile.open(archive,'r:gz')as t:
  for e in t:
   assert e.isfile()and safe(e.name)and e.name not in out
   b=t.extractfile(e).read();assert index[e.name]=={'sha256':digest(b),'bytes':len(b)};out[e.name]=b
 assert set(out)==set(index);return out

def reference(repo,ref):
 rel=ref['repository_relative_directory'];assert safe(rel)
 p=repo/rel
 for n,h in ref['files'].items():
  assert safe(n)and (p/n).stat().st_size==h['bytes']and sha(p/n)==h['sha256']
 return members(p/'execution.tar.gz',read(p/'index.json'))

def reports(text):
 assert not any(v in text for v in ['warning:','error:','sorryAx',"declaration uses 'sorry'"])
 rs=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",text)
 assert [n for n,_ in rs]==CLIENTS
 assert all({a.strip()for a in v.split(',')if a.strip()}<={'propext','Classical.choice','Quot.sound'}for _,v in rs)
 return [list(x)for x in rs]

def validate(m,basis_repo,current_repo=None):
 J=lambda n:json.loads(m[n]);result=J('execution/result.json');inv=J('execution/inventory.json');done=J('execution/completed.json')
 pd=J('execution/primary-completed.json');ld=J('execution/legacy-completed.json');pr=J('execution/primary-result.json');lr=J('execution/legacy-result.json');before=J('execution/before.json');tool=J('execution/toolchain.json');owner=J('execution/owner.json');providers=J('execution/providers.json');prep=J('preparation/prepared-inventory.json')
 refs=J('publication/references.json');pm=reference(basis_repo,refs['phase7_primary']);lm=reference(basis_repo,refs['phase5_legacy'])
 # One referenced phase6 archive supplies raw logs reused by phase7; never copy/replay it.
 p6ref=json.loads(pm['review/basis-reference.json']);p6=reference(basis_repo,p6ref)
 assert m['execution/primary-result.json']==pm['execution/result.json']and m['execution/primary-completed.json']==pm['execution/completed.json']
 assert m['execution/legacy-result.json']==lm['execution/result.json']and m['execution/legacy-completed.json']==lm['execution/completed.json']
 pi=json.loads(pm['execution/inventory.json']);li=json.loads(lm['execution/inventory.json'])
 assert pr['status']==lr['status']==result['status']=='PASS'
 assert (pr['primary_project_modules'],pr['typed_audits'],pr['axiom_reports'])==(187,2,10)
 assert (result['primary_project_modules'],result['legacy_only_modules'],result['project_modules'],result['fresh_legacy_modules'],result['reused_legacy_modules'])==(187,15,202,0,15)
 assert result['fresh_modules']==[]and set(result['reused_modules'])==EXTRA
 assert result['new_legacy_audit_executed']and result['all202_selected_objects_sources_dependencies_logs_rechecked_after_audit']and result['immutable_basis_inputs_rechecked_after_audit']
 assert result['primary_result_sha256']==digest(m['execution/primary-result.json'])and result['legacy_result_sha256']==digest(m['execution/legacy-result.json'])
 assert result['inventory_sha256']==digest(m['execution/inventory.json'])and result['completed_sha256']==digest(m['execution/completed.json'])
 assert inv==prep['union']and pi==prep['primary']
 rows={r['module']:r for r in inv['modules']};prows={r['module']:r for r in pi['modules']};lrows={r['module']:r for r in li['modules']}
 assert len(rows)==len(inv['modules'])==202 and len(prows)==187 and set(rows)-set(prows)==EXTRA
 assert set(done)==set(rows)and set(pd)==set(prows)and set(providers)==set(rows)
 assert inv['external_imports']==pi['external_imports']==['Init']
 assert inv['modules']==pi['modules']+[r for r in li['modules']if r['module']in EXTRA]
 assert not any(n.startswith('execution/attempts/')for n in m)
 seen=set();origins=json.loads(pm['execution/reused-log-origins.json'])
 for row in inv['modules']:
  mod=row['module'];rec=done[mod];assert set(row['imports'])<=seen|{'Init'};seen.add(mod)
  assert rec['status']=='PASS'and rec.get('exit_code',0)==0 and not rec.get('timed_out',False)
  assert rec['source_sha256']==row['source_sha256']==before[row['source']]
  assert rec['dependencies']=={d:done[d]['object_sha256']for d in row['imports']if d in done}
  assert re.fullmatch('[0-9a-f]{64}',rec['object_sha256'])
  if mod in prows:
   assert rec=={**pd[mod],'origin':'phase7_primary_hash_bound'}
   src=pm['execution/sources/'+mod.replace('.','/')+'.lean']
   if mod in origins:
    origin=origins[mod];log=p6[origin['basis_member']];assert digest(log)==origin['sha256']
   else:log=pm['execution/logs/'+mod+'.log']
   assert providers[mod]==str(Path(owner['primary'])/'objects'/(mod.replace('.','/')+'.olean'))
  else:
   assert row==lrows[mod]and rec=={**ld[mod],'origin':'phase5_legacy_hash_bound'}
   found=[(n,json.loads(b))for n,b in lm.items()if n.startswith('execution/attempts/')and n.endswith('/record.json')and json.loads(b)['module']==mod]
   assert len(found)==1;n,record=found[0];assert record==ld[mod];folder=n.rsplit('/',1)[0]
   src=lm[folder+'/'+Path(row['source']).name];log=lm[folder+'/compiler.log']
   assert providers[mod]==str(Path(owner['legacy'])/'objects'/(mod.replace('.','/')+'.olean'))
  assert digest(src)==row['source_sha256']and digest(log)==rec['log_sha256']
  imports=[x for line in src.decode().splitlines()if line.startswith('import ')for x in line[7:].split()]
  assert imports==row['imports']
  if current_repo is not None:
   # Resolve source relative to the recorded repository, not historical absolute paths.
   roots=[current_repo/root/(mod.replace('.','/')+'.lean')for root in ['Computability/BusyBeaver/Lean','Logic/FirstOrder/Lean','SetTheory/ZF/Lean','SetTheory/BoundedConsistency/Lean']]
   found=[p for p in roots if p.is_file()];assert len(found)==1 and sha(found[0])==row['source_sha256']
 audit=J('execution/audit/record.json');assert audit==result['audit']and audit['status']=='PASS'
 src=m['execution/audit/LegacyAudit.lean'];log=m['execution/audit/compiler.log']
 assert src==m['preparation/LegacyAudit.lean']==lm['execution/audit/LegacyAudit.lean']
 assert digest(src)==audit['source_sha256']and digest(log)==audit['log_sha256']
 assert audit['reports']==reports(log.decode())and audit['warnings']==0 and audit['exit_code']==0 and not audit['timed_out']
 assert audit['expected_axiom_reports']==5 and audit['timeout_seconds']==120 and audit['memory_mebibytes']==12288
 assert audit['dependencies']=={mod:r['object_sha256']for mod,r in done.items()}
 assert audit['compiler_sha256']==tool['lean']['sha256']
 ad=Path(audit['log']).parent;run=ad.parent
 assert audit['source']==str(ad/'LegacyAudit.lean')and audit['log']==str(ad/'compiler.log')
 assert audit['command']==[tool['lean']['path'],'-j1','-M12288','--root='+str(ad),'-o',str(ad/'LegacyAudit.olean'),str(ad/'LegacyAudit.lean')]
 assert tool==json.loads(pm['execution/toolchain.json'])==json.loads(lm['execution/toolchain.json'])
 freeze=J('preparation/freeze.json')
 for n,h in freeze['driver_inputs'].items():assert digest(m['preparation/'+n])==h
 assert digest(m['execution/build.py'])==owner['driver_sha256']==digest(m['preparation/build.py'])
 assert digest(m['execution/gates.py'])==owner['gates_sha256']==digest(m['preparation/gates.py'])
 assert digest(m['execution/supervisor.py'])==owner['helper_sha256']==SUPERVISOR
 for n in freeze['driver_inputs']:assert before[str(run.parent/n)]==digest(m['preparation/'+n])
 for n in freeze['control_files']:assert digest(m['preparation/'+n])==freeze['control_files'][n]
 review=J('execution/primary-review.json');assert review['status']=='PASS_ROOT_READ_ONLY_BINDINGS'and review['result_sha256']==digest(m['execution/primary-result.json'])
 reach=set()
 def visit(mod):
  if mod=='Init'or mod in reach:return
  reach.add(mod)
  for d in rows[mod]['imports']:visit(d)
 for line in src.decode().splitlines():
  if line.startswith('import '):
   for mod in line[7:].split():visit(mod)
 assert len(reach)==45 and result['audit_transitive_project_providers']=={mod:done[mod]['object_sha256']for mod in sorted(reach)}
 changed=[mod for mod in sorted(reach)if done[mod]['object_sha256']!=ld[mod]['object_sha256']]
 assert changed==['BusyBeaver.ZFC.DomRho8']
 return {'status':'PASS_SAVED_LEGACY_BINDINGS','primary_modules':187,'legacy_modules':15,'union_modules':202,'fresh_legacy_modules':0,'reused_legacy_modules':15,'fresh_audit_modules':1,'typed_clients':5,'axiom_reports':5,'audit_warnings':0,'audit_transitive_project_modules':45,'changed_historical_audit_objects':changed,'scope':'Saved incremental provider/source/import/log records and exact fresh five-client audit; referenced primary/phase5/phase6 archives read as data only. No compiler or live-object claim.'}
