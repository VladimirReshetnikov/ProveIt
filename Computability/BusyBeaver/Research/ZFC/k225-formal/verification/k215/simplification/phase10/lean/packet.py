"""Validate compact phase10 records against the already checked phase9 packet."""
from pathlib import Path,PurePosixPath
import hashlib,json,re
import basis
HERE=Path(__file__).resolve().parent
RUN='/tmp/k215-phase10-main/full-run1'
ISO='/tmp/k215-generic-cd52-check/run1'
PREV='/tmp/k215-phase9-main/full-run2'
OLD='/tmp/k215-proof-phase8/lean-run1'
ROOT='/home/codex/.codex/worktrees/ec20/Proofs'
CORE='BusyBeaver.ZFC.DominatedImplication'
FRESH={'BusyBeaver.ZFC.'+m for m in ['DominatedImplication','DomRho8','KCodeDom','L2RootPerm','L2AxiomsPerm','SeedPerm','EnumPerm','KEndpoint215']}
ISO_FRESH={CORE,'BusyBeaver.ZFC.DomRho8','BusyBeaver.ZFC.KCodeDom','GenericCD52Api','NumericCD52Api'}
TARGETS=['BusyBeaver.ZFC.KEndpoint215','BusyBeaver.ZFC.KDecoderPrefix215']
AUDIT_NAMES={
 'EndpointAudit215':['EndpointAudit215.blank_halts_exactly_when_zfc_has_a_finite_refutation','EndpointAudit215.nonhalting_exactly_when_zfc_is_consistent'],
 'K215Audit':['SetTheory.BusyBeaver.ZFC.KEndpoint215.blank_halts_iff_zfc_refutation','SetTheory.BusyBeaver.ZFC.KEndpoint215.nonhalting_iff_zfc_consistency','SetTheory.BusyBeaver.ZFC.KDense215.commutes','SetTheory.BusyBeaver.ZFC.KBoot215.boot','SetTheory.BusyBeaver.ZFC.KSites215.covered','SetTheory.BusyBeaver.ZFC.KEndpoint215.p215_boot_iff','K215Audit.blank_halts_exact','K215Audit.nonhalting_exact']}
AUDIT_PINS={'EndpointAudit215':'d13596021774c5b26937b13cf6cca58342af99f59626b9205ff10b9df1e6fc7d','K215Audit':'9144acc6c597c4a53928fc62be00d5e25d9f32f519797d17a5058d03b5460986'}
NS='SetTheory.BusyBeaver.ZFC.'
ISO_REPORTS={CORE:[NS+'DominatedImplication.'+n for n in ['rho8_all','composition','lift_right']],
 'BusyBeaver.ZFC.DomRho8':[NS+'DomRho8.'+n for n in ['rho8_all','composition','lift_right','rho8_all_of_restricted']],
 'BusyBeaver.ZFC.KCodeDom':[NS+'KCodeDom.cdom_iff_c222'],
 'GenericCD52Api':['GenericCD52Api.'+n for n in ['unrestricted','composition','lifting','only_explicit_fields']],
 'NumericCD52Api':['NumericCD52Api.'+n for n in ['restricted_without_truth','unrestricted','composition','lifting','same_numeric_calculus']]}
BINARY={'.olean','.ilean','.o','.so','.a','.vo','.vos','.vok','.glob','.pyc','.pyo'}
def digest(data):return hashlib.sha256(data).hexdigest()
def sha(p):return digest(Path(p).read_bytes())
def dump(x):return(json.dumps(x,indent=2)+'\n').encode()
def safe(name):
 p=PurePosixPath(name);assert not p.is_absolute()and'..'not in p.parts and str(p)==name
 assert not set(p.suffixes)&BINARY and p.suffix not in{'.gz','.zip','.tar'}
def manifest(data):return{n:{'sha256':digest(b),'bytes':len(b)}for n,b in sorted(data.items())}
def validate(members,repo,basis_data=None,current_repo=None):
 for n in members:safe(n)
 prior,checked,h=basis.load(repo)if basis_data is None else basis_data
 assert members['review/basis-reference.json']==(HERE/'basis-reference.json').read_bytes()
 routes=json.loads(members['path-map.json']);resolved={}
 for path,r in routes.items():
  assert PurePosixPath(path).is_absolute()and set(r)=={'storage','key','sha256','bytes'}
  assert r['storage']in{'packet','phase9'};data=(members if r['storage']=='packet'else prior)[r['key']]
  assert digest(data)==r['sha256']and len(data)==r['bytes'];resolved[path]=data
 at=lambda p:resolved[str(p)];read=lambda p:json.loads(at(p))
 old_inv=json.loads(prior['member:execution/inventory.json']);old_rows={r['module']:r for r in old_inv['modules']};old=json.loads(prior['member:execution/completed.json'])
 assert len(old)==len(old_rows)==197
 old8=read(OLD+'/completed.json');old8rows={x['module']:x for x in read(OLD+'/inventory.json')['modules']}
 oldtool=read(OLD+'/toolchain.json');compiler=oldtool['lean']['path'];helper=ROOT+'/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/lean/build.py'
 binary={p['path']:p['sha256']for p in oldtool.values()if isinstance(p,dict)and'path'in p and'sha256'in p and(p['path'].endswith('.olean')or p['path'].endswith('/bin/lean')or p['path'].endswith('/bin/lake'))}
 for root,records in [(OLD,old8),(PREV,old)]:
  binary.update({root+'/objects/'+m.replace('.','/')+'.olean':r['object_sha256']for m,r in records.items()})
 def run_check(root,targets,fresh,count,iso=False):
  result=read(root+'/result.json');before=read(root+'/before.json');inv=read(root+'/inventory.json');done=read(root+'/completed.json');tool=read(root+'/toolchain.json')
  assert result['status']=='PASS'and result['selected_project_modules']==count
  assert result['targets']==inv['targets']==before['targets']==targets
  assert before['rows']==inv['modules']and before['external_imports']==inv['external_imports']==['Init']
  assert before['audit_endpoint']==(not iso)
  assert digest(at(root+'/inventory.json'))==result['inventory_sha256']and digest(at(root+'/completed.json'))==result['completed_sha256']
  assert tool==oldtool
  entries,closures=h.graph(inv['modules'],targets);assert len(entries)==len(done)==count and set(entries)==set(done)
  assert set(result['fresh_modules'])==fresh and not result['phase8_reused_modules']and set(result['isolated_reused_modules'])==set(entries)-fresh
  assert result['basis_reuse_rejects_transitive_source_changes']and result['isolated_reuse_requires_exact_transitive_sources_and_imports']
  changed={m for m,e in entries.items()if m not in old_rows or(e['source_sha256'],e['imports'])!=(old_rows[m]['source_sha256'],old_rows[m]['imports'])}
  forced={m for m in entries if closures[m]&changed};assert forced==fresh
  if not iso:assert changed=={CORE}and set(entries)==set(old_rows)
  changed8,forced8,_=h.source_scope(entries,closures,old8rows,old_rows)
  assert sorted(changed8)==before['changed_sources']==result['source_changed_modules']and sorted(forced8)==before['force_basis_rebuild']==result['force_basis_rebuild_modules']
  map_paths=[p for p,pin in before['inputs'].items()if pin==result['map_sha256']];assert len(map_paths)==1
  plan=read(map_paths[0]);plans={r['module']:r for r in plan['modules']};assert len(plans)==len(plan['modules'])
  assert plan['reuse_ledger']=={'directory':PREV,**{n:digest(prior['member:execution/'+n])for n in['result.json','inventory.json','completed.json']}}
  assert result['runner_sha256']==before['runner_sha256']=='287ad156c55681c2c00dabc524d799df4c43f342455c64805031591a8e81e37a'
  assert before['inputs']['/tmp/k215-phase9-main/build-v4.py']==result['runner_sha256']
  assert before['inputs'][helper]=='a3cf7cc38004bca5e2a2df10c607fe5353896c0454069b4ff24d6b5176c32fbd'
  objects={m:r['object_sha256']for m,r in done.items()};report_count=0;warnings=0
  for m,row in entries.items():
   rec=done[m];source=at(row['source']);log=at(rec['log']);text=log.decode();reports=h.reports(log)
   assert digest(source)==row['source_sha256']==rec['source_sha256']and h.imports(source)==row['imports']
   assert rec['dependencies']=={d:objects[d]for d in row['imports']if d!='Init'}
   assert rec['status']=='PASS'and rec.get('exit_code',0)==0 and not rec.get('timed_out',False)and digest(log)==rec['log_sha256']
   warnings+=text.count('warning:')
   if m in fresh:
    assert rec['origin']=='phase9_fresh'and rec['timeout_seconds']==120 and rec['memory_mebibytes']==12288
    assert rec['compiler_sha256']==oldtool['lean']['sha256']and rec['helper_sha256']==before['inputs'][helper]
    obj=root+'/objects/'+m.replace('.','/')+'.olean';src=root+'/workspace/'+m.replace('.','/')+'.lean'
    assert rec['command']==[compiler,'-j1','-M12288','--root='+root+'/workspace','-o',obj,src]
    assert digest(at(src))==row['source_sha256']and rec['source']==src
    assert rec['reports']==[list(x)for x in reports]and rec['warnings']==text.count('warning:')
    assert read(str(PurePosixPath(rec['log']).parent/'record.json'))==rec
    if iso:
     assert[n for n,_ in reports]==ISO_REPORTS[m]and not rec['warnings'];report_count+=len(reports)
     expected_axioms=set()if m in {CORE,'GenericCD52Api'}else {'propext','Quot.sound'}
     assert all({v.strip()for v in ax.split(',')if v.strip()}==expected_axioms for _,ax in reports)
   else:
    assert rec=={**old[m],'origin':'isolated_checked'}
    assert all((entries[d]['source_sha256'],entries[d]['imports'])==(old_rows[d]['source_sha256'],old_rows[d]['imports'])for d in closures[m])
   if m in plans and'reports'in plans[m]:assert[n for n,_ in reports]==plans[m]['reports']and'warning:'not in text
   if current_repo is not None and not iso:
    found=[Path(current_repo)/r/(m.replace('.','/')+'.lean')for r in h.ROOTS if(Path(current_repo)/r/(m.replace('.','/')+'.lean')).is_file()]
    assert len(found)==1 and sha(found[0])==row['source_sha256']
  for p,pin in before['inputs'].items():
   if p in binary:assert binary[p]==pin
   else:assert digest(at(p))==pin,p
  audits=result['audits'];assert [r['module']for r in audits]==([]if iso else list(AUDIT_NAMES))
  for rec in audits:
   m=rec['module'];q=root+'/audit-'+m;log=at(rec['log']);found=h.reports(log)
   assert rec['status']=='PASS'and rec['exit_code']==0 and not rec['timed_out']and'warning:'not in log.decode()
   assert[n for n,_ in found]==AUDIT_NAMES[m]and[list(x)for x in found]==rec['named_reports']
   assert digest(at(rec['source']))==digest(at(q+'/'+m+'.lean'))==rec['source_sha256']==AUDIT_PINS[m]
   assert digest(log)==rec['log_sha256']and rec['dependencies']==objects
   assert rec['command']==[compiler,'-j1','-M12288','--root='+q,'-o',q+'/'+m+'.olean',q+'/'+m+'.lean']
   assert rec['compiler_sha256']==oldtool['lean']['sha256']and rec['timeout_seconds']==120 and rec['memory_mebibytes']==12288
   assert read(q+'/'+m+'.json')==rec
  if iso:assert report_count==17
  return result,entries,closures,warnings
 result,entries,closures,warnings=run_check(RUN,TARGETS,FRESH,197)
 isolated,_,_,iso_warnings=run_check(ISO,['GenericCD52Api','NumericCD52Api'],ISO_FRESH,16,True)
 sites=sorted(m for m in entries if m.startswith('BusyBeaver.ZFC.KSites215Batch'));assert len(sites)==9
 before_files=read('/tmp/k215-phase10-main/producer-before.json')['files'];assert len(before_files)==5
 for row in before_files:
  assert digest(at(row['historical_snapshot']))==digest(at(row['canonical']))==row['sha256']and len(at(row['historical_snapshot']))==row['bytes']
  assert read(RUN+'/before.json')['inputs'][row['canonical']]==row['sha256']
 adoption=read('/tmp/k215-phase10-main/adoption.json')
 assert adoption['status']=='EXACT_CHECKED_FOUR_FILE_ADOPTION'and adoption['adapter_unchanged']
 assert adoption['compiled_full_result_sha256']==digest(at(RUN+'/result.json'))
 assert adoption['reproduction_sha256']==digest(at('/tmp/k215-phase10-main/producer-execution.json'))
 assert len(adoption['files'])==4 and len({r['target']for r in adoption['files']})==4
 historical={r['canonical']:r for r in before_files}
 for row in adoption['files']:
  path=PurePosixPath(row['target']);assert not path.is_absolute()and'..'not in path.parts
  data=members['adoption/'+row['target']];assert digest(data)==row['sha256']
  if row['target'].endswith('/DominatedImplication.lean'):
   assert row['sha256']==entries[CORE]['source_sha256']=='5e524b3fd128e91ae1be067ec12392978713b29c129a37b55272cc4091c9bf3f'
   assert row['before_sha256']==old_rows[CORE]['source_sha256']
  else:assert historical[ROOT+'/'+row['target']]['sha256']==row['before_sha256']
  if current_repo is not None:assert sha(Path(current_repo)/row['target'])==row['sha256']
 peer=read('/tmp/k215-phase10-main-peer/actual-review.json');assert peer['status']=='PASS_INDEPENDENT_PHASE10_TRANSITIVE_REVIEW'
 assert peer['pins'][RUN+'/result.json']==digest(at(RUN+'/result.json'))and peer['pins']['/tmp/k215-phase10-main-peer/review.py']==digest(at('/tmp/k215-phase10-main-peer/review.py'))
 assert peer['fresh_count']==8 and peer['exact_phase9_reuse_count']==189 and peer['all_before_inputs_rehashed_without_exception']
 return {'status':'PASS_SAVED_PHASE10_RECORDS','modules':197,'endpoint_modules':len(closures[TARGETS[0]]),'prefix_only_modules':sorted(set(entries)-closures[TARGETS[0]]),'fresh_modules':sorted(FRESH),'fresh_count':8,'phase9_reused_count':189,'site_batches_unchanged':sites,'typed_clients':2,'typed_reports':10,'audit_warnings':0,'project_warning_occurrences':warnings,'isolated_modules':16,'isolated_fresh':5,'isolated_reports':17,'isolated_warning_occurrences':iso_warnings,'isolated_fresh_warnings':0,'raw_result_sha256':digest(at(RUN+'/result.json')),'isolated_result_sha256':digest(at(ISO+'/result.json')),'phase9_archive_sha256':checked['archive_sha256'],'current_sources_checked':current_repo is not None,'scope':'Saved source/import/object-hash/log/raw-command provenance, with exact local phase9 validation. No live-object, new compiler or producer-execution claim. Five original producer inputs are historical snapshots; adoption is documented separately.'}
