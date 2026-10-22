"""Validate two compact phase12 record sets against the exact local phase11 packet."""
from pathlib import Path,PurePosixPath
import hashlib,json,re
import basis
HERE=Path(__file__).resolve().parent
ROOT='/home/codex/.codex/worktrees/ec20/Proofs'
BASE='/tmp/k215-generic-cd58-check/inline-full-run1'
OLD='/tmp/k215-proof-phase8/lean-run1'
PREP='/tmp/k215-phase12-import-check'
EXEC='/tmp/k215-phase12-import-execution'
PROPOSAL='/tmp/k215-phase12-import-proposal'
MAIN=PREP+'/primary-run1';COMP=PREP+'/compatibility-run1'
PRODUCER='Computability/BusyBeaver/Research/ZFC/k225-formal/generate_l2k222.py'
OLD_PRODUCER='058710ffc00994301fad082c62358901ae609ddf7fd4b264c3b150f19c4ac7b3'
NEW_PRODUCER='c720d5bf58d4c9119bfb6a6d206451e18c7287caf0518c8a666b38cc0b2e74f6'
DRIVER='4242f1dab9adcf9a5f1b89ef87d5a65568e1ef302627fb89183e2a94dd99dcb5'
BOUNDARY='f7d0a50ce268bafb9050d90d6d8d72c753eb5d99ba870ab07aeba1407bd54026'
FREEZE='e590f66fcd627abcddd3e52b8929d13597032c61662c854af8198af4ee31d60d'
NS='SetTheory.BusyBeaver.ZFC.'
PREFIX='BusyBeaver.ZFC.'
TARGETS=[PREFIX+'KEndpoint215',PREFIX+'KDecoderPrefix215']
CLIENTS=['WFModelCompat12','ZFNativeCompat12']
CLIENT_REPORTS={'WFModelCompat12':[NS+'WFModelCompat12.'+n for n in ['domain_axioms','domain_models','quotient_models']], 'ZFNativeCompat12':[NS+'ZFNativeCompat12.'+n for n in ['models','native','refutation','halt_zf','con_zf','halt_zfc','con_zfc']]}
AUDIT_NAMES={'EndpointAudit215':['EndpointAudit215.blank_halts_exactly_when_zfc_has_a_finite_refutation','EndpointAudit215.nonhalting_exactly_when_zfc_is_consistent'],'K215Audit':[NS+'KEndpoint215.blank_halts_iff_zfc_refutation',NS+'KEndpoint215.nonhalting_iff_zfc_consistency',NS+'KDense215.commutes',NS+'KBoot215.boot',NS+'KSites215.covered',NS+'KEndpoint215.p215_boot_iff','K215Audit.blank_halts_exact','K215Audit.nonhalting_exact']}
AUDIT_PINS={'EndpointAudit215':'d13596021774c5b26937b13cf6cca58342af99f59626b9205ff10b9df1e6fc7d','K215Audit':'9144acc6c597c4a53928fc62be00d5e25d9f32f519797d17a5058d03b5460986'}
REMOVED={PREFIX+n for n in ['Dag254','DecodeFresh254','Enum254','L2Axioms254','L2AxiomsEval254','L2Control254','L2Lib254','L2Macros254','L2Root254','NativeDecoded254','NativeTheory254','QuotientZF0','WFModel','WFTheory','ZFNative']}
NEW={PREFIX+'WFModelCore',PREFIX+'ZFModels'}
FRESH_MAIN={PREFIX+n for n in ['ConstructibleChoice','KEndpoint','KEndpoint215','KLowerQHyp','KQ1ZF','KUpper222','L2AxiomsPerm','L2Control222','L2Lib222','L2Macros222','L2Perm','L2RootPerm','SeedPerm','WFModelCore','ZFModels']}
FRESH_COMP={PREFIX+n for n in ['WFModel','ZFNative','WFTheory']}|set(CLIENTS)
BINARY={'.olean','.ilean','.o','.so','.a','.vo','.vos','.vok','.glob','.pyc','.pyo'}
def digest(b):return hashlib.sha256(b).hexdigest()
def sha(p):return digest(Path(p).read_bytes())
def dump(x):return(json.dumps(x,indent=2)+'\n').encode()
def safe(name):
 p=PurePosixPath(name);assert not p.is_absolute()and'..'not in p.parts and str(p)==name
 assert not set(p.suffixes)&(BINARY|{'.gz','.zip','.tar'})
def absent(p):assert not Path(p).exists()and not Path(p).is_symlink()
def manifest(data):return{n:{'sha256':digest(b),'bytes':len(b)}for n,b in sorted(data.items())}
def resolve_routes(members,prior,routes):
 resolved={}
 for path,r in routes.items():
  assert PurePosixPath(path).is_absolute()and set(r)=={'storage','key','sha256','bytes'}and r['storage']in{'packet','phase11'}
  data=(members if r['storage']=='packet'else prior)[r['key']]
  assert digest(data)==r['sha256']and len(data)==r['bytes'];resolved[path]=data
 return resolved
def same_source_closure(entries,previous,closure):
 assert all((entries[d]['source_sha256'],entries[d]['imports'])==(previous[d]['source_sha256'],previous[d]['imports'])for d in closure)
def exact_reuse(record,previous,origin):assert record=={**previous,'origin':origin}
def named_reports(log,names,reader):
 found=reader(log);assert [n for n,_ in found]==names and 'warning:'not in log.decode();return found
def explicit_externals(rows):
 modules={r['module']for r in rows};external={d for r in rows for d in r['imports']if d not in modules}
 assert external<={'Init'};return sorted(external)
def validate(members,repo,basis_data=None,current_repo=None):
 for n in members:safe(n)
 prior,checked,h=basis.load(repo)if basis_data is None else basis_data
 assert members['review/basis-reference.json']==(HERE/'basis-reference.json').read_bytes()
 routes=json.loads(members['path-map.json']);resolved=resolve_routes(members,prior,routes)
 at=lambda p:resolved[str(p)];read=lambda p:json.loads(at(p))
 old_inv=json.loads(prior['member:execution/inventory.json']);oldrows={r['module']:r for r in old_inv['modules']};old=json.loads(prior['member:execution/completed.json'])
 assert len(oldrows)==len(old)==197 and digest(prior['member:execution/result.json'])=='53a7307848e6445a46b13e39b4283e335f5793660ca23f46659dc26c8f8e794d'
 old8=read(OLD+'/completed.json');tool=read(OLD+'/toolchain.json');compiler=tool['lean']['path'];helper=ROOT+'/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/lean/build.py'
 binary={v['path']:v['sha256']for k,v in tool.items()if k in{'lean','lake','Init.olean'}}
 for root,done in [(BASE,old),(OLD,old8)]:binary.update({root+'/objects/'+m.replace('.','/')+'.olean':r['object_sha256']for m,r in done.items()})
 prep=read(PREP+'/freeze.json');assert digest(at(PREP+'/freeze.json'))==FREEZE
 for name,pin in prep['files'].items():assert digest(at(PREP+'/'+name))==pin
 proposal=read(PROPOSAL+'/freeze.json');assert len(proposal['files'])==8
 production={r['target']:r for r in proposal['files']};assert len(production)==8
 for row in production.values():assert digest(at(row['source']))==row['sha256']and len(at(row['source']))==row['bytes']
 boundary=read(PREP+'/producer-boundary.json');assert digest(at(PREP+'/producer-boundary.json'))==BOUNDARY
 def run_check(root,targets,fresh,count,secondary=None):
  result=read(root+'/result.json');before=read(root+'/before.json');inv=read(root+'/inventory.json');done=read(root+'/completed.json')
  assert result['status']=='PASS'and result['selected_project_modules']==count
  assert result['targets']==inv['targets']==before['targets']==targets and before['rows']==inv['modules']
  assert before['external_imports']==inv['external_imports']==explicit_externals(inv['modules'])and before['audit_endpoint']==(secondary is None)
  assert digest(at(root+'/inventory.json'))==result['inventory_sha256']and digest(at(root+'/completed.json'))==result['completed_sha256']
  assert read(root+'/toolchain.json')==tool
  entries,closures=h.graph(inv['modules'],targets);assert len(entries)==len(done)==count and set(entries)==set(done)
  assert set(result['fresh_modules'])==fresh
  expected_origins={'candidate_fresh':fresh,'phase11_checked':set(result['phase11_reused_modules']),'secondary_checked':set(result['secondary_reused_modules'])}
  assert set().union(*expected_origins.values())==set(entries)and sum(map(len,expected_origins.values()))==count
  assert result['basis_reuse_rejects_transitive_source_changes']and result['secondary_reuse_requires_exact_transitive_sources_and_imports']
  changed={m for m,e in entries.items()if m not in oldrows or(e['source_sha256'],e['imports'])!=(oldrows[m]['source_sha256'],oldrows[m]['imports'])}
  forced={m for m in entries if closures[m]&changed}
  assert sorted(changed)==before['changed_sources']==result['source_changed_modules']and sorted(forced)==before['force_basis_rebuild']==result['force_basis_rebuild_modules']
  if secondary is None:
   assert forced==fresh and set(entries)==set(oldrows)-REMOVED|NEW and not expected_origins['secondary_checked']
  else:
   assert len(expected_origins['secondary_checked'])==52 and len(expected_origins['phase11_checked'])==12 and len(forced)==7
  maps=[p for p,pin in before['inputs'].items()if pin==result['map_sha256']];assert len(maps)==1
  plan=read(maps[0]);plans={r['module']:r for r in plan['modules']};assert len(plans)==len(plan['modules'])
  assert plan['expected']=={'modules':[r['module']for r in inv['modules']],'changed':sorted(changed),'forced':sorted(forced)}
  if secondary is not None:
   pins=plan['reuse_ledger'];assert pins['directory']==MAIN
   for name in ['result.json','inventory.json','completed.json']:assert pins[name]==digest(at(MAIN+'/'+name))
  assert result['basis_result_sha256']==digest(prior['member:execution/result.json'])and result['producer_boundary_sha256']==BOUNDARY
  assert result['runner_sha256']==before['runner_sha256']==DRIVER==digest(at(PREP+'/build.py'))
  assert before['inputs'][PREP+'/build.py']==DRIVER and before['inputs'][helper]=='a3cf7cc38004bca5e2a2df10c607fe5353896c0454069b4ff24d6b5176c32fbd'
  objects={m:r['object_sha256']for m,r in done.items()};warnings={k:0 for k in expected_origins};report_counts={k:0 for k in expected_origins}
  for m,row in entries.items():
   rec=done[m];source=at(row['source']);log=at(rec['log']);text=log.decode();reports=h.reports(log);origin=rec['origin']
   assert m in expected_origins[origin]
   assert digest(source)==row['source_sha256']==rec['source_sha256']and h.imports(source)==row['imports']
   assert rec['dependencies']=={d:objects[d]for d in row['imports']if d!='Init'}
   assert rec['status']=='PASS'and rec.get('exit_code',0)==0 and not rec.get('timed_out',False)and digest(log)==rec['log_sha256']
   warnings[origin]+=text.count('warning:');report_counts[origin]+=len(reports)
   if origin=='candidate_fresh':
    assert rec['timeout_seconds']==120 and rec['memory_mebibytes']==12288
    assert rec['compiler_sha256']==tool['lean']['sha256']and rec['helper_sha256']==before['inputs'][helper]
    src=root+'/workspace/'+m.replace('.','/')+'.lean';obj=root+'/objects/'+m.replace('.','/')+'.olean'
    assert rec['command']==[compiler,'-j1','-M12288','--root='+root+'/workspace','-o',obj,src]
    assert rec['source']==src and digest(at(src))==row['source_sha256']
    assert read(str(PurePosixPath(rec['log']).parent/'record.json'))==rec
    assert rec['reports']==[list(x)for x in reports]and rec['warnings']==text.count('warning:')
   else:
    previous,prevrows=(old,oldrows)if origin=='phase11_checked'else secondary
    exact_reuse(rec,previous[m],origin)
    same_source_closure(entries,prevrows,closures[m])
    if origin=='phase11_checked':assert m not in forced
   if m in CLIENT_REPORTS:named_reports(log,CLIENT_REPORTS[m],h.reports)
   if m in plans and'reports'in plans[m]:assert [n for n,_ in reports]==plans[m]['reports']and not text.count('warning:')
   if m in plans:
    assert plans[m]['source_sha256']==row['source_sha256']and plans[m]['imports']==row['imports']
    assert plans[m]['before_sha256']==oldrows.get(m,{}).get('source_sha256')
   if current_repo is not None and m not in CLIENTS:
    found=[Path(current_repo)/r/(m.replace('.','/')+'.lean')for r in h.ROOTS if(Path(current_repo)/r/(m.replace('.','/')+'.lean')).is_file()]
    assert len(found)==1 and sha(found[0])==row['source_sha256']
  for p,pin in before['inputs'].items():
   if p in binary:assert binary[p]==pin
   else:assert digest(at(p))==pin,p
  assert before['absent_inputs']==sorted(r['canonical']for r in boundary['files']if r['current_state']=='absent')
  audits=result['audits'];assert [r['module']for r in audits]==(list(AUDIT_NAMES)if secondary is None else [])
  for rec in audits:
   m=rec['module'];q=root+'/audit-'+m;log=at(rec['log']);reports=h.reports(log)
   assert rec['status']=='PASS'and rec['exit_code']==0 and not rec['timed_out']and'warning:'not in log.decode()
   assert [list(x)for x in named_reports(log,AUDIT_NAMES[m],h.reports)]==rec['named_reports']
   assert digest(at(rec['source']))==digest(at(q+'/'+m+'.lean'))==rec['source_sha256']==AUDIT_PINS[m]
   assert digest(log)==rec['log_sha256']and rec['dependencies']==objects
   assert rec['command']==[compiler,'-j1','-M12288','--root='+q,'-o',q+'/'+m+'.olean',q+'/'+m+'.lean']
   assert rec['compiler_sha256']==tool['lean']['sha256']and rec['timeout_seconds']==120 and rec['memory_mebibytes']==12288
   assert read(q+'/'+m+'.json')==rec
  label=PurePosixPath(root).name;outer=read(EXEC+'/'+label+'-outer.json')
  assert outer['status']=='OUTER_EXIT_0'and outer['exit_code']==0 and outer['exception']is None and outer['helper_inputs_unchanged']and outer['plan_unchanged']
  assert outer['command']==read(outer['plan'])['command']and outer['plan_sha256']==digest(at(outer['plan']))
  assert outer['command'][0:3]==['python','-B',PREP+'/build.py']and outer['command'][outer['command'].index('--out')+1]==root and outer['command'][outer['command'].index('--map')+1]==maps[0]
  assert outer['wrapper_sha256']==digest(at(EXEC+'/run.py'))and outer['freeze_sha256']==FREEZE
  assert outer['before_helper_inputs']==outer['after_helper_inputs']=={PREP+'/'+n:p for n,p in prep['files'].items()}
  for key in ['stdout','stderr']:assert outer[key+'_sha256']==digest(at(outer[key]))
  receipt=read(EXEC+('/primary-actual-review.json'if secondary is None else'/compatibility-actual-review.json'))
  assert receipt['status']=='PASS_READ_ONLY_TRANSITIVE_ACTUAL'and receipt['result_sha256']==digest(at(root+'/result.json'))
  assert receipt['reviewer_sha256']==digest(at(EXEC+'/review.py'))and receipt['all_inputs_sources_objects_logs_rehashed']and receipt['source_transitive_reuse_checked']
  binary.update({root+'/objects/'+m.replace('.','/')+'.olean':r['object_sha256']for m,r in done.items()})
  return result,entries,closures,done,warnings,report_counts
 main,entries,closures,done,mwarn,mreports=run_check(MAIN,TARGETS,FRESH_MAIN,184)
 comp,cent,cclose,cdone,cwarn,creports=run_check(COMP,CLIENTS,FRESH_COMP,69,(done,entries))
 project=(set(entries)|set(cent))-set(CLIENTS);assert len(project)==199 and project==set(oldrows)|NEW
 assert len(closures[TARGETS[0]])==179 and len(set(entries)-closures[TARGETS[0]])==5
 sites=sorted(m for m in entries if m.startswith(PREFIX+'KSites215Batch'));assert len(sites)==9
 for m in sites:assert done[m]=={**old[m],'origin':'phase11_checked'}
 assert mwarn=={'candidate_fresh':4,'phase11_checked':16,'secondary_checked':0}and cwarn=={'candidate_fresh':0,'phase11_checked':1,'secondary_checked':6}
 assert mreports['candidate_fresh']==7 and creports['candidate_fresh']==15
 assert boundary['phase11_result_sha256']==digest(prior['member:execution/result.json'])and boundary['phase8_result_sha256']==digest(at(OLD+'/result.json'))
 assert len(boundary['files'])==5
 for key in ['phase11_adoption','previous_boundary','producer_before_original']:
  r=boundary[key];assert digest(at(r['path']))==r['sha256']
 for p,pin in boundary['additional_inputs'].items():assert digest(at(p))==pin
 ancestry=read(OLD+'/result.json')
 assert {str(PurePosixPath(r['canonical']).relative_to(ROOT))for r in boundary['files']}==set(ancestry['producer_pins'])
 for r in boundary['files']:
  assert r['phase8_sha256']==ancestry['producer_pins'][str(PurePosixPath(r['canonical']).relative_to(ROOT))]
  for k in ['phase8_snapshot','historical_original']:assert digest(at(r[k]))==r['phase8_sha256']
  assert digest(at(r['phase10_snapshot']))==r['phase10_sha256']
  if r['current_state']=='present':
   for k in ['current_snapshot','canonical']:assert digest(at(r[k]))==r['current_sha256']
   if current_repo is not None:assert sha(Path(current_repo)/PurePosixPath(r['canonical']).relative_to(ROOT))==r['current_sha256']
  else:
   assert r['current_state']=='absent'and digest(at(r['retired_snapshot']))==r['phase10_sha256']
   if current_repo is not None:absent(Path(current_repo)/PurePosixPath(r['canonical']).relative_to(ROOT))
 adoption=read(PROPOSAL+'/adoption.json');assert adoption['status']=='EXACT_CHECKED_PHASE12_ADOPTION'
 assert adoption['primary_result_sha256']==digest(at(MAIN+'/result.json'))and adoption['compatibility_result_sha256']==digest(at(COMP+'/result.json'))
 writes={r['target']:r for r in adoption['files']};assert set(writes)==set(production)and len(writes)==8
 for target,r in writes.items():
  p=production[target];assert all(r[k]==p[k]for k in ['source','target','sha256','bytes','before_sha256'])
  data=members['adoption/'+target];assert digest(data)==r['sha256']and len(data)==r['bytes']and data==at(r['source'])
  if target.endswith('.lean'):
   m=PREFIX+PurePosixPath(target).stem;row=(entries|cent)[m];assert row['source_sha256']==r['sha256']
  else:assert target==PRODUCER and r['sha256']==NEW_PRODUCER and r['before_sha256']==OLD_PRODUCER
  if r['before_sha256']is not None:assert digest(at(r['archived_before']))==r['before_sha256']
  else:assert r['archived_before']is None
  if current_repo is not None:assert sha(Path(current_repo)/target)==r['sha256']
 for root in [MAIN,COMP]:assert read(root+'/before.json')['inputs'][ROOT+'/'+PRODUCER]==OLD_PRODUCER
 assert digest(at(ROOT+'/'+PRODUCER))==OLD_PRODUCER
 root_review=read(PROPOSAL+'/root-actual-review.json');assert adoption['root_actual_review_sha256']==digest(at(PROPOSAL+'/root-actual-review.json'))
 assert root_review['status']=='PASS_INDEPENDENT_ROOT_PHASE12_ACTUALS'and root_review['all_sources_objects_logs_dependencies_and_inputs_rehashed']
 assert [r['result_sha256']for r in root_review['runs']]==[digest(at(MAIN+'/result.json')),digest(at(COMP+'/result.json'))]
 assert adoption['source_peer_sha256']==digest(at('/tmp/k215-phase12-import-peer/review.json'))
 current=read(PROPOSAL+'/current-review.json');assert current['status']=='PASS_CURRENT_PHASE12_ADOPTION'and current['adoption_sha256']==digest(at(PROPOSAL+'/adoption.json'))
 assert current['canonical_writes']==8 and current['project_sources']==199
 literal=read(PROPOSAL+'/producer-literal-check.json');assert literal['status']=='PASS_EXACT_THREE_MODULE_LITERAL_REPRODUCTION'and literal['producer_sha256']==NEW_PRODUCER
 assert literal['producer_executed']is False and literal['supplied_execution']is False
 assert [r['module']for r in literal['modules']]==['L2Lib222','L2Macros222','L2Control222']
 for r in literal['modules']:assert entries[PREFIX+r['module']]['source_sha256']==r['sha256']and len(at(entries[PREFIX+r['module']]['source']))==r['bytes']
 correction=read(PROPOSAL+'/scope-correction.json');old_adopt=read(PROPOSAL+'/metadata-history/adoption-before-scope-correction.json');old_current=read(PROPOSAL+'/metadata-history/current-review-before-scope-correction.json')
 assert correction['before_sha256']==digest(at(PROPOSAL+'/metadata-history/adoption-before-scope-correction.json'))and correction['after_sha256']==digest(at(PROPOSAL+'/adoption.json'))
 assert {k:v for k,v in old_adopt.items()if k!='scope'}=={k:v for k,v in adoption.items()if k!='scope'}
 assert {k:v for k,v in old_current.items()if k!='adoption_sha256'}=={k:v for k,v in current.items()if k!='adoption_sha256'}
 return {'status':'PASS_SAVED_PHASE12_RECORDS','primary_modules':184,'endpoint_modules':179,'prefix_modules':5,'primary_fresh':15,'primary_phase11_reuse':169,'endpoint_clients':2,'endpoint_reports':10,'endpoint_audit_warnings':0,'primary_warning_occurrences':20,'compatibility_project_modules':67,'compatibility_client_modules':2,'compatibility_fresh':5,'compatibility_primary_reuse':52,'compatibility_phase11_reuse':12,'compatibility_client_reports':10,'compatibility_existing_facade_reports':5,'compatibility_fresh_warnings':0,'compatibility_inherited_warnings':7,'combined_project_modules':199,'site_batches_unchanged':sites,'primary_result_sha256':digest(at(MAIN+'/result.json')),'compatibility_result_sha256':digest(at(COMP+'/result.json')),'phase11_archive_sha256':checked['archive_sha256'],'current_sources_checked':current_repo is not None,'scope':'Two recorded Lean checks with exact source/import/object-hash/log/command provenance. No live-object verification or new compiler invocation by this saved reader. The old L2 producer before-input bytes remain historical; seven compiled sources and one producer are checked separately as current adoption.'}
