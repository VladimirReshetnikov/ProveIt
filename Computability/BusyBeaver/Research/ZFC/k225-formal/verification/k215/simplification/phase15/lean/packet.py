"""Validate phase15 saved records against the exact local phase14 packet.
No compiler, producer or archived Python is executed by this reader.
"""
from pathlib import Path, PurePosixPath
import hashlib, json, re
import basis
HERE = Path(__file__).resolve().parent
ROOT = '/home/codex/.codex/worktrees/ec20/Proofs'
PREP = '/tmp/k215-phase15-check'
EXEC = '/tmp/k215-phase15-execution'
FIRST, SECOND, MAIN, COMP = [PREP+'/'+s for s in ['primary-run1','primary-run2','primary-run3','compatibility-run1']]
RETRY = '/tmp/k215-phase15-retry'
CLIENT_RETRY = '/tmp/k215-phase15-client-retry'
BASE = '/tmp/k215-phase14-check/primary-run2'
BASE_COMP = '/tmp/k215-phase14-check/compatibility-run1'
OLD = '/tmp/k215-proof-phase8/lean-run1'
DRIVER = '198b075493d80cf554f5755a37ccfbc5afb90fcfa498b900d805f13312e458ec'
FREEZE = 'bf7ee51d71e671876ca5b1b8c4933493cee3907c993b36b2658e2f4a6196cb06'
BOUNDARY = '8d039df9d25e21af1122727278f378b0016cdb235d3c18b3e883a144696840a0'
BASE_RESULTS = ['3454f69d71477171f20d91733093821fa3198253dece63802c59d045bf3991df','008d6626c9c2b11400713bda9dff89aa5385f276d0898f13c1f0dd19cda857b1']
P = 'BusyBeaver.ZFC.'
NS = 'SetTheory.'+P
OLD_API = ['GenericShared13Api','NumericCD52Api','LukasShared13Api','DerivedRows14Api','ThmKDerived14Api','KEindDerived14Api','ProfileTC14Api']
NEW_API = ['BasicInterfaces15Api','TransRec15Api','QuotientSharing15Api']
API = OLD_API+NEW_API
CLIENTS = ['WFModelCompat12','ZFNativeCompat12']
TARGETS = [P+'KEndpoint215',P+'KDecoderPrefix215']+API
STANDARD = {'propext','Classical.choice','Quot.sound'}
PQ = {'propext','Quot.sound'}
LEAN_DIR = 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/'
FORMAL = 'Computability/BusyBeaver/Research/ZFC/k225-formal/'
AUDIT_NAMES = {
 'EndpointAudit215': ['EndpointAudit215.blank_halts_exactly_when_zfc_has_a_finite_refutation', 'EndpointAudit215.nonhalting_exactly_when_zfc_is_consistent'],
 'K215Audit': [NS + 'KEndpoint215.blank_halts_iff_zfc_refutation', NS + 'KEndpoint215.nonhalting_iff_zfc_consistency', NS + 'KDense215.commutes', NS + 'KBoot215.boot', NS + 'KSites215.covered', NS + 'KEndpoint215.p215_boot_iff', 'K215Audit.blank_halts_exact', 'K215Audit.nonhalting_exact']}
AUDIT_PINS = {'EndpointAudit215': 'd13596021774c5b26937b13cf6cca58342af99f59626b9205ff10b9df1e6fc7d', 'K215Audit': '9144acc6c597c4a53928fc62be00d5e25d9f32f519797d17a5058d03b5460986'}
PRIOR_ADOPTIONS = {
 LEAN_DIR + 'DominatedImplication.lean': 'bd07364a829e8a1535b0ecf1ee6ed0c292d5af35e01a6db8f152dd2610e247d8',
 LEAN_DIR + 'Lukasiewicz.lean': '7d443a733b5c5ddd0d49728cf1ea7d855dd445f156934c13578bacc008c59874',
 FORMAL + 'generate_dominated_implication_lean.py': 'ebcbb86642d4d389748451dc662b42f7ac62e7aa4b235bbf4e5d8e5a1ec5c1e9',
 FORMAL + 'rho8cd/derivation_core.txt': '4141248ed90a6813c07f274351336963acde1d82f6ea463a33e5f7d64bed8005',
 FORMAL + 'rho8cd/generate_domrho8_cd.py': '63da860d3a957010c53d783a2b8995acef3d8e3806823f24fc5833738dc1d56a'}
PRIOR_WRITES = {LEAN_DIR + n + ".lean": p for n,p in {'TarskiDerived': 'af15c7f2946d2d2f335d540acc33f69afca4bd884cf4dfe7bfcbc323707e4b19', 'TarskiLeibniz': 'bf57b911ce313037bce71ef6f680a36bb54ce7be9d504d6533c612bd4d9831e7', 'KThmK': '396779f2da512975580d8a34e322cd589fbf22c33018cfd5b389b99c4398b4dc', 'KEind222': '090f7bbb58295d186f9dd10ee86041f8b65d2f4ebea6d496bafdd88f2d56b507', 'CompositionModel': 'ffcd2758db64f989424fc915f9d881ad5106befac0e99875c890e07932d6913e', 'KLowerEqv': '7d8646d8e043223a1653456d44138053e347517b30b21f3989ec326376cc7d12', 'ProfileComposition': '2d2af6f596cef80f52c8463a40089be53f55d3b7c0d5ecc09742180a6e00f8cf'}.items()}
PRIOR_ADOPTIONS.update(PRIOR_WRITES)
ADOPTIONS = {'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/PowerSets.lean': 'fe2f9aa8deb9a4bebb96c0685858b3df6f8c5ade3fba7b524468a61dbcfbac98', 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/PSCCalibration.lean': 'b5fe4fc694a00304acc057c17789c4f9334909ffa7c88dfa0db661cdf1c4159d', 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/WFModelCore.lean': '390b3d8d662ce5d8fb62dd9cabc628e11afd08872b60dbd0e4a522cc17db73f5', 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KDenseBridge.lean': 'ce03e85f85fd726ed241e56718efa0920e00a5b6d324ce271ddede731146b16e', 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/InternalRank.lean': 'f58d808ed2516595bf476ab6df80049b76c179dd7f117b6eebbe08e93fa41ff5', 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/TransRec.lean': 'da6b8f9136328f0582cd50f0514988109245c038e0cfb37435c3bcf2a24db7fe', 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/QuotientModel.lean': '2bbcd0337538f1fd378ee959007d5eeb5f26d03d6379a3aa9c44abe04b8540a2', 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KQ1Model.lean': '304c3c66d456dd2a204636e95f9aa2c6f57fbf73a0d7b0a00577552d9ed1535e', 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KQ1ZF.lean': 'ad279bf8b620c7b0a5e216962d6297190750cf136133edef4eeeb63520e2e67d', 'Computability/BusyBeaver/Research/ZFC/k225-formal/generate_kq1.py': '8837ba3cbe0a82c4f166160f58d39ef35bd9d5d50adcac5078d4cf26eaaf7e42'}
CREATED = LEAN_DIR+'PowerSets.lean'
RETAINED_ABSENCES = [LEAN_DIR+'KProfileTC.lean', FORMAL+'generate_profile_tc.py', FORMAL+'dominated_implication_templates/core-prefix.txt', FORMAL+'dominated_implication_templates/core-suffix.txt']

NEW_PROFILES = {'BasicInterfaces15Api': [['BasicInterfaces15Api.power_sets', []], ['BasicInterfaces15Api.calibration', ['Classical.choice', 'Quot.sound', 'propext']], ['BasicInterfaces15Api.dense', ['Quot.sound', 'propext']]], 'TransRec15Api': [['SetTheory.BusyBeaver.ZFC.TransRec15Api.cumulative_shape', ['Classical.choice']], ['SetTheory.BusyBeaver.ZFC.TransRec15Api.operation_shape', ['Classical.choice']], ['SetTheory.BusyBeaver.ZFC.TransRec15Api.approximation_shape', ['Classical.choice']], ['SetTheory.BusyBeaver.ZFC.TransRec15Api.cumulative_formula', []], ['SetTheory.BusyBeaver.ZFC.TransRec15Api.operation_formula', []], ['SetTheory.BusyBeaver.ZFC.TransRec15Api.cumulative_semantics', ['Classical.choice', 'Quot.sound', 'propext']], ['SetTheory.BusyBeaver.ZFC.TransRec15Api.cumulative_exists', ['Classical.choice', 'Quot.sound', 'propext']], ['SetTheory.BusyBeaver.ZFC.TransRec15Api.cumulative_unique', ['Classical.choice', 'Quot.sound', 'propext']], ['SetTheory.BusyBeaver.ZFC.TransRec15Api.cumulative_spec', ['Classical.choice', 'Quot.sound', 'propext']], ['SetTheory.BusyBeaver.ZFC.TransRec15Api.cumulative_mono', ['Classical.choice', 'Quot.sound', 'propext']], ['SetTheory.BusyBeaver.ZFC.TransRec15Api.cumulative_trans', ['Classical.choice', 'Quot.sound', 'propext']], ['SetTheory.BusyBeaver.ZFC.TransRec15Api.operation_semantics', ['Classical.choice', 'Quot.sound', 'propext']], ['SetTheory.BusyBeaver.ZFC.TransRec15Api.operation_exists', ['Classical.choice', 'Quot.sound', 'propext']], ['SetTheory.BusyBeaver.ZFC.TransRec15Api.operation_unique', ['Classical.choice', 'Quot.sound', 'propext']], ['SetTheory.BusyBeaver.ZFC.TransRec15Api.operation_spec', ['Classical.choice', 'Quot.sound', 'propext']], ['SetTheory.BusyBeaver.ZFC.TransRec15Api.operation_mono', ['Classical.choice', 'Quot.sound', 'propext']], ['SetTheory.BusyBeaver.ZFC.TransRec15Api.relation_unique', ['Classical.choice', 'Quot.sound', 'propext']], ['SetTheory.BusyBeaver.ZFC.TransRec15Api.relation_mono', ['Classical.choice', 'Quot.sound', 'propext']]], 'QuotientSharing15Api': [['QuotientSharing15Api.shared_syntax', []], ['QuotientSharing15Api.strong_congruence', ['Classical.choice', 'Quot.sound', 'propext']], ['QuotientSharing15Api.weak_congruence', ['Quot.sound', 'propext']], ['QuotientSharing15Api.strong_satisfaction', ['Classical.choice', 'Quot.sound', 'propext']], ['QuotientSharing15Api.weak_satisfaction', ['Quot.sound', 'propext']], ['QuotientSharing15Api.strong_extensionality', ['Classical.choice', 'Quot.sound', 'propext']], ['QuotientSharing15Api.weak_extensionality', ['Quot.sound', 'propext']]]}

BINARY = {'.olean', '.ilean', '.o', '.so', '.a', '.vo', '.vos', '.vok', '.glob', '.pyc', '.pyo'}
HELPERS = ['basis.py', 'basis-reference.json', 'packet.py', 'collect.py', 'review_saved.py', 'controls.py', 'README.md','prepare_config.py','prepare_draft.py']

def digest(data): return hashlib.sha256(data).hexdigest()
def sha(path): return digest(Path(path).read_bytes())
def dump(value): return (json.dumps(value, indent=2) + '\n').encode()
def safe(name):
 p = PurePosixPath(name)
 assert name and not p.is_absolute() and '..' not in p.parts and str(p) == name
 assert not set(p.suffixes) & (BINARY | {'.gz', '.zip', '.tar'})
def historical_file(path, historical): return historical.get(str(path),{}).get('snapshot',str(path))
def absent(path): assert not Path(path).exists() and not Path(path).is_symlink()
def manifest(data): return {n: {'sha256': digest(b), 'bytes': len(b)} for n, b in sorted(data.items())}
def resolve_routes(members, prior, routes):
 result = {}
 for path, row in routes.items():
  assert PurePosixPath(path).is_absolute() and set(row) == {'storage', 'key', 'sha256', 'bytes'}
  assert row['storage'] in {'packet', 'phase14'}
  data = (members if row['storage'] == 'packet' else prior)[row['key']]
  assert digest(data) == row['sha256'] and len(data) == row['bytes']
  result[path] = data
 return result

def same_source_closure(entries, previous, closure):
 assert all((entries[d]['source_sha256'], entries[d]['imports']) == (previous[d]['source_sha256'], previous[d]['imports']) for d in closure)
def exact_reuse(record, previous, origin): assert record == {**previous, 'origin': origin}
def exact_resume(record, previous):
 assert record == previous and record['status']=='PASS'
def reports(data):
 text = data.decode()
 assert 'error:' not in text and 'sorryAx' not in text
 found = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", text)
 assert all(axioms <= STANDARD for _, axioms in profiles(found))
 return found

def profiles(found): return [(name, {x.strip() for x in raw.split(',') if x.strip()}) for name, raw in found]
def named_reports(data, names, expected=None):
 found = reports(data)
 assert [n for n, _ in found] == names and 'warning:' not in data.decode()
 if expected is not None: assert [ax for _, ax in profiles(found)] == [set(x) for x in expected]
 return found

def explicit_externals(rows):
 modules = {r['module'] for r in rows}
 found = {d for r in rows for d in r['imports'] if d not in modules}
 assert found <= {'Init'}
 return sorted(found)

def freeze_check(directory, pin, read, at):
 assert digest(at(directory+'/freeze.json')) == pin
 f = read(directory+'/freeze.json')
 for n, p in f['files'].items(): assert digest(at(directory+'/'+n)) == p
 for n, p in f.get('external_inputs',{}).items(): assert digest(at(n)) == p
 return f

def validate(members, repo, basis_data=None, current_repo=None):
 for n in members: safe(n)
 prior, checked, h = basis.load(repo) if basis_data is None else basis_data
 assert members['review/basis-reference.json'] == (HERE/'basis-reference.json').read_bytes()
 resolved = resolve_routes(members, prior, json.loads(members['path-map.json']))
 at = lambda p: resolved[str(p)]
 read = lambda p: json.loads(at(p))
 cfg = json.loads(members['review/config.json'])
 assert cfg['status'] == 'FROZEN_COMPLETED_PHASE15_INPUTS'
 assert cfg['new_api_profiles']==NEW_PROFILES
 for p,r in cfg['files'].items(): assert digest(at(p)) == r['sha256'] and len(at(p)) == r['bytes']
 old, oldrows, oldkind = {}, {}, {}
 for root,count,kind,pin in [(BASE_COMP,70,'phase14_compatibility_checked',BASE_RESULTS[1]),(BASE,190,'phase14_primary_checked',BASE_RESULTS[0])]:
  assert digest(at(root+'/result.json')) == pin
  inv,done = read(root+'/inventory.json'),read(root+'/completed.json')
  assert at(root+'/inventory.json') == prior['path:'+root+'/inventory.json']
  assert at(root+'/completed.json') == prior['path:'+root+'/completed.json']
  assert len(inv['modules']) == len(done) == count
  for row in inv['modules']:
   m=row['module']
   if m in old: assert (row['source_sha256'],row['imports'],done[m]['object_sha256']) == (oldrows[m]['source_sha256'],oldrows[m]['imports'],old[m]['object_sha256'])
   old[m],oldrows[m],oldkind[m]=done[m],row,kind
 assert len(old)==207
 tool=read(BASE+'/toolchain.json');compiler=tool['lean']['path']
 assert tool==read(BASE_COMP+'/toolchain.json')==read(OLD+'/toolchain.json')
 supervisor=ROOT+'/'+FORMAL+'verification/k215/lean/build.py'
 binary={v['path']:v['sha256']for k,v in tool.items()if k in {'lean','lake','Init.olean'}}
 for root in [OLD,BASE,BASE_COMP]:
  binary.update({root+'/objects/'+m.replace('.','/')+'.olean':r['object_sha256']for m,r in read(root+'/completed.json').items()})
 ref=json.loads(members['review/basis-reference.json'])
 binary.update({str(PurePosixPath(ROOT)/ref['repository_relative_directory']/n):r['sha256']for n,r in ref['files'].items()})
 freeze_check(PREP,FREEZE,read,at)
 assert digest(at(PREP+'/build.py'))==DRIVER and digest(at(PREP+'/producer-boundary.json'))==BOUNDARY
 boundary=read(PREP+'/producer-boundary.json')
 for p,pin in boundary['present_inputs'].items(): assert (binary[p]if p in binary else digest(at(p)))==pin
 assert set(boundary['absent_inputs'])=={ROOT+'/'+p for p in RETAINED_ABSENCES+[CREATED]}
 assert {str(PurePosixPath(p).relative_to(ROOT)):v for p,v in boundary['accepted_five_files'].items()} == {p:v for p,v in PRIOR_ADOPTIONS.items()if p not in PRIOR_WRITES}
 for root,pin in cfg['retry_freezes'].items(): freeze_check(root,pin,read,at)
 assert set(cfg['retry_freezes'])=={RETRY,CLIENT_RETRY}
 # Original maps stay raw. The first correction changes only KQ1ZF/Dense;
 # the second correction changes only the quotient client's opens.
 plans=[read(p)for p in [PREP+'/primary-map.json',RETRY+'/primary-map.json',CLIENT_RETRY+'/primary-map.json']]
 by=[{r['module']:r for r in p['modules']}for p in plans]
 assert set(by[1])-set(by[0])=={P+'KQ1ZF'} and not set(by[0])-set(by[1])
 assert all(by[0][m]==by[1][m]for m in by[0]if m!=P+'KDenseBridge')
 assert {k:v for k,v in plans[0].items()if k not in {'modules','expected'}} == {k:v for k,v in plans[1].items()if k not in {'modules','expected'}}
 corrected=json.loads(json.dumps(plans[1]));q=next(r for r in corrected['modules']if r['module']=='QuotientSharing15Api')
 q['source']=by[2]['QuotientSharing15Api']['source'];q['source_sha256']=by[2]['QuotientSharing15Api']['source_sha256']
 assert corrected==plans[2]
 assert q['source_sha256']=='de617903b04e5bad6e30587fdc5a490ead6fd35c271cc439e8146bb15a3df657'
 assert at(q['source']).replace(b'open SetTheory SetTheory.BusyBeaver.ZFC',b'open SetTheory.BusyBeaver.ZFC').replace(b'ProfileModel ProfileCollection',b'ProfileModel')==at(by[1]['QuotientSharing15Api']['source'])
 for root in [RETRY,CLIENT_RETRY]: assert at(root+'/compatibility-template.json')==at(PREP+'/compatibility-template.json')
 successful={}; inventories={}; closures_by={}; summaries={}
 def run_check(root,targets,count,partial=None,secondary=None):
  before=read(root+'/before.json');inv=read(root+'/inventory.json');done=read(root+'/completed.json')
  entries,closures=h.graph(inv['modules'],targets)
  assert before['rows']==inv['modules'] and before['targets']==inv['targets']==targets
  assert before['external_imports']==inv['external_imports']==explicit_externals(inv['modules'])
  assert len(entries)==count and read(root+'/toolchain.json')==tool and before['runner_sha256']==DRIVER
  assert before['audit_endpoint']==(root!=COMP)
  assert before['inputs'][supervisor]=='a3cf7cc38004bca5e2a2df10c607fe5353896c0454069b4ff24d6b5176c32fbd'
  for p,pin in before['inputs'].items(): assert (binary[p]if p in binary else digest(at(p)))==pin,p
  assert before['absent_inputs']==boundary['absent_inputs']
  changed={m for m,r in entries.items()if m not in oldrows or (r['source_sha256'],r['imports'])!=(oldrows[m]['source_sha256'],oldrows[m]['imports'])}
  forced={m for m in entries if closures[m]&changed}
  assert sorted(changed)==before['changed_sources'] and sorted(forced)==before['force_basis_rebuild']
  plan=read(cfg['maps'][root]);ps={r['module']:r for r in plan['modules']}
  assert before['inputs'][cfg['maps'][root]]==digest(at(cfg['maps'][root]))
  assert plan['expected']=={'modules':[r['module']for r in inv['modules']],'changed':sorted(changed),'forced':sorted(forced)}
  assert set(done)==({r['module']for r in inv['modules'][:partial]}if partial is not None else set(entries))
  if root in [SECOND,MAIN]:
   prev=FIRST if root==SECOND else SECOND
   for m,r in successful[prev].items():
    exact_resume(done[m],r);assert entries[m]==inventories[prev][m]
  kinds={k:set()for k in ['candidate_fresh','phase14_primary_checked','phase14_compatibility_checked','secondary_checked']}
  objects={m:r['object_sha256']for m,r in done.items()};warn={k:0 for k in kinds};found_by={}
  for m,r in done.items():
   row=entries[m];log=at(r['log']);found=reports(log);origin=r['origin'];assert origin in kinds;kinds[origin].add(m)
   assert digest(at(row['source']))==row['source_sha256']==r['source_sha256'] and h.imports(at(row['source']))==row['imports']
   assert r['dependencies']=={d:objects[d]for d in row['imports']if d!='Init'}
   assert r['status']=='PASS'and r.get('exit_code',0)==0 and not r.get('timed_out',False)and digest(log)==r['log_sha256']
   warn[origin]+=log.decode().count('warning:')
   if found:found_by[m]=[[n,sorted(a)]for n,a in profiles(found)]
   if origin=='candidate_fresh':
    owner=COMP if root==COMP else (FIRST if m in successful.get(FIRST,{}) else SECOND if m in successful.get(SECOND,{}) else root)
    src=owner+'/workspace/'+m.replace('.','/')+'.lean';obj=owner+'/objects/'+m.replace('.','/')+'.olean'
    assert r['source']==src and digest(at(src))==row['source_sha256']
    assert r['command']==[compiler,'-j1','-M12288','--root='+owner+'/workspace','-o',obj,src]
    assert r['timeout_seconds']==120 and r['memory_mebibytes']==12288 and r['compiler_sha256']==tool['lean']['sha256'] and r['helper_sha256']==before['inputs'][supervisor]
    assert read(str(PurePosixPath(r['log']).parent/'record.json'))==r
    assert at(str(PurePosixPath(r['log']).parent/PurePosixPath(src).name))==at(src)
    assert r['reports']==[list(x)for x in found]and r['warnings']==log.decode().count('warning:')and 0<=r['seconds']<=150
   else:
    previous,prevrows=(successful[MAIN],inventories[MAIN])if origin=='secondary_checked'else(old,oldrows)
    exact_reuse(r,previous[m],origin);same_source_closure(entries,prevrows,closures[m])
    if origin!='secondary_checked':assert m not in forced and origin==oldkind[m]
   if m in ps:
    p=ps[m];assert p['source_sha256']==row['source_sha256']and p['imports']==row['imports']and p['before_sha256']==oldrows.get(m,{}).get('source_sha256')
    if 'reports'in p:
     named_reports(log,p['reports'],p.get('report_axioms'))
     if m in OLD_API+CLIENTS: assert row['source_sha256']==oldrows[m]['source_sha256']and profiles(found)==profiles(reports(at(old[m]['log'])))
     if m in NEW_API:assert found_by[m]==cfg['new_api_profiles'][m]
  if partial is not None:
   failing='BusyBeaver.ZFC.KQ1ZF'if root==FIRST else 'QuotientSharing15Api'
   assert inv['modules'][partial]['module']==failing
   assert [len(v)for v in kinds.values()]==([19,68,0,0]if root==FIRST else[44,149,0,0])
   failpath=root+'/attempts/'+('020-BusyBeaver.ZFC.KQ1ZF'if root==FIRST else'026-QuotientSharing15Api')+'/record.json'
   failure=read(failpath);log=at(failure['log']);src=root+'/workspace/'+failing.replace('.','/')+'.lean';obj=root+'/objects/'+failing.replace('.','/')+'.olean'
   assert failure['module']==failing and failure['status']=='FAIL'and failure['exit_code']==1 and failure['object_sha256']is None and not failure['timed_out']
   assert digest(log)==failure['log_sha256']and b'error:'in log and b'sorryAx'in log
   assert digest(at(src))==entries[failing]['source_sha256']==failure['source_sha256']
   assert failure['dependencies']=={d:objects[d]for d in entries[failing]['imports']if d!='Init'}
   assert failure['command']==[compiler,'-j1','-M12288','--root='+root+'/workspace','-o',obj,src]
   assert failure['timeout_seconds']==120 and failure['memory_mebibytes']==12288 and failure['compiler_sha256']==tool['lean']['sha256']
   result=None
  else:
   result=read(root+'/result.json');assert digest(at(root+'/result.json'))==cfg['results'][root]
   assert result['status']=='PASS'and result['selected_project_modules']==count and result['targets']==targets
   assert result['inventory_sha256']==digest(at(root+'/inventory.json'))and result['completed_sha256']==digest(at(root+'/completed.json'))
   assert result['source_changed_modules']==sorted(changed)and result['force_basis_rebuild_modules']==sorted(forced)
   assert result['basis_reuse_rejects_transitive_source_changes']and result['secondary_reuse_requires_exact_transitive_sources_and_imports']
   assert result['retained_retirements']==boundary['retained_retirements']and result['retired_modules_absent_from_candidate']==[P+'KProfileTC']
   assert result['map_sha256']==digest(at(cfg['maps'][root]))and result['runner_sha256']==DRIVER and result['producer_boundary_sha256']==BOUNDARY
   assert result['basis_result_sha256']==BASE_RESULTS[0]and result['compatibility_basis_result_sha256']==BASE_RESULTS[1]
   for kind,key in [('candidate_fresh','fresh_modules'),('phase14_primary_checked','phase14_primary_reused_modules'),('phase14_compatibility_checked','phase14_compatibility_reused_modules'),('secondary_checked','secondary_reused_modules')]:assert set(result[key])==kinds[kind]
   assert [len(v)for v in kinds.values()]==([45,149,0,0]if root==MAIN else[6,0,11,54])
   if root==MAIN:assert forced==kinds['candidate_fresh']and changed=={P+PurePosixPath(p).stem for p in ADOPTIONS if p.endswith('.lean')}|set(NEW_API)
   else:
    assert plan=={**read(CLIENT_RETRY+'/compatibility-template.json'),'reuse_ledger':plan['reuse_ledger']}
    pins=plan['reuse_ledger'];assert pins['directory']==MAIN
    for n in ['result.json','inventory.json','completed.json']:assert pins[n]==digest(at(MAIN+'/'+n))
   audits=result['audits'];assert [r['module']for r in audits]==(list(AUDIT_NAMES)if root==MAIN else[])
   baseline_audits={r['module']:r for r in read(BASE+'/result.json')['audits']}
   for r in audits:
    m=r['module'];q=root+'/audit-'+m;log=at(r['log']);found=named_reports(log,AUDIT_NAMES[m])
    assert profiles(found)==profiles(reports(at(baseline_audits[m]['log'])))
    assert r['status']=='PASS'and r['exit_code']==0 and not r['timed_out']and r['named_reports']==[list(x)for x in found]
    assert digest(at(r['source']))==digest(at(q+'/'+m+'.lean'))==r['source_sha256']==AUDIT_PINS[m]
    assert digest(log)==r['log_sha256']and r['dependencies']==objects
    assert r['command']==[compiler,'-j1','-M12288','--root='+q,'-o',q+'/'+m+'.olean',q+'/'+m+'.lean']
    assert r['compiler_sha256']==tool['lean']['sha256']and r['timeout_seconds']==120 and r['memory_mebibytes']==12288
    assert read(q+'/'+m+'.json')==r
  outer=read(EXEC+'/'+PurePosixPath(root).name+'-outer.json')
  argv=['python3','-B',PREP+'/build.py','--out',root,'--map',cfg['maps'][root]]
  if root==COMP:argv+=['--reuse',MAIN]
  for target in targets:argv+=['--target',target]
  if root!=COMP:argv+=['--audit-endpoint']
  assert outer['argv']==argv and outer['cwd']==ROOT and outer['exit_code']==(1 if partial is not None else 0)and outer['frozen_files_unchanged']
  assert outer['status']==('FAIL_OUTER_EXIT'if partial is not None else'PASS_OUTER_EXIT_ZERO')
  assert digest(at(cfg['outer_wrappers'][PurePosixPath(root).name]))==outer['wrapper_sha256']
  for k in ['stdout','stderr']:assert digest(at(outer[k]))==outer[k+'_sha256']
  successful[root],inventories[root],closures_by[root]=done,entries,closures
  binary.update({root+'/objects/'+m.replace('.','/')+'.olean':r['object_sha256']for m,r in done.items()})
  summaries[root]={'providers':len(done),'fresh':len(kinds['candidate_fresh']),'warnings_by_origin':warn,'report_profiles':found_by,'result_sha256':None if partial is not None else digest(at(root+'/result.json'))}
  return result
 run_check(FIRST,TARGETS,194,87)
 run_check(SECOND,TARGETS,194,193)
 run_check(MAIN,TARGETS,194)
 run_check(COMP,CLIENTS,71,secondary=True)
 for directory,previous,new,n,fresh,oldcount in [(RETRY,FIRST,SECOND,87,19,68),(CLIENT_RETRY,SECOND,MAIN,193,44,149)]:
  init=read(directory+'/initialization-result.json')
  assert init['status']=='VALIDATED_PARTIAL_PROVIDER_RESUME_NOT_PRIMARY_PASS'and init['original_result_absent']and not init['compiler_invoked']
  assert init['resumed_providers']==n and init['prior_successful_fresh_invocations']==fresh and init['prior_phase14_reused_providers']==oldcount
  assert init['new_completed_sha256']==init['original_completed_sha256']==digest(at(previous+'/completed.json'))
  for name,root in [('original',previous),('new',new)]:
   for key in ['before','inventory']:assert init[name+'_'+key+'_sha256']==digest(at(root+'/'+key+'.json'))
  assert init['new_map_sha256']==digest(at(directory+'/primary-map.json'))and init['runner_unchanged_sha256']==DRIVER and init['initializer_sha256']==digest(at(directory+'/initialize.py'))
 entries=inventories[MAIN];cent=inventories[COMP];project=(set(entries)|set(cent))-set(API+CLIENTS)
 assert len(project)==199 and project==(set(oldrows)-set(OLD_API+CLIENTS))|{P+'PowerSets'}
 endpoint=closures_by[MAIN][TARGETS[0]];prefix=closures_by[MAIN][TARGETS[1]]-endpoint
 assert len(endpoint)==176 and len(prefix)==5 and len(set(entries)-set(API))==184
 sites=sorted(m for m in entries if m.startswith(P+'KSites215Batch'));assert len(sites)==9
 for m in sites:exact_reuse(successful[MAIN][m],old[m],'phase14_primary_checked')
 assert sum(len(summaries[MAIN]['report_profiles'][m])for m in OLD_API)==34
 assert sum(len(summaries[MAIN]['report_profiles'][m])for m in NEW_API)==28
 assert sum(len(summaries[COMP]['report_profiles'][m])for m in CLIENTS)==10
 validate_adoption(cfg,read,at,members,entries,cent,oldrows,project,current_repo)
 controls=json.loads(members['review/controls-result.json']);assert controls['status']=='PASS_METADATA_ONLY'and all(r['matched']for r in controls['checks'])
 assert controls['inputs']=={n:digest(members['review/'+n])for n in ['packet.py','controls.py']}
 return {'status':'PASS_SAVED_PHASE15_RECORDS','runs':summaries,'primary_providers':194,'primary_project_modules':184,'endpoint_modules':176,'prefix_modules':5,'intentional_full_calibration_extras':3,'api_clients':10,'old_api_reports':34,'new_api_reports':28,'endpoint_clients':2,'endpoint_reports':10,'compatibility_providers':71,'compatibility_project_modules':69,'compatibility_clients':2,'compatibility_reports':10,'combined_project_modules':199,'selected_fresh_by_primary_attempt':[19,25,1],'primary_phase14_reuse':149,'compatibility_fresh':6,'compatibility_primary_reuse':54,'compatibility_phase14_reuse':11,'failed_attempts_retained':2,'unchanged_site_batches':sites,'phase14_archive_sha256':checked['archive_sha256'],'current_sources_checked':current_repo is not None,'adopted_files':ADOPTIONS,'retained_absences':RETAINED_ABSENCES,'scope':'Recorded Lean source/import/object-hash/log/command provenance; two failed attempts excluded. Saved reader does not check live objects or invoke a compiler/producer. Nine physical site batches remain exact inherited checks.'}
def validate_adoption(cfg,read,at,members,entries,cent,oldrows,project,current_repo):
 receipt=read(cfg['adoption']['receipt']);assert receipt==cfg['adoption']['raw']
 assert receipt['status']=='ADOPTED_EXACT_CHECKED_PHASE15'and receipt['source_writes']==9 and receipt['producer_writes']==1 and receipt['retirements']==0
 current=read(cfg['root_current_review']);assert current['status']=='PASS_CURRENT_PHASE15_ADOPTION'and current['adoption_sha256']==digest(at(cfg['adoption']['receipt']))
 actual=read(cfg['root_actual_review']);assert actual['status']=='PASS_ROOT_RAW_PHASE15_ACTUAL'
 for k,root in [('primary',MAIN),('compatibility',COMP)]:assert actual[k]['directory']==root and actual[k]['result_sha256']==digest(at(root+'/result.json'))
 assert {m:r['sha256']for m,r in actual['sources'].items()}=={m:(entries|cent)[m]['source_sha256']for m in project}
 rows=receipt['files'];assert len(rows)==10
 assert {r['path']:r['after_sha256']for r in rows}==ADOPTIONS
 assert {r['path']for r in rows if r['action']=='create'}=={CREATED}
 assert all(r['action']=='replace'for r in rows if r['path']!=CREATED)
 assert set(cfg['historical_inputs'])=={ROOT+'/'+p for p in ADOPTIONS if p!=CREATED}
 for r in rows:
  target=r['path'];assert digest(members['adoption/'+target])==r['after_sha256']
  assert members['adoption/'+target]==at(r['candidate'])
  if target==CREATED:assert r['before_sha256']is None and r['before_snapshot']is None
  else:
   snapshot=str(PurePosixPath(ROOT)/r['before_snapshot'])
   assert digest(at(snapshot))==digest(at(ROOT+'/'+target))==r['before_sha256']
   assert cfg['historical_inputs'][ROOT+'/'+target]=={'snapshot':snapshot,'sha256':r['before_sha256']}
  if target.endswith('.lean'):
   m=P+PurePosixPath(target).stem;assert (entries|cent)[m]['source_sha256']==r['after_sha256']
   assert oldrows.get(m,{}).get('source_sha256')==r['before_sha256']
  if current_repo is not None:assert sha(Path(current_repo)/target)==r['after_sha256']
 for path,pin in PRIOR_ADOPTIONS.items():
  assert digest(at(ROOT+'/'+path))==pin
  if current_repo is not None:assert sha(Path(current_repo)/path)==pin
 if current_repo is not None:
  for p in RETAINED_ABSENCES:absent(Path(current_repo)/p)
  roots=['Computability/BusyBeaver/Lean','SetTheory/Lean']
  # The exact per-module canonical paths are independently bound by the owned
  # root current-source receipt; no guess about a duplicate search root.
  current=cfg['project_source_paths'];assert set(current)==project
  for m,p in current.items():
   assert not PurePosixPath(p).is_absolute()and '..'not in PurePosixPath(p).parts
   assert sha(Path(current_repo)/p)==(entries|cent)[m]['source_sha256']
 reproduce=read(cfg['reproduction']);assert reproduce['status']=='PASS_TWO_AUTHORIZED_MAINTAINED_PRODUCER_REPRODUCTIONS'
 assert reproduce['baseline_drift']=={} and reproduce['candidate_model_exact']and reproduce['other_five_outputs_exact_baseline']and reproduce['all_original_frozen_and_canonical_inputs_unchanged']
 assert [r['kind']for r in reproduce['runs']]==['baseline','adapted']
 outputs=[]
 for r in reproduce['runs']:
  directory=r['cwd'];assert r['argv']==['python3','-B',directory+'/generate_kq1.py']and r['cap_seconds']==30 and r['exit_code']==0
  assert r['input_before']==r['input_after']and r['producer_sha256']==r['input_before']['generate_kq1.py']
  for p,pin in r['input_before'].items():assert digest(at(directory+'/'+p))==pin
  assert sorted(r['exact_added_paths'])==sorted('BusyBeaver/ZFC/'+n for n in r['outputs'])and len(r['outputs'])==6
  for n,pin in r['outputs'].items():assert digest(at(directory+'/BusyBeaver/ZFC/'+n))==pin
  for label in ['stdout','stderr']:assert digest(at(str(PurePosixPath(directory).parent/(r['kind']+'.'+label+'.txt'))))==r[label+'_sha256']
  outputs.append(r['outputs'])
 assert outputs[1]['KQ1Model.lean']==ADOPTIONS[LEAN_DIR+'KQ1Model.lean']
 assert {k:v for k,v in outputs[0].items()if k!='KQ1Model.lean'}=={k:v for k,v in outputs[1].items()if k!='KQ1Model.lean'}
 for path,pin in reproduce['before_pins'].items():assert digest(at(path))==pin
