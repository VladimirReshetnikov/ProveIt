"""Validate phase14's two recorded closures against the pinned phase13 evidence.

This reader checks records, sources, imports and raw logs. Only collect.py checks
live object bytes; neither reader invokes Lean or a supplied producer.
"""
from pathlib import Path, PurePosixPath
import hashlib, json, re
import basis

HERE = Path(__file__).resolve().parent
ROOT = '/home/codex/.codex/worktrees/ec20/Proofs'
PREP = '/tmp/k215-phase14-check'
EXEC = '/tmp/k215-phase14-execution'
FIRST, MAIN, COMP = PREP + '/primary-run1', PREP + '/primary-run2', PREP + '/compatibility-run1'
RETRY = '/tmp/k215-phase14-retry'
BASE = '/tmp/k215-phase13-upstream-check/primary-run1'
BASE_COMP = '/tmp/k215-phase13-upstream-check/compatibility-run1'
OLD = '/tmp/k215-proof-phase8/lean-run1'
DRIVER = '5238f2f5cdb826450cb1488a874e291654614e67ec31fdbb2e9a26c0d688b293'
FREEZE = 'b74517e2f8cab00ddf2bc4a9e8667161036a517e1569233f8a5ff8b0a7accc65'
BOUNDARY = 'e4cacf2d74a378b33624d5035233e02f93b112e59ef52f569a62c155d8941387'
RETRY_FREEZE = 'cf22ecb2057efdcdf3035b932153ed399d2f278c6f19d07d18301a0f13554dee'
BASE_RESULTS = ['00a44b3ce690bfcd397f53275c2dcec69d25423de8e029086b0aefe020fb397e', 'bd9e50bce1c8a463719d83c201f402dad3edd89c0621ae827082b75638a3c74f']
P = 'BusyBeaver.ZFC.'
NS = 'SetTheory.' + P
OLD_API = ['GenericShared13Api', 'NumericCD52Api', 'LukasShared13Api']
NEW_API = ['DerivedRows14Api', 'ThmKDerived14Api', 'KEindDerived14Api', 'ProfileTC14Api']
API = OLD_API + NEW_API
CLIENTS = ['WFModelCompat12', 'ZFNativeCompat12']
TARGETS = [P + 'KEndpoint215', P + 'KDecoderPrefix215'] + API
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
PQ = {'propext', 'Quot.sound'}
AUDIT_NAMES = {
 'EndpointAudit215': ['EndpointAudit215.blank_halts_exactly_when_zfc_has_a_finite_refutation', 'EndpointAudit215.nonhalting_exactly_when_zfc_is_consistent'],
 'K215Audit': [NS + 'KEndpoint215.blank_halts_iff_zfc_refutation', NS + 'KEndpoint215.nonhalting_iff_zfc_consistency', NS + 'KDense215.commutes', NS + 'KBoot215.boot', NS + 'KSites215.covered', NS + 'KEndpoint215.p215_boot_iff', 'K215Audit.blank_halts_exact', 'K215Audit.nonhalting_exact']}
AUDIT_PINS = {'EndpointAudit215': 'd13596021774c5b26937b13cf6cca58342af99f59626b9205ff10b9df1e6fc7d', 'K215Audit': '9144acc6c597c4a53928fc62be00d5e25d9f32f519797d17a5058d03b5460986'}
LEAN_DIR = 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/'
FORMAL = 'Computability/BusyBeaver/Research/ZFC/k225-formal/'
PRIOR_ADOPTIONS = {
 LEAN_DIR + 'DominatedImplication.lean': 'bd07364a829e8a1535b0ecf1ee6ed0c292d5af35e01a6db8f152dd2610e247d8',
 LEAN_DIR + 'Lukasiewicz.lean': '7d443a733b5c5ddd0d49728cf1ea7d855dd445f156934c13578bacc008c59874',
 FORMAL + 'generate_dominated_implication_lean.py': 'ebcbb86642d4d389748451dc662b42f7ac62e7aa4b235bbf4e5d8e5a1ec5c1e9',
 FORMAL + 'rho8cd/derivation_core.txt': '4141248ed90a6813c07f274351336963acde1d82f6ea463a33e5f7d64bed8005',
 FORMAL + 'rho8cd/generate_domrho8_cd.py': '63da860d3a957010c53d783a2b8995acef3d8e3806823f24fc5833738dc1d56a'}
ADOPTIONS = {LEAN_DIR + n + ".lean": p for n,p in {'TarskiDerived': 'af15c7f2946d2d2f335d540acc33f69afca4bd884cf4dfe7bfcbc323707e4b19', 'TarskiLeibniz': 'bf57b911ce313037bce71ef6f680a36bb54ce7be9d504d6533c612bd4d9831e7', 'KThmK': '396779f2da512975580d8a34e322cd589fbf22c33018cfd5b389b99c4398b4dc', 'KEind222': '090f7bbb58295d186f9dd10ee86041f8b65d2f4ebea6d496bafdd88f2d56b507', 'CompositionModel': 'ffcd2758db64f989424fc915f9d881ad5106befac0e99875c890e07932d6913e', 'KLowerEqv': '7d8646d8e043223a1653456d44138053e347517b30b21f3989ec326376cc7d12', 'ProfileComposition': '2d2af6f596cef80f52c8463a40089be53f55d3b7c0d5ecc09742180a6e00f8cf'}.items()}
RETIRED = {
 LEAN_DIR+"KProfileTC.lean": "0d344c2298abf0e6d998179b61baeab9b0226cc49c365552ef94de258417c173",
 FORMAL+"generate_profile_tc.py": "bf307e9a953a24f7303786e30f23c53f34b81519e794748d118e4403692b9822"}

NEW_PROFILES = {'DerivedRows14Api': [['DerivedRows14Api.deduction', ['propext']], ['DerivedRows14Api.vacuity', ['propext']], ['DerivedRows14Api.atomic_rewrite', ['propext']]], 'ThmKDerived14Api': [['ThmKDerived14Api.reflexivity', ['propext']], ['ThmKDerived14Api.leibniz', ['propext']], ['ThmKDerived14Api.specialization', ['propext', 'Classical.choice', 'Quot.sound']], ['ThmKDerived14Api.alpha', ['propext', 'Classical.choice', 'Quot.sound']]], 'KEindDerived14Api': [['KEindDerived14Api.interpretation', ['propext', 'Classical.choice', 'Quot.sound']], ['KEindDerived14Api.completeness', ['propext', 'Classical.choice', 'Quot.sound']]], 'ProfileTC14Api': [['SetTheory.BusyBeaver.ZFC.ProfileTC14Api.strong_to_transitive', []], ['SetTheory.BusyBeaver.ZFC.ProfileTC14Api.from_transitive', ['propext', 'Classical.choice', 'Quot.sound']], ['SetTheory.BusyBeaver.ZFC.ProfileTC14Api.from_containers', ['propext', 'Classical.choice', 'Quot.sound']], ['SetTheory.BusyBeaver.ZFC.ProfileTC14Api.tag_trans', ['propext', 'Classical.choice', 'Quot.sound']], ['SetTheory.BusyBeaver.ZFC.ProfileTC14Api.tag_ext', ['propext', 'Classical.choice', 'Quot.sound']]]}

BINARY = {'.olean', '.ilean', '.o', '.so', '.a', '.vo', '.vos', '.vok', '.glob', '.pyc', '.pyo'}
HELPERS = ['basis.py', 'basis-reference.json', 'packet.py', 'collect.py', 'review_saved.py', 'controls.py', 'README.md']

def digest(data): return hashlib.sha256(data).hexdigest()
def sha(path): return digest(Path(path).read_bytes())
def dump(value): return (json.dumps(value, indent=2) + '\n').encode()
def safe(name):
 p = PurePosixPath(name)
 assert name and not p.is_absolute() and '..' not in p.parts and str(p) == name
 assert not set(p.suffixes) & (BINARY | {'.gz', '.zip', '.tar'})
def absent(path): assert not Path(path).exists() and not Path(path).is_symlink()
def manifest(data): return {n: {'sha256': digest(b), 'bytes': len(b)} for n, b in sorted(data.items())}
def resolve_routes(members, prior, routes):
 result = {}
 for path, row in routes.items():
  assert PurePosixPath(path).is_absolute() and set(row) == {'storage', 'key', 'sha256', 'bytes'}
  assert row['storage'] in {'packet', 'phase13'}
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

def validate(members, repo, basis_data=None, current_repo=None):
 for name in members: safe(name)
 prior, checked, h = basis.load(repo) if basis_data is None else basis_data
 assert members['review/basis-reference.json'] == (HERE / 'basis-reference.json').read_bytes()
 resolved = resolve_routes(members, prior, json.loads(members['path-map.json']))
 at = lambda path: resolved[str(path)]
 read = lambda path: json.loads(at(path))
 cfg = json.loads(members['review/config.json'])
 assert cfg['status'] == 'FROZEN_COMPLETED_PHASE14_INPUTS'
 for path, row in cfg['files'].items():
  assert digest(at(path)) == row['sha256'] and len(at(path)) == row['bytes']
 old, oldrows, oldkind = {}, {}, {}
 for root, count, kind, pin in [(BASE_COMP, 70, 'phase13_compatibility_checked', BASE_RESULTS[1]), (BASE, 187, 'phase13_primary_checked', BASE_RESULTS[0])]:
  assert digest(at(root + '/result.json')) == pin
  inv = read(root + '/inventory.json'); done = read(root + '/completed.json')
  assert at(root + '/inventory.json') == prior['path:' + root + '/inventory.json']
  assert at(root + '/completed.json') == prior['path:' + root + '/completed.json']
  assert len(inv['modules']) == len(done) == count
  for row in inv['modules']:
   m = row['module']
   if m in old: assert (row['source_sha256'], row['imports'], done[m]['object_sha256']) == (oldrows[m]['source_sha256'], oldrows[m]['imports'], old[m]['object_sha256'])
   old[m], oldrows[m], oldkind[m] = done[m], row, kind
 assert len(old) == len(oldrows) == 204
 tool = read(BASE + '/toolchain.json'); compiler = tool['lean']['path']
 assert tool == read(BASE_COMP + '/toolchain.json') == read(OLD + '/toolchain.json')
 helper = ROOT + '/' + FORMAL + 'verification/k215/lean/build.py'
 binary = {v['path']: v['sha256'] for k, v in tool.items() if k in {'lean', 'lake', 'Init.olean'}}
 for root in [OLD, BASE, BASE_COMP]:
  binary.update({root + '/objects/' + m.replace('.', '/') + '.olean': r['object_sha256'] for m, r in read(root + '/completed.json').items()})
 freeze = read(PREP + '/freeze.json'); assert digest(at(PREP + '/freeze.json')) == FREEZE
 for name, pin in freeze['files'].items(): assert digest(at(PREP + '/' + name)) == pin
 boundary = read(PREP + '/producer-boundary.json'); assert digest(at(PREP + '/producer-boundary.json')) == BOUNDARY
 allplans = {}
 for path in [RETRY+'/primary-map.json', PREP+'/compatibility-template.json']:
  for r in read(path)['modules']:
   if r['module'] in allplans: assert allplans[r['module']] == r
   allplans[r['module']] = r
 assert len(allplans) == 19
 assert cfg['new_api_profiles'] == NEW_PROFILES
 resumed = check_resume(read, at, h, tool, binary, cfg)
 def run_check(root, targets, count, secondary=None):
  result = read(root + '/result.json'); before = read(root + '/before.json')
  inv = read(root + '/inventory.json'); done = read(root + '/completed.json')
  assert digest(at(root + '/result.json')) == cfg['results'][root]
  assert result['status'] == 'PASS' and result['selected_project_modules'] == count
  assert result['targets'] == inv['targets'] == before['targets'] == targets and before['rows'] == inv['modules']
  assert before['external_imports'] == inv['external_imports'] == explicit_externals(inv['modules'])
  assert before['audit_endpoint'] == (secondary is None) and read(root + '/toolchain.json') == tool
  assert digest(at(root + '/inventory.json')) == result['inventory_sha256']
  assert digest(at(root + '/completed.json')) == result['completed_sha256']
  entries, closures = h.graph(inv['modules'], targets)
  if root == MAIN:
   for m,r in resumed.items(): exact_resume(done[m],r)
   assert set(done)-set(resumed) == {'ProfileTC14Api'}
  assert len(entries) == len(done) == count and set(entries) == set(done)
  changed = {m for m, r in entries.items() if m not in oldrows or (r['source_sha256'], r['imports']) != (oldrows[m]['source_sha256'], oldrows[m]['imports'])}
  forced = {m for m in entries if closures[m] & changed}
  assert sorted(changed) == before['changed_sources'] == result['source_changed_modules']
  assert sorted(forced) == before['force_basis_rebuild'] == result['force_basis_rebuild_modules']
  assert result['basis_reuse_rejects_transitive_source_changes'] and result['secondary_reuse_requires_exact_transitive_sources_and_imports']
  kinds = {'candidate_fresh': set(result['fresh_modules']), 'phase13_primary_checked': set(result['phase13_primary_reused_modules']), 'phase13_compatibility_checked': set(result['phase13_compatibility_reused_modules']), 'secondary_checked': set(result['secondary_reused_modules'])}
  assert set().union(*kinds.values()) == set(entries) and sum(map(len, kinds.values())) == count
  if secondary is None:
   assert [len(v) for v in kinds.values()] == [66, 124, 0, 0] and forced == kinds['candidate_fresh']
   assert changed == {P+PurePosixPath(p).stem for p in ADOPTIONS} | set(NEW_API)
   assert set(entries) == ({r['module'] for r in read(BASE + '/inventory.json')['modules']} - {P+'KProfileTC'}) | set(NEW_API)
  else:
   assert [len(v) for v in kinds.values()] == [16, 0, 1, 53]
   assert kinds['phase13_compatibility_checked'] == {P+'Dag254'} and len(forced) == 42
   assert changed == {P+n for n in ['ProfileComposition','CompositionModel','TarskiDerived','TarskiLeibniz']}
   assert set(entries) == {r['module'] for r in read(BASE_COMP + '/inventory.json')['modules']}
  maps = [p for p, pin in before['inputs'].items() if pin == result['map_sha256']]; assert len(maps) == 1
  plan = read(maps[0]); plans = {r['module']: r for r in plan['modules']}
  assert len(plans) == len(plan['modules'])
  for m, r in plans.items():
   assert all(r[k] == v for k, v in allplans[m].items())
   assert set(r) - set(allplans[m]) <= {'report_axioms'}
   if m == 'LukasShared13Api': assert [set(a) for a in r['report_axioms']] == [set()]*7 + [STANDARD]
   if m == 'WFModelCompat12': assert [set(a) for a in r['report_axioms']] == [STANDARD]*3
   if m == 'ZFNativeCompat12': assert [set(a) for a in r['report_axioms']] == [PQ]+[STANDARD]*6
  assert plan['expected'] == {'modules': [r['module'] for r in inv['modules']], 'changed': sorted(changed), 'forced': sorted(forced)}
  if secondary is not None:
   pins = plan['reuse_ledger']; assert pins['directory'] == MAIN
   for name in ['result.json', 'inventory.json', 'completed.json']: assert pins[name] == digest(at(MAIN + '/' + name))
  assert result['basis_result_sha256'] == BASE_RESULTS[0] and result['compatibility_basis_result_sha256'] == BASE_RESULTS[1]
  assert result['producer_boundary_sha256'] == BOUNDARY
  assert result['runner_sha256'] == before['runner_sha256'] == DRIVER == digest(at(PREP + '/build.py'))
  assert before['inputs'][helper] == 'a3cf7cc38004bca5e2a2df10c607fe5353896c0454069b4ff24d6b5176c32fbd'
  objects = {m: r['object_sha256'] for m, r in done.items()}
  warnings = {k: 0 for k in kinds}; report_counts = {k: 0 for k in kinds}; report_profiles = {}
  for m, row in entries.items():
   rec = done[m]; source = at(row['source']); log = at(rec['log']); text = log.decode(); found = reports(log); origin = rec['origin']
   assert m in kinds[origin] and digest(source) == row['source_sha256'] == rec['source_sha256'] and h.imports(source) == row['imports']
   assert rec['dependencies'] == {d: objects[d] for d in row['imports'] if d != 'Init'}
   assert rec['status'] == 'PASS' and rec.get('exit_code', 0) == 0 and not rec.get('timed_out', False) and digest(log) == rec['log_sha256']
   warnings[origin] += text.count('warning:'); report_counts[origin] += len(found)
   if found: report_profiles[m] = [[n, sorted(a)] for n, a in profiles(found)]
   if origin == 'candidate_fresh':
    compiled_root = FIRST if root == MAIN and m in resumed else root
    src = compiled_root + '/workspace/' + m.replace('.', '/') + '.lean'; obj = compiled_root + '/objects/' + m.replace('.', '/') + '.olean'
    assert rec['timeout_seconds'] == 120 and rec['memory_mebibytes'] == 12288
    assert rec['compiler_sha256'] == tool['lean']['sha256'] and rec['helper_sha256'] == before['inputs'][helper]
    assert rec['command'] == [compiler, '-j1', '-M12288', '--root='+compiled_root+'/workspace', '-o', obj, src]
    assert rec['source'] == src and digest(at(src)) == row['source_sha256']
    assert read(str(PurePosixPath(rec['log']).parent / 'record.json')) == rec
    assert at(str(PurePosixPath(rec['log']).parent / PurePosixPath(src).name)) == source
    assert rec['reports'] == [list(x) for x in found] and rec['warnings'] == text.count('warning:')
    assert 0 <= rec['seconds'] <= rec['timeout_seconds'] + 30
   else:
    previous, prevrows = secondary if origin == 'secondary_checked' else (old, oldrows)
    exact_reuse(rec, previous[m], origin); same_source_closure(entries, prevrows, closures[m])
    if origin != 'secondary_checked': assert m not in forced and origin == oldkind[m]
   if m in plans:
    r = plans[m]; assert r['source_sha256'] == row['source_sha256'] and r['imports'] == row['imports']
    assert r['before_sha256'] == oldrows.get(m, {}).get('source_sha256')
    if 'reports' in r:
     named_reports(log, r['reports'], r.get('report_axioms'))
     if m in NEW_API: assert profiles(found) == [(name,set(ax)) for name,ax in cfg['new_api_profiles'][m]]
     if m in OLD_API + CLIENTS:
      assert row['source_sha256'] == oldrows[m]['source_sha256']
      assert profiles(found) == profiles(reports(at(old[m]['log'])))
   if current_repo is not None and m not in API + CLIENTS:
    paths = [Path(current_repo)/r/(m.replace('.', '/')+'.lean') for r in h.ROOTS if (Path(current_repo)/r/(m.replace('.', '/')+'.lean')).is_file()]
    assert len(paths) == 1 and sha(paths[0]) == row['source_sha256']
  for path, pin in before['inputs'].items(): assert (binary[path] if path in binary else digest(at(path))) == pin, path
  assert before['absent_inputs'] == sorted(r['canonical'] for r in boundary['files'] if r['current_state'] == 'absent')
  assert result['proposed_retirements'] == boundary['proposed_retirements']
  assert result['retired_modules_absent_from_candidate'] == [P+'KProfileTC'] and P+'KProfileTC' not in entries
  audits = result['audits']; assert [r['module'] for r in audits] == (list(AUDIT_NAMES) if secondary is None else [])
  for rec in audits:
   m = rec['module']; q = root + '/audit-' + m; log = at(rec['log'])
   expected = [STANDARD, STANDARD] if m == 'EndpointAudit215' else [STANDARD, STANDARD, {'propext'}, PQ, PQ, STANDARD, STANDARD, STANDARD]
   found = named_reports(log, AUDIT_NAMES[m], expected)
   assert rec['status'] == 'PASS' and rec['exit_code'] == 0 and not rec['timed_out']
   assert rec['named_reports'] == [list(x) for x in found]
   assert digest(at(rec['source'])) == digest(at(q+'/'+m+'.lean')) == rec['source_sha256'] == AUDIT_PINS[m]
   assert digest(log) == rec['log_sha256'] and rec['dependencies'] == objects
   assert rec['command'] == [compiler, '-j1', '-M12288', '--root='+q, '-o', q+'/'+m+'.olean', q+'/'+m+'.lean']
   assert rec['compiler_sha256'] == tool['lean']['sha256'] and rec['timeout_seconds'] == 120 and rec['memory_mebibytes'] == 12288
   assert read(q+'/'+m+'.json') == rec and len(rec['object_sha256']) == 64
  check_outer(root, maps[0], cfg, read, at, freeze)
  binary.update({root+'/objects/'+m.replace('.', '/')+'.olean': r['object_sha256'] for m, r in done.items()})
  return result, entries, closures, done, warnings, report_counts, report_profiles
 main, entries, closures, done, mwarn, mreports, mprofiles = run_check(MAIN, TARGETS, 190)
 comp, cent, cclose, cdone, cwarn, creports, cprofiles = run_check(COMP, CLIENTS, 70, (done, entries))
 project = (set(entries) | set(cent)) - set(API + CLIENTS)
 assert len(project) == 198 and project == set(oldrows) - set(OLD_API + CLIENTS) - {P+'KProfileTC'}
 endpoint = closures[TARGETS[0]]; prefix = closures[TARGETS[1]] - endpoint
 assert len(endpoint) == 178 and len(prefix) == 5 and len(set(entries)-set(API)) == 183
 sites = sorted(m for m in entries if m.startswith(P+'KSites215Batch')); assert len(sites) == 9
 for m in sites: exact_reuse(done[m], old[m], 'phase13_primary_checked')
 assert sum(len(mprofiles[m]) for m in OLD_API) == 20 and sum(len(mprofiles[m]) for m in NEW_API) == 14
 assert [ax for _, ax in mprofiles['LukasShared13Api']] == [[]]*7 + [sorted(STANDARD)]
 assert [n for n, _ in cprofiles[P+'WFTheory']] == [NS+'WFTheory.'+n for n in ['zf_consistent_of_model', 'c254_of_zf_refutation', 'c254_refutation_iff_zf', 'native_refutation_iff_zf', 'native_consistency_iff_zf']]
 assert sum(len(cprofiles[m]) for m in CLIENTS) == 10
 assert all(set(ax) == STANDARD for _, ax in cprofiles[P+'WFTheory'])
 # Original producer and derivation inputs remain historical even after adoption.
 assert boundary['phase13_primary_result_sha256'] == BASE_RESULTS[0] and boundary['phase13_compatibility_result_sha256'] == BASE_RESULTS[1]
 assert boundary['phase8_result_sha256'] == digest(at(OLD+'/result.json'))
 for key in ['producer_before_original', 'phase11_adoption', 'previous_boundary', 'phase12_adoption', 'phase12_boundary', 'phase13_adoption', 'phase13_boundary']:
  r = boundary[key]; assert digest(at(r['path'])) == r['sha256']
 for path, pin in boundary['additional_inputs'].items(): assert digest(at(path)) == pin
 for r in boundary['files']:
  for key in ['phase8_snapshot', 'historical_original']: assert digest(at(r[key])) == r['phase8_sha256']
  assert digest(at(r['phase10_snapshot'])) == r['phase10_sha256']
  if r['current_state'] == 'present':
   assert digest(at(r['current_snapshot'])) == digest(at(r['canonical'])) == r['current_sha256']
  else:
   assert r['current_state'] == 'absent' and digest(at(r['retired_snapshot'])) == r['phase10_sha256']
   if current_repo is not None: absent(Path(current_repo)/PurePosixPath(r['canonical']).relative_to(ROOT))
 # The accepted phase13 five files are unchanged; the two new retirements
 # were present compilation inputs and are saved through explicit before snapshots.
 assert {str(PurePosixPath(p).relative_to(ROOT)):v for p,v in boundary['accepted_five_files'].items()} == PRIOR_ADOPTIONS
 for p,pin in boundary['accepted_five_files'].items():
  assert digest(at(p)) == pin
  if current_repo is not None: assert sha(Path(current_repo)/PurePosixPath(p).relative_to(ROOT)) == pin
 retired = boundary['proposed_retirements']
 assert len(retired) == 2 and {str(PurePosixPath(r['canonical']).relative_to(ROOT)):r['before_sha256'] for r in retired} == RETIRED
 for r in retired:
  assert r['current_state'] == 'present_before_candidate_check' and r['proposed_state'] == 'absent_only_after_accepted_adoption'
  assert digest(at(r['canonical'])) == digest(at(r['before_snapshot'])) == r['before_sha256']
  if current_repo is not None: absent(Path(current_repo)/PurePosixPath(r['canonical']).relative_to(ROOT))
 adopted = cfg['adoption']['files']; assert len(adopted) == 9
 raw_adoption = read(cfg['adoption']['receipt'])
 assert raw_adoption['status'] == 'ADOPTED_EXACT_CHECKED_PHASE14' and raw_adoption['files'] == adopted
 assert raw_adoption['source_writes'] == 7 and raw_adoption['retirements'] == 2
 assert {r['path']:r['after_sha256'] for r in adopted if r['action']=='replace'} == ADOPTIONS
 assert {r['path']:r['before_sha256'] for r in adopted if r['action']=='retire'} == RETIRED
 root_review = read(cfg['root_review'])
 assert root_review['status'] == 'PASS_ROOT_RAW_PHASE14_ACTUAL' and root_review['distinct_project_modules'] == 198
 for key,directory in [('primary',MAIN),('compatibility',COMP)]:
  assert root_review[key]['directory'] == directory and root_review[key]['result_sha256'] == digest(at(directory+'/result.json'))
 expected_sources = {m:(entries|cent)[m]['source_sha256'] for m in project}
 assert {m:r['sha256'] for m,r in root_review['sources'].items()} == expected_sources
 for r in adopted:
  archived = ROOT+'/'+r['before_snapshot']; assert digest(at(archived)) == r['before_sha256']
  if r['action'] == 'replace':
   data = members['adoption/'+r['path']]
   assert digest(data) == r['after_sha256'] and data == at(r['candidate'])
   m = P+PurePosixPath(r['path']).stem
   assert entries[m]['source_sha256'] == r['after_sha256'] and oldrows[m]['source_sha256'] == r['before_sha256']
   if current_repo is not None: assert sha(Path(current_repo)/r['path']) == r['after_sha256']
  else:
   assert r['action'] == 'retire' and r['after_sha256'] is None and r['candidate'] is None
   if current_repo is not None: absent(Path(current_repo)/r['path'])
 assert set(cfg['historical_inputs']) == {ROOT+'/'+p for p in RETIRED}
 for path,r in cfg['historical_inputs'].items():
  target = str(PurePosixPath(path).relative_to(ROOT)); row = next(x for x in adopted if x['path']==target)
  assert r['sha256'] == row['before_sha256'] and r['snapshot'] == ROOT+'/'+row['before_snapshot'] and digest(at(path)) == r['sha256']
 controls = json.loads(members['review/controls-result.json'])
 assert controls['status'] == 'PASS_METADATA_ONLY' and controls['compiler_producer_collector_prior_reader_invoked'] is False
 assert controls['positive'] == sum(r['expected_accept'] for r in controls['checks']) and controls['negative'] == sum(not r['expected_accept'] for r in controls['checks'])
 assert all(r['matched'] for r in controls['checks'])
 assert controls['inputs'] == {'/tmp/k215-phase14-publication/'+n: digest(members['review/'+n]) for n in ['controls.py', 'packet.py']}
 assert members['review/controls.stdout.log'] == dump(controls) and not members['review/controls.stderr.log']
 for root in [MAIN, COMP]:
  before = read(root+'/before.json')
  for path, r in cfg['historical_inputs'].items():
   if path in before['inputs']: assert before['inputs'][path] == r['sha256']
 return {'status': 'PASS_SAVED_PHASE14_RECORDS', 'primary_providers': 190, 'primary_project_modules': 183, 'endpoint_modules': 178, 'prefix_modules': 5, 'primary_fresh': 66, 'primary_original_successful_fresh': 65, 'primary_retry_fresh': 1, 'original_failed_client_attempts': 1, 'primary_phase13_reuse': 124, 'api_clients': 7, 'api_reports': 34, 'old_api_reports': 20, 'new_api_reports': 14, 'core_reports': 6, 'core_axioms': [], 'endpoint_clients': 2, 'endpoint_reports': 10, 'endpoint_warnings': 0, 'primary_warnings_by_origin': mwarn, 'primary_report_counts_by_origin': mreports, 'compatibility_providers': 70, 'compatibility_project_modules': 68, 'compatibility_clients': 2, 'compatibility_fresh': 16, 'compatibility_primary_reuse': 53, 'compatibility_phase13_reuse': 1, 'compatibility_client_reports': 10, 'compatibility_facade_reports': 5, 'compatibility_warnings_by_origin': cwarn, 'compatibility_report_counts_by_origin': creports, 'combined_project_modules': 198, 'unchanged_site_batches': sites, 'primary_result_sha256': digest(at(MAIN+'/result.json')), 'compatibility_result_sha256': digest(at(COMP+'/result.json')), 'phase13_archive_sha256': checked['archive_sha256'], 'current_sources_checked': current_repo is not None, 'adopted_files': ADOPTIONS, 'retired_files': RETIRED, 'prior_five_adoptions_unchanged': PRIOR_ADOPTIONS, 'selected_report_profiles': {m: (mprofiles|cprofiles)[m] for m in allplans if m in (mprofiles|cprofiles)}, 'scope': 'Recorded Lean source/import/object-hash/log/command provenance for both selected closures. The seven API clients, two endpoint clients, and two compatibility clients are distinct. Nine site batches are exact inherited checks. No live-object verification or compiler execution by this saved reader; attributed research renderer remains inert.'}


def check_outer(root, source_map, cfg, read, at, freeze):
 label = 'primary-run2' if root == MAIN else 'compatibility-run1'
 outer = read(EXEC+'/'+label+'-outer.json')
 argv = ['python3','-B',PREP+'/build.py','--out',root,'--map',source_map]
 if root == COMP: argv += ['--reuse',MAIN]
 for target in (TARGETS if root == MAIN else CLIENTS): argv += ['--target',target]
 if root == MAIN: argv += ['--audit-endpoint']
 assert outer['argv'] == argv and outer['cwd'] == ROOT
 assert outer['status'] == 'PASS_OUTER_EXIT_ZERO' and outer['exit_code'] == 0 and outer['frozen_files_unchanged']
 assert outer['seconds'] >= 0
 if root==MAIN: assert outer['retry_freeze_sha256'] == RETRY_FREEZE
 else:
  assert outer['final_map_sha256']==digest(at(source_map))
  assert outer['primary_result_sha256']==digest(at(MAIN+'/result.json'))
 for key in ['stdout','stderr']: assert digest(at(outer[key])) == outer[key+'_sha256']
 wrapper = cfg['outer_wrappers'][label]
 assert digest(at(wrapper)) == outer['wrapper_sha256']

def check_resume(read, at, h, tool, binary, cfg):
 retry_freeze = read(RETRY+'/freeze.json')
 assert digest(at(RETRY+'/freeze.json')) == RETRY_FREEZE
 for n,pin in retry_freeze['files'].items(): assert digest(at(RETRY+'/'+n)) == pin
 for p,pin in retry_freeze['external_inputs'].items(): assert digest(at(p)) == pin
 init = read(RETRY+'/initialization-result.json')
 assert init['status'] == 'VALIDATED_PARTIAL_PROVIDER_RESUME_NOT_PRIMARY_PASS'
 assert init['original_primary_status'] == 'FAILED_CLIENT_ELABORATION' and init['original_result_absent']
 assert init['failed_client_excluded'] == 'ProfileTC14Api' and init['resumed_providers'] == 189
 assert init['prior_successful_fresh_invocations'] == 65 and init['prior_phase13_reused_providers'] == 124
 assert init['new_calls_still_required'] == ['ProfileTC14Api','EndpointAudit215','K215Audit'] and not init['compiler_invoked']
 for label,root in [('original',FIRST),('new',MAIN)]:
  for n in ['before','inventory']:
   assert digest(at(root+'/'+n+'.json')) == init[label+'_'+n+'_sha256']
 first = read(FIRST+'/completed.json'); inv = read(FIRST+'/inventory.json'); before = read(FIRST+'/before.json')
 assert digest(at(FIRST+'/completed.json')) == init['original_completed_sha256'] == init['new_completed_sha256']
 assert len(first) == 189 and set(first) == {r['module'] for r in inv['modules']}-{'ProfileTC14Api'}
 assert sum(r['origin']=='candidate_fresh' for r in first.values()) == 65
 assert sum(r['origin']=='phase13_primary_checked' for r in first.values()) == 124
 assert read(FIRST+'/toolchain.json') == tool and before['runner_sha256'] == DRIVER
 assert before['rows'] == inv['modules'] and before['targets'] == inv['targets'] == TARGETS
 current = {r['module']:r for r in read(MAIN+'/inventory.json')['modules']}
 for row in inv['modules']:
  m=row['module']
  if m != 'ProfileTC14Api': assert current[m] == row
  else:
   assert row['source_sha256'] == '2b18426e7177682e48d271282d06b6e85f943053b341e1ac379768b869f1b8e1'
   assert current[m]['source_sha256'] == '2385bc17262454b91c11ba6f4758adddb58b005ab38cf7e5efdbc07d5c3bac6e'
   assert row['imports'] == current[m]['imports']
 for p,pin in before['inputs'].items(): assert (binary[p] if p in binary else digest(at(p))) == pin,p
 failed = read(FIRST+'/attempts/066-ProfileTC14Api/record.json')
 assert failed['module']=='ProfileTC14Api' and failed['status']=='FAIL' and failed['exit_code']==1
 assert failed['object_sha256'] is None and not failed['timed_out']
 assert failed['source_sha256']=='2b18426e7177682e48d271282d06b6e85f943053b341e1ac379768b869f1b8e1'
 assert digest(at(failed['source'])) == failed['source_sha256'] and digest(at(failed['log'])) == failed['log_sha256']
 assert b'error:' in at(failed['log']) and b'sorryAx' in at(failed['log'])
 assert failed['dependencies']=={d:first[d]['object_sha256'] for d in current['ProfileTC14Api']['imports']}
 src=FIRST+'/workspace/ProfileTC14Api.lean';obj=FIRST+'/objects/ProfileTC14Api.olean'
 assert failed['command']==[tool['lean']['path'],'-j1','-M12288','--root='+FIRST+'/workspace','-o',obj,src]
 assert failed['compiler_sha256']==tool['lean']['sha256'] and failed['timeout_seconds']==120 and failed['memory_mebibytes']==12288
 outer=read(EXEC+'/primary-run1-outer.json')
 assert outer['status']=='FAIL_OUTER_EXIT' and outer['exit_code']==1 and outer['frozen_files_unchanged']
 assert outer['freeze_sha256']==FREEZE and digest(at(cfg['outer_wrappers']['primary-run1']))==outer['wrapper_sha256']
 for key in ['stdout','stderr']: assert digest(at(outer[key]))==outer[key+'_sha256']
 oldplan=read(PREP+'/primary-map.json');newplan=read(RETRY+'/primary-map.json')
 replacement=next(r for r in newplan['modules'] if r['module']=='ProfileTC14Api')
 expected=json.loads(json.dumps(oldplan))
 r=next(r for r in expected['modules'] if r['module']=='ProfileTC14Api')
 r['source'],r['source_sha256']=replacement['source'],replacement['source_sha256']
 assert expected==newplan
 assert init['new_map_sha256']==digest(at(RETRY+'/primary-map.json')) and init['runner_unchanged_sha256']==DRIVER
 assert init['initializer_sha256']==digest(at(RETRY+'/initialize.py'))
 return first
