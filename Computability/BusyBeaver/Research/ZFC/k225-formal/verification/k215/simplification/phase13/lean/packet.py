"""Validate phase13's two recorded closures against the pinned phase12 evidence.

This reader checks records, sources, imports and raw logs. Only collect.py checks
live object bytes; neither reader invokes Lean or a supplied producer.
"""
from pathlib import Path, PurePosixPath
import hashlib, json, re
import basis

HERE = Path(__file__).resolve().parent
ROOT = '/home/codex/.codex/worktrees/ec20/Proofs'
PREP = '/tmp/k215-phase13-upstream-check'
EXEC = '/tmp/k215-phase13-upstream-execution'
MAIN, COMP = PREP + '/primary-run1', PREP + '/compatibility-run1'
BASE = '/tmp/k215-phase12-import-check/primary-run1'
BASE_COMP = '/tmp/k215-phase12-import-check/compatibility-run1'
OLD = '/tmp/k215-proof-phase8/lean-run1'
DRIVER = 'b92ef55882a1869a40b57f3e746ba40b11a4c79dc2d8f0f5273704d373aff624'
FREEZE = '01c6f3c207490dd3cab316ec849537a0cddf136679fba1717ace5f199e4421ba'
BOUNDARY = 'b5ad74566d101c75d180195b3a1cb75c703e26d1d7421c207ef389396db2d3c9'
BASE_RESULTS = ['a5fce6a787751ba527cc368ff97b770d28eeb517149d5e3f99b17dd7c738df5e', '7223a5fa4f5fe56e331d2dc27efc7b2d8e50f473d081eed9e145278728e68f9c']
P = 'BusyBeaver.ZFC.'
NS = 'SetTheory.' + P
API = ['GenericShared13Api', 'NumericCD52Api', 'LukasShared13Api']
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
ADOPTIONS = {
 LEAN_DIR + 'DominatedImplication.lean': 'bd07364a829e8a1535b0ecf1ee6ed0c292d5af35e01a6db8f152dd2610e247d8',
 LEAN_DIR + 'Lukasiewicz.lean': '7d443a733b5c5ddd0d49728cf1ea7d855dd445f156934c13578bacc008c59874',
 FORMAL + 'generate_dominated_implication_lean.py': 'ebcbb86642d4d389748451dc662b42f7ac62e7aa4b235bbf4e5d8e5a1ec5c1e9',
 FORMAL + 'rho8cd/derivation_core.txt': '4141248ed90a6813c07f274351336963acde1d82f6ea463a33e5f7d64bed8005',
 FORMAL + 'rho8cd/generate_domrho8_cd.py': '63da860d3a957010c53d783a2b8995acef3d8e3806823f24fc5833738dc1d56a'}
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
  assert row['storage'] in {'packet', 'phase12'}
  data = (members if row['storage'] == 'packet' else prior)[row['key']]
  assert digest(data) == row['sha256'] and len(data) == row['bytes']
  result[path] = data
 return result

def same_source_closure(entries, previous, closure):
 assert all((entries[d]['source_sha256'], entries[d]['imports']) == (previous[d]['source_sha256'], previous[d]['imports']) for d in closure)
def exact_reuse(record, previous, origin): assert record == {**previous, 'origin': origin}
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
 assert cfg['status'] == 'FROZEN_COMPLETED_PHASE13_INPUTS'
 for path, row in cfg['files'].items():
  assert digest(at(path)) == row['sha256'] and len(at(path)) == row['bytes']
 old, oldrows, oldkind = {}, {}, {}
 for root, count, kind, pin in [(BASE_COMP, 69, 'phase12_compatibility_checked', BASE_RESULTS[1]), (BASE, 184, 'phase12_primary_checked', BASE_RESULTS[0])]:
  assert digest(at(root + '/result.json')) == pin
  inv = read(root + '/inventory.json'); done = read(root + '/completed.json')
  assert at(root + '/inventory.json') == prior['path:' + root + '/inventory.json']
  assert at(root + '/completed.json') == prior['path:' + root + '/completed.json']
  assert len(inv['modules']) == len(done) == count
  for row in inv['modules']:
   m = row['module']
   if m in old: assert (row['source_sha256'], row['imports'], done[m]['object_sha256']) == (oldrows[m]['source_sha256'], oldrows[m]['imports'], old[m]['object_sha256'])
   old[m], oldrows[m], oldkind[m] = done[m], row, kind
 assert len(old) == len(oldrows) == 201
 tool = read(BASE + '/toolchain.json'); compiler = tool['lean']['path']
 assert tool == read(BASE_COMP + '/toolchain.json') == read(OLD + '/toolchain.json')
 helper = ROOT + '/' + FORMAL + 'verification/k215/lean/build.py'
 binary = {v['path']: v['sha256'] for k, v in tool.items() if k in {'lean', 'lake', 'Init.olean'}}
 for root in [OLD, BASE, BASE_COMP]:
  binary.update({root + '/objects/' + m.replace('.', '/') + '.olean': r['object_sha256'] for m, r in read(root + '/completed.json').items()})
 freeze = read(PREP + '/freeze.json'); assert digest(at(PREP + '/freeze.json')) == FREEZE
 for name, pin in freeze['files'].items(): assert digest(at(PREP + '/' + name)) == pin
 boundary = read(PREP + '/producer-boundary.json'); assert digest(at(PREP + '/producer-boundary.json')) == BOUNDARY
 allplans = {r['module']: r for r in read(PREP + '/candidate-map.json')['modules']}
 assert len(allplans) == 9
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
  assert len(entries) == len(done) == count and set(entries) == set(done)
  changed = {m for m, r in entries.items() if m not in oldrows or (r['source_sha256'], r['imports']) != (oldrows[m]['source_sha256'], oldrows[m]['imports'])}
  forced = {m for m in entries if closures[m] & changed}
  assert sorted(changed) == before['changed_sources'] == result['source_changed_modules']
  assert sorted(forced) == before['force_basis_rebuild'] == result['force_basis_rebuild_modules']
  assert result['basis_reuse_rejects_transitive_source_changes'] and result['secondary_reuse_requires_exact_transitive_sources_and_imports']
  kinds = {'candidate_fresh': set(result['fresh_modules']), 'phase12_primary_checked': set(result['phase12_primary_reused_modules']), 'phase12_compatibility_checked': set(result['phase12_compatibility_reused_modules']), 'secondary_checked': set(result['secondary_reused_modules'])}
  assert set().union(*kinds.values()) == set(entries) and sum(map(len, kinds.values())) == count
  if secondary is None:
   assert [len(v) for v in kinds.values()] == [36, 151, 0, 0] and forced == kinds['candidate_fresh']
   assert changed == {P+'DominatedImplication', P+'Lukasiewicz'} | set(API)
   assert set(entries) == {r['module'] for r in read(BASE + '/inventory.json')['modules']} | set(API)
  else:
   assert [len(v) for v in kinds.values()] == [16, 0, 1, 53]
   assert kinds['phase12_compatibility_checked'] == {P+'Dag254'} and len(forced) == 23
   assert changed == {P+'DominatedImplication', P+'Lukasiewicz'}
   assert set(entries) == {r['module'] for r in read(BASE_COMP + '/inventory.json')['modules']} | {P+'DominatedImplication'}
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
    src = root + '/workspace/' + m.replace('.', '/') + '.lean'; obj = root + '/objects/' + m.replace('.', '/') + '.olean'
    assert rec['timeout_seconds'] == 120 and rec['memory_mebibytes'] == 12288
    assert rec['compiler_sha256'] == tool['lean']['sha256'] and rec['helper_sha256'] == before['inputs'][helper]
    assert rec['command'] == [compiler, '-j1', '-M12288', '--root='+root+'/workspace', '-o', obj, src]
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
    if 'reports' in r: named_reports(log, r['reports'], r.get('report_axioms'))
   if current_repo is not None and m not in API + CLIENTS:
    paths = [Path(current_repo)/r/(m.replace('.', '/')+'.lean') for r in h.ROOTS if (Path(current_repo)/r/(m.replace('.', '/')+'.lean')).is_file()]
    assert len(paths) == 1 and sha(paths[0]) == row['source_sha256']
  for path, pin in before['inputs'].items(): assert (binary[path] if path in binary else digest(at(path))) == pin, path
  assert before['absent_inputs'] == sorted(r['canonical'] for r in boundary['files'] if r['current_state'] == 'absent')
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
  label = PurePosixPath(root).name; outer = read(EXEC+'/'+label+'-outer.json')
  assert outer['status'] == 'OUTER_EXIT_0' and outer['exit_code'] == 0 and outer['exception'] is None and outer['helper_inputs_unchanged'] and outer['plan_unchanged']
  assert outer['command'] == read(outer['plan'])['command'] and outer['plan_sha256'] == digest(at(outer['plan']))
  assert outer['command'][:3] == ['python', '-B', PREP+'/build.py'] and outer['command'][outer['command'].index('--out')+1] == root and outer['command'][outer['command'].index('--map')+1] == maps[0]
  assert outer['wrapper_sha256'] == digest(at(EXEC+'/run.py')) and outer['freeze_sha256'] == FREEZE
  assert outer['before_helper_inputs'] == outer['after_helper_inputs'] == {PREP+'/'+n: p for n, p in freeze['files'].items()}
  for key in ['stdout', 'stderr']: assert outer[key+'_sha256'] == digest(at(outer[key]))
  binary.update({root+'/objects/'+m.replace('.', '/')+'.olean': r['object_sha256'] for m, r in done.items()})
  return result, entries, closures, done, warnings, report_counts, report_profiles
 main, entries, closures, done, mwarn, mreports, mprofiles = run_check(MAIN, TARGETS, 187)
 comp, cent, cclose, cdone, cwarn, creports, cprofiles = run_check(COMP, CLIENTS, 70, (done, entries))
 project = (set(entries) | set(cent)) - set(API + CLIENTS)
 assert len(project) == 199 and project == set(oldrows) - set(CLIENTS)
 endpoint = closures[TARGETS[0]]; prefix = closures[TARGETS[1]] - endpoint
 assert len(endpoint) == 179 and len(prefix) == 5 and len(set(entries)-set(API)) == 184
 sites = sorted(m for m in entries if m.startswith(P+'KSites215Batch')); assert len(sites) == 9
 for m in sites: exact_reuse(done[m], old[m], 'phase12_primary_checked')
 assert sum(len(mprofiles[m]) for m in API) == 20
 assert [ax for _, ax in mprofiles['LukasShared13Api']] == [[]]*7 + [sorted(STANDARD)]
 assert [n for n, _ in cprofiles[P+'WFTheory']] == [NS+'WFTheory.'+n for n in ['zf_consistent_of_model', 'c254_of_zf_refutation', 'c254_refutation_iff_zf', 'native_refutation_iff_zf', 'native_consistency_iff_zf']]
 assert sum(len(cprofiles[m]) for m in CLIENTS) == 10
 assert all(set(ax) == STANDARD for _, ax in cprofiles[P+'WFTheory'])
 # Original producer and derivation inputs remain historical even after adoption.
 assert boundary['phase12_primary_result_sha256'] == BASE_RESULTS[0] and boundary['phase12_compatibility_result_sha256'] == BASE_RESULTS[1]
 assert boundary['phase8_result_sha256'] == digest(at(OLD+'/result.json'))
 for key in ['producer_before_original', 'phase11_adoption', 'previous_boundary', 'phase12_adoption', 'phase12_boundary']:
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
 adopted = cfg['adoption']['files']; assert len(adopted) == 5 and {r['target']: r['sha256'] for r in adopted} == ADOPTIONS
 raw_adoption = read(cfg['adoption']['receipt'])
 assert raw_adoption['status'] == 'EXACT_CHECKED_PHASE13_ADOPTION'
 assert raw_adoption['primary_result_sha256'] == digest(at(MAIN+'/result.json')) and raw_adoption['compatibility_result_sha256'] == digest(at(COMP+'/result.json'))
 normalized = [{**r, 'archived_before': ROOT+'/'+r['archived_before']} for r in raw_adoption['files']]
 assert adopted == normalized
 root_review = read(cfg['root_review'])
 assert digest(at(cfg['root_review'])) == raw_adoption['root_actual_review_sha256'] and root_review['status'] == 'PASS_ROOT_RAW_PHASE13_ACTUAL'
 assert root_review['distinct_project_modules'] == 199
 for key, directory in [('primary', MAIN), ('compatibility', COMP)]:
  assert root_review[key]['directory'] == directory and root_review[key]['result_sha256'] == digest(at(directory+'/result.json'))
 current = read(cfg['current_review'])
 assert current['status'] == 'PASS_CURRENT_PHASE13_ADOPTION' and current['adoption_sha256'] == digest(at(cfg['adoption']['receipt']))
 assert current['project_sources'] == 199 and current['canonical_writes'] == 5
 expected_sources = {m: (entries|cent)[m]['source_sha256'] for m in project}
 assert {m: r['sha256'] for m, r in current['sources'].items()} == expected_sources
 assert {m: r['sha256'] for m, r in root_review['sources'].items()} == expected_sources
 assert all(r['all_other_before_inputs_current_exact'] for r in current['runs'])
 for r in adopted:
  target = r['target']; data = members['adoption/'+target]
  assert digest(data) == r['sha256'] and len(data) == r['bytes'] and data == at(r['source'])
  assert digest(at(r['archived_before'])) == r['before_sha256']
  if target.endswith('.lean'):
   m = P+PurePosixPath(target).stem; assert entries[m]['source_sha256'] == r['sha256'] and oldrows[m]['source_sha256'] == r['before_sha256']
  if current_repo is not None: assert sha(Path(current_repo)/target) == r['sha256']
 assert set(cfg['historical_inputs']) == {ROOT+'/'+FORMAL+p for p in ['generate_dominated_implication_lean.py', 'rho8cd/derivation_core.txt']}
 for path, r in cfg['historical_inputs'].items():
  target = str(PurePosixPath(path).relative_to(ROOT)); row = next(x for x in adopted if x['target'] == target)
  assert r['sha256'] == row['before_sha256'] and r['snapshot'] == row['archived_before'] and digest(at(path)) == r['sha256']
 canonical_producer = read('/tmp/k215-phase13-root/canonical-producer-actual.json')
 assert canonical_producer['command'] == ['python3', '-B', ROOT+'/'+FORMAL+'generate_dominated_implication_lean.py', '--check'] and canonical_producer['exit_code'] == 0
 for stream in ['stdout', 'stderr']: assert canonical_producer[stream+'_sha256'] == digest(at('/tmp/k215-phase13-root/canonical-producer.'+stream+'.txt'))
 controls = json.loads(members['review/controls-result.json'])
 assert controls['status'] == 'PASS_METADATA_ONLY' and controls['compiler_producer_collector_prior_reader_invoked'] is False
 assert controls['positive'] == sum(r['expected_accept'] for r in controls['checks']) and controls['negative'] == sum(not r['expected_accept'] for r in controls['checks'])
 assert all(r['matched'] for r in controls['checks'])
 assert controls['inputs'] == {'/tmp/k215-phase13-publication/'+n: digest(members['review/'+n]) for n in ['controls.py', 'packet.py']}
 assert members['review/controls.stdout.log'] == dump(controls) and not members['review/controls.stderr.log']
 for root in [MAIN, COMP]:
  before = read(root+'/before.json')
  for path, r in cfg['historical_inputs'].items():
   if path in before['inputs']: assert before['inputs'][path] == r['sha256']
 return {'status': 'PASS_SAVED_PHASE13_RECORDS', 'primary_providers': 187, 'primary_project_modules': 184, 'endpoint_modules': 179, 'prefix_modules': 5, 'primary_fresh': 36, 'primary_phase12_reuse': 151, 'api_clients': 3, 'api_reports': 20, 'core_reports': 6, 'core_axioms': [], 'endpoint_clients': 2, 'endpoint_reports': 10, 'endpoint_warnings': 0, 'primary_warnings_by_origin': mwarn, 'primary_report_counts_by_origin': mreports, 'compatibility_providers': 70, 'compatibility_project_modules': 68, 'compatibility_clients': 2, 'compatibility_fresh': 16, 'compatibility_primary_reuse': 53, 'compatibility_phase12_reuse': 1, 'compatibility_client_reports': 10, 'compatibility_facade_reports': 5, 'compatibility_warnings_by_origin': cwarn, 'compatibility_report_counts_by_origin': creports, 'combined_project_modules': 199, 'unchanged_site_batches': sites, 'primary_result_sha256': digest(at(MAIN+'/result.json')), 'compatibility_result_sha256': digest(at(COMP+'/result.json')), 'phase12_archive_sha256': checked['archive_sha256'], 'current_sources_checked': current_repo is not None, 'adopted_files': ADOPTIONS, 'selected_report_profiles': {m: (mprofiles|cprofiles)[m] for m in allplans if m in (mprofiles|cprofiles)}, 'scope': 'Recorded Lean source/import/object-hash/log/command provenance for both selected closures. The three API clients, two endpoint clients, and two compatibility clients are distinct. Nine site batches are exact inherited checks. No live-object verification or compiler execution by this saved reader; attributed research renderer remains inert.'}
