#!/usr/bin/env python3
"""Author-side read-only review of existing CalibratedRotation244 evidence.

This independently written metadata reviewer never imports or executes delivered
guards, compiler binaries, emitters or proof scripts. It writes only its receipt.
"""
from pathlib import Path
import ast
import hashlib
import json
import re

B = Path('/tmp/zfc243-calibrated-source')
MODULE = 'BusyBeaver.ZFC.CalibratedRotation244'
PREFIX = 'SetTheory.BusyBeaver.ZFC.CalibratedRotation244.'
NAMES = ['program_halts_iff_original', 'seed_halts_iff_original',
         'halts_iff_native_refutation', 'halts_iff_zf_refutation',
         'halts_iff_zfc_refutation', 'nonhalting_iff_zf_consistency',
         'nonhalting_iff_zfc_consistency']
PINS = {
    'CalibratedRotation244.lean': '73dcce68c6caa8823f72741455e191f03ebbf092feb173d2dcd78b8f30a3caec',
    'Audit.lean': 'd009f2de2cbf5b906d9bc8d036e2c89144ce7e0011f86f736cc8a7e53d47dc34',
    'check.py': '72450d12eff1eb3cbd3c5a6a98c70977b86cff3a5398ebb078a5a35e3d048418',
    'boundary.json': 'fa7b90f59d436acba506fbd043ef8e174df6ad268d71ea72aae6bc3d9cb6fccc',
    'run1/verification.json': '268ad4e655af8659c3738936eddf2dc9aa131289173b25dd21616044078db27f',
}
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
checks = 0
identities = {}
def check(condition, detail):
    global checks
    checks += 1
    if not condition:
        raise AssertionError(detail)
def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def pin(p, expected):
    p = Path(p).resolve()
    check(str(p) not in identities or identities[str(p)] == expected, 'Conflicting identity: ' + str(p))
    if str(p) not in identities:
        check(digest(p) == expected, 'Changed bytes: ' + str(p))
        identities[str(p)] = expected
    return p
def desc(p):
    p = Path(p).resolve()
    return {'path': str(p), 'sha256': digest(p)}
def load(p):
    return json.loads(Path(p).read_text())
def imports(p):
    return re.findall(r'^import\s+([A-Za-z_][A-Za-z_0-9.]*)\s*$', Path(p).read_text(), re.M)
def probe_names(text):
    return re.findall(r'^#print axioms (\S+)$', text, re.M)
def raw_reports(text):
    matches = re.findall(r"^'([^\n]+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", text, re.M)
    return [{'name': n, 'axioms': sorted({x.strip() for x in a.split(',') if x.strip()})} for n, a in matches]
def module_path(m):
    return Path(m.replace('.', '/')).with_suffix('.olean')
def record_checks(e, probes, callers, built=True, historical=False, actual_tools=None):
    check(e['status'] == ('PASS' if built else 'PREPARED_NOT_BUILT'), 'Terminal outcome')
    check(e['before'] == e['after'] and e['all_input_provider_postchecks'], 'Input postchecks')
    for p, h in e['before'].items():
        pin(p, h)
    for k in ['source', 'audit']:
        pin(e[k]['path'], e[k]['sha256'])
        pin(e[k]['snapshot'], e[k]['sha256'])
    pin(e['compiler']['path'], e['compiler']['sha256'])
    actual = {r['module']: r for r in e['actual_first_providers']}
    check(len(actual) == len(e['actual_first_providers']), 'Unique first providers')
    expected = {r['module'] for r in e['reused_modules']}
    if actual_tools is None:
        actual_tools = [r['module'] for r in e['toolchain_providers']]
    check(set(actual) == expected | set(actual_tools), 'Exact first-provider names')
    for r in e['reused_modules']:
        for k in ['source', 'object']:
            p = pin(r[k], r[k + '_sha256'])
            check(e['before'].get(str(p)) == r[k + '_sha256'], 'Provider is tracked')
        q = actual[r['module']]
        check(Path(q['actual_first']).resolve() == Path(r['object']).resolve() and q['sha256'] == r['object_sha256'], 'Selected first object')
    toolroot = Path(e['compiler']['path']).parent.parent / 'lib/lean'
    for r in e['toolchain_providers']:
        p = pin(r['object'], r['object_sha256'])
        check(p == (toolroot / module_path(r['module'])).resolve(), 'Exact toolchain object')
        if r['module'] in actual:
            check(Path(actual[r['module']]['actual_first']).resolve() == p and actual[r['module']]['sha256'] == r['object_sha256'], 'First tool object')
    if not built:
        check(e['prepare_only'] is True and e['commands'] == [] and e['fresh_modules'] == [], 'Preparation never compiled')
        return
    check([c['label'] for c in e['commands']] == ['source', 'audit'], 'Exactly source and audit')
    for c in e['commands']:
        check(c['exit_code'] == 0 and c.get('timed_out', False) is False and c.get('interrupted') is None, 'Successful compiler command')
        h = hashlib.sha256(c['output'].encode()).hexdigest()
        pin(c['log'], h)
        if not historical:
            check(c['log_sha256'] == h, 'Modern raw log hash')
        else:
            check('log_sha256' not in c and 'interrupted' not in c, 'Historical output-only log schema preserved')
        check('sorryAx' not in c['output'] and 'error:' not in c['output'], 'Clean raw output')
    audit_text = Path(e['audit']['snapshot']).read_text()
    rr = raw_reports(e['commands'][1]['output'])
    check([r['name'] for r in rr] == probe_names(audit_text) and len(rr) == probes, 'Exact ordered reports')
    check(rr == e['axiom_reports'] and all(set(r['axioms']) <= STANDARD for r in rr), 'Exact standard axioms')
    check(len(re.findall(r'^example\b', audit_text, re.M)) == callers, 'Typed caller census')
    check((e['named_axiom_probes'], e['callers']) == (probes, callers), 'Recorded audit census')
    check(e['warnings'] == sum(c['output'].count('warning:') for c in e['commands']) == 0, 'Zero warnings')
    check(e['only_standard_axioms'] and e['all_fresh_objects_unchanged_after_audit'], 'Final proof postchecks')
    check(len(e['fresh_modules']) == 1 and e['source_object_recorded_before_audit'], 'Fresh pre-audit source capture')
    f = e['fresh_modules'][0]
    pin(f['path'], f['sha256'])
    check(f['source_sha256'] == e['source']['sha256'], 'Fresh source binding')
    check(all(e['source_pass_object'][k] == v for k, v in f.items()) and e['source_pass_object']['source_command_index'] == 0, 'Source capture precedes audit')
    cap = e['fresh_first_provider_before_audit']
    cp = cap.get('path', cap.get('actual_first'))
    check(cap['module'] == f['module'] and cap['sha256'] == f['sha256'] and Path(cp).resolve() == Path(f['path']).resolve(), 'Pre-audit first object')
    if historical:
        check(Path(cap['resolved']).resolve() == Path(cp).resolve(), 'Historical resolved first object')

for name, h in PINS.items():
    pin(B / name, h)
b = load(B / 'boundary.json')
e = load(B / 'run1/verification.json')
p = load(B / 'prepared1/verification.json')
pin(B / 'prepared1/verification.json', digest(B / 'prepared1/verification.json'))
for d in b['static_inputs']:
    pin(d['path'], d['sha256'])
for key in ['reused_modules', 'toolchain_providers', 'compiler']:
    check(e[key] == p[key] == b[key], 'Exact boundary and preparation ' + key)
record_checks(e, 7, 9)
record_checks(p, 7, 9, built=False)
pool = {}
for name, d in b['parents'].items():
    pin(d['path'], d['sha256'])
    parent = load(d['path'])
    record_checks(parent, d['probes'], d['callers'], historical=name == 'calibration_pool', actual_tools=d['actual_tool_names'])
    check(parent['compiler'] == e['compiler'], 'Parent compiler matches')
    check(probe_names(Path(parent['audit']['snapshot']).read_text()) == d['audit_names'] == d['report_names'], 'Parent exact names')
    f = parent['fresh_modules'][0]
    rows = parent['reused_modules'] + [{'module': f['module'], 'source': parent['source']['path'], 'source_sha256': f['source_sha256'], 'object': f['path'], 'object_sha256': f['sha256']}]
    for r in rows:
        row = {k: r[k] for k in ['module', 'source', 'source_sha256', 'object', 'object_sha256']}
        check(r['module'] not in pool or pool[r['module']] == row, 'Consistent merged parent provider')
        pool[r['module']] = row
selected = {r['module']: r for r in e['reused_modules']}
check(len(selected) == 198 and len(pool) == b['candidate_provider_count'] == 856, 'Exact selected and available census')
check(sorted(set(pool) - set(selected)) == b['excluded_candidate_modules'] and len(b['excluded_candidate_modules']) == 658, 'Exact excluded providers')
check(all(pool[k] == r for k, r in selected.items()), 'Every selected pair from actual evidence')
seen = set()
toolset = {'Init'}
def visit(m):
    if m in {'Init', 'Lean.Elab.Tactic.Omega'}:
        toolset.add(m)
        return
    check(m in selected, 'Import must be selected: ' + m)
    if m in seen:
        return
    seen.add(m)
    for x in imports(selected[m]['source']):
        visit(x)
for m in imports(B / 'CalibratedRotation244.lean'):
    visit(m)
check(seen == set(selected) and sorted(seen) == e['exact_project_import_closure'] == p['exact_project_import_closure'], 'Independent exact import DFS')
check(toolset == {'Init'} == {r['module'] for r in e['toolchain_providers']}, 'Only Init selected')
check(imports(B / 'Audit.lean') == [MODULE], 'Exact audit import')
check(probe_names((B / 'Audit.lean').read_text()) == [PREFIX + n for n in NAMES], 'Seven intended public statements')
for x in [e, p]:
    check(x['shared_timeout_seconds'] == 120 and x['memory_mebibytes'] == 4096 and x['LEAN_NUM_THREADS'] == '1', 'Default resource budget')
    check(x['global_option_overrides'] == [] and x['compiler_version_query_performed'] is False and x['dependency_build'] is False and x['downloads'] is False, 'No extra execution privileges')
    roots = [Path(x['LEAN_PATH']), Path(x['compiler']['path']).parent.parent / 'lib/lean']
    for r in x['reused_modules'] + x['toolchain_providers']:
        first = next((root / module_path(r['module'])).resolve() for root in roots if (root / module_path(r['module'])).is_file())
        check(first == Path(r['object']).resolve(), 'Current actual provider search order')
for i, c in enumerate(e['commands']):
    expected = [e['compiler']['path'], '-j1', '-M4096', '--root=' + str(B / 'run1/sources')]
    if i == 0:
        expected += ['-o', e['fresh_modules'][0]['path']]
    expected += [e[['source', 'audit'][i]]['snapshot']]
    check(c['command'] == expected, 'Exact command and resource switches')
check(sum(c['seconds'] for c in e['commands']) < 120, 'Shared elapsed budget')
guard = (B / 'check.py').read_text()
ast.parse(guard)
template = Path('/tmp/zfc243-source-bridge/check-v2.py').read_text()
check(guard[guard.index('    def save():'):] == template[template.index('    def save():'):].replace('named_axiom_probes=9,callers=10', 'named_axiom_probes=7,callers=9'), 'Execution tail changes only audit census')
for name in ['CalibratedRotation244.lean', 'Audit.lean']:
    text = (B / name).read_text()
    check(not re.search(r'\b(sorry|admit|native_decide)\b|set_option\s+(maxHeartbeats|maxRecDepth)', text), 'Default kernel proof source')
for path, h in identities.items():
    check(digest(path) == h, 'Close-time input rehash: ' + path)
out = {
    'status': 'EXISTING_ACTUAL_EVIDENCE_REVIEW_PASS', 'findings': [],
    'reviewer_role': 'Author-side existing-evidence review: opening_encoder authored this source, typed audit and guard. The script independently reads recorded execution and current bytes; this is not independent source authorship. Root alone executed the proof commands.',
    'verification': desc(B / 'run1/verification.json'),
    'source': desc(B / 'CalibratedRotation244.lean'), 'audit': desc(B / 'Audit.lean'),
    'guard': desc(B / 'check.py'), 'boundary': desc(B / 'boundary.json'),
    'preparation': desc(B / 'prepared1/verification.json'), 'reviewer_source': desc(__file__),
    'fresh_module': e['fresh_modules'][0], 'checks': checks,
    'actual_input_count': len(e['before']), 'preparation_input_count': len(p['before']),
    'unique_current_identities_rehashed_at_close': len(identities),
    'selected_projects': 198, 'selected_tools': ['Init'], 'candidate_pool': 856, 'excluded_projects': 658,
    'probes': 7, 'callers': 9, 'warnings': 0, 'axiom_reports': e['axiom_reports'],
    'source_seconds': e['commands'][0]['seconds'], 'audit_seconds': e['commands'][1]['seconds'],
    'scope': 'Arbitrary-register rotation equivalence composed with routed-program calibration; at LogicalSeed246.initial, halting iff native/ZF/ZFC refutation and nonhalting iff corresponding ZF/ZFC consistency. No binary-machine/blank-tape endpoint or internal PA theorem.',
    'parent_schema_limits': ['BinaryRouting245 has historical output-bound logs without modern interrupted/log_sha256 fields and a fresh first capture using actual_first/resolved. These exact schemas were checked, not strengthened retroactively.', 'The 198 selected cached source/object pairs are attested by the two actual parent records. No dependency rebuild or clean-checkout proof claim.'],
    'source_review': ['All source and audit statements and the complete guard/delta read.', 'SourceRotation244.program_halts_iff and BisimRouting245.program_halts_iff have the matching arbitrary-register/empty-pointer orientation.', 'LogicalSeed246.initial definition and all three refutation equivalences match the composition; two consistency results use not_congr.', 'Typed clients cover all seven public theorems plus halting-to-ZF and ZFC-refutation-to-halting directions.'],
    'supplied_guard_or_compiler_execution': False,
}
target = B / 'author-run1-evidence-review.json'
check(not target.exists(), 'Immutable new review destination')
target.write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps({'review': desc(target), 'checks': checks, 'unique_identities': len(identities)}, indent=2))
