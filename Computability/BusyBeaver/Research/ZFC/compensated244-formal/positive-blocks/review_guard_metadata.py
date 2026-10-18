"""Independent source/metadata review only. Never imports or runs the guard."""
from pathlib import Path
import ast, hashlib, json, re

W = Path('/tmp/zfc244-positive-blocks')
H = W / 'history/run1-ambiguous-axiom-name'
checks = []
def ck(c, s):
    if not c: raise AssertionError(s)
    checks.append(s)
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def desc(p): return {'path': str(p), 'sha256': sha(p)}
guard = W / 'check.py'
text = guard.read_text()
ast.parse(text)
ck(sha(guard) == '3a4545756b944b368a98bd46da1ae963699a5670c528cd09f2297f77843a9b2a', 'frozen current guard')
old = (H / 'check.py').read_text()
expected = old.replace("AUDIT_SHA='71a250662d517d3de726ee741ae2bd2ad0a7b618919f8131f788823283148084'", "AUDIT_SHA='fce10923ebc4cae49367da0f8dde77202b5f92e00f7ca8b0d3dbb33a7dfb2abe'")
expected = expected.replace("==PROBES,'Audit short names changed.'", "==[PREFIX+n for n in PROBES],'Audit qualified names changed.'")
ck(expected == text, 'exact two guard substitutions; execution policy unchanged')
prefix = 'SetTheory.BusyBeaver.ZFC.PositiveBlockBisimulation.'
audit = (W / 'Audit.lean').read_text()
old_audit = (H / 'Audit.lean').read_text()
ck(re.sub(r'^#print axioms (\S+)$', lambda m: '#print axioms ' + prefix + m[1], old_audit, flags=re.M) == audit, 'only four print identifiers qualified')
ck(len(re.findall(r'^example\b', audit, re.M)) == 4, 'four typed caller bodies unchanged')
b = json.loads((W / 'boundary.json').read_text())
parent = Path(b['parent']['path'])
ck(sha(parent) == b['parent']['sha256'] == '41ff9364f37d9eb33ff1eb2b4bbc0e5f17f0a44ac02a4a7dcdbdfa6c5b1ccf87', 'exact actual ancestor record')
e = json.loads(parent.read_text())
ck(e['status'] == 'PASS' and e['before'] == e['after'], 'ancestor terminal PASS and before/after binding')
ck(e['named_axiom_probes'] == e['callers'] == 11, 'ancestor 11/11 scope')
ck([x['label'] for x in e['commands']] == ['source', 'audit'] and all(x['exit_code'] == 0 and not x.get('timed_out') for x in e['commands']), 'ancestor successful ordered commands')
for k in ['source', 'audit']:
    ck(sha(e[k]['snapshot']) == e[k]['sha256'], 'ancestor preserved ' + k + ' snapshot')
selected = {x['module']: x for x in b['reused_modules']}
ck(set(selected) == {'BusyBeaver.Core', 'BusyBeaver.ZFC.RuntimePerm252'}, 'only two selected project providers')
first = {x['module']: x for x in e['actual_first_providers']}
for m, row in selected.items():
    ck(row == next(x for x in e['reused_modules'] if x['module'] == m), 'selected ancestor descriptor ' + m)
    for k in ['source', 'object']:
        p = Path(row[k]).resolve()
        ck(sha(p) == row[k + '_sha256'] == e['before'][str(p)] == e['after'][str(p)], 'current selected ' + k + ' ' + m)
    ck(Path(first[m]['actual_first']).resolve() == Path(row['object']).resolve() and first[m]['sha256'] == row['object_sha256'], 'historical actual first ' + m)
seen = set()
tool_names = {'Init'}
def visit(m):
    if m in {'Init', 'Lean.Elab.Tactic.Omega'}: tool_names.add(m); return
    ck(m in selected, 'selected DFS ' + m)
    if m in seen: return
    seen.add(m)
    for n in re.findall(r'^import\s+(\S+)\s*$', Path(selected[m]['source']).read_text(), re.M): visit(n)
for m in re.findall(r'^import\s+(\S+)\s*$', (W / 'PositiveBlockBisimulation.lean').read_text(), re.M): visit(m)
ck(seen == set(selected), 'complete exact two-project DFS')
ck(b['toolchain_providers'] == e['toolchain_providers'] and {x['module'] for x in b['toolchain_providers']} == tool_names, 'exact Init/Omega boundary')
for row in b['toolchain_providers']:
    p = Path(row['object']).resolve()
    ck(sha(p) == row['object_sha256'] == e['before'][str(p)] == e['after'][str(p)], 'current tool ' + row['module'])
ck(sha(b['compiler']['path']) == b['compiler']['sha256'] and b['compiler'] == e['compiler'], 'compiler binary without version execution')
aliases = {sha(H / 'check.py'): H / 'check.py', sha(H / 'Audit.lean'): H / 'Audit.lean'}
for name in ['prepared1', 'prepared2', 'run1']:
    record = json.loads((W / name / 'verification.json').read_text())
    ck(record['before'] == record['after'], name + ' before/after stable')
    for path, digest in record['before'].items():
        chosen = aliases[digest] if digest in aliases else Path(path)
        ck(sha(chosen) == digest, name + ' current or explicitly archived input ' + path)
    ck(len(record['before']) == 16 and len(record['reused_modules']) == 2, name + ' sixteen inputs/two projects')
    ck(record['shared_timeout_seconds'] == 120 and record['memory_mebibytes'] == 4096 and record['LEAN_NUM_THREADS'] == '1' and record['global_option_overrides'] == [], name + ' unchanged default limits')
    ck(not record['compiler_version_query_performed'] and not record['dependency_build'] and not record['downloads'], name + ' no version/build/download')
    if name.startswith('prepared'):
        ck(record['status'] == 'PREPARED_NOT_BUILT' and record['commands'] == [] and record['fresh_modules'] == [], name + ' genuinely unbuilt')
    else:
        ck(record['status'] == 'FAIL' and record['error'] == "RuntimeError('Wrong actual reports.')", 'original exact fail-closed census rejection')
        ck(all(x['exit_code'] == 0 for x in record['commands']), 'original source/audit processes succeeded; guard rejected report census')
        for command in record['commands']:
            ck(Path(command['log']).read_text() == command['output'] and sha(command['log']) == command['log_sha256'], 'original raw ' + command['label'] + ' output')
        names = re.findall(r"^'([^\n]+)' depends on axioms:", record['commands'][1]['output'], re.M)
        ck(len(names) == 5 and names[2] == 'SetTheory.BusyBeaver.ZFC.RuntimePerm252.halts_iff', 'ambiguity emitted the additional actual ancestor theorem')
ck('deadline=time.monotonic()+120' in text and "'-j1','-M4096'" in text and 'start_new_session=True' in text and 'os.killpg' in text, 'shared process-group bound and literal compiler limits')
ck(text.index('source_object_recorded_before_audit=True') < text.index("out=run('audit'"), 'source object saved and first-provider bound before audit')
result = {
    'status': 'INDEPENDENT_GUARD_BOUNDARY_PREPARATION_REVIEW_PASS', 'findings': [],
    'reviewer_role': 'Independent source/metadata reviewer; no authorship of this guard/source/audit, no supplied execution or compiler/version call.',
    'guard': desc(guard), 'source': desc(W / 'PositiveBlockBisimulation.lean'), 'audit': desc(W / 'Audit.lean'),
    'boundary': desc(W / 'boundary.json'), 'parent': desc(parent), 'reviewer_source': desc(Path(__file__)),
    'records': [desc(W / x / 'verification.json') for x in ['prepared1', 'prepared2', 'run1']],
    'scope': 'Full current guard and boundary source review, selected two-project current providers/Init/Omega, both actual preparations and original failed census lineage. Does not revalidate all851 ancestor providers or independently audit the later successful run2; that receipt is assigned separately.',
    'historical_rebindings': [{'sha256': h, 'preserved_path': str(p)} for h, p in aliases.items()],
    'source_scope': 'Generic positive-block halting equivalence under an explicit Simulation premise for Core tapes; no instantiated244 invariant/local-identity or calibration theorem.',
    'checks': checks,
}
out = W / 'independent-guard-boundary-preparation-review.json'
with out.open('x') as stream: stream.write(json.dumps(result, indent=2) + '\n')
print(sha(out), len(checks))
