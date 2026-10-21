#!/usr/bin/env python3
"""Independent live Lean artifact/assumption audit; no subprocess or proof execution."""
from pathlib import Path
import argparse
import hashlib
import json
import re


def uncomment(s):
    out = []; i = 0; depth = 0; string = False
    while i < len(s):
        if depth:
            if s.startswith('/-', i): depth += 1; out.extend('  '); i += 2
            elif s.startswith('-/', i): depth -= 1; out.extend('  '); i += 2
            else: out.append('\n' if s[i] == '\n' else ' '); i += 1
        elif string:
            if s[i] == '\\' and i + 1 < len(s): out.extend('  '); i += 2
            elif s[i] == '"': string = False; out.append(' '); i += 1
            else: out.append('\n' if s[i] == '\n' else ' '); i += 1
        elif s.startswith('/-', i): depth = 1; out.extend('  '); i += 2
        elif s.startswith('--', i):
            j = s.find('\n', i); j = len(s) if j < 0 else j
            out.extend(' ' * (j - i)); i = j
        elif s[i] == '"': string = True; out.append(' '); i += 1
        else: out.append(s[i]); i += 1
    assert depth == 0 and not string
    return ''.join(out)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['build', 'repo', 'output']:
        parser.add_argument('--' + name, type=Path, required=True)
    args = parser.parse_args()
    build, repo, output = args.build.resolve(), args.repo.resolve(), args.output.resolve()
    assert __debug__ and not output.exists(), 'Assertions and fresh output required'
    before = {}

    def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
    def bind(p):
        p = str(Path(p)); h = sha(p)
        assert p not in before or before[p] == h, ('Changed during review', p)
        before[p] = h
        return h
    def doc(p): bind(p); return json.loads(Path(p).read_text())
    def text(p): bind(p); return Path(p).read_text()

    inv = doc(build / 'inventory-v5.json')
    done = doc(build / 'completed.json')
    attempts = doc(build / 'attempts.json')
    boundary = doc(build / 'toolchain-boundary-v5.json')
    author = doc(build / 'final-review.json')
    complete = doc(build / 'build-complete.json')
    entries = {r['module']: r for r in inv['project_modules']}
    order = inv['order']; target = 'BusyBeaver.ZFC.KEndpoint215'
    assert len(entries) == len(order) == len(set(order)) == 204
    assert order == [r['module'] for r in inv['project_modules']]
    assert set(done) == set(entries) and inv['target'] == target
    assert inv['toolchain'] == 'leanprover/lean4:v4.32.0'
    assert boundary['inventory_sha256'] == bind(build / 'inventory-v5.json')
    for k in ['lean', 'lake', 'Init.olean', 'project_toolchain']:
        r = boundary[k]; assert bind(r['path']) == r['sha256']
    assert text(build / 'workspace/lean-toolchain') == 'leanprover/lean4:v4.32.0\n'
    assert text(build / 'workspace/lakefile.toml') == 'name = "K215KernelCheck"\n\n[[lean_lib]]\nname = "K215KernelCheck"\n'
    assert complete['status'] == 'FULL_CURRENT_SOURCE_CLOSURE_PASS'
    assert complete['modules'] == 204 and complete['target'] == target
    assert complete['completed_sha256'] == bind(build / 'completed.json')
    assert complete['inventory_sha256'] == bind(build / 'inventory-v5.json')

    roots = [repo / p for p in ['Computability/BusyBeaver/Lean', 'Logic/FirstOrder/Lean',
                              'SetTheory/ZF/Lean', 'SetTheory/BoundedConsistency/Lean']]
    cache = build / 'workspace/.lake/build/lib/lean'
    edges = {}; sources = {}; objects = {}; selected = {}; warnings = {}; externals = set()
    elapsed = 0.0
    for m in order:
        e, r = entries[m], done[m]
        source = repo / e['relative_source']
        candidates = [root for root in roots if root / (m.replace('.', '/') + '.lean') == source]
        assert len(candidates) == 1
        clean = uncomment(text(source))
        imports = []
        for line in clean.splitlines():
            z = re.match(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(.*)$', line)
            if z: imports.extend(z.group(1).split())
        assert imports == e['imports'], (m, imports, e['imports'])
        assert not re.search(r'\b(?:axiom|sorry|admit|unsafe|native_decide|implemented_by|addDecl|mkAxiom|opaque|constant)\b', clean), m
        deps = set(imports) & entries.keys(); externals.update(set(imports) - entries.keys())
        assert deps <= selected.keys(), (m, 'not topological')
        edges[m] = sorted(deps)
        assert r['module'] == m and r['source'] == str(source)
        assert r['source_sha256'] == e['sha256'] == bind(source)
        assert r['status'] == 'PASS' and r['exit_code'] == 0 and not r['timed_out']
        assert r['source_unchanged'] is True
        assert r == [a for a in attempts if a['module'] == m][-1]
        assert r['dependencies'] == {d: done[d]['object_sha256'] for d in deps}
        obj = cache / (m.replace('.', '/') + '.olean')
        assert bind(obj) == r['object_sha256']
        assert r['companions'] == {str(p): bind(p) for p in obj.parent.glob(obj.name + '*')}
        assert str(obj) in r['companions']
        assert r['command'] == ['lake', 'env', 'lean', '-j1', '-M12288',
                               '--root=' + str(candidates[0]), '-o', str(obj), str(source)]
        assert r['cwd'] == str(build / 'workspace')
        assert r['timeout_seconds'] == 900 and r['memory_mebibytes'] == 12288
        log = text(r['log']); assert bind(r['log']) == r['log_sha256']
        assert 'error:' not in log and 'sorryAx' not in log
        warnings[m] = len(re.findall(r'\bwarning:', log))
        selected[m] = {'source_sha256': bind(source), 'object_sha256': bind(obj),
                       'log_sha256': bind(r['log']), 'attempt': r['index']}
        sources[str(source)] = bind(source); objects[str(obj)] = bind(obj); elapsed += r['seconds']
    assert externals == {'Init'} and inv['direct_external_imports'] == ['Init']
    assert {str(p) for p in cache.rglob('*.olean')} == set(objects)
    closure = set()
    def visit(m):
        if m in closure: return
        closure.add(m)
        for d in edges[m]: visit(d)
    visit(target); assert closure == set(order)
    assert len(attempts) == 208
    failures = [r for r in attempts if r['status'] != 'PASS']
    assert [(r['index'], r['module']) for r in failures] == [(151, 'BusyBeaver.ZFC.KSource215'),
        (199, 'BusyBeaver.ZFC.DomRho8'), (204, 'BusyBeaver.ZFC.L2RootPerm'), (206, 'BusyBeaver.ZFC.SeedPerm')]
    for r in failures: assert bind(r['log']) == r['log_sha256']

    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    reports = {}
    expected_names = {
        'independent': ['EndpointAudit215.blank_halts_exactly_when_zfc_has_a_finite_refutation',
                        'EndpointAudit215.nonhalting_exactly_when_zfc_is_consistent'],
        'axiom-components': ['SetTheory.BusyBeaver.ZFC.KEndpoint215.blank_halts_iff_zfc_refutation',
            'SetTheory.BusyBeaver.ZFC.KEndpoint215.nonhalting_iff_zfc_consistency',
            'SetTheory.BusyBeaver.ZFC.KDense215.commutes', 'SetTheory.BusyBeaver.ZFC.KBoot215.boot',
            'SetTheory.BusyBeaver.ZFC.KSites215.covered', 'SetTheory.BusyBeaver.ZFC.KEndpoint215.p215_boot_iff',
            'K215Audit.blank_halts_exact', 'K215Audit.nonhalting_exact']}
    for label, names in expected_names.items():
        folder = build / 'audit' / label; r = doc(folder / 'verification.json')
        assert r['status'] == 'PASS' and r['exit_code'] == 0 and not r['timed_out']
        assert r['inputs_unchanged'] and r['before'] == r['after']
        assert r['modules'] == 204 and r['exact_module_set'] and r['exact_direct_dependency_edges']
        for p, h in r['before'].items(): assert bind(p) == h
        assert sources.items() <= r['before'].items() and objects.items() <= r['before'].items()
        src = Path(r['source']); assert bind(src) == r['source_sha256'] == bind(folder / src.name)
        if label == 'independent':
            assert bind(src) == bind(Path(__file__).resolve().parents[1] / 'EndpointAudit215.lean')
        obj = folder / (src.stem + '.olean')
        assert r['fresh_companions'] == {str(p): bind(p) for p in folder.glob(src.stem + '.olean*')}
        assert str(obj) in r['fresh_companions']
        assert r['command'] == ['lake', 'env', 'lean', '-j1', '-M12288',
                               '--root=' + str(src.parent), '-o', str(obj), str(src)]
        assert r['cwd'] == str(build / 'workspace') and r['timeout_seconds'] == 120
        log = text(folder / 'compiler.log'); assert bind(folder / 'compiler.log') == r['log_sha256']
        rows = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", log, re.S)
        assert [n for n, _ in rows] == names
        assert not re.sub(r"'[^']+' depends on axioms: \[[^]]*\]", '', log, flags=re.S).strip()
        axioms = {n: sorted(x.strip() for x in body.split(',')) for n, body in rows}
        assert all(set(xs) <= allowed for xs in axioms.values())
        reports[label] = {'record_sha256': bind(folder / 'verification.json'),
                          'source_sha256': bind(src), 'object_sha256': bind(obj),
                          'log_sha256': bind(folder / 'compiler.log'), 'axioms': axioms}
    assert author['status'] == 'PASS' and author['project_modules'] == 204
    assert author['exact_direct_project_edges'] == edges
    assert author['fresh_objects'] == {m: selected[m]['object_sha256'] for m in order}
    assert author['completed_sha256'] == bind(build / 'completed.json')
    assert author['attempts_sha256'] == bind(build / 'attempts.json')
    assert author['inventory_sha256'] == bind(build / 'inventory-v5.json')
    assert author['toolchain_boundary_sha256'] == bind(build / 'toolchain-boundary-v5.json')
    # Rebind the previously independently parsed cross-language literal inputs, without rerunning it.
    old = doc(Path(__file__).resolve().parents[1] / 'actual/partition-v2/literal-bindings.json')
    assert old['status'] == 'PASS_LITERAL_BINDINGS'
    for rel, pin in old['pins'].items(): assert bind(repo / rel) == pin['sha256']
    assert old['working_states'] == 215 and old['actions'] == 430 and old['source_leaves'] == 4751
    assert old['lean_boot_matches_checkpoint']
    after = {p: sha(p) for p in before}; assert after == before
    result = {'status': 'INDEPENDENT_LEAN_ACTUAL_PEER_PASS', 'module_count': 204,
        'scope': 'Independent read-only live artifact, exact command/dependency, literal-pin and raw axiom-report review; no compiler rerun.',
        'explicit_external_imports': ['Init'], 'axiom_reports': reports,
        'selected_successes': selected, 'direct_edges': edges,
        'source_warnings': {m: c for m, c in warnings.items() if c},
        'source_warning_count': sum(warnings.values()), 'successful_source_seconds': elapsed,
        'historical_failed_attempts': [{'index': r['index'], 'module': r['module'],
            'log_sha256': r['log_sha256'], 'timed_out': r['timed_out']} for r in failures],
        'working_states': 215, 'actions': 430, 'expanded_source_leaves': 4751,
        'literal_inputs_unchanged_since_independent_parse': True,
        'author_review_sha256': bind(build / 'final-review.json'),
        'all_bound_inputs_unchanged': True, 'inputs': before}
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open('x') as f: f.write(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ['status', 'module_count', 'working_states', 'actions', 'expanded_source_leaves', 'source_warning_count']}, indent=2))


if __name__ == '__main__': main()
