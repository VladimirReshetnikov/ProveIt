"""Replay and pin the complete cochain/geometric whole-call comparison.

No discovery, benchmark, test, PDF build, or historical publication main runs.
The core checkpoint supplies byte-pinned regression dependencies only.
"""
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import re
import sys

DATA = Path(__file__).resolve().parent
ROOT = DATA.parent.parent
sys.path.insert(0, str(ROOT/'fast'))
from strict_pachner32_publication import included_tex, python_dependencies
from geometric_descent_publication import diagnostics
from geometric_descent_research.common import canonical_bytes, source_hashes
from geometric_descent_research.check_evidence import check_benchmark

EXPECTED_MUTATIONS = (
    'audit changed source pin', 'audit missing case', 'audit missing arm',
    'audit bool call count', 'audit geometric method relabelled',
    'audit input PD changed', 'audit endpoint equality negated',
    'bool pivot counter', 'missing capped anchors', 'exceeded pivot cap',
    'geometric result recast as v4',
    'partial marked complete without terminal proof',
    'macro counts algebraically consistent but absent',
    'elementary totals consistent with D but contradict UDD proofs',
    'geometric macro wrong source binding', 'nonterminal endpoint hash changed',
    'native-valid same-diagram wrong-policy proof',
    'timed native-valid wrong full result with recomputed hash',
    'timing changed audit hash', 'timing wrong coverage',
    'timing pair order reversed', 'timing bool duration',
    'timing float byte count', 'timing changed hash', 'timing missing full result',
    'timing warmup result altered and rehashed', 'timing forged median ratio',
)
EXPECTED_VALID_CONTROLS = (
    'unchanged complete audit', 'unchanged complete benchmark',
    'native-valid same-diagram legacy proof in v5',
)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def same(a, b):
    return canonical_bytes(a) == canonical_bytes(b)


def value_at(value, path):
    assert type(path) is list
    for key in path:
        assert type(key) in (str, int)
        value = value[key]
    return value


def mutation_document(original, operations):
    """Bind retained edit programs to their hashes, without replaying controls."""
    assert type(operations) is list and operations
    value = deepcopy(original)
    for operation in operations:
        assert type(operation) is dict
        path = operation['path']
        assert type(path) is list and path
        parent = value_at(value, path[:-1])
        assert type(path[-1]) in (str, int)
        kind = operation['operation']
        if kind == 'set':
            assert set(operation) == {'operation', 'path', 'value'}
            parent[path[-1]] = deepcopy(operation['value'])
        elif kind == 'delete':
            assert set(operation) == {'operation', 'path'}
            del parent[path[-1]]
        elif kind == 'copy':
            assert set(operation) == {'operation', 'path', 'source_path'}
            parent[path[-1]] = deepcopy(value_at(value, operation['source_path']))
        elif kind == 'reverse':
            assert set(operation) == {'operation', 'path'}
            target = value_at(value, path)
            assert type(target) is list
            target.reverse()
        else:
            assert kind == 'rehash-result'
            assert set(operation) == {'operation', 'path'}
            target = value_at(value, path)
            payload = canonical_bytes(target['result'])
            target['result_sha256'] = sha256(payload).hexdigest()
            target['serialized_bytes'] = len(payload)
    assert not same(value, original), 'retained control has an ineffective edit'
    return value


def main():
    if not __debug__:
        raise RuntimeError('publication replay requires assertions enabled')
    audit_path = DATA/'geometric-descent-audit.json'
    benchmark_path = DATA/'geometric-descent-benchmark.json'
    audit_bytes = audit_path.read_bytes()
    audit = json.loads(audit_bytes)
    benchmark = json.loads(benchmark_path.read_bytes())
    pins = source_hashes()
    assert check_benchmark(benchmark, audit, audit_bytes)
    assert same(audit['source_sha256'], pins) and same(benchmark['source_sha256'], pins)
    assert len(pins) == 305
    assert all(r['endpoint_comparison']['exact_typed_equality'] is True for r in audit['records'])
    assert [r['id'] for r in audit['records']] == ['circle', 'trefoil', 'figure_eight', 'TT', 'T25', 'T27', 'W34']
    for record in audit['records']:
        a, b = (record['arms'][arm]['result'] for arm in ('cochain', 'geometric'))
        assert a['status'] == b['status']
        assert a['stats']['lp_pivots'] == b['stats']['lp_pivots']
        assert a['stats']['nodes_attempted'] == b['stats']['nodes_attempted']
    assert [r['arms']['geometric']['result']['status'] for r in audit['records']] == ['UNKNOT']+['KNOTTED']*5+['INCONCLUSIVE']

    # Evidence rejection controls are retained, not rerun by this helper.
    controls_path = DATA/'geometric-descent-corruption-controls.json'
    controls_script = DATA/'geometric-descent-corruption-controls.py'
    controls = json.loads(controls_path.read_bytes())
    assert controls['schema'] == 'geometric-descent-corruption-controls-v1'
    assert controls['passed'] is True and controls['failures'] == [] and controls['active_control'] is None
    assert same(controls['source_sha256'], pins)
    assert controls['script_sha256'] == digest(controls_script)
    assert controls['audit_sha256'] == digest(audit_path)
    assert controls['benchmark_sha256'] == digest(benchmark_path)
    assert controls['discovery_used'] is False and controls['timings_performed'] is False
    assert controls['exhaustive'] is False and controls['execution_trace_reconstructed'] is False
    records = controls['records']
    assert type(records) is list and len(records) == 27
    assert [r['name'] for r in records] == list(EXPECTED_MUTATIONS)
    assert all(r['rejected'] is True and r['expected'] == 'rejected' for r in records)
    assert controls['skipped_controls'] == []
    valid = controls['valid_controls']
    assert type(valid) is list and [r['name'] for r in valid] == list(EXPECTED_VALID_CONTROLS)
    assert all(r['accepted'] is True for r in valid)
    assert same(controls['rejected_mutations'], 27)
    assert same(controls['accepted_valid_controls'], 3)
    assert same([valid[0]['calls'], valid[1]['calls']], [14, 50])
    controls_log = DATA/'geometric-descent-corruption-controls.txt'
    lines = [line for line in controls_log.read_text().splitlines() if line.strip()]
    assert len(lines) == 1
    assert same(json.loads(lines[0]), dict(passed=True, rejected_mutations=27,
        accepted_valid_controls=3, skipped_controls=0))

    cache = controls['native_verifier_cache']
    assert cache['unchanged_controls_populate_first'] is True
    assert cache['callbacks_bypass'] is True
    assert cache['research_checker_results_cached'] is False
    assert cache['fresh_duplicate_native_replay_claimed'] is False
    assert set(cache['functions']) == {'verify_crushing_chain',
        'verify_crushing_recognition', 'verify_normal_pachner_descent',
        'verify_normal_geometric_descent'}
    for counts in cache['functions'].values():
        for key in ('hits', 'misses', 'bypasses', 'exceptions', 'returned_true',
                    'returned_false', 'nonboolean_returns'):
            assert type(counts[key]) is int and counts[key] >= 0
        assert counts['misses']+counts['bypasses'] == sum(counts[key] for key in (
            'exceptions', 'returned_true', 'returned_false', 'nonboolean_returns'))
        entries = counts['entries']
        assert type(entries) is list
        assert all(type(entry['result']) is bool and
            re.fullmatch('[0-9a-f]{64}', entry['arguments_sha256']) for entry in entries)
        assert len({entry['arguments_sha256'] for entry in entries}) == len(entries)
        assert len(entries) <= counts['returned_true']+counts['returned_false']

    # Preserve the stronger control: a valid native same-diagram proof is
    # rejected solely as evidence for the wrong selected experimental policy.
    control_case = valid[2]['case_id']
    cases = {record['id']: record for record in audit['records']}
    assert control_case in cases
    alternate = deepcopy(cases[control_case]['arms']['cochain']['result'])
    chain = (alternate['partial_chain'] if alternate['status'] == 'INCONCLUSIVE'
             else alternate['certificate']['chain'])
    assert any(step['schema'] == 'normal-pachner-descent-v1' for step in chain['steps'])
    chain['schema'] = 'diagram-crushing-v5'
    alternate_sha256 = sha256(canonical_bytes(alternate)).hexdigest()
    assert valid[2]['result_sha256'] == alternate_sha256
    native_control_names = {'native-valid same-diagram wrong-policy proof',
        'timed native-valid wrong full result with recomputed hash'}
    for record in records:
        assert record['target'] in ('audit', 'benchmark')
        original = audit if record['target'] == 'audit' else benchmark
        mutated = mutation_document(original, record['mutations'])
        assert record['mutated_document_sha256'] == sha256(canonical_bytes(mutated)).hexdigest()
        if record['name'] not in native_control_names:
            assert record['native_validity'] is None
            continue
        assert record['native_validity'] is True and record['case_id'] == control_case
        changed_case = next(row for row in mutated['records'] if row['id'] == control_case)
        if record['name'] == 'native-valid same-diagram wrong-policy proof':
            assert record['target'] == 'audit'
            assert record['direct_policy_replay_rejected'] is True
            assert same(changed_case['arms']['geometric']['result'], alternate)
        else:
            assert record['target'] == 'benchmark'
            assert record['native_control_result_sha256'] == alternate_sha256
            sample = changed_case['paired'][0]['samples']['geometric']
            assert same(sample['result'], alternate)
            assert sample['result_sha256'] == alternate_sha256
            assert same(sample['serialized_bytes'], len(canonical_bytes(alternate)))

    environment_path = DATA/'geometric-descent-environment.json'
    environment = json.loads(environment_path.read_bytes())
    assert same(environment['affinity'], [5]) and type(environment['host_logical_cpus']) is int
    assert environment['host_logical_cpus'] > 0
    assert type(environment['returncode']) is int and environment['returncode'] == 0
    assert environment['python'] == benchmark['python']
    assert environment['platform'] == benchmark['platform']
    command = environment['command']
    assert type(command) is list and command and all(type(part) is str and part for part in command)
    assert command[1:] == ['-B', '-S', '-m', 'geometric_descent_research.benchmark',
        '--audit', '../synthesis/data/geometric-descent-audit.json',
        '--output', '../synthesis/data/geometric-descent-benchmark.json']
    assert environment['before']['utc'] < environment['after']['utc']

    # Native modules, test modules, static imports and serialized fixtures
    # must still be exactly those covered by the published 364-test run.
    core_path = DATA/'geometric-descent-publication.json'
    core = json.loads(core_path.read_bytes())
    assert same({key: core[key] for key in ('schema', 'passed', 'tests',
        'test_modules', 'skipped_tests')}, dict(schema='geometric-descent-core-publication-v1',
        passed=True, tests=364, test_modules=41, skipped_tests=0))
    core_pins = core['files_sha256']
    assert len(core_pins) == 950
    tested = {name: value for name, value in core_pins.items()
              if name != 'fast/README.md' and (name.startswith(('fast/', 'reports/79/')) or name in (
                  'synthesis/data/boundary-unlayer-audit.json',
                  'synthesis/data/coherent-obstruction-certificate.json',
                  'synthesis/data/geometric-descent-test-command.txt',
                  'synthesis/data/geometric-descent-tests.txt'))}
    assert tested and all(digest(ROOT/name) == value for name, value in tested.items())
    current_native = set((ROOT/'fast/fastunknot').rglob('*.py'))
    historical_native = {ROOT/name for name in core_pins
        if name.startswith('fast/fastunknot/') and name.endswith('.py')}
    assert current_native == historical_native, 'native Python file set changed since the tests'
    test_command = DATA/'geometric-descent-test-command.txt'
    modules = set(re.findall(r'\btests\.(test_[A-Za-z0-9_]+)\b', test_command.read_text()))
    assert len(modules) == 41
    test_files = {ROOT/'fast/tests'/(name+'.py') for name in modules}
    test_initializer = ROOT/'fast/tests/__init__.py'
    if test_initializer.is_file():
        test_files.add(test_initializer)
    # Dynamic fixture reads are not visible to the static import walker.
    fixtures = {DATA/'boundary-unlayer-audit.json',
        DATA/'coherent-obstruction-certificate.json',
        ROOT/'reports/79/repro/fast/commitment_research/coherent-obstruction-certificate.json',
        ROOT/'reports/79/repro/fast/shared_cover_research/results/exhaustion.json',
        ROOT/'fast/tests/fixtures/causal_noncanonical.json',
        ROOT/'fast/conflict_composition_research/data/generation/tt-state.json.gz',
        ROOT/'fast/strict_pachner32_research/data/generation/euler-queries.json.gz'}
    current_test_dependencies = python_dependencies(test_files | fixtures)
    for path in current_native | current_test_dependencies:
        assert path.is_file() and path.is_relative_to(ROOT)
        name = str(path.relative_to(ROOT))
        assert name in core_pins and digest(path) == core_pins[name], (
            'current native/test dependency is not covered by the core tests', name)
    historical_logs = {DATA/f'geometric-descent-latex-{i}.txt' for i in (1, 2, 3)}
    historical_helpers = {DATA/'strict_pachner32_publication.py',
                          DATA/'geometric_descent_publication.py'}
    for path in historical_logs | historical_helpers:
        assert digest(path) == core_pins[str(path.relative_to(ROOT))]
    builds = [DATA/f'geometric-descent-evidence-latex-{i}.txt' for i in (1, 2, 3)]
    for path in builds:
        log = path.read_text()
        assert 'Output written on report.pdf' in log
        assert not re.search(r'^!|Emergency stop|Fatal error occurred', log, re.MULTILINE)
    final = builds[-1].read_text()
    assert not re.search(r'undefined references|undefined on input|Rerun to get|Label\(s\) may have changed|multiply.defined labels', final)
    baseline = DATA/'geometric-descent-latex-3.txt'
    assert not (diagnostics(final)-diagnostics(baseline.read_text()))
    match = re.search(r'Output written on report\.pdf \((\d+) pages, (\d+) bytes\)', final)
    assert match
    pdf = ROOT/'synthesis/report.pdf'
    assert pdf.read_bytes().startswith(b'%PDF-') and pdf.stat().st_size == int(match[2])
    tex = included_tex(ROOT/'synthesis/report.tex')
    assert ROOT/'synthesis/geometric_descent_crushing.tex' in tex
    files = {Path(__file__).resolve(), DATA/'strict_pachner32_publication.py',
        DATA/'geometric_descent_publication.py', core_path, baseline,
        audit_path, benchmark_path, controls_path, controls_script, environment_path,
        DATA/'geometric_descent_benchmark_run.py', pdf, ROOT/'fast/README.md',
        ROOT/'synthesis/README.md', *builds, *tex, *historical_logs,
        *current_native, *current_test_dependencies}
    for name in ('geometric-descent-audit.txt', 'geometric-descent-benchmark.txt',
                 'geometric-descent-corruption-controls.txt'):
        files.add(DATA/name)
    files.update(ROOT/name for name in tested)
    files.update(ROOT/name for name in pins)
    files = python_dependencies(files)
    assert all(p.is_file() and p.is_relative_to(ROOT) for p in files)
    assert source_hashes() == pins
    result = dict(schema='geometric-descent-evidence-publication-v1', passed=True,
        tests=364, test_modules=41, skipped_tests=0, ordinary_audit_calls=14,
        exact_endpoint_comparisons=7, equal_endpoints=7, timed_and_warmup_calls=50,
        benchmark_cases=5, rejected_controls=len(records), accepted_valid_controls=3,
        native_valid_wrong_policy_control=True,
        corruption_controls_reexecuted=False,
        duplicate_native_control_replay_cached=True,
        general_quasipolynomial=False, resolving_parameter_transport_claimed=False,
        discovery_run_by_this_helper=False, timing_run_by_this_helper=False,
        tests_or_build_run_by_this_helper=False,
        report_pages=int(match[1]), report_bytes=int(match[2]),
        benchmark_summaries={r['id']: r['summary'] for r in benchmark['records']},
        tested_dependency_count=len(tested), current_native_modules=len(current_native),
        current_test_dependency_count=len(current_test_dependencies), included_tex_files=len(tex),
        files_sha256={str(p.relative_to(ROOT)): digest(p) for p in sorted(files)})
    (DATA/'geometric-descent-evidence-publication.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(dict(passed=True, tests=364, ordinary_audit_calls=14,
        timed_and_warmup_calls=50, rejected_controls=len(records),
        report_pages=int(match[1]), pinned_files=len(files), general_quasipolynomial=False), sort_keys=True))


if __name__ == '__main__':
    main()
