"""Reproduce the finite V1 proof-certificate validation.

This test/producer code is untrusted support. It is not imported by the checker.
The written proof establishes the general theorem; these tests verify concrete
fully expanded primitive certificates, their target guard, and scope boundaries.
"""
import ast
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import platform
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
CHECKER = ROOT / 'code/qe_restricted.py'
BASELINE = ROOT / 'reference/baseline_bytes.py'
FIXTURES = ROOT / 'fixtures/qe_cases.json'
GUARD = """            if not m[1:] and not (t == [0] or type(t) is int and k <= t < 0):
                raise ValueError('QE target must be canonical one or an allocated numerical variable')
"""


def core(path):
    tree = ast.parse(path.read_text())
    tree.body = [n for n in tree.body
                 if isinstance(n, (ast.Import, ast.ImportFrom, ast.FunctionDef, ast.Assign))]
    return compile(ast.fix_missing_locations(tree), str(path), 'exec')


def run_core(compiled, packet):
    namespace = {}
    exec(compiled, namespace)
    data = copy.deepcopy(packet)
    try:
        namespace['q'] = data.pop
        result = namespace['c'](data.pop(), [])
        accepted = bool(result)
        error = None
    except BaseException as exception:
        accepted = False
        error = type(exception).__name__
    return {'accepted': accepted, 'remaining_instructions': len(data),
            'final_freshness_floor': namespace['k'], 'error': error}


def tree_nodes(proof):
    return 1 + sum(tree_nodes(proof[key])
                   for key in ('major', 'minor', 'premise', 'continuation') if key in proof)


def cli(path, packet, optimized):
    command = [sys.executable] + (['-O'] if optimized else []) + [str(path)]
    process = subprocess.run(command, input=json.dumps(packet), text=True,
                             capture_output=True, timeout=10)
    return {'accepted': process.returncode == 0 and process.stdout == 'ACCEPT\n',
            'exit_status': process.returncode, 'stdout': process.stdout,
            'optimized': optimized}


def load_producer():
    spec = importlib.util.spec_from_file_location('qe_producer', ROOT / 'code/qe_producer.py')
    producer = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(producer)
    return producer


def main():
    records = json.loads(FIXTURES.read_text())['cases']
    producer = load_producer()
    reproduced = json.loads(json.dumps(producer.create_cases()))
    reproduction_ok = reproduced == records
    restricted_text = CHECKER.read_text()
    # Discard only the explanatory module docstring; the frozen program begins
    # at its unchanged import. Deleting the one target guard must recover the
    # exact inherited source bytes, so unrelated edits cannot go unnoticed.
    inherited_part = restricted_text[restricted_text.index('import json\n'):]
    source_guard_only = (inherited_part.count(GUARD) == 1 and
                         inherited_part.replace(GUARD, '', 1) == BASELINE.read_text())
    compiled = core(CHECKER)
    runs = []
    failures = []
    for case in records:
        result = run_core(compiled, case['packet'])
        if result['accepted'] != case['accept']:
            failures.append({'case': case['name'], 'kind': 'in_process', 'result': result})
        if case['accept'] and result['remaining_instructions'] != 0:
            failures.append({'case': case['name'], 'kind': 'unused_accepted_prefix', 'result': result})
        subprocess_results = []
        for optimized in (False, True):
            cli_result = cli(CHECKER, case['packet'], optimized)
            expected_stdout = 'ACCEPT\n' if case['accept'] else 'REJECT\n'
            if ((cli_result['exit_status'] == 0) != case['accept'] or
                    cli_result['stdout'] != expected_stdout):
                failures.append({'case': case['name'], 'kind': 'CLI', 'result': cli_result})
            subprocess_results.append(cli_result)
        runs.append({'case': case['name'], 'expected': case['accept'],
                     'closed': case.get('closed', False), 'in_process': result,
                     'cli': subprocess_results})
    baseline_runs = []
    for case in records:
        if case.get('baseline_accept') or case['name'].startswith('expanded_QE_'):
            result = cli(BASELINE, case['packet'], False)
            baseline_runs.append({'case': case['name'], 'result': result})
            if not result['accepted']:
                failures.append({'case': case['name'], 'kind': 'baseline', 'result': result})
    comparisons = []
    for case in records:
        if case['name'].startswith('expanded_QE_'):
            suffix = case['name'][12:]
            direct = next(c for c in records if c['name'] == 'reject_direct_QE_' + suffix)
            expanded_count = tree_nodes(case['proof_tree'])
            direct_count = tree_nodes(direct['proof_tree'])
            row = {'case': suffix, 'expanded_primitive_nodes': expanded_count,
                   'direct_primitive_nodes': direct_count,
                   'increase': expanded_count - direct_count,
                   'expanded_packet_instructions': len(case['packet']) - 1,
                   'direct_packet_instructions': len(direct['packet']) - 1}
            comparisons.append(row)
            if row['increase'] != 9:
                failures.append({'case': suffix, 'kind': 'proof_node_bound', 'result': row})
    positive_packets = {}
    for case in records:
        if case['name'].startswith('expanded_QE_'):
            suffix = case['name'][12:]
            path = ROOT / ('fixtures/qe_' + suffix + '.json')
            matches = json.loads(path.read_text()) == case['packet']
            positive_packets[str(path.relative_to(ROOT))] = {
                'matches_fixture': matches,
                'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
            if not matches:
                failures.append({'case': case['name'], 'kind': 'standalone_packet_mismatch'})
    report = {
        'python': platform.python_version(),
        'checker': 'code/qe_restricted.py',
        'baseline': 'reference/baseline_bytes.py',
        'checker_sha256': hashlib.sha256(CHECKER.read_bytes()).hexdigest(),
        'baseline_sha256': hashlib.sha256(BASELINE.read_bytes()).hexdigest(),
        'source_change_is_only_target_guard_plus_docstring': source_guard_only,
        'producer_reproduced_every_fixture': reproduction_ok,
        'cases': len(records),
        'accepted_closed_cases': sum(c['accept'] and c.get('closed', False) for c in records),
        'rejected_cases': sum(not c['accept'] for c in records),
        'restricted_cli_runs': 2 * len(records),
        'baseline_cli_runs': len(baseline_runs),
        'all_accepted_packets_consumed_completely': all(
            r['in_process']['remaining_instructions'] == 0 for r in runs if r['expected']),
        'proof_size_comparisons': comparisons,
        'standalone_positive_packets': positive_packets,
        'results': runs,
        'baseline_results': baseline_runs,
        'failures': failures,
        'all_passed': source_guard_only and reproduction_ok and not failures,
        'scope': ('Finite replay of three closed fully expanded QE translations, including a nested '
                  'numerical target and equality transport beneath Q; direct forbidden-target, '
                  'freshness, target-alias, missing-computation, malformed-syntax, and falsity controls. '
                  'The producer implements a QE macro for supplied primitive premise trees; it does '
                  'not implement an arbitrary-proof translator, and this suite is not a metatheory '
                  'formalization or a proof of absolute minimality.')
    }
    output = ROOT / 'evidence/qe_validation.json'
    output.parent.mkdir(exist_ok=True)
    output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: report[k] for k in (
        'cases', 'accepted_closed_cases', 'rejected_cases', 'restricted_cli_runs',
        'baseline_cli_runs', 'source_change_is_only_target_guard_plus_docstring',
        'producer_reproduced_every_fixture', 'all_accepted_packets_consumed_completely',
        'proof_size_comparisons', 'failures', 'all_passed')}, indent=2))
    if not report['all_passed']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
