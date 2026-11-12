"""Reproduce full-source measurements and concrete kernel evidence.

All certificate generation, trace translation and source measurement stay
outside the measured kernels. This is finite regression evidence, not a
formal verification of the universal metatheorems or a minimality proof.
"""
from pathlib import Path
import ast
import concurrent.futures
import copy
import hashlib
import importlib.util
import json
import platform
import random
import subprocess
import sys

from translate_uniform import translate

ROOT = Path(__file__).resolve().parents[1]
PROFILES = ('tokens', 'structure', 'bytes')
BASELINE_CASES = json.loads((ROOT / 'fixtures/baseline_cases.json').read_text())['cases']


def load_module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


MEASURE = load_module(ROOT / 'reference/source_measure.py', 'source_measure')


def core(path):
    tree = ast.parse(path.read_text())
    tree.body = [n for n in tree.body if isinstance(n, (ast.Import, ast.ImportFrom, ast.Assign, ast.FunctionDef))]
    return compile(ast.fix_missing_locations(tree), str(path), 'exec')


PATHS = {(p, kind): ROOT / folder / (prefix + p + '.py')
         for p in PROFILES
         for kind, folder, prefix in [('old', 'reference', 'baseline_'),
                                      ('new', 'code', 'kernel_'),
                                      ('explicit', 'reference', 'uniform_explicit_')]}
CORES = {key: core(path) for key, path in PATHS.items()}


def run(profile, kind, packet):
    namespace = {}
    exec(CORES[profile, kind], namespace)
    data = copy.deepcopy(packet)
    try:
        namespace['q'] = data.pop
        result = namespace['c'](namespace['q'](), [])
        accepted = bool(result) if kind == 'old' else True
    except BaseException:
        accepted = False
    return accepted, namespace['k'], data


def assert_equivalent(profile, packet):
    explicit = run(profile, 'explicit', packet)
    sentinel = run(profile, 'new', packet)
    if explicit[0] != sentinel[0] or explicit[0] and explicit[1:] != sentinel[1:]:
        raise RuntimeError(('Sentinel/exception discrepancy', profile, packet, explicit, sentinel))


def tree_paths(value):
    yield ()
    if isinstance(value, list):
        for index, child in enumerate(value):
            for path in tree_paths(child):
                yield (index,) + path


def replaced(value, path, replacement):
    if not path:
        return copy.deepcopy(replacement)
    result = copy.deepcopy(value)
    at = result
    for index in path[:-1]:
        at = at[index]
    at[path[-1]] = copy.deepcopy(replacement)
    return result


def focused_cases():
    # M is the iterator-base computation I(0,0;u.0)=0.
    M = [[0, 0, 0], 0]
    return [
        {'name': 'fresh/zero_computation', 'packet': [[0, 0], M], 'accept': True},
        {'name': 'fresh/positive_initializer', 'packet': [[0, 0], [[0, [0], 0], [0]]], 'accept': True},
        {'name': 'fresh/false_computation', 'packet': [[0, 0], [[0, 0, 0], [0]]], 'accept': False},
        # The new uniform continuation adds[] as a theorem context entry.
        {'name': 'fresh/truth_shortcut', 'packet': [[0, 0], [M, []], []], 'accept': True},
        {'name': 'fresh/mismatch_with_truth_available', 'packet': [[0, 0], [M, [1, 0]], []], 'accept': False},
        {'name': 'fresh/mismatch_followed_by_computation', 'packet': [[0, 0], [0, 0], [M, [1, 0]], [[0], 0]], 'accept': False},
        {'name': 'fresh/scalar_zero_with_truth_available', 'packet': [[0, 0], [M, 0], 0], 'accept': False},
        *[{'name': 'fresh/scalar_goal_' + str(i), 'packet': [[0, 0], x], 'accept': False}
          for i, x in enumerate([0, False, True, -1, -100, 0.5, -0.5])],
        *[{'name': 'fresh/malformed_goal_' + str(i), 'packet': [x], 'accept': False}
          for i, x in enumerate([None, '', 'x', 'abc', {}, {'x': 1}, [0, 0, 0, 0]])],
        {'name': 'fresh/empty_packet', 'packet': [], 'accept': False},
    ]


def cli(job):
    profile, kind, optimized, case = job
    command = [sys.executable] + (['-O'] if optimized else []) + [str(PATHS[profile, kind])]
    process = subprocess.run(command, input=json.dumps(case['packet']), text=True,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=10)
    expected = ('ACCEPT\n', 0) if case['accept'] else ('REJECT\n', 1)
    if (process.stdout, process.returncode) != expected:
        raise RuntimeError(('CLI result', profile, kind, optimized, case['name'],
                            process.stdout, process.returncode, process.stderr))
    return 1


def main():
    (ROOT / 'evidence').mkdir(exist_ok=True)
    translated = []
    for case in BASELINE_CASES:
        for profile in PROFILES:
            if run(profile, 'old', case['packet'])[0] != case['accept']:
                raise RuntimeError(('Baseline fixture', profile, case['name']))
        if case['accept']:
            packet, stats = translate(case['packet'])
            translated.append({'name': case['name'], 'packet': packet, 'accept': True,
                               'translation': stats})
    (ROOT / 'fixtures/translated_cases.json').write_text(json.dumps({
        'source': 'fixtures/baseline_cases.json', 'cases': translated,
        'translation_failures': [],
        'scope': 'Concrete successful old certificates; universal metatheory is a written proof.'}, indent=2) + '\n')
    # Unchanged negative packets are included only after their new verdicts
    # are checked. No general raw-format equivalence is asserted.
    negatives = [c for c in BASELINE_CASES if not c['accept']]
    fresh = focused_cases()
    cases = translated + negatives + fresh
    (ROOT / 'fixtures/focused_cases.json').write_text(json.dumps({'cases': fresh}, indent=2) + '\n')
    for profile in PROFILES:
        for case in cases:
            assert_equivalent(profile, case['packet'])
            if run(profile, 'new', case['packet'])[0] != case['accept']:
                raise RuntimeError(('New fixture', profile, case['name']))
    rng = random.Random(2026110907)
    replacements = [None, False, True, -100, -3, -1, 0, 1, 2, 4, 100,
                    -0.5, 0.5, 1.5, '', 'x', 'abc', {}, {'x': 1}, [], [0],
                    [0, 0], [0, 0, 0], [0, 0, 0, 0]]
    mutations = []
    for case in cases:
        locations = list(tree_paths(case['packet']))
        for _ in range(24):
            mutations.append(replaced(case['packet'], rng.choice(locations), rng.choice(replacements)))
    for profile in PROFILES:
        for packet in mutations:
            assert_equivalent(profile, packet)
    jobs = [(p, 'old', optimized, case) for p in PROFILES for optimized in (False, True) for case in BASELINE_CASES]
    jobs += [(p, 'new', optimized, case) for p in PROFILES for optimized in (False, True) for case in cases]
    with concurrent.futures.ThreadPoolExecutor(max_workers=6) as pool:
        cli_runs = sum(pool.map(cli, jobs))
    metrics = {p: {kind: MEASURE.metrics(PATHS[p, kind]) for kind in ('old', 'new', 'explicit')} for p in PROFILES}
    receipt = {
        'python': platform.python_version(), 'implementation': platform.python_implementation(),
        'source_snapshot': '7e694b036f89a0f16313089329555da531d6a656',
        'baseline_case_count': len(BASELINE_CASES), 'translated_positive_cases': len(translated),
        'translation_failures': [], 'unchanged_negative_cases_rechecked': len(negatives),
        'new_focused_cases': len(fresh), 'uniform_fixture_cases': len(cases),
        'uniform_fixture_comparison_pairs': len(cases) * len(PROFILES),
        'sentinel_exception_mutation_comparison_pairs': len(mutations) * len(PROFILES),
        'fresh_cli_runs': cli_runs,
        'ordinary_and_optimized_python': True, 'accepted_final_states_compared': True,
        'all_passed': True, 'metrics': metrics,
        'old_coordinate_envelope': {k: min(metrics[p]['old'][k] for p in PROFILES) for k in ('normalized_tokens', 'ast_nodes', 'normalized_bytes')},
        'new_coordinate_envelope': {k: min(metrics[p]['new'][k] for p in PROFILES) for k in ('normalized_tokens', 'ast_nodes', 'normalized_bytes')},
        'limits': 'Finite certificate and malformed-input regression evidence. No formal metatheory verification, absolute size lower bound or raw old/new format identity is claimed.'}
    (ROOT / 'evidence/kernel_validation.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: v for k, v in receipt.items() if k != 'metrics'}, indent=2))


if __name__ == '__main__':
    main()
