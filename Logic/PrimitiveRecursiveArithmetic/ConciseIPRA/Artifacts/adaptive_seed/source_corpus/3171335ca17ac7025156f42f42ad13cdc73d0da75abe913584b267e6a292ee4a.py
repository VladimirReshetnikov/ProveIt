"""Reproduce semantic regression fixtures, whole-source metrics and CLI runs.

The generated finite tests do not prove soundness or bi-interpretability.
Every checked process is a complete standalone kernel, not an extracted core.
"""
import concurrent.futures
import hashlib
import json
import platform
import runpy
import subprocess
import sys
from pathlib import Path

from translate import translate

ROOT = Path(__file__).resolve().parents[1]
PROFILES = ('principal', 'tokens', 'ast', 'bytes', 'readable')


def kernel_path(profile):
    name = {'principal': 'kernel.py', 'readable': 'readable.py'}.get(profile, 'kernel_' + profile + '.py')
    return ROOT / 'code' / name


def packet(instructions, goal):
    return list(reversed(instructions)) + [goal]


def negative_cases():
    comp = [0, 0, 0, 0]
    false = [0, [0]]
    major = [[0, 0, 0], 0]
    goals = {
        'false_zero_computation': [[[0, 0, 0], [0]]],
        'false_positive_initializer': [[[0, [0], 0], 0]],
        'false_successor_computation': [[[[0], 0, [3]], 0]],
        'malformed_successor_counter': [[[[0, 0], 0, 0], 0]],
        'false_numerical_equation': [false],
        'scalar_zero_rejects': [0],
        'future_root_parameter': [[-1, 0]],
        'oversized_formula_constructor': [[0, 0, 0, 0]],
        'null_syntax': [None],
        'string_syntax': ['x'],
        'mapping_syntax': [{'': 0}],
    }
    result = [{'name': name, 'packet': packet([comp], goal[0]), 'accept': False}
              for name, goal in goals.items()]
    result.extend([
        {'name': 'missing_instruction', 'packet': [false], 'accept': False},
        {'name': 'wrong_instruction_arity', 'packet': [[0, 0, 0], major], 'accept': False},
        {'name': 'empty_packet', 'packet': [], 'accept': False},
        {'name': 'nonarray_packet', 'packet': None, 'accept': False},
        {'name': 'unscoped_witness', 'packet': packet([[0, 0, 0, 1]],
                                                  [0, 0, [3, 3]]), 'accept': False},
        {'name': 'false_after_unmatched_endpoints',
         'packet': packet([[major, 0, 0, 0], comp, comp], false), 'accept': False},
        {'name': 'false_after_unmatched_target',
         'packet': packet([[major, major[0], 0, [0, 0]], comp, comp], false),
         'accept': False},
        {'name': 'false_major_cannot_be_used',
         'packet': packet([[false, 0, 0, 0], comp, comp], false), 'accept': False},
    ])
    return result


def fixtures():
    source = json.loads((ROOT / 'reference/baseline_cases.json').read_text())['cases']
    source = [x for x in source if x['accept']]
    output = {}
    for focused in (False, True):
        cases = []
        for x in source:
            for unmatched in (None, 'endpoints', 'target'):
                value, stats = translate(x['packet'], focused, unmatched)
                cases.append({'name': x['name'] + '/' + (unmatched or 'canonical'),
                              'packet': value, 'accept': True,
                              'translation': stats})
        cases.extend(negative_cases())
        if not focused:
            # This noncanonical truth alias illustrates why the theorem is
            # about decoded consequences, not old/new raw verdict identity.
            major = [[0, 0, 0], 0]
            cases.append({'name': 'decoded_truth_alias_after_unmatched',
                          'packet': packet([[major, 0, 0, 0], [0, 0, 0, 0]], []),
                          'accept': True})
        output['focused' if focused else 'ordinary'] = cases
    return output


def run_one(item):
    profile, case = item
    path = kernel_path(profile)
    proc = subprocess.run([sys.executable, '-I', '-S', str(path)],
                          input=json.dumps(case['packet']), text=True,
                          capture_output=True, timeout=15)
    accepted = proc.returncode == 0 and proc.stdout == 'ACCEPT\n'
    rejected = proc.returncode != 0 and proc.stdout == 'REJECT\n'
    okay = accepted if case['accept'] else rejected
    return {'profile': profile, 'name': case['name'], 'expected': case['accept'],
            'accepted': accepted, 'verdict_valid': accepted or rejected,
            'pass': okay,
            **({} if okay else {'returncode': proc.returncode,
                               'stdout': proc.stdout, 'stderr': proc.stderr[-1800:]})}


def main():
    data = fixtures()
    (ROOT / 'tests/fixtures.json').write_text(json.dumps(data, indent=2) + '\n')
    work = [(p, case) for p in PROFILES
            for case in data['focused' if p == 'bytes' else 'ordinary']]
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(run_one, work))
    failures = [x for x in results if not x['pass']]
    metric = runpy.run_path(str(ROOT / 'reference/source_measure.py'))['metrics']
    measured = {p: metric(kernel_path(p))
                for p in PROFILES}
    summary = {
        'status': 'PASS' if not failures else 'FAIL',
        'python': platform.python_version(),
        'whole_program_runs': len(results),
        'profiles': {p: {'runs': sum(x['profile'] == p for x in results),
                         'expected_accept': sum(x['profile'] == p and x['expected'] for x in results),
                         'expected_reject': sum(x['profile'] == p and not x['expected'] for x in results)}
                     for p in PROFILES},
        'metrics': measured,
        'coordinate_envelope': {k: min(x[k] for x in measured.values())
                                for k in ('normalized_tokens', 'ast_nodes', 'normalized_bytes')},
        'failures': failures,
        'scope': 'Finite complete-process regression tests; universal metatheorems are written proofs.',
    }
    (ROOT / 'evidence/validation.json').write_text(json.dumps(summary, indent=2) + '\n')
    (ROOT / 'evidence/validation_cases.json').write_text(json.dumps(results, indent=2) + '\n')
    print(json.dumps(summary, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
