"""Bounded, untimed differential against the exact pre-optimization sources.

Run from any directory with Python 3 and git.  This is supplemental finite
validation, not an exhaustive oracle, a benchmark, or a complexity theorem.
Every case and allowance is fixed below before inspecting any result.
"""
from __future__ import annotations

import argparse
import hashlib
import inspect
import io
import json
import random
import subprocess
import sys
import tarfile
import types
from collections import Counter
from fractions import Fraction
from math import gcd
from pathlib import Path

DATA = Path(__file__).resolve().parent
ROOT = DATA.parent.parent
FAST = ROOT / 'fast'
REPOSITORY = ROOT.parent.parent
PREFIX = 'Topology/UnknotRecognition/'
REVISION = '973c6fdee7b9ee6239c16b8d325207b6f667e95e'
SEED = 937
CHANGED = {'fast/fastunknot/exact_lp.py', 'fast/fastunknot/normal_euler_tree.py'}
sys.path.insert(0, str(FAST))

from fastunknot import exact_lp, normal_euler_tree, normal_euler_transversal
from fastunknot.integer_codec import encoded_integer, json_safe
from fastunknot.normal_euler_tree_verify import verify_euler_branch_tree
from fastunknot.normal_surface_geometry import _prepare, _coordinates
from normal_orbit_research.fixtures import layered_torus


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def dumps(value):
    return json.dumps(json_safe(value), sort_keys=True, separators=(',', ':'), ensure_ascii=True)


def typed_equal(left, right):
    if type(left) is not type(right):
        return False
    if type(left) is dict:
        return left.keys() == right.keys() and all(typed_equal(left[k], right[k]) for k in left)
    if type(left) in (list, tuple):
        return len(left) == len(right) and all(typed_equal(a, b) for a, b in zip(left, right))
    return left == right


def typed_form(value):
    """Retain a digest that distinguishes tuples/lists and integers/booleans."""
    name = type(value).__name__
    if type(value) is dict:
        return [name, [[typed_form(k), typed_form(value[k])] for k in sorted(value)]]
    if type(value) in (list, tuple):
        return [name, [typed_form(v) for v in value]]
    return [name, json_safe(value)]


def native_hashes():
    return {str(path.relative_to(ROOT)): sha(path.read_bytes())
            for path in sorted((FAST / 'fastunknot').rglob('*.py'))}


def fixed_hashes():
    paths = [Path(__file__).resolve(), FAST / 'normal_orbit_research' / 'fixtures.py']
    initializer = FAST / 'normal_orbit_research' / '__init__.py'
    if initializer.is_file():
        paths.append(initializer)
    return {str(p.relative_to(ROOT)): sha(p.read_bytes()) for p in paths}


def git(*arguments):
    return subprocess.check_output(['git', *arguments], cwd=REPOSITORY)


def historical_modules(current):
    archive = git('archive', '--format=tar', REVISION, PREFIX + 'fast/fastunknot')
    with tarfile.open(fileobj=io.BytesIO(archive)) as handle:
        historical = {member.name[len(PREFIX):]: handle.extractfile(member).read()
                      for member in handle.getmembers()
                      if member.isfile() and member.name.endswith('.py')}
    require(set(historical) == set(current), 'historical/current native Python file sets differ')
    old_hashes = {path: sha(raw) for path, raw in historical.items()}
    changed = {path for path in current if current[path] != old_hashes[path]}
    require(changed == CHANGED, 'native differences are not exactly the two declared files')
    modules, source_hashes = {}, {}
    for basename in ('exact_lp', 'normal_euler_tree', 'normal_euler_transversal'):
        path = 'fast/fastunknot/' + basename + '.py'
        raw = git('show', REVISION + ':' + PREFIX + path)
        require(raw == historical[path], 'git show/archive source disagreement')
        name = 'fastunknot._prepared_differential_old_' + basename
        module = types.ModuleType(name)
        module.__package__ = 'fastunknot'
        module.__file__ = 'git:' + REVISION + ':' + PREFIX + path
        sys.modules[name] = module
        exec(compile(raw, module.__file__, 'exec'), module.__dict__)
        modules[basename] = module
        source_hashes[path] = sha(raw)
    old_lp, old_tree, old_transversal = (modules[k] for k in (
        'exact_lp', 'normal_euler_tree', 'normal_euler_transversal'))
    old_tree.solve_nonnegative_kernel = old_lp.solve_nonnegative_kernel
    old_transversal._EulerMaskOracle = old_tree._EulerMaskOracle
    old_transversal._euler_search_stats = old_tree._euler_search_stats
    old_transversal._mask = old_tree._mask
    return modules, dict(revision=REVISION, native_files_sha256=old_hashes,
                        loaded_source_sha256=source_hashes,
                        changed_native_files=sorted(changed),
                        unchanged_native_files=len(current)-len(changed))


class Checks:
    def __init__(self, trace=False):
        self.count, self.events = 0, [] if trace else None

    def __call__(self):
        self.count += 1
        if self.events is None:
            return
        frame = inspect.currentframe().f_back
        try:
            module = frame.f_globals.get('__name__', '')
            function = frame.f_code.co_name
            if module in ('fastunknot.exact_lp', 'fastunknot._prepared_differential_old_exact_lp'):
                module = 'fastunknot.exact_lp'
                if function == 'solve_nonnegative_kernel':
                    # Old parsing lived in the facade; its entry and per-row
                    # callback sites now straddle facade and parsing helper.
                    event = ('facade', 'matrix.row' if 'source' in frame.f_locals else 'entry')
                elif function == '_parse_kernel_matrix':
                    event = ('facade', 'matrix.row')
                else:
                    event = (function, frame.f_lineno - frame.f_code.co_firstlineno)
            else:
                event = (module, function, frame.f_lineno - frame.f_code.co_firstlineno)
            self.events.append(event)
        finally:
            del frame

    def record(self):
        result = dict(count=self.count)
        if self.events is not None:
            runs = []
            for event in self.events:
                if runs and runs[-1][0] == list(event):
                    runs[-1][1] += 1
                else:
                    runs.append([list(event), 1])
            result.update(events_sha256=sha(dumps(self.events).encode()), events_rle=runs)
        return result


def rational(value):
    if type(value) in (list, tuple):
        require(len(value) == 2, 'rational length')
        numerator, denominator = map(encoded_integer, value)
        require(denominator > 0, 'positive rational denominator')
        return Fraction(numerator, denominator)
    return Fraction(encoded_integer(value))


def rank(rows):
    """Small exact rank replay, using rightmost pivots independently of LP."""
    echelon = {}
    for original in rows:
        row = list(map(Fraction, original))
        for column in sorted(echelon, reverse=True):
            coefficient = row[column]
            if coefficient:
                row = [a-coefficient*b for a, b in zip(row, echelon[column])]
        pivot = next((j for j in range(len(row)-1, -1, -1) if row[j]), None)
        if pivot is not None:
            divisor = row[pivot]
            echelon[pivot] = [a/divisor for a in row]
    return len(echelon)


def replay_lp(matrix, objective, options, answer):
    C, c = [[rational(v) for v in row] for row in matrix], list(map(rational, objective))
    n = len(c)
    require(type(answer) is dict, 'LP result dictionary')
    require(all(type(v) is int and v >= 0 for v in answer['stats'].values()), 'LP statistics')
    selected = answer['equation_rows']
    require(type(selected) is list and all(type(i) is int and 0 <= i < len(C) for i in selected),
            'selected original row indices')
    require(selected == sorted(set(selected)), 'unique sorted original rows')
    retained = [C[i] for i in selected]
    r = rank(C)
    require(rank(retained) == r, 'original row span')
    if options['reduce_rows']:
        require(len(selected) == r, 'independent original row subset')
    else:
        require(selected == list(range(len(C))), 'unreduced original rows')
    status = answer['status']
    summary = dict(status=status, original_rank=r)
    if status == 'POSITIVE':
        x = list(map(rational, answer['x']))
        ray = list(map(encoded_integer, answer['primitive_x']))
        require(len(x) == len(ray) == n and all(v >= 0 for v in ray), 'nonnegative primal')
        require(sum(x) == 1 and sum(ray) > 0 and gcd(*ray) == 1, 'normalized primitive primal')
        require(x == [Fraction(v, sum(ray)) for v in ray], 'ray/point correspondence')
        require(all(sum(a*b for a, b in zip(row, x)) == 0 for row in C), 'original primal rows')
        value = sum(a*b for a, b in zip(c, x))
        require(value > 0 and rational(answer['objective']) == value, 'positive objective')
        support = [j for j, v in enumerate(ray) if v]
        support_rank = rank([[row[j] for j in support] for row in C])
        require(support_rank == len(support)-1, 'original-support extreme ray')
        inequalities = retained + [[-v for v in row] for row in retained] + [[Fraction(1)]*n]
        m = len(inequalities)
        basis = answer['basis']
        require(type(basis) is list and len(basis) == m and len(set(basis)) == m and
                all(type(j) is int and 0 <= j < n+m for j in basis), 'literal slack basis')
        require(set(support) <= set(basis), 'basis contains positive support')
        basis_matrix = [[row[j] if j < n else Fraction(int(j-n == i)) for j in basis]
                        for i, row in enumerate(inequalities)]
        require(rank(basis_matrix) == m, 'original slack basis nonsingularity')
        summary.update(primal=True, support_size=len(support), support_rank=support_rank,
                       basis_rank=m)
    elif status == 'NONPOSITIVE':
        y = list(map(rational, answer['y']))
        require(len(y) == len(C), 'original-row dual length')
        require(all(sum(C[i][j]*y[i] for i in range(len(C))) >= c[j] for j in range(n)),
                'original-row dual inequalities')
        summary['dual'] = True
    else:
        require(status == 'INCONCLUSIVE', 'known LP status')
        require(not ({'x', 'primitive_x', 'y', 'objective', 'basis'} & answer.keys()),
                'no partial mathematical LP certificate')
        summary['capped_without_certificate'] = True
    return summary


def replay_euler(source, allowed, answer):
    require(type(answer) is dict, 'Euler result dictionary')
    require(all(type(v) is int and v >= 0 for v in answer['stats'].values()), 'Euler statistics')
    n = len(source['tetrahedra'])
    mask = [[t, q] for t in range(n) for q in range(3)] if allowed is None else allowed
    status = answer['status']
    if status == 'NO_POSITIVE_EULER':
        require(typed_equal(answer['certificate']['allowed_types'], mask), 'negative root mask')
        require(verify_euler_branch_tree(source, answer['certificate']), 'independent negative tree')
        return dict(status=status, negative_tree=True)
    if status == 'POSITIVE_EULER':
        prepared = _prepare(source, lambda: None)
        checked = _coordinates(prepared, answer['coordinates'], lambda: None)
        chi, rows = checked['euler_characteristic'], checked['rows']
        require(chi > 0 and type(answer['euler_characteristic']) is int and
                answer['euler_characteristic'] == chi, 'original source positive Euler')
        require(all(not rows[t][4+q] or [t, q] in mask for t in range(n) for q in range(3)),
                'positive root mask')
        minima = {}
        for t in range(n):
            for v in range(4):
                root = prepared['vertex_roots'][4*t+v]
                minima[root] = min(minima.get(root, rows[t][v]), rows[t][v])
        require(not any(minima.values()), 'canonical triangle minima')
        qvalues = [v for row in rows for v in row[4:]]
        require(sum(qvalues) > 0, 'nonlink positive vector')
        # The public positive API also permits nonextreme points.  Original
        # matching/admissibility/Euler replay suffices; no extra API is assumed.
        return dict(status=status, original_matching=True, admissible=True,
                    canonical=True, euler_characteristic=chi)
    require(status == 'INCONCLUSIVE' and 'certificate' not in answer, 'honest Euler cap')
    return dict(status=status, capped_without_certificate=True)


def matrix_cases():
    rng = random.Random(SEED)
    problems = []
    for i in range(48):
        n, m = i % 6, (i // 6) % 5
        problems.append((f'seeded-{i:02d}', [[rng.randrange(-2, 3) for _ in range(n)]
                                          for _ in range(m)],
                         [rng.randrange(-2, 3) for _ in range(n)]))
    problems.extend([
        ('empty', [], []), ('zero-width', [[], []], []),
        ('dependent', [[1, -1], [2, -2], [0, 0]], [1, 0]),
        ('rational', [[[1, 2], -1], [1, -2]], [[3, 2], -1]),
        ('binary-20001-bit', [[1, '-'+hex(1 << 20000)]], [1, 0]),
        ('free-with-zero-row', [[0, 0, 0]], [-1, 0, 2]),
    ])
    profiles = [
        ('polynomial', dict(max_pivots=128, max_ellipsoid_iterations=256,
                            max_feasibility_calls=128)),
        ('bland', dict(policy='bland', max_pivots=128)),
        ('pivot-cap-zero', dict(max_pivots=0, max_ellipsoid_iterations=256,
                               max_feasibility_calls=128)),
    ]
    cases = []
    for label, C, c in problems:
        for reduce_rows in (False, True):
            for profile, options in profiles:
                cases.append(dict(id=f'{label}/rows-{reduce_rows}/{profile}', matrix=C,
                                  objective=c, options=dict(options, reduce_rows=reduce_rows)))
    fallback_problems = [('positive-line', [[1, -1]], [1, 0]),
                         ('negative-line', [[1, -1]], [1, -2]),
                         ('positive-free', [], [1]), ('negative-free', [], [-1])]
    fallback_profiles = [('fallback', 2048, 128), ('ellipsoid-cap-zero', 0, 128),
                         ('feasibility-cap-zero', 2048, 0)]
    for label, C, c in fallback_problems:
        for reduce_rows in (False, True):
            for profile, iterations, decisions in fallback_profiles:
                options = dict(reduce_rows=reduce_rows, max_pivots=128, fast_path_pivots=0,
                               max_ellipsoid_iterations=iterations, max_feasibility_calls=decisions)
                cases.append(dict(id=f'{label}/rows-{reduce_rows}/{profile}', matrix=C,
                                  objective=c, options=options))
    require(len(cases) == 348, 'fixed LP pair count')
    return cases


def euler_cases():
    fixtures = {str(n): layered_torus(n)[0] for n in (1, 2)}
    masks = [(1, 'full', None), (1, 'empty', []),
             (1, 'mixed', [[0, 0], [0, 1]]), (1, 'meridian', [[0, 2]]),
             (2, 'full', None), (2, 'empty', []),
             (2, 'mixed-negative', [[0, 0], [0, 1], [1, 0], [1, 1]]),
             (2, 'branch', [[0, 0], [1, 0], [1, 1], [1, 2]])]
    base = dict(max_nodes=16, max_pivots=128, max_anchors=64,
                max_ellipsoid_iterations=256, max_feasibility_calls=64)
    profiles = [('bounded', base), ('node-cap-zero', dict(base, max_nodes=0)),
                ('fallback-caps-zero', dict(base, lp_fast_path_pivots=0,
                                           max_ellipsoid_iterations=0, max_feasibility_calls=0))]
    cases = []
    for n, label, mask in masks:
        for strategy in ('anchors', 'envelope'):
            for profile, options in profiles:
                common = dict(options, strategy=strategy)
                for model in ('source', 'restricted'):
                    cases.append(dict(id=f'layered-{n}/{label}/{strategy}/{profile}/tree-{model}',
                                      kind='tree', fixture=str(n), allowed_types=mask,
                                      options=dict(common, model=model)))
                cases.append(dict(id=f'layered-{n}/{label}/{strategy}/{profile}/transversal',
                                  kind='transversal', fixture=str(n), allowed_types=mask,
                                  options=dict(common, candidate_policy='conflicts', max_hitting_subsets=64)))
    require(len(cases) == 144, 'fixed Euler pair count')
    return fixtures, cases


def invoke(function, args, options, replay, *, trace):
    checks = Checks(trace)
    try:
        answer = function(*args, **options, check=checks)
    except Exception as exc:
        return dict(exception=dict(type=type(exc).__name__, message=str(exc)),
                    checks=checks.record()), None, checks.events
    record = dict(result=answer, typed_result_sha256=sha(dumps(typed_form(answer)).encode()),
                  checks=checks.record())
    try:
        record['replay'] = replay(answer)
    except Exception as exc:
        record['replay_error'] = dict(type=type(exc).__name__, message=str(exc))
    return record, answer, checks.events


def loaded_repository_hashes():
    paths = set()
    for module in tuple(sys.modules.values()):
        filename = getattr(module, '__file__', None)
        if filename and not filename.startswith('git:'):
            path = Path(filename).resolve()
            if path.suffix == '.py' and path.is_relative_to(ROOT):
                paths.add(path)
    return {str(p.relative_to(ROOT)): sha(p.read_bytes()) for p in sorted(paths)}


def run():
    before, fixed_before = native_hashes(), fixed_hashes()
    old, baseline = historical_modules(before)
    lp_cases = matrix_cases()
    fixtures, source_cases = euler_cases()
    records = []
    for case in lp_cases:
        C, c, options = case['matrix'], case['objective'], case['options']
        replay = lambda answer: replay_lp(C, c, options, answer)
        older, left, trace_left = invoke(old['exact_lp'].solve_nonnegative_kernel,
            (C, c), options, replay, trace=True)
        newer, right, trace_right = invoke(exact_lp.solve_nonnegative_kernel,
            (C, c), options, replay, trace=True)
        equal = left is not None and right is not None and typed_equal(left, right)
        trace_equal = trace_left == trace_right
        passed = equal and trace_equal and 'replay' in older and 'replay' in newer
        records.append(dict(case, kind='lp', historical=older, current=newer,
                            typed_output_equal=equal, public_callback_trace_equal=trace_equal,
                            passed=passed))
    for case in source_cases:
        source, mask, options = fixtures[case['fixture']], case['allowed_types'], case['options']
        module = 'normal_euler_' + case['kind']
        function = 'search_euler_' + case['kind']
        current = normal_euler_tree if case['kind'] == 'tree' else normal_euler_transversal
        replay = lambda answer: replay_euler(source, mask, answer)
        older, left, _ = invoke(getattr(old[module], function), (source, mask), options, replay, trace=False)
        newer, right, _ = invoke(getattr(current, function), (source, mask), options, replay, trace=False)
        equal = left is not None and right is not None and typed_equal(left, right)
        passed = equal and 'replay' in older and 'replay' in newer
        records.append(dict(case, historical=older, current=newer,
                            typed_output_equal=equal, passed=passed))
    after, fixed_after = native_hashes(), fixed_hashes()
    pins_unchanged = before == after and fixed_before == fixed_after
    counts = Counter(record['kind'] for record in records)
    statuses = {arm: dict(Counter(record[arm].get('result', {}).get('status', 'EXCEPTION')
                                 for record in records)) for arm in ('historical', 'current')}
    module_hashes = loaded_repository_hashes()
    require(all(before.get(p, fixed_before.get(p)) == digest for p, digest in module_hashes.items()),
            'runtime imported repository file is outside the initial pinned closure')
    return dict(schema='prepared-euler-matrix-differential-v1',
                passed=pins_unchanged and all(record['passed'] for record in records),
                seed=SEED, historical=baseline, native_files_sha256=before,
                native_files_after_sha256=after, input_files_sha256=fixed_before,
                input_files_after_sha256=fixed_after,
                loaded_repository_module_sha256=module_hashes,
                source_pins_unchanged=pins_unchanged, fixtures=fixtures,
                totals=dict(pairs=len(records), calls=2*len(records), lp_pairs=counts['lp'],
                            tree_pairs=counts['tree'], transversal_pairs=counts['transversal'],
                            passed_pairs=sum(record['passed'] for record in records),
                            failed_pairs=sum(not record['passed'] for record in records),
                            raw_callback_trace_pairs=counts['lp']),
                statuses=statuses, records=records,
                scope=dict(finite_differential=True, historical_sources_executed=True,
                           current_other_native_files_byte_equal=True,
                           source_callbacks_may_change=True,
                           raw_public_callback_order_compared=True,
                           negative_proofs_independently_replayed=True,
                           original_primal_dual_and_positive_euler_replayed=True,
                           timings_recorded=False, benchmark=False,
                           exhaustive_oracle=False, general_quasipolynomial=False))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=DATA / 'prepared-euler-matrix-differential.json')
    args = parser.parse_args()
    result = run()
    args.output.write_text(dumps(result)+'\n')
    summary = {key: result[key] for key in ('schema', 'passed', 'totals', 'statuses', 'source_pins_unchanged')}
    summary.update(output=str(args.output.resolve()), output_sha256=sha(args.output.read_bytes()),
                   historical_revision=REVISION, native_files=len(result['native_files_sha256']),
                   timings_recorded=False, general_quasipolynomial=False)
    print(json.dumps(summary, sort_keys=True, indent=2))
    if not result['passed']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
