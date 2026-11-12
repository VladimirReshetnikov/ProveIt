#!/usr/bin/env python3
"""Reproduce finite verification of the tolerant native iPRA checker.

Only the Python standard library is needed. Run from any working directory:
    python3 test_harness.py

The measured candidate and controls are executed unchanged in isolated CLI
processes, with and without -O. The bounded adversarial search instruments
only an in-memory copy, leaving all measured files unchanged. Finite tests
are not a proof of the universal soundness or bi-interpretability theorems.
"""
import ast
import concurrent.futures
import copy
import hashlib
import io
import json
import math
from pathlib import Path
import random
import subprocess
import sys
import time
import tokenize

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'evidence'
OUT.mkdir(exist_ok=True)
SOURCES = json.loads((ROOT / 'sources.json').read_text())
CASES = json.loads((ROOT / 'fixtures/cases.json').read_text())
PROGRAMS = {row['label']: ROOT / row['path'] for row in SOURCES['programs']}
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.COMMENT,
        tokenize.NEWLINE, tokenize.NL, tokenize.INDENT, tokenize.DEDENT}
FALSE_GOAL = [0, [0]]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def dumps(data):
    # NaN and Infinity are deliberate probes of the extra literals accepted
    # by Python's standard JSON reader; they are not standard JSON numbers.
    return (json.dumps(data, separators=(',', ':'), allow_nan=True) + '\n').encode()


def report_value(data):
    """Keep reports standard JSON while spelling tested nonfinite literals."""
    if type(data) is float and not math.isfinite(data):
        return {'python_json_number': 'NaN' if math.isnan(data) else 'Infinity' if data > 0 else '-Infinity'}
    if type(data) is list:
        return [report_value(value) for value in data]
    if type(data) is dict:
        return {key: report_value(value) for key, value in data.items()}
    return data


def exact_tree(data):
    return type(data) is int or type(data) is list and all(map(exact_tree, data))


def source_metrics(path):
    raw = path.read_bytes()
    tree = ast.parse(raw.decode())
    normalized = ast.unparse(tree) + '\n'
    return {
        'source_sha256': sha(raw),
        'normalized_sha256': sha(normalized.encode()),
        'tokens': sum(t.type not in SKIP for t in tokenize.generate_tokens(io.StringIO(normalized).readline)),
        'ast_nodes': sum(1 for _ in ast.walk(tree)),
        'normalized_bytes': len(normalized.encode()),
    }


def alias(data, mode):
    changed = 0

    def transform(value):
        nonlocal changed
        if type(value) is list:
            return [transform(x) for x in value]
        if type(value) is int:
            if mode == 'exact_float':
                out = float(value)
                if int(out) != value:
                    raise ValueError('Fixture has an integer not exactly representable as a float')
                changed += 1
                return out
            if mode == 'zero_false' and value == 0:
                changed += 1
                return False
            if mode == 'one_true' and value == 1:
                changed += 1
                return True
        return value

    result = transform(data)
    return result, changed


def cli_run(job):
    command = [sys.executable, '-I', '-S', '-B']
    if job['optimized']:
        command.append('-O')
    command.append(str(PROGRAMS[job['program']]))
    try:
        process = subprocess.run(command, input=job['input'], capture_output=True, timeout=10)
        accepted = process.returncode == 0 and process.stdout == b'ACCEPT\n'
        result = {k: v for k, v in job.items() if k != 'input'}
        result.update(accepted=accepted, exit_code=process.returncode,
                      stdout=process.stdout.decode(errors='replace'),
                      passed=accepted == job['expected'])
        if not result['passed']:
            result['stderr_tail'] = process.stderr.decode(errors='replace')[-1500:]
        return result
    except subprocess.TimeoutExpired:
        return {**{k: v for k, v in job.items() if k != 'input'},
                'accepted': False, 'timeout': True, 'passed': False}


def add_jobs(jobs, name, data, expected_by_program, suite, **extra):
    payload = data if type(data) is bytes else dumps(data)
    for program, expected in expected_by_program.items():
        for optimized in (False, True):
            jobs.append({'name': name, 'suite': suite, 'program': program,
                         'optimized': optimized, 'expected': expected,
                         'input_sha256': sha(payload), 'input': payload, **extra})


def boundary_cases(base):
    """Explicit accepted extensions and malformed/false-goal probes."""
    cases = []
    # The thirteen inherited positive fixtures contain no scalar1. These
    # paired real neutral-premise steps make the1->True test nonvacuous.
    for name, value, strict_expected in [('one', 1, True), ('true', True, False)]:
        cases.append({'name': 'used_neutral_' + name,
                      'data': base[:-1] + [[value, 0, 0, 0], base[-1]],
                      'expected': {'candidate': True, 'strict_size': strict_expected, 'strict_bytes': strict_expected},
                      'reason': 'The actual scalar major1 and its Boolean aliasTrue both read as a neutral formula.'})
    for name, value in [('null', None), ('object', {'unused': 'data'}),
                        ('string', 'unused'), ('float', 0.5), ('false', False),
                        ('nan', float('nan')), ('infinity', float('inf'))]:
        cases.append({'name': 'unread_' + name, 'data': [value] + base,
                      'expected': {'candidate': True, 'strict_size': False, 'strict_bytes': False},
                      'reason': 'An unread prefix is not part of the proof used by the candidate.'})
    for name, value in [('fraction', 0.5), ('negative_fraction', -0.5),
                        ('nan', float('nan')), ('infinity', float('inf')),
                        ('negative_infinity', -float('inf'))]:
        neutral = [value, 0, 0, 0]
        cases.append({'name': 'used_neutral_' + name,
                      'data': base[:-1] + [neutral, base[-1]],
                      'expected': {'candidate': True, 'strict_size': False, 'strict_bytes': False},
                      'reason': 'The extra proved scalar major has the neutral formula reading.'})
        cases.append({'name': 'false_goal_neutral_' + name,
                      'data': [neutral, FALSE_GOAL],
                      'expected': {'candidate': False, 'strict_size': False, 'strict_bytes': False},
                      'reason': 'A neutral major cannot prove the false canonical equation.'})
    for name, value in [('empty_string', ''), ('string', 'x'), ('null', None), ('object', {})]:
        cases.append({'name': 'active_non_number_' + name,
                      'data': base[:-1] + [[value, 0, 0, 0], base[-1]],
                      'expected': {'candidate': False, 'strict_size': False, 'strict_bytes': False},
                      'reason': 'The exact array discriminator rejects an active nonnumeric scalar.'})
    for mode in ('exact_float', 'zero_false', 'one_true'):
        aliased, changed = alias([FALSE_GOAL], mode)
        if changed:
            cases.append({'name': 'unproved_false_goal_' + mode, 'data': aliased,
                          'expected': {'candidate': False, 'strict_size': False, 'strict_bytes': False},
                          'reason': 'Numeral aliases do not change a false conclusion.'})
    return cases


class BudgetExceeded(Exception):
    pass


class Instrument(ast.NodeTransformer):
    def visit_FunctionDef(self, node):
        node = self.generic_visit(node)
        if node.name == 'c':
            node.body.insert(0, ast.Expr(value=ast.Call(func=ast.Name(id='_tick', ctx=ast.Load()), args=[], keywords=[])))
        return node

    def visit_Lambda(self, node):
        node = self.generic_visit(node)
        node.body = ast.BoolOp(op=ast.Or(), values=[
            ast.Call(func=ast.Name(id='_tick', ctx=ast.Load()), args=[], keywords=[]), node.body])
        return node


def make_bounded_candidate():
    tree = ast.parse(PROGRAMS['candidate'].read_text())
    body = []
    for statement in tree.body:
        if isinstance(statement, ast.Assign) and any(isinstance(x, ast.Name) and x.id == 'q' for x in statement.targets):
            break
        body.append(statement)
    tree.body = body
    tree = ast.fix_missing_locations(Instrument().visit(tree))
    remaining = [0]

    def tick():
        remaining[0] -= 1
        if remaining[0] < 0:
            raise BudgetExceeded()
        return False

    namespace = {'_tick': tick}
    exec(compile(tree, 'bounded_candidate_copy.py', 'exec'), namespace)

    def run(data, limit=2000):
        # Round-trip through the actual standard parser, preserving its
        # concrete handling of booleans, floats, and nonfinite literals.
        stack = json.loads(dumps(data))
        remaining[0] = limit
        try:
            namespace['q'] = stack.pop
            namespace['c']([], stack.pop())
            return 'accepted', limit - remaining[0]
        except BudgetExceeded:
            return 'budget_exceeded', limit + 1
        except RecursionError:
            return 'recursion_limit', limit - remaining[0]
        except Exception:
            return 'rejected', limit - remaining[0]

    return run


def tree_paths(tree, path=()):
    yield path
    if type(tree) is list:
        for index, value in enumerate(tree):
            yield from tree_paths(value, path + (index,))


def replace(tree, path, value):
    tree = copy.deepcopy(tree)
    if not path:
        return copy.deepcopy(value)
    node = tree
    for index in path[:-1]:
        node = node[index]
    node[path[-1]] = copy.deepcopy(value)
    return tree


def adversarial_search(run):
    names = ['false_float_capture.json', 'future_witness_capture.json',
             'context_leak_attack.json', 'scalar_false_sentinel_attack.json',
             'transport_reflexivity_local.json', 'computation_zero_local.json',
             'computation_successor_local.json']
    seeds = [(name, json.loads((ROOT / 'fixtures' / name).read_text())[:-1] + [FALSE_GOAL]) for name in names]
    pool = [None, False, True, 0, 1, 2, 3, 5, 7, -1, -2, -3,
            -0.5, -1.5, -2.5, 0.0, 1.0, 3.0, 3.5, 4.5, 5.25,
            0.5, 1.5, 1e300, -1e300, float('nan'), float('inf'),
            -float('inf'), '', 'x', {}, {'': 0}, [], [0], [0, 0],
            [0, [0]], [[0], 0], [3, 0], [3, [0]], [0, 3], [[0], 3],
            [0, 0, 0], [[3, 0]], [[5, 0, 7], [5, 0, 5]]]
    rng = random.Random(2061112)
    counts = {}
    suites = {}
    hits = []
    index = 0
    log_path = OUT / 'adversarial_trials.jsonl'
    started = time.time()
    with log_path.open('w') as log:

        def check(data, suite, detail):
            nonlocal index
            outcome, calls = run(data)
            index += 1
            counts[outcome] = counts.get(outcome, 0) + 1
            suites[suite] = suites.get(suite, 0) + 1
            row = {'trial': index, 'suite': suite, 'detail': detail,
                   'input_sha256': sha(dumps(data)), 'outcome': outcome, 'calls': calls}
            log.write(json.dumps(row, separators=(',', ':')) + '\n')
            if outcome == 'accepted':
                hits.append({**row, 'certificate': data})

        for name, data in seeds:
            for path in tree_paths(data):
                if path and path[0] != len(data) - 1:
                    for replacement_index, value in enumerate(pool):
                        check(replace(data, path, value), 'one_subtree',
                              [name, path, replacement_index])
        for trial in range(20000):
            name, data = rng.choice(seeds)
            candidate = copy.deepcopy(data)
            mutations = []
            for _ in range(rng.randint(1, 3)):
                paths = [p for p in tree_paths(candidate) if p and p[0] != len(candidate) - 1]
                if paths:
                    path = rng.choice(paths)
                    replacement_index = rng.randrange(len(pool))
                    candidate = replace(candidate, path, pool[replacement_index])
                    mutations.append([path, replacement_index])
            check(candidate, 'random_mutation', [trial, name, mutations])
        for trial in range(15000):
            packet_indices = [[rng.randrange(len(pool)) for _ in range(4)] for __ in range(rng.randint(1, 4))]
            packets = [[copy.deepcopy(pool[i]) for i in packet] for packet in packet_indices]
            check(packets + [FALSE_GOAL], 'random_short_stack', [trial, packet_indices])
    return {'random_seed': 2061112, 'false_public_goal': FALSE_GOAL,
            'trial_count': index, 'counts': counts, 'suites': suites,
            'call_bound': 2000, 'accepted_false_goals': hits,
            'pool': pool, 'seconds': time.time() - started,
            'log': str(log_path.relative_to(ROOT)), 'log_sha256': sha(log_path.read_bytes()),
            'evidence_status': 'Finite bounded adversarial search; not a proof.'}


def main():
    start = time.time()
    source_rows = []
    for row in SOURCES['programs']:
        measured = source_metrics(ROOT / row['path'])
        if measured['source_sha256'] != row['sha256']:
            raise SystemExit('Source hash mismatch: ' + row['path'])
        source_rows.append({**row, **measured})
    jobs = []
    positives = []
    fixture_rows = []
    for case in CASES:
        payload = (ROOT / 'fixtures' / case['file']).read_bytes()
        if sha(payload) != case['sha256']:
            raise SystemExit('Fixture hash mismatch: ' + case['file'])
        data = json.loads(payload)
        canonical_alphabet = exact_tree(data)
        fixture_rows.append({**case, 'exact_integer_list_alphabet': canonical_alphabet})
        add_jobs(jobs, case['file'], payload,
                 {name: case['expected'] for name in PROGRAMS}, 'shared_fixture',
                 exact_integer_list_alphabet=canonical_alphabet)
        if case['expected'] and canonical_alphabet:
            positives.append((case['file'], data))
            for mode in ('exact_float', 'zero_false', 'one_true'):
                transformed, changed = alias(data, mode)
                if changed:
                    add_jobs(jobs, case['file'] + ':' + mode, transformed,
                             {'candidate': True}, 'numeral_alias',
                             base_fixture=case['file'], transform=mode,
                             changed_scalar_occurrences=changed)
    base = json.loads((ROOT / 'fixtures/computation_zero_local.json').read_text())
    boundaries = boundary_cases(base)
    (OUT / 'boundary_cases.json').write_text(json.dumps(report_value(boundaries), indent=2, allow_nan=False) + '\n')
    for case in boundaries:
        add_jobs(jobs, case['name'], case['data'], case['expected'], 'boundary')
    with concurrent.futures.ThreadPoolExecutor(max_workers=6) as executor:
        cli_results = list(executor.map(cli_run, jobs))
    failures = [row for row in cli_results if not row['passed']]
    bounded = make_bounded_candidate()
    instrument_sanity = []
    for name, data in positives:
        outcome, calls = bounded(data, limit=1000000)
        instrument_sanity.append({'name': name, 'outcome': outcome,
                                  'calls': calls, 'passed': outcome == 'accepted'})
    adversarial = adversarial_search(bounded)
    coverage = {
        'zero_computation': 'computation_zero_local.json',
        'successor_computation': 'computation_successor_local.json',
        'retained_hypotheses_and_equation_progress': 'guarded_induction_with_used_hypothesis_local.json',
        'equational_transport': 'derived_zero_source_equational_transport_local.json',
        'closure_elimination': 'compound_implication_elimination_local.json',
        'existential_opening': 'guarded_lift_elimination_local.json',
        'compound_case_introduction': 'compound_case_introduction_local.json',
        'equation_case_introduction': 'old_atomic_case_local.json',
    }
    passed = not failures and all(x['passed'] for x in instrument_sanity) and not adversarial['accepted_false_goals']
    receipt = {
        'python': sys.version, 'candidate_source_matches_pinned_copy': True,
        'metric_convention': 'Whole standalone module; ast.unparse plus LF; significant tokens exclude whitespace/comments.',
        'sources': source_rows, 'fixture_count': len(CASES),
        'positive_exact_integer_fixture_count': len(positives),
        'fixtures': fixture_rows, 'rule_coverage_examples': coverage,
        'cli_process_executions': len(cli_results),
        'cli_suite_counts': {suite: sum(x['suite'] == suite for x in cli_results) for suite in sorted({x['suite'] for x in cli_results})},
        'cli_failures': failures, 'cli_results': cli_results,
        'instrumentation_sanity': instrument_sanity,
        'adversarial_search': adversarial,
        'candidate_source_unchanged_after_testing': sha(PROGRAMS['candidate'].read_bytes()) == SOURCES['programs'][0]['sha256'],
        'seconds': time.time() - start, 'all_expected_checks_passed': passed,
        'limitations': [
            'Finite fixture execution and mutation search do not prove the semantic soundness theorem.',
            'The candidate deliberately accepts numerical aliases and unread noninteger data rejected by alphabet-validating controls.',
            'Different acceptance languages are compared only where the expectation is explicitly specified.',
            'Bounded-call or recursion-limit outcomes in the adversarial log are not proofs of rejection by an unbounded idealized algorithm.',
            'NaN and Infinity are extra literals accepted by Python json, not standard JSON numeric syntax.'
        ],
        'report_nonfinite_encoding': 'A tested nonfinite float is represented in reports as {"python_json_number":"NaN|Infinity|-Infinity"}; CLI test input uses the actual Python-json literal.',
    }
    (OUT / 'verification.json').write_text(json.dumps(report_value(receipt), indent=2, allow_nan=False) + '\n')
    print(json.dumps({
        'all_expected_checks_passed': passed,
        'candidate_metrics': {key: source_rows[0][key] for key in ['tokens', 'ast_nodes', 'normalized_bytes', 'source_sha256']},
        'fixture_count': len(CASES), 'positive_exact_integer_fixtures': len(positives),
        'cli_process_executions': len(cli_results), 'cli_failures': len(failures),
        'adversarial_trials': adversarial['trial_count'], 'adversarial_outcomes': adversarial['counts'],
        'accepted_false_goals': len(adversarial['accepted_false_goals']), 'seconds': receipt['seconds']
    }, indent=2))
    if not passed:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
