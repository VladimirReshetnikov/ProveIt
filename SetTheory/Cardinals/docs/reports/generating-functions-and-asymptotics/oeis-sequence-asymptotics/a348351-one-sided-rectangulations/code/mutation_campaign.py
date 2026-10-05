#!/usr/bin/env python3
"""Run pristine baselines and deliberate corruptions in isolated copies.

Only stdlib is available to child interpreters (-I -S -B), with and without -O.
A mathematical mutation counts as detected only by its named CHECK_FAIL code.
SyntaxError, import failures, crashes, and arbitrary nonzero exits do not count.
Original source/fixture/README files are actually hashed before and after.
"""
import copy
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
ORIGINALS = ['verify_report111.py', 'report111_fixture.json',
             'mutation_campaign.py', 'README.md']


class CampaignFailure(Exception):
    pass


def require(condition, message):
    if not condition:
        raise CampaignFailure(message)


def hashes():
    return {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in ORIGINALS}


def execute(directory, optimized):
    flags = ['-I', '-S', '-B'] + (['-O'] if optimized else [])
    return subprocess.run([sys.executable, *flags, str(directory / 'verify_report111.py')],
                          cwd=directory, capture_output=True, text=True, timeout=90)


def diagnostic(result):
    if result.returncode != 1 or result.stdout.strip():
        return None
    lines = result.stderr.strip().splitlines()
    if len(lines) != 1 or not lines[0].startswith('CHECK_FAIL '):
        return None
    return lines[0].split(' ', 1)[1].split(':', 1)[0]


def changed(fixture, path, value):
    result = copy.deepcopy(fixture)
    target = result
    for key in path[:-1]:
        target = target[key]
    target[path[-1]] = value
    return json.dumps(result, indent=2) + '\n'


def mutations(fixture, original_text, source):
    result = []

    def fixture_change(name, path, value, expected):
        result.append((name, changed(fixture, path, value), source, expected, 'mathematical'))

    fixture_change('transition_sign', ['edges', 0, 'delta'], [-1, 0], 'source.transitions')
    fixture_change('state_order', ['colors'], list('BGRW'), 'source.state-order')
    fixture_change('matrix_entry', ['matrix', 0, 0], 3, 'source.matrix')
    fixture_change('gamma_conjugate', ['gamma'], [7, -1, 2], 'pf.gamma')
    fixture_change('right_eigenvector', ['right', 0], [3, 1, 4], 'pf.right-eigenvector')
    swapped = copy.deepcopy(fixture['stationary'])
    swapped[0], swapped[1] = swapped[1], swapped[0]
    fixture_change('stationary_state', ['stationary'], swapped, 'stationary.invariance')
    fixture_change('conditional_drift_sign', ['conditional_drift', 0, 0], [-1, 0, 2], 'drift.conditional')
    fixture_change('corrector_sign', ['corrector', 0, 0], [-7, -1, 8], 'corrector.poisson')
    fixture_change('covariance_sign', ['covariance', 0, 1], [17, -5, 272], 'covariance.effective')
    fixture_change('covariance_diagonal', ['covariance', 0, 0], [53, 13, 272], 'covariance.effective')
    fixture_change('correlation_sign', ['rho'], [-29, 7, 4], 'covariance.correlation')
    fixture_change('angle_cosine_sign', ['two_cos'], [29, -7, 2], 'angle.cosine-sign')
    fixture_change('angle_polynomial', ['two_cos_polynomial', 0], 3, 'angle.minimal-polynomial')
    fixture_change('length_n_instead_of_n_minus_one', ['conventions', 'length_shift'], 0, 'count.indexing')
    fixture_change('terminal_red', ['conventions', 'terminal_color'], 'R', 'count.terminal-white')
    fixture_change('wrong_spatial_endpoint', ['conventions', 'endpoint'], [1, 0], 'count.endpoint')
    fixture_change('wrong_initial_state', ['conventions', 'initial_colors'], list('BBGW'), 'count.initial-states')
    fixture_change('oeis_last_term', ['oeis', 16], fixture['oeis'][16] + 1, 'count.oeis-prefix')
    fixture_change('duality_displacement_sign', ['duality', 'reverse_displacement'], 1, 'duality.reversed-edge')
    fixture_change('duality_stationary_ratio', ['duality'],
                   {'reverse_displacement': -1, 'numerator_state': 'to', 'denominator_state': 'from'},
                   'duality.edge-balance')
    fixture_change('wrong_cycle_displacement', ['cycles', '-N'],
                   [['R', 'W', 0, 0], ['W', 'R', -1, 0], ['R', 'R', 0, 0]], 'cycles.displacement')
    fixture_change('connector_too_short', ['connector', 'terminal_extra'], 2, 'connector.padding-size')
    fixture_change('connector_wrong_state', ['connector', 'first_color'], 'G', 'connector.terminal.edge')
    fixture_change('schedule_wrong_scale', ['schedule', 'scale_ratio'], 3, 'schedule.definition')
    fixture_change('schedule_missing_descent', ['schedule', 'stair_multiplicity'], 1, 'schedule.definition')

    fixture_change('annulus_scale_too_small', ['annulus', 'q'], 1, 'annulus.q-at-least-two')
    fixture_change('annulus_step_bound_too_small', ['annulus', 'b'], 1, 'annulus.step-bound')
    fixture_change('annulus_step_bound_skips_scale', ['annulus', 'b'], 100, 'annulus.no-skip')
    fixture_change('annulus_time_reserve', ['annulus', 'delta'], [1, 0, 1], 'annulus.time-reserve')
    fixture_change('annulus_wrong_geometric_power', ['annulus', 'geometric_denominator_power'], 1, 'annulus.geometric-sum')
    fixture_change('annulus_middle_off_by_one', ['annulus', 'middle_time_offset'], 1, 'annulus.exact-middle-time')
    fixture_change('annulus_last_hit_recovery', ['annulus', 'first_hit_policy'], 'last', 'annulus.first-hit-recovery')
    fixture_change('annulus_seed_wrong_direction', ['annulus', 'north_step'], [1, 0], 'annulus.seed-endpoint-time')

    malformed = []
    d = copy.deepcopy(fixture)
    d['unexpected'] = 0
    malformed.append(('unknown_fixture_field', json.dumps(d), 'schema.inventory'))
    d = copy.deepcopy(fixture)
    del d['gamma']
    malformed.append(('missing_fixture_field', json.dumps(d), 'schema.inventory'))
    malformed.extend([
        ('duplicate_json_key', original_text.replace('"schema_version": 1', '"schema_version": 1, "schema_version": 1', 1), 'schema.duplicate-key'),
        ('truncated_json', original_text[:-3], 'schema.json'),
        ('boolean_as_integer', changed(fixture, ['matrix', 0, 0], True), 'schema.integer'),
        ('float_as_integer', changed(fixture, ['matrix', 0, 0], 2.0), 'schema.integer'),
        ('nonfinite_number', original_text.replace('"schema_version": 1', '"schema_version": NaN', 1), 'schema.nonfinite-number'),
        ('zero_field_denominator', changed(fixture, ['gamma'], [7, 1, 0]), 'schema.field-canonical'),
        ('noncanonical_field', changed(fixture, ['gamma'], [14, 2, 4]), 'schema.field-canonical'),
        ('wrong_matrix_size', changed(fixture, ['matrix'], fixture['matrix'][:3]), 'schema.size'),
        ('wrong_covariance_size', changed(fixture, ['covariance', 0], fixture['covariance'][0] + [[0, 0, 1]]), 'schema.size'),
        ('wrong_oeis_size', changed(fixture, ['oeis'], fixture['oeis'][:-1]), 'schema.size'),
        ('wrong_edge_inventory', changed(fixture, ['edges'], fixture['edges'][:-1]), 'schema.size'),
        ('wrong_edge_color_type', changed(fixture, ['edges', 0, 'from'], 1), 'schema.color'),
        ('wrong_cycle_color_type', changed(fixture, ['cycles', '0', 0, 0], 1), 'schema.color'),
        ('duplicate_edge', changed(fixture, ['edges', 1], fixture['edges'][0]), 'schema.duplicate-edge'),
    ])
    result.extend((name, text, source, code, 'schema') for name, text, code in malformed)

    code_cases = [
        ('implementation_martingale_sign', '(dx, dy)[v] + h[j][v] - h[i][v]',
         '(dx, dy)[v] + h[j][v] + h[i][v]', 'martingale.increment-bound'),
        ('implementation_endpoint_state', 'new[x + dx, y + dy, d] += value',
         'new[x + dx, y + dy, c] += value', 'count.oeis-prefix'),
        ('implementation_connector_size', "D = 4 * H + cfg['terminal_extra']",
         "D = 3 * H + cfg['terminal_extra']", 'connector.padding-size'),
        ('implementation_field_relation', 'self.a * other.a + 17 * self.b * other.b',
         'self.a * other.a + 16 * self.b * other.b', 'pf.gamma'),
        ('implementation_source_inequality', "xmin = 0 if c in 'BR' or d in 'BG' else -1",
         "xmin = 0 if c in 'BR' and d in 'BG' else -1", 'source.transitions'),
    ]
    for name, old, new, expected in code_cases:
        require(source.count(old) == 1, 'Source mutation target must occur exactly once: ' + name)
        mutant = source.replace(old, new, 1)
        compile(mutant, '<' + name + '>', 'exec')
        result.append((name, original_text, mutant, expected, 'implementation'))
    require(len({x[0] for x in result}) == len(result), 'Duplicate mutation names')
    return result


def campaign():
    before = hashes()
    source = (ROOT / 'verify_report111.py').read_text()
    fixture_text = (ROOT / 'report111_fixture.json').read_text()
    fixture = json.loads(fixture_text)
    outcomes, baselines = [], []
    try:
        with tempfile.TemporaryDirectory(prefix='report111_isolated_') as temporary:
            base = Path(temporary)
            clean = base / 'pristine'
            clean.mkdir()
            for filename in ['verify_report111.py', 'report111_fixture.json']:
                shutil.copyfile(ROOT / filename, clean / filename)
            # BOTH pristine baselines must pass before ANY corrupted run.
            for optimized in [False, True]:
                run = execute(clean, optimized)
                require(run.returncode == 0 and not run.stderr,
                        'Pristine baseline failed: ' + run.stderr)
                parsed = json.loads(run.stdout)
                require(parsed['status'] == 'PASS' and parsed['guards_total'] > 100000 and
                        parsed['oeis_n0_to_n16'] == fixture['oeis'] and
                        parsed['checker_sha256'] == before['verify_report111.py'] and
                        parsed['fixture_sha256'] == before['report111_fixture.json'],
                        'Invalid pristine result')
                baselines.append(parsed)
            require(baselines[0] == baselines[1], 'Normal and -O baselines differ')

            # Prove the harness itself rejects a syntax-only broken checker.
            broken = base / 'syntax_only_negative_control'
            broken.mkdir()
            (broken / 'verify_report111.py').write_text('def broken(:\n')
            shutil.copyfile(clean / 'report111_fixture.json', broken / 'report111_fixture.json')
            syntax_control = execute(broken, False)
            require(syntax_control.returncode != 0 and diagnostic(syntax_control) is None
                    and 'SyntaxError' in syntax_control.stderr,
                    'Syntax-only negative control was incorrectly accepted')

            for name, text, mutant_source, expected, category in mutations(fixture, fixture_text, source):
                directory = base / name
                directory.mkdir()
                (directory / 'verify_report111.py').write_text(mutant_source)
                (directory / 'report111_fixture.json').write_text(text)
                modes = []
                for optimized in [False, True]:
                    result = execute(directory, optimized)
                    observed = diagnostic(result)
                    require(observed == expected,
                            name + ' (' + ('-O' if optimized else 'normal') + ') expected ' + expected
                            + ', observed ' + repr(observed) + '; stderr=' + result.stderr[:1200])
                    modes.append({'optimized': optimized, 'diagnostic': observed, 'exit_code': result.returncode})
                outcomes.append({'name': name, 'category': category, 'expected_diagnostic': expected, 'modes': modes})
    finally:
        after = hashes()
        require(before == after, 'ORIGINAL FILES CHANGED during campaign')
    return {'status': 'PASS', 'pristine_baselines_checked_first': True,
            'isolated_child_flags': ['-I', '-S', '-B'], 'modes': ['normal', '-O'],
            'pristine_guards_each': baselines[0]['guards_total'],
            'normal_optimized_results_identical': True, 'syntax_only_failure_rejected': True,
            'mutation_count': len(outcomes), 'corrupted_runs': 2 * len(outcomes),
            'original_sha256_before': before, 'original_sha256_after': after,
            'originals_unchanged': before == after, 'mutations': outcomes,
            'scope': 'Regression evidence for finite exact mathematics and fixture validation; not machine certification of analytic probability or differential-equation theorems.'}


if __name__ == '__main__':
    try:
        print(json.dumps(campaign(), indent=2, sort_keys=True))
    except (CampaignFailure, OSError, subprocess.SubprocessError, ValueError) as exc:
        print('CAMPAIGN_FAIL ' + str(exc), file=sys.stderr)
        sys.exit(1)
