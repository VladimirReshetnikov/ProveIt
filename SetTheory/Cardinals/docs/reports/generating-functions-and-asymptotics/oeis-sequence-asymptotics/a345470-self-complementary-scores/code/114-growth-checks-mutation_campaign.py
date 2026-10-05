#!/usr/bin/env python3
"""Named semantic/schema mutations: require expected diagnostics, not crashes.
Each trial uses new temporary files; normal and -O runs must both reject.
The clean source files are hashed before and after, without altering them.
"""
import argparse
import ast
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


class CampaignError(Exception):
    pass


def require(condition, message):
    if not condition:
        raise CampaignError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def hashes(directory, selected=None):
    return {p.name: digest(p.read_bytes()) for p in sorted(directory.iterdir())
            if p.is_file() and (selected is None or p.name in selected)}


def execute(directory, optimized, group):
    cmd = [sys.executable] + (['-O'] if optimized else [])
    cmd += [str(directory / 'validate.py'), '--fixtures', str(directory / 'fixtures.json'), '--only', group]
    return subprocess.run(cmd, cwd=directory, capture_output=True, text=True, timeout=180)


def change_fixture(original, path, value):
    f = json.loads(original)
    node = f
    for key in path[:-1]:
        node = node[key]
    node[path[-1]] = value
    return json.dumps(f, indent=2) + '\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    home = Path(__file__).resolve().parent
    source = (home / 'validate.py').read_text()
    fixture = (home / 'fixtures.json').read_text()
    ast_tree = ast.parse(source)
    require(not any(isinstance(n, ast.Assert) for n in ast.walk(ast_tree)), 'Validator contains an optimization-disabled assert')
    input_names = {'validate.py', 'fixtures.json', 'mutation_campaign.py'}
    before = hashes(home, input_names)
    cases = []
    def source_case(name, old, new, diagnostic, group, occurrences=1):
        require(source.count(old) == occurrences, f'Mutation {name}: expected {occurrences} exact source targets')
        changed = source.replace(old, new, 1)
        ast.parse(changed)  # Reject accidental syntax-only mutations before running.
        cases.append((name, changed, fixture, diagnostic, group))
    def fixture_case(name, path, value, diagnostic, group='schema'):
        cases.append((name, source, change_fixture(fixture, path, value), diagnostic, group))
    source_case('wrong_even_terminal_velocity', 'endpoint = -1 if n % 2 == 0 else 0',
                'endpoint = 0 if n % 2 == 0 else -1', 'WALK_COUNT', 'counts')
    source_case('extra_final_slack_area_test', 'if r <= m and new_area < int(strict):',
                'if r <= m + 1 and new_area < int(strict):', 'WALK_COUNT', 'counts')
    source_case('integrate_previous_velocity', 'new_area = area + new_velocity',
                'new_area = area + velocity', 'WALK_COUNT', 'counts')
    source_case('strict_walk_used_for_weak', 'if r <= m and new_area < int(strict):',
                'if r <= m and new_area <= int(strict):', 'WALK_COUNT', 'counts')
    source_case('incorrect_composition_weight', 'w = weighted + u',
                'w = weighted + part', 'COMPOSITION_COUNT', 'counts')
    source_case('weaken_strict_score_test', 'if s >= r * (r - 1) // 2 + int(strict):',
                'if s >= r * (r - 1) // 2:', 'COMPOSITION_COUNT', 'counts')
    source_case('wrong_reflection_center', 'tuple(n - 1 - x for x in reversed(half))',
                'tuple(n - 2 - x for x in reversed(half))', 'REFLECTED_TOTAL', 'exhaustive')
    source_case('discard_slack_in_gap_map', '((n - 1) // 2 - half[-1],)',
                '(0,)', 'GAP_SLACK_COMPOSITION', 'exhaustive')
    source_case('drop_area_plus_one_shift', '(area >= 0) == (area + 1 > 0)',
                '(area >= 0) == (area > 0)', 'AREA_PLUS_ONE_SHIFT', 'exhaustive')
    source_case('wrong_frozen_tested_endpoint', 'positive_endpoint_probability(m - 1, 0 if n % 2 == 0 else 1)',
                'positive_endpoint_probability(m - 1, 1 if n % 2 == 0 else 0)', 'FROZEN_LOWER_CLASS', 'exhaustive')
    source_case('incorrect_odd_to_even_injection', 'image = half if n % 2 == 0 else half + (m,)',
                'image = half if n % 2 == 0 else half + (m + 1,)', 'MONOTONE_INJECTION_ORDER', 'exhaustive')
    source_case('wrong_negative_binomial_ratio', 'F(2 * ell + d, 2 * (ell + d + 1))',
                'F(2 * ell + d, 2 * (ell + d + 2))', 'NB_RATIO', 'distribution')
    source_case('wrong_normalizing_tail', 'for j in range(ell)), F(0))',
                'for j in range(ell + 1)), F(0))', 'NB_NORMALIZATION_EXACT_TAIL', 'distribution')
    source_case('wrong_negative_binomial_mode', 'F(comb(2 * ell - 2, ell - 1), 2 * 4 ** (ell - 1))',
                'F(comb(2 * ell - 2, ell - 1), 4 * 4 ** (ell - 1))', 'NB_MODE_FORMULA', 'distribution')
    source_case('wrong_gaussian_cross_term', 'mono(6, (0, 0, -2, 0))',
                'mono(-6, (0, 0, -2, 0))', 'DENSITY_RATIO_ALGEBRA', 'algebra')
    source_case('empty_first_bridge_block', 'h, q = ell // 2, ell - ell // 2',
                'h, q = 0, ell', 'BRIDGE_SPLIT_BOUNDS', 'algebra')
    source_case('insufficient_area_protection', '16 * t ** 3 > suffix ** 3',
                't ** 3 > suffix ** 3', 'AREA_PROTECTION_L4', 'algebra')
    fixture_case('changed_weak_published_term', ['sequence_sources', 0, 'terms', 8], 20, 'OEIS_PREFIX', 'counts')
    fixture_case('changed_strong_published_term', ['sequence_sources', 1, 'terms', 8], 12, 'OEIS_PREFIX', 'counts')
    fixture_case('wrong_variance', ['constants', 'variance'], [1, 1], 'INCREMENT_VARIANCE', 'distribution')
    fixture_case('wrong_exponential_certificate', ['constants', 'exponential_absolute_moment'], [3, 2], 'EXPONENTIAL_MOMENT', 'distribution')
    fixture_case('wrong_density_ratio_sign', ['constants', 'density_bw_coefficient'], [4, 1], 'DENSITY_RATIO_ALGEBRA', 'algebra')
    fixture_case('wrong_frozen_first_part', ['constants', 'frozen_first_g'], 0, 'FROZEN_FIRST_G', 'exhaustive')
    fixture_case('wrong_frozen_slack', ['constants', 'frozen_slack_g'], 1, 'FROZEN_SLACK_G', 'exhaustive')
    fixture_case('wrong_frozen_probability', ['constants', 'frozen_probability'], [1, 4], 'FROZEN_FACTOR', 'exhaustive')
    fixture_case('wrong_formal_inverse_exponent', ['constants', 'inverse_loglog_coefficient'], [1, 2], 'INVERSE_LOGLOG_COEFFICIENT', 'algebra')
    fixture_case('boolean_schema', ['schema_version'], True, 'FIXTURE_SCHEMA_VERSION')
    fixture_case('boolean_term', ['sequence_sources', 0, 'terms', 0], True, 'FIXTURE_INTEGER_TERM')
    fixture_case('boolean_range', ['ranges', 'dp_max_n'], True, 'FIXTURE_RANGE_VALUE')
    fixture_case('shortened_prefix', ['sequence_sources', 0, 'terms'], json.loads(fixture)['sequence_sources'][0]['terms'][:-1], 'FIXTURE_PREFIX_LENGTH')
    fixture_case('reduced_check_range', ['ranges', 'dp_max_n'], 10, 'FIXTURE_RANGE_VALUE')
    fixture_case('noncanonical_fraction', ['constants', 'variance'], [4, 2], 'FIXTURE_RATIONAL_REDUCED')
    fixture_case('zero_denominator', ['constants', 'variance'], [2, 0], 'FIXTURE_RATIONAL_TYPE')
    fixture_case('wrong_offset', ['sequence_sources', 0, 'offset'], 1, 'FIXTURE_OFFSET')
    fixture_case('missing_limitations', ['limitations'], [], 'FIXTURE_LIMITATIONS')
    cases.append(('duplicate_json_key', source, fixture.replace('"schema_version": 1,', '"schema_version": 1, "schema_version": 1,', 1), 'FIXTURE_DUPLICATE_KEY', 'schema'))
    extra = json.loads(fixture)
    extra['unrecognized'] = 1
    cases.append(('unexpected_fixture_key', source, json.dumps(extra), 'FIXTURE_ROOT_KEYS', 'schema'))
    records = []
    baseline_hashes = []
    for optimized in [False, True]:
        with tempfile.TemporaryDirectory(prefix='score_clean_replay_') as tmp:
            directory = Path(tmp)
            (directory / 'validate.py').write_text(source)
            (directory / 'fixtures.json').write_text(fixture)
            result = execute(directory, optimized, 'all')
            require(result.returncode == 0 and not result.stderr, f'Clean replay failed optimized={optimized}: {result.stderr}')
            parsed = json.loads(result.stdout)
            require(parsed['status'] == 'PASS', 'Clean replay did not report PASS')
            baseline_hashes.append(digest(result.stdout.encode()))
    require(baseline_hashes[0] == baseline_hashes[1], 'Normal and optimized clean outputs differ')
    for name, changed_source, changed_fixture, diagnostic, group in cases:
        for optimized in [False, True]:
            with tempfile.TemporaryDirectory(prefix='score_mutation_') as tmp:
                directory = Path(tmp)
                (directory / 'validate.py').write_text(changed_source)
                (directory / 'fixtures.json').write_text(changed_fixture)
                mutated_before = hashes(directory)
                result = execute(directory, optimized, group)
                expected = 'VALIDATION_FAILURE ' + diagnostic
                first = result.stderr.strip().splitlines()[0] if result.stderr.strip() else ''
                require(result.returncode == 2 and (first == expected or first.startswith(expected + ':'))
                        and 'Traceback' not in result.stderr and 'SyntaxError' not in result.stderr,
                        f'{name}, optimized={optimized}: wrong failure ({result.returncode}): {result.stderr[:500]}')
                mutated_after = hashes(directory)
                require(mutated_before == mutated_after, f'{name}: validator modified its mutation inputs')
                records.append({'name': name, 'optimized': optimized, 'expected_diagnostic': diagnostic,
                                'observed_diagnostic': first, 'exit_code': result.returncode,
                                'fresh_directory': True, 'mutant_before_sha256': mutated_before,
                                'mutant_after_sha256': mutated_after})
    after = hashes(home, input_names)
    require(before == after, 'The campaign modified original inputs')
    summary = {'status': 'PASS', 'named_cases': len(cases), 'rejected_runs': len(records),
               'normal_and_optimized': True, 'syntax_only_or_crash_rejections_counted': 0,
               'assert_statements_in_validator': 0,
               'fresh_directory_clean_replay': {'runs': 2, 'stdout_sha256': baseline_hashes,
                                               'normal_optimized_outputs_identical': True},
               'original_before_sha256': before, 'original_after_sha256': after,
               'original_inputs_unchanged': True, 'results': records}
    rendered = json.dumps(summary, indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end='')


if __name__ == '__main__':
    try:
        main()
    except CampaignError as e:
        print('CAMPAIGN_FAILURE ' + str(e), file=sys.stderr)
        sys.exit(2)
