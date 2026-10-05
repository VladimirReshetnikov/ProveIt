#!/usr/bin/env python3
"""Exact finite validation for self-complementary score sequences.
Python >=3.10; standard library only. Guards remain active under python -O.
The independent enumerators share no recurrence helper or result cache.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations_with_replacement
from math import comb, isqrt
from pathlib import Path
import argparse
import hashlib
import json
import sys


class ValidationError(Exception):
    pass


def require(condition, code, detail=''):
    if not condition:
        raise ValidationError(code + (': ' + detail if detail else ''))


def unique_object(pairs):
    obj = {}
    for key, value in pairs:
        require(key not in obj, 'FIXTURE_DUPLICATE_KEY', key)
        obj[key] = value
    return obj


def exact_keys(obj, keys, code):
    require(type(obj) is dict and set(obj) == set(keys), code)


def load_fixtures(path):
    try:
        f = json.loads(path.read_text(encoding='utf-8'), object_pairs_hook=unique_object)
    except (OSError, UnicodeError, json.JSONDecodeError) as e:
        raise ValidationError('FIXTURE_PARSE: ' + str(e)) from e
    exact_keys(f, ['schema_version', 'sequence_sources', 'ranges', 'constants', 'limitations'], 'FIXTURE_ROOT_KEYS')
    require(type(f['schema_version']) is int and f['schema_version'] == 1, 'FIXTURE_SCHEMA_VERSION')
    require(type(f['sequence_sources']) is list and len(f['sequence_sources']) == 2, 'FIXTURE_SOURCE_COUNT')
    for s, name, length in zip(f['sequence_sources'], ['A345470', 'A351869'], [35, 39]):
        exact_keys(s, ['id', 'offset', 'url', 'retrieved_utc_date', 'terms'], 'FIXTURE_SOURCE_KEYS')
        require(s['id'] == name and s['url'] == 'https://oeis.org/' + name, 'FIXTURE_SOURCE_ID')
        require(type(s['offset']) is int and s['offset'] == 0, 'FIXTURE_OFFSET')
        require(s['retrieved_utc_date'] == '2026-10-02', 'FIXTURE_SOURCE_DATE')
        require(type(s['terms']) is list and len(s['terms']) == length, 'FIXTURE_PREFIX_LENGTH')
        require(all(type(v) is int and v >= 0 for v in s['terms']), 'FIXTURE_INTEGER_TERM')
    expected_ranges = {'dp_max_n': 38, 'brute_max_n': 9, 'exhaustive_max_n': 17,
                       'mass_max_length': 32, 'mass_max_k': 64, 'split_max_length': 1000}
    exact_keys(f['ranges'], expected_ranges, 'FIXTURE_RANGE_KEYS')
    require(all(type(f['ranges'][k]) is int and f['ranges'][k] == v for k, v in expected_ranges.items()), 'FIXTURE_RANGE_VALUE')
    rational_names = ['variance', 'exponential_base', 'exponential_absolute_moment',
                      'density_aw_coefficient', 'density_bw_coefficient',
                      'inverse_loglog_coefficient', 'frozen_probability']
    exact_keys(f['constants'], rational_names + ['frozen_first_g', 'frozen_slack_g'], 'FIXTURE_CONSTANT_KEYS')
    for key in rational_names:
        pair = f['constants'][key]
        require(type(pair) is list and len(pair) == 2 and all(type(v) is int for v in pair)
                and pair[1] > 0, 'FIXTURE_RATIONAL_TYPE', key)
        require(F(*pair).numerator == pair[0] and F(*pair).denominator == pair[1], 'FIXTURE_RATIONAL_REDUCED', key)
    for key in ['frozen_first_g', 'frozen_slack_g']:
        require(type(f['constants'][key]) is int and f['constants'][key] >= 0, 'FIXTURE_FROZEN_TYPE', key)
    expected_limits = [
        'Finite exact tests do not prove a bijection for all n.',
        'No numerical certification of Denisov-Wachtel survival, conditional convergence, cone estimates, or the resulting Theta laws is attempted.',
        'No asymptotic equivalent, parity-specific leading constant, limiting strong/all ratio, or general inverse asymptotic is numerically certified.']
    require(f['limitations'] == expected_limits, 'FIXTURE_LIMITATIONS')
    return f


def half_score_dp(n, strict):
    if n <= 1:
        return 1
    m, cap = n // 2, (n - 1) // 2
    states = {(0, 0): 1}  # (last score, sum of scores)
    for r in range(1, m + 1):
        new = defaultdict(int)
        for (last, total), multiplicity in states.items():
            for score in range(last, cap + 1):
                s = total + score
                if s >= r * (r - 1) // 2 + int(strict):
                    new[(score, s)] += multiplicity
        states = new
    return sum(states.values())


def composition_dp(n, strict):
    if n <= 1:
        return 1
    m, cap = n // 2, (n - 1) // 2
    states = {(0, 0): 1}  # (sum of G's, weighted sum of G's)
    for r in range(1, m + 1):
        new = defaultdict(int)
        for (used, weighted), multiplicity in states.items():
            for part in range(cap - used + 1):
                u = used + part
                w = weighted + u
                # sum_i (r-i+1)G_i - binom(r,2)
                if w - r * (r - 1) // 2 >= int(strict):
                    new[(u, w)] += multiplicity
        states = new
    # Append exactly one slack part cap-used, never another area test.
    return sum(states.values())


def integrated_walk_dp(n, strict):
    if n <= 1:
        return 1
    m, cap = n // 2, (n - 1) // 2
    endpoint = -1 if n % 2 == 0 else 0
    states = {(1, 0): 1}  # (velocity, area), no composition-total coordinate
    for r in range(1, m + 2):
        remaining = m + 1 - r
        new = defaultdict(int)
        for (velocity, area), multiplicity in states.items():
            # A future increment is >= -1, so endpoint reachability bounds new velocity.
            for new_velocity in range(velocity - 1, endpoint + remaining + 1):
                new_area = area + new_velocity
                if r <= m and new_area < int(strict):
                    continue
                new[(new_velocity, new_area)] += multiplicity
        states = new
    return sum(value for (v, a), value in states.items() if v == endpoint)


def full_score_brute(n, strict):
    if n <= 1:
        return 1
    count = 0
    for scores in combinations_with_replacement(range(n), n):
        if sum(scores) != n * (n - 1) // 2:
            continue
        if any(scores[j] + scores[n - j - 1] != n - 1 for j in range(n)):
            continue
        if all(sum(scores[:r]) >= r * (r - 1) // 2 + int(strict) for r in range(1, n)):
            count += 1
    return count


def reflect(n, half):
    return tuple(half) + ((n // 2,) if n % 2 else ()) + tuple(n - 1 - x for x in reversed(half))


def gaps(n, half):
    return (half[0],) + tuple(b - a for a, b in zip(half, half[1:])) + ((n - 1) // 2 - half[-1],)


def compositions(total, parts):
    if parts == 1:
        yield (total,)
    else:
        for first in range(total + 1):
            for rest in compositions(total - first, parts - 1):
                yield (first,) + rest


def positive_endpoint_probability(steps, target):
    # Independent suffix walk started at (area,velocity)=(1,1).
    needed = target - 1 + steps
    if needed < 0:
        return F(0)
    paths = 0
    for gs in compositions(needed, steps) if steps else [()]:
        if steps == 0 and target != 1:
            continue
        area, velocity = 1, 1
        for g in gs:
            velocity += g - 1
            area += velocity
            if area <= 0:
                break
        else:
            paths += int(velocity == target)
    return F(paths, 2 ** (needed + steps))


def check_counts(f, summary):
    all_counts = []
    comparisons = 0
    for strict in [False, True]:
        seq = []
        for n in range(f['ranges']['dp_max_n'] + 1):
            direct = half_score_dp(n, strict)
            require(composition_dp(n, strict) == direct, 'COMPOSITION_COUNT', f'n={n}, strict={strict}')
            require(integrated_walk_dp(n, strict) == direct, 'WALK_COUNT', f'n={n}, strict={strict}')
            comparisons += 2
            seq.append(direct)
        source = f['sequence_sources'][int(strict)]
        require(seq[:len(source['terms'])] == source['terms'], 'OEIS_PREFIX', source['id'])
        all_counts.append(seq)
    brute_checks = 0
    for n in range(f['ranges']['brute_max_n'] + 1):
        for strict in [False, True]:
            require(full_score_brute(n, strict) == all_counts[int(strict)][n], 'FULL_SCORE_BRUTE', f'n={n}, strict={strict}')
            brute_checks += 1
    C, D = all_counts
    require(D[1] == 1 and D[2] == 0, 'STRONG_SMALL_CASE_EXCEPTION')
    require(all(C[n] <= C[n + 1] for n in range(1, len(C) - 1)), 'WEAK_MONOTONICITY')
    require(all(D[n] <= D[n + 1] for n in range(2, len(D) - 1)), 'STRONG_MONOTONICITY')
    require(all(d <= c for c, d in zip(C, D)), 'STRONG_SUBSET_COUNT')
    summary['enumeration'] = {'n_range': [0, f['ranges']['dp_max_n']], 'both_strictnesses': True,
                              'independent_pairwise_comparisons': comparisons,
                              'brute_n_range': [0, f['ranges']['brute_max_n']], 'brute_checks': brute_checks,
                              'A345470_source_terms': len(f['sequence_sources'][0]['terms']),
                              'A351869_source_terms': len(f['sequence_sources'][1]['terms']),
                              'C': C, 'D': D}
    return all_counts


def check_exhaustive(f, summary):
    half_candidates = composition_candidates = injection_checks = frozen_checks = 0
    slack_counterexamples = {}
    require(f['constants']['frozen_first_g'] == 1, 'FROZEN_FIRST_G')
    require(f['constants']['frozen_slack_g'] == 0, 'FROZEN_SLACK_G')
    freeze_weight = F(*f['constants']['frozen_probability'])
    require(freeze_weight == F(1, 4) * F(1, 2), 'FROZEN_FACTOR')
    for n in range(2, f['ranges']['exhaustive_max_n'] + 1):
        m, cap = n // 2, (n - 1) // 2
        gap_images, good = set(), {False: [], True: []}
        frozen = 0
        for half in combinations_with_replacement(range(cap + 1), m):
            half_candidates += 1
            full = reflect(n, half)
            excesses = [sum(full[:r]) - r * (r - 1) // 2 for r in range(n + 1)]
            require(sum(full) == n * (n - 1) // 2, 'REFLECTED_TOTAL')
            require(all(excesses[n - r] == excesses[r] for r in range(n + 1)), 'LANDAU_REFLECTION')
            gs = gaps(n, half)
            require(len(gs) == m + 1 and min(gs) >= 0 and sum(gs) == cap, 'GAP_SLACK_COMPOSITION')
            require(tuple(sum(gs[:r]) for r in range(1, m + 1)) == half, 'GAP_INVERSE')
            require(gs not in gap_images, 'GAP_INJECTIVE')
            gap_images.add(gs)
            velocity, area = 1, 0
            for r, g in enumerate(gs[:-1], 1):
                velocity += g - 1
                area += velocity
                require(velocity == half[r - 1] - r + 1, 'VELOCITY_IDENTITY')
                require(area == excesses[r], 'AREA_IDENTITY')
                require((area >= 0) == (area + 1 > 0), 'AREA_PLUS_ONE_SHIFT')
            final_velocity = velocity + gs[-1] - 1
            require(final_velocity == cap - m == (-1 if n % 2 == 0 else 0), 'FINAL_SLACK_ENDPOINT')
            require(final_velocity - 1 == (-2 if n % 2 == 0 else -1), 'SUM_INCREMENT_ENDPOINT')
            require(F(1, 2 ** (sum(gs) + len(gs))) == F(1, 2 ** n), 'COMPOSITION_PROBABILITY')
            for strict in [False, True]:
                hgood = all(x >= int(strict) for x in excesses[1:m + 1])
                fullgood = all(x >= int(strict) for x in excesses[1:n])
                require(hgood == fullgood, 'HALF_FULL_LANDAU_EQUIVALENCE')
                if hgood:
                    good[strict].append(half)
            if all(x > 0 for x in excesses[1:m + 1]) and gs[0] == 1 and gs[-1] == 0:
                frozen += 1
                require(excesses[1] == 1 and half[0] == 1, 'FROZEN_INITIAL_STATE')
                require(velocity == (0 if n % 2 == 0 else 1), 'FROZEN_TESTED_ENDPOINT')
            for strict in [False, True]:
                if all(x >= int(strict) for x in excesses[1:m + 1]) and area + final_velocity < int(strict):
                    slack_counterexamples.setdefault('strict' if strict else 'weak',
                        {'n': n, 'half_scores': list(half), 'tested_area': area,
                         'final_velocity': final_velocity, 'untested_area': area + final_velocity})
        # Enumerate all weak compositions separately, rather than only checking generated images.
        direct_compositions = set(compositions(cap, m + 1))
        composition_candidates += len(direct_compositions)
        require(gap_images == direct_compositions, 'GAP_SURJECTIVE_FINITE')
        for strict, halves in good.items():
            images = set()
            for half in halves:
                image = half if n % 2 == 0 else half + (m,)
                image_full = reflect(n + 1, image)
                require(tuple(sorted(image_full)) == image_full and 0 <= image[0] <= image[-1] <= n // 2, 'MONOTONE_INJECTION_ORDER')
                require(all(sum(image_full[:r]) - r * (r - 1) // 2 >= int(strict)
                            for r in range(1, n + 1)), 'MONOTONE_INJECTION_LANDAU')
                require(image not in images, 'MONOTONE_INJECTION_DISTINCT')
                images.add(image)
                if n % 2:
                    old_last = sum(half) - m * (m - 1) // 2
                    new_last = sum(image) - (m + 1) * m // 2
                    require(new_last == old_last, 'MONOTONE_LAST_EXCESS')
                injection_checks += 1
        expected = freeze_weight * positive_endpoint_probability(m - 1, 0 if n % 2 == 0 else 1)
        require(F(frozen, 2 ** n) == expected, 'FROZEN_LOWER_CLASS', f'n={n}')
        frozen_checks += 1
    require(set(slack_counterexamples) == {'weak', 'strict'}, 'FINAL_STEP_COUNTEREXAMPLE_MISSING')
    require(slack_counterexamples['weak']['n'] == 2 and slack_counterexamples['strict']['n'] == 4, 'FINAL_STEP_MINIMAL_COUNTEREXAMPLES')
    require(not all(sum(reflect(2, (0,))[:r]) - r * (r - 1) // 2 > 0 for r in range(1, 2)), 'STRONG_N1_INJECTION_EXCEPTION')
    summary['exhaustive'] = {'n_range': [2, f['ranges']['exhaustive_max_n']],
                             'half_candidates': half_candidates, 'composition_candidates': composition_candidates,
                             'valid_injection_checks': injection_checks, 'frozen_class_checks': frozen_checks,
                             'extra_area_test_counterexamples': slack_counterexamples}


def nb_mass(length, d):
    return F(0) if d < -length else F(comb(2 * length + d - 1, length - 1), 2 ** (2 * length + d))


def check_distribution(f, summary):
    checks = 0
    for ell in range(1, f['ranges']['mass_max_length'] + 1):
        require(nb_mass(ell, -ell - 1) == 0, 'NB_SUPPORT')
        mode = F(comb(2 * ell - 2, ell - 1), 2 * 4 ** (ell - 1))
        require(nb_mass(ell, -1) == mode, 'NB_MODE_FORMULA')
        if ell >= 2:
            require(nb_mass(ell, -2) == mode, 'NB_SECOND_MODE')
        for k in range(f['ranges']['mass_max_k'] + 1):
            d = k - ell
            p = nb_mass(ell, d)
            require(p == F(ell, 2 * ell + d) * F(comb(2 * ell + d, ell), 2 ** (2 * ell + d)), 'NB_BINOMIAL_FORM')
            require(nb_mass(ell, d + 1) / p == F(2 * ell + d, 2 * (ell + d + 1)), 'NB_RATIO')
            require(p <= mode, 'NB_MAXIMUM')
            partial = sum((nb_mass(ell, j - ell) for j in range(k + 1)), F(0))
            tail = sum((F(comb(ell + k, j), 2 ** (ell + k)) for j in range(ell)), F(0))
            require(partial + tail == 1, 'NB_NORMALIZATION_EXACT_TAIL')
            checks += 1
    # Convolution check is independent of the closed negative-binomial formula.
    states = {0: F(1)}
    for ell in range(1, 9):
        new = defaultdict(F)
        for used, probability in states.items():
            for g in range(17 - used):
                new[used + g] += probability * F(1, 2 ** (g + 1))
        states = new
        require(all(p == nb_mass(ell, total - ell) for total, p in states.items()), 'NB_INDEPENDENT_CONVOLUTION')
    # Rational generating-function identities for the geometric series at q=1/2.
    q = F(1, 2)
    S0, S1, S2 = 1 / (1 - q), q / (1 - q) ** 2, q * (1 + q) / (1 - q) ** 3
    mean = (S1 - S0) / 2
    second = (S2 - 2 * S1 + S0) / 2
    require(mean == 0, 'INCREMENT_MEAN')
    require(second == F(*f['constants']['variance']) == 2, 'INCREMENT_VARIANCE')
    exp_base = F(*f['constants']['exponential_base'])
    require(exp_base == F(3, 2) and 1 < exp_base < 2, 'EXPONENTIAL_BASE')
    moment = exp_base / 2 + 1 / (4 * (1 - exp_base / 2))
    require(moment == F(*f['constants']['exponential_absolute_moment']) == F(7, 4), 'EXPONENTIAL_MOMENT')
    for N in range(65):
        finite = exp_base / 2 + sum((exp_base ** x / 2 ** (x + 2) for x in range(N + 1)), F(0))
        tail = (exp_base / 2) ** (N + 1) / (4 * (1 - exp_base / 2))
        require(finite + tail == moment, 'EXPONENTIAL_MOMENT_TAIL')
    require(0 - (-1) == 1 and F(1, 2) > 0 and F(1, 4) > 0, 'SPAN_ONE_CERTIFICATE')
    summary['increment_distribution'] = {'mass_ratio_normalization_cases': checks,
                                          'convolution_lengths': 8, 'variance': str(second),
                                          'exponential_base': str(exp_base), 'absolute_exponential_moment': str(moment),
                                          'note': 'Finite tail equalities and rational geometric-series certificates, not a numerical local limit.'}


# Exact multivariate Laurent polynomials in (a,b,t,w), with rational coefficients.
def poly_add(*polys):
    out = defaultdict(F)
    for p in polys:
        for key, value in p.items():
            out[key] += value
    return {key: value for key, value in out.items() if value}


def poly_scale(p, scale):
    return {key: value * scale for key, value in p.items() if value * scale}


def poly_mul(p, q):
    out = defaultdict(F)
    for kp, vp in p.items():
        for kq, vq in q.items():
            out[tuple(x + y for x, y in zip(kp, kq))] += vp * vq
    return {key: value for key, value in out.items() if value}


def mono(coef, powers):
    return {powers: F(coef)}


def gaussian_exponent(a, y, u, v):
    # -6(u-a-t*y)^2/t^3 + 6(u-a-t*y)(v-y)/t^2 - 2(v-y)^2/t.
    delta = poly_add(u, poly_scale(a, -1), poly_scale(poly_mul(mono(1, (0, 0, 1, 0)), y), -1))
    speed = poly_add(v, poly_scale(y, -1))
    return poly_add(poly_mul(mono(-6, (0, 0, -3, 0)), poly_mul(delta, delta)),
                    poly_mul(mono(6, (0, 0, -2, 0)), poly_mul(delta, speed)),
                    poly_mul(mono(-2, (0, 0, -1, 0)), poly_mul(speed, speed)))


def check_algebra(f, summary):
    a, b, w = mono(1, (1, 0, 0, 0)), mono(1, (0, 1, 0, 0)), mono(1, (0, 0, 0, 1))
    difference = poly_add(gaussian_exponent(a, poly_scale(b, -1), {}, poly_scale(w, -1)),
                          poly_scale(gaussian_exponent(a, poly_scale(b, -1), {}, w), -1))
    expected = {(1, 0, -2, 1): F(*f['constants']['density_aw_coefficient']),
                (0, 1, -1, 1): F(*f['constants']['density_bw_coefficient'])}
    require(difference == expected == {(1, 0, -2, 1): F(12), (0, 1, -1, 1): F(-4)}, 'DENSITY_RATIO_ALGEBRA')
    split_checks = endpoint_checks = 0
    for ell in range(2, f['ranges']['split_max_length'] + 1):
        h, q = ell // 2, ell - ell // 2
        require(h + q == ell and h >= 1 and q >= 1 and 3 * h >= ell and 2 * q >= ell, 'BRIDGE_SPLIT_BOUNDS')
        require(h * h <= 2 * ell * q and q * q <= 3 * ell * h, 'BRIDGE_COEFFICIENT_BOUNDS')
        t = ell // 2
        suffix = ell - t
        require(t <= suffix <= t + 1 <= 2 * t, 'LOWER_SPLIT_BOUNDS')
        require(16 * t ** 3 > suffix ** 3, 'AREA_PROTECTION_L4')
        for target in [-2, -1, 0, 1, 2]:
            if suffix >= target * target:
                for velocity in range(-isqrt(t), isqrt(t) + 1):
                    require((target - velocity) ** 2 <= 4 * suffix, 'BRIDGE_ENDPOINT_WINDOW')
                    endpoint_checks += 1
        split_checks += 1
    # The identity below checks the formal 3/4 inversion coefficient on exact powers of 2.
    alpha = F(*f['constants']['inverse_loglog_coefficient'])
    require(alpha == F(3, 4), 'INVERSE_LOGLOG_COEFFICIENT')
    inverse_cases = 0
    for r in range(1, 17):
        L = 2 ** (4 * r)
        for shift in range(-3, 4):
            n = L + 3 * r + shift
            lhs = F(2 ** (4 * (n - L)), n ** 3)
            rhs = F(2 ** (4 * shift), 1) * F(L, n) ** 3 if shift >= 0 else F(1, 2 ** (-4 * shift)) * F(L, n) ** 3
            require(lhs == rhs, 'FORMAL_INVERSE_POWER_IDENTITY')
            inverse_cases += 1
    summary['exact_algebra'] = {'density_log_ratio': '12*a*w/t^2 - 4*b*w/t = 4*w*(3*a-b*t)/t^2',
                               'split_lengths_checked': split_checks, 'endpoint_window_cases': endpoint_checks,
                               'formal_inverse_power_cases': inverse_cases,
                               'note': 'Polynomial identity is exact. Integer-range tests support bookkeeping, not limit theorems.'}


def check_thresholds(all_counts, summary):
    checked = 0
    for seq in all_counts:
        targets = {1}
        for value in seq[1:]:
            targets.update(x for x in [value - 1, value, value + 1] if 1 <= x <= seq[-1])
        for x in sorted(targets):
            n = next(i for i in range(1, len(seq)) if seq[i] >= x)
            require(seq[n] >= x and all(value < x for value in seq[1:n]), 'INVERSE_MINIMUM')
            require(n == 1 or seq[n - 1] < x, 'INVERSE_ADJACENT_THRESHOLD')
            checked += 1
    summary['finite_threshold_inverse_cases'] = checked


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fixtures', type=Path, default=Path(__file__).with_name('fixtures.json'))
    parser.add_argument('--output', type=Path)
    parser.add_argument('--only', choices=['all', 'schema', 'counts', 'exhaustive', 'distribution', 'algebra'], default='all')
    args = parser.parse_args()
    try:
        f = load_fixtures(args.fixtures)
        summary = {'status': 'PASS', 'arithmetic': 'Python standard-library integers and fractions.Fraction only',
                   'fixture_sha256': hashlib.sha256(args.fixtures.read_bytes()).hexdigest()}
        if args.only in ['all', 'counts']:
            seqs = check_counts(f, summary)
            check_thresholds(seqs, summary)
        if args.only in ['all', 'exhaustive']:
            check_exhaustive(f, summary)
        if args.only in ['all', 'distribution']:
            check_distribution(f, summary)
        if args.only in ['all', 'algebra']:
            check_algebra(f, summary)
        summary['limitations'] = f['limitations']
        rendered = json.dumps(summary, indent=2, sort_keys=True) + '\n'
        if args.output:
            args.output.write_text(rendered, encoding='utf-8')
        print(rendered, end='')
        return 0
    except ValidationError as e:
        print('VALIDATION_FAILURE ' + str(e), file=sys.stderr)
        return 2


if __name__ == '__main__':
    sys.exit(main())
