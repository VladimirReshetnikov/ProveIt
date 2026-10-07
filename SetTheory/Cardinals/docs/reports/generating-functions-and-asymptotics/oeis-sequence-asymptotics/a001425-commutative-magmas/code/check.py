#!/usr/bin/env python3
"""Reproduce all Report200 data with explicit, optimization-safe checks.

    python3 code/check.py --output-dir data
    python3 -O code/check.py --output-dir data_optimized
    python3 code/check.py --exact-only --output-dir data_exact

Exact enumeration, amplitudes, finite tails, and exhaustive small tables use
only Python's standard library. Full mode additionally uses SymPy and mpmath.
No private paths, source receipts, network access, or input files are needed.
"""
import sys
sys.dont_write_bytecode = True

import argparse
from collections import Counter
from fractions import Fraction as Q
import hashlib
import json
from math import factorial
from pathlib import Path
import magma as m

OEIS_DISPLAYED_TERMS = (
    1, 1, 4, 129, 43968, 254429900, 30468670170912,
    91267244789189735259, 8048575431238519331999571800,
    24051927835861852500932966021650993560,
    2755731922430783367615449408031031255131879354330,
    13513302615133133128014689228630596983478739041461798638894834,
)
SOURCE = {'sequence': 'OEIS A001425', 'url': 'https://oeis.org/A001425',
          'displayed_terms_checked': 'n=0 through n=11', 'source_check_date': '2026-10-04',
          'scope': 'Only the 12 displayed terms are comparison data. No b-file or third-party PDF is required or redistributed.'}


class Checks:
    def __init__(self):
        self.number = 0

    def __call__(self, condition, message):
        self.number += 1
        if not condition:
            raise RuntimeError(message)


def malformed_input_tests(check):
    cases = [
        ('negative order', lambda: m.count(-1)),
        ('floating order', lambda: m.count(3.0)),
        ('Boolean order', lambda: m.count(True)),
        ('text order', lambda: m.count('3')),
        ('unknown counting method', lambda: m.count(3, 'unknown')),
        ('negative partition size', lambda: list(m.partitions(-1))),
        ('zero minimum partition part', lambda: list(m.partitions(3, 0))),
        ('nonintegral minimum partition part', lambda: list(m.partitions(3, 1.5))),
        ('zero cycle length', lambda: m.pair_orbits((0,))),
        ('negative cycle length', lambda: m.trace_orbits((-2,))),
        ('floating cycle length', lambda: m.fixed_count((2.0,))),
        ('Boolean cycle length', lambda: m.fixed_count((True,))),
        ('unordered collection instead of cycle list', lambda: m.pair_orbits({2, 3})),
        ('text cycle collection', lambda: m.trace_orbits('23')),
        ('zero fixed-point power', lambda: m.fixed_points((2,), 0)),
        ('zero divisor argument', lambda: m.divisors(0)),
        ('zero Moebius argument', lambda: m.mobius(0)),
        ('identity part in moved sector', lambda: m.sector(3, (1, 2))),
        ('sector support exceeds order', lambda: m.sector(2, (3,))),
        ('normalized sector at zero', lambda: m.sector(0, ())),
        ('negative defect', lambda: m.sectors_through_defect(-1)),
        ('empty amplitude sector', lambda: m.amplitude(())),
        ('negative amplitude order', lambda: m.amplitude((2,), -1)),
        ('floating amplitude order', lambda: m.amplitude((2,), 1.5)),
        ('empty direct-series sector', lambda: m.direct_log_series(())),
        ('tail outside domain', lambda: m.rational_tail_lower(7, 0)),
        ('tail support domain violated', lambda: m.rational_tail_lower(15, 3)),
        ('negative tail defect', lambda: m.rational_tail_lower(12, -1)),
        ('unsafe exhaustive range', lambda: m.exhaustive_tables(4)),
    ]
    rows = []
    for name, call in cases:
        caught = False
        try:
            call()
        except ValueError:
            caught = True
        check(caught, 'Malformed input was not rejected: ' + name)
        rows.append({'case': name, 'result': 'ValueError'})
    return rows


def exact_computations(check):
    counts, types = [], []
    zero_types = fixed_point_free_types = compared = 0
    for n in range(25):
        sums = {route: Q(0) for route in ('walk', 'trace', 'grouped')}
        for p in m.partitions(n):
            walk_h, trace_h = m.pair_orbits(p), m.trace_orbits(p)
            check(walk_h == trace_h, f'Pair-orbit and trace histograms disagree at {p}')
            values = {route: m.fixed_count(p, route) for route in sums}
            mu = tuple(k for k in p if k > 1)
            split = m.sector_fixed_count(n, mu)
            check(len(set(values.values()) | {split}) == 1, f'Fixed-count routes disagree at n={n}, type={p}')
            z = m.z_type(p)
            check(factorial(n) % z == 0, 'Nonintegral conjugacy-class size')
            for route in sums:
                sums[route] += Q(values[route], z)
            s, d = sum(mu), sum(mu) - len(mu)
            loss = n * (n + 1) // 2 - sum(walk_h.values())
            check(Q(loss) >= (n - s) * d + Q(s * s, 4), 'Support orbit-loss inequality failed')
            if d:
                check(d + 1 <= s <= min(2 * d, n), 'Moved-support range failed')
                loss_bound = d * (n - d) if 2 * d <= n else Q(n * n, 4)
                check(loss >= loss_bound, 'Defect orbit-loss inequality failed')
                moved_h = m.pair_orbits(mu)
                check(moved_h.get(1, 0) == mu.count(2), 'Moved-pair singleton characterization failed')
                check(sum(moved_h.values()) <= Q(s * (s + 2), 4), 'Moved-pair orbit bound failed')
            check(values['walk'] <= n**sum(walk_h.values()), 'Fixed count exceeds orbit majorant')
            if n > 0:
                compared += 1
                zero_types += values['walk'] == 0
                fixed_point_free_types += s == n
            types.append({'n': n, 'cycle_type': list(p), 'moved_type': list(mu),
                          'support': s, 'defect': d, 'pair_orbits': {str(k): v for k, v in walk_h.items()},
                          'orbit_loss': loss, 'conjugacy_class_size': str(factorial(n) // z),
                          'fixed_count': str(values['walk']), 'all_four_methods_agree': True})
        check(all(value.denominator == 1 for value in sums.values()), 'Burnside count nonintegral')
        check(len(set(sums.values())) == 1, f'Independent Burnside sums disagree at n={n}')
        counts.append(sums['walk'].numerator)
    check(tuple(counts[:12]) == OEIS_DISPLAYED_TERMS, 'Displayed OEIS terms disagree')

    family = m.sectors_through_defect(4)
    check(len(family) == 11, 'Expected eleven sectors through defect four')
    expansions = []
    for mu in family:
        expansion = m.amplitude(mu, 5)
        direct = m.direct_log_series(mu, 5)
        check(direct[-1] == -Q(sum(mu), 2), 'Amplitude pole failed to match')
        check(direct[0] == Q(expansion['C']), 'Amplitude constant failed to match')
        check([str(direct[j]) for j in range(1, 6)] == expansion['log_coeff'], 'Direct Laurent coefficients disagree')
        alternate = m.exponential_by_partitions([direct[j] for j in range(1, 6)])
        check([str(v) for v in alternate] == expansion['relative_coeff'], 'Independent exponentiation disagrees')
        expansion['direct_log_pole'] = str(direct[-1])
        expansion['direct_log_constant'] = str(direct[0])
        expansion['independent_formal_series_check'] = 'pass'
        expansions.append(expansion)
    printed = {(2,): ['1', '-10/3', '55/18', '-286/405', '-463/9720'],
               (3,): ['1', '-21/4', '325/32', '-5607/640'],
               (2, 2): ['1', '-62/3', '1667/9', '-383402/405']}
    for mu, expected in printed.items():
        check(m.amplitude(mu)['relative_coeff'][:len(expected)] == expected,
              'Leading displayed sector coefficients disagree')

    tail_rows = []
    for n in range(8, 25):
        normalized = Q(factorial(n) * counts[n], n**(n * (n + 1) // 2))
        by_defect = Counter()
        permutations_by_defect = Counter()
        for record in types:
            if record['n'] == n:
                d = record['defect']
                class_size = int(record['conjugacy_class_size'])
                by_defect[d] += Q(class_size * int(record['fixed_count']), n**(n * (n + 1) // 2))
                permutations_by_defect[d] += class_size
        for d, size in permutations_by_defect.items():
            check(size <= n**(2 * d), 'Permutation-count defect bound failed')
            if 0 < 2 * d <= n:
                check(by_defect[d] <= Q(n)**(2 * d - d * (n - d)), 'Per-defect H_d bound failed')
        for defect in range(n // 4):
            remainder = normalized - 1 - sum((m.sector(n, mu) for mu in m.sectors_through_defect(defect)), Q(0))
            direct_tail = sum((v for d, v in by_defect.items() if d > defect), Q(0))
            check(remainder == direct_tail, 'Omitted-tail sum does not match subtraction')
            lower_bound_on_B = m.rational_tail_lower(n, defect)
            check(0 <= remainder <= lower_bound_on_B, f'Exact finite-tail check failed at n={n}, D={defect}')
            tail_rows.append({'n': n, 'D': defect, 'odd_n': bool(n % 2),
                              'R_D_exact': str(remainder),
                              'rational_lower_bound_on_B_D': str(lower_bound_on_B),
                              'R_D_over_rational_lower_bound_exact': str(remainder / lower_bound_on_B),
                              'passes_stronger_rational_inequality': True})
    check(len(tail_rows) == 62, 'Finite-tail coverage changed unexpectedly')
    brute = [m.exhaustive_tables(n) for n in range(4)]
    check(brute[3]['labeled_automorphism_order_counts'] == {1: 696, 2: 24, 3: 8, 6: 1}, 'n=3 exhaustive distribution differs')
    check(sum(row['labeled_total'] for row in brute) == 739, 'Exhaustive count including empty law differs')
    malformed = malformed_input_tests(check)
    return counts, types, expansions, tail_rows, brute, {
        'status': 'pass', 'exact_arithmetic': 'Python integers and fractions.Fraction; no floating comparisons',
        'maximum_n': 24, 'positive_order_partition_types_checked': compared,
        'zero_fixed_count_types': zero_types, 'fixed_point_free_types': fixed_point_free_types,
        'sector_count': len(expansions), 'correction_coefficients_per_sector': 5,
        'finite_tail_checks': len(tail_rows), 'odd_n_tail_checks': sum(row['odd_n'] for row in tail_rows),
        'labeled_tables_enumerated_including_empty': sum(row['labeled_total'] for row in brute),
        'labeled_tables_enumerated_positive_order': sum(row['labeled_total'] for row in brute[1:]),
        'malformed_input_tests': malformed,
        'explicit_top_level_checks': check.number,
        'internal_checks': 'Additional explicit invariant checks run within each mathematical routine.',
        'limitations': ['Finite computations do not prove the infinite-family tail or asymptotic statements.',
                       'The rational lower bound on B_D is a stronger finite test, not a claimed replacement bound valid for all n.',
                       'Asymptotic inverse statements retain eventual qualifiers; no numerical cutoff is certified.']}


def write_json(path, data):
    path.write_text(json.dumps(data, indent=2, ensure_ascii=True) + '\n', encoding='utf-8')


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--output-dir', type=Path, default=Path(__file__).resolve().parent.parent / 'data')
    parser.add_argument('--exact-only', action='store_true', help='skip optional SymPy and mpmath checks')
    args = parser.parse_args()
    # Check optional dependencies before writing a partial full-mode output.
    if not args.exact_only:
        try:
            import symbolic
            import diagnostics
        except ImportError as exc:
            parser.error(f'Full mode requires SymPy and mpmath ({exc}). Install code/requirements.txt or use --exact-only.')
    check = Checks()
    counts, types, expansions, tails, brute, validation = exact_computations(check)
    optional_symbolic = symbolic.run() if not args.exact_only else None
    optional_diagnostics = diagnostics.run() if not args.exact_only else None
    output = args.output_dir
    output.mkdir(parents=True, exist_ok=True)
    payloads = {
        'counts.json': {'source': SOURCE, 'integer_encoding': 'decimal strings to avoid loss in JSON readers',
                        'all_three_Burnside_methods_agree': True,
                        'exact_counts_0_to_24': [str(v) for v in counts],
                        'displayed_OEIS_terms': [str(v) for v in OEIS_DISPLAYED_TERMS],
                        'displayed_terms_match': True},
        'fixed_counts.json': {'description': 'Every cycle type through n=24: explicit pair-orbit walk, trace/Moebius inversion, grouped cycle formula, and support factorization agree.',
                              'records': types},
        'sectors.json': {'description': 'All eleven moved cycle types through defect four, with p_0 through p_5 and L_1 through L_5.',
                         'coefficient_encoding': 'exact rational strings', 'expansions': expansions},
        'finite_tails.json': {'description': 'Exact finite checks R_D <= rational lower bound <= B_D for every admissible (n,D), 8<=n<=24.',
                             'lower_bound_construction': 'Replace 3-n/2 and n-3*n^2/16 by their floors. Both replacements decrease B_D.',
                             'scope': 'All omitted classes are included in each exact R_D; infinite-n validity is proved in the report.',
                             'checks': tails},
        'exhaustive_tables.json': {'description': 'Every labeled table and every relabeling permutation at n=0,1,2,3; unlabeled classes identified directly.',
                                  'records': brute},
        'validation.json': validation,
    }
    if optional_symbolic is not None:
        payloads['symbolic_checks.json'] = optional_symbolic
        payloads['diagnostics.json'] = optional_diagnostics
    for name, payload in payloads.items():
        write_json(output / name, payload)
    (output / 'counts.txt').write_text('# OEIS A001425: exact counts computed independently\n# n U_n\n' +
                                     ''.join(f'{n} {value}\n' for n, value in enumerate(counts)), encoding='utf-8')
    header = ['mu', 'd', 's', 'beta', 'C', 'z', 'p0', 'p1', 'p2', 'p3', 'p4', 'p5']
    lines = ['\t'.join(header)]
    for a in expansions:
        lines.append('\t'.join([','.join(map(str, a['mu'])), str(a['defect']), str(a['support']),
                                str(a['beta']), a['C'], str(a['z'])] + a['relative_coeff']))
    (output / 'sector_coefficients.tsv').write_text('\n'.join(lines) + '\n', encoding='utf-8')
    summary = [
        'PASS: Report200 reproducibility checks',
        'Exact arithmetic: standard-library integers and rational fractions',
        'Exact counts: n=0 through 24; all 12 displayed OEIS terms agree',
        f'Positive-order partition types: {validation["positive_order_partition_types_checked"]}',
        'Fixed counts: four agreeing routes; pair orbit histograms: two independent routes',
        'Amplitude coefficients: all 11 sectors through defect 4; p0 through p5',
        'Finite tail inequalities: 62 exact checks, including odd n',
        'Exhaustive tables: 739 including the empty operation; 738 at positive order',
        f'Malformed inputs rejected: {len(validation["malformed_input_tests"])}',
        'Optional symbolic checks: ' + ('skipped' if args.exact_only else 'pass'),
        'Optional high-precision diagnostics: ' + ('skipped' if args.exact_only else 'pass; not proof'),
        'Explicit exception checks remain active under python -O',
        'No computation here supplies a uniform inverse cutoff or a worldwide originality claim.',
    ]
    (output / 'summary.txt').write_text('\n'.join(summary) + '\n', encoding='utf-8')
    names = sorted(list(payloads) + ['counts.txt', 'sector_coefficients.tsv', 'summary.txt'])
    manifest = {name: hashlib.sha256((output / name).read_bytes()).hexdigest() for name in names}
    write_json(output / 'manifest.json', {'algorithm': 'SHA-256', 'files': manifest,
                                         'scope': 'Hashes of outputs emitted in this run; excludes this manifest.'})
    print('\n'.join(summary))


if __name__ == '__main__':
    main()
