"""Run exact checks, generate CSV/JSON data, and print a reproducibility report.

Usage: python code/verify.py
No dependencies beyond the Python 3.10+ standard library. Finite checks
complement, but do not replace, the article's proofs. No test constructs a high
power tower.

This is the merged suite. It runs both families of checks that the two source
packages ran independently:

  * the DECIMAL suite, for bases ending in 9, the exact transient, the minimal
    prime counterexample, the CRT prime families, the density counts, and the
    general-radix affine laws;
  * the DIAGONAL suite, for the family a = B-1 with even B, the gap-general
    local distances, the leading-difference congruence, the fixed points, the
    capped hyperoperations, the higher-arrow saturation, and the local Lambert
    series.

The two grids OVERLAP (both cover even radices 4..100 at heights 0..10), so the
per-suite subtotals below must not be read as counts of distinct mathematical
facts, and must not simply be added to obtain one. The combined total reported
here is the number of assertions this program actually executes.

Three levels of validation are kept, so that no test reuses the routine it is
meant to check: literal constructed integer towers, two independent modular
oracles (a restricted Euler chain on {2,5}-supported moduli, and a general
totient chain with a capped exponent lift), and only then the specialized
evaluators.
"""
from __future__ import annotations
import csv
import json
import platform
from dataclasses import asdict
from functools import lru_cache
from pathlib import Path
from math import gcd, isqrt
from tetration import (DecimalProfile, valuation, residue_towers,
    tower_mod_25_euler, primes_below, is_prime_trial, prime_delay_progression,
    delay_tail_density, stable_radix_residue, local_lines,
    stable_digits_radix, first_permanent_height, factor_trial,
    tetration_mod, difference_residue, predicted_prime_distance,
    capped_hyper, knuth_mod, local_lambert_residue)

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'data'
DATA.mkdir(exist_ok=True)
checks = 0
counts: dict[str, int] = {}
diagonal_counts: dict[str, int] = {}


def check(condition: bool, message: str) -> None:
    global checks
    checks += 1
    if not condition:
        raise AssertionError(message)


def dcheck(group: str, condition: bool) -> None:
    """Counted check for the diagonal suite, grouped by check family."""
    global checks
    checks += 1
    diagonal_counts[group] = diagonal_counts.get(group, 0) + 1
    if not condition:
        raise AssertionError(f'{group}: failed check {diagonal_counts[group]}')


def write_csv(name: str, rows: list[dict]) -> None:
    if not rows:
        raise ValueError('refusing to write empty CSV')
    with (DATA/name).open('w', newline='', encoding='utf-8') as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


# ---------------------------------------------------------------------------
# The general totient-chain oracle, with a capped exponent lift.
#
# For a modulus M with P = phi(M), an exponent E >= P is replaced by
# (E mod P) + P. This is valid even when the base shares a factor with M: at a
# prime power p**f dividing M with p | base, both exponents are at least
# P >= phi(p**f) >= f, so both powers vanish modulo p**f; the Chinese remainder
# theorem finishes the argument. Smaller exponents are obtained exactly by a
# capped evaluation. This oracle does NOT reuse the fixed-modulus iteration
# whose correctness the article proves.
# ---------------------------------------------------------------------------


@lru_cache(maxsize=None)
def phi(n: int) -> int:
    out = n
    for p in factor_trial(n):
        out = out // p * (p - 1)
    return out


def cap_power(a: int, n: int, cap: int) -> int:
    x = 1
    for _ in range(n):
        x *= a
        if x >= cap:
            return cap
    return x


@lru_cache(maxsize=None)
def cap_tower(a: int, h: int, cap: int) -> int:
    if cap <= 1:
        return cap
    if h == 0:
        return 1
    threshold, z = 0, 1
    while z < cap:
        threshold += 1
        z *= a
    e = cap_tower(a, h - 1, threshold)
    return cap if e == threshold else a**e


@lru_cache(maxsize=None)
def oracle(a: int, h: int, modulus: int) -> int:
    if modulus == 1:
        return 0
    if h == 0:
        return 1
    period = phi(modulus)
    small = cap_tower(a, h - 1, period)
    if small < period:
        return pow(a, small, modulus)
    e = oracle(a, h - 1, period) + period
    return pow(a, e, modulus)


def decimal_suite() -> list[dict]:
    """All checks inherited from the decimal investigation."""
    global checks
    before = checks
    # Verify all predicted local valuations with nonzero exact residue differences.
    # The decimal working precision is strictly larger than both valuations.
    for a in range(9, 20000, 10):
        profile = DecimalProfile.for_base(a)
        max_h = 10
        precision = max(profile.s + max_h*profile.u, max_h*profile.e) + 2
        mod = 10**precision
        rs = residue_towers(a, max_h + 1, mod)
        for h in range(max_h+1):
            difference = (rs[h+1] - rs[h]) % mod
            check(difference != 0, f'precision too low: {a}, {h}')
            v2, v5 = valuation(difference, 2), valuation(difference, 5)
            check(v2 == profile.s + h*profile.u, f'v2: {a}, {h}')
            check(v5 == h*profile.e, f'v5: {a}, {h}')
            check(min(v2, v5) == profile.stable_digits(h), f'digits: {a}, {h}')
        onset = profile.onset
        check(all(profile.speed(h) == profile.eventual_speed
                  for h in range(onset, onset+10)), f'onset: {a}')
        if onset > 1:
            check(profile.speed(onset-1) != profile.eventual_speed,
                  f'onset sharpness: {a}')
    counts['decimal_2000_bases_heights_0_to_10'] = checks - before

    before = checks
    # An independent Euler-chain algorithm checks residue iteration.
    for a in list(range(9, 1000, 10)) + [2749, 16249, 781249]:
        for precision in (1, 2, 4, 8, 16):
            mod = 10**precision
            rs = residue_towers(a, 9, mod)
            for h in range(10):
                check(rs[h] == tower_mod_25_euler(a, h, mod),
                      f'Euler cross-check: {a}, {h}, {precision}')
    counts['independent_euler_chain_cross_checks'] = checks - before

    before = checks
    # Direct second towers; no reduction of exponents is needed for this test.
    for a in range(3, 200, 2):
        exact = pow(a, a)
        for B in range(4, 50, 2):
            if a == B-1:
                rs = residue_towers(a, 2, B**5)
                check(rs[2] == exact % (B**5), 'direct second tower')
    check(pow(3, 27) == 7625597484987, 'direct third tower')
    check(pow(3, 27, 64) == 59 and 27 % 64 == 27, 'OEIS counterexample')
    # The hand-checkable certificate printed in the article.
    check(pow(3, 8, 64) == 33 and pow(3, 16, 64) == 1, 'hand certificate steps')
    check((1*33*9*3) % 64 == 59, 'hand certificate product')
    try:
        residue_towers(2, 4, 7)
    except ValueError:
        check(True, 'guard rejected invalid exponent reduction')
    else:
        check(False, 'guard failed')
    naive, mod = 1, 7
    for _ in range(4):
        naive = pow(2, naive, mod)
    check(naive == 4 and pow(2, 16, 7) == 2,
          'unsupported residue iteration actually fails')
    # T_4(2)=65536; use its residue directly as an additional check.
    check(65536 % 7 == 2, 'direct T4 base 2')
    # Exponents may not be reduced modulo the output modulus in general.
    check(pow(2, 3, 3) != pow(2, 6, 3), 'exponent reduction is not generic')
    counts['direct_towers_and_guard'] = checks - before

    before = checks
    for B in range(4, 102, 2):
        a = B - 1
        mod = B**14
        rs = residue_towers(a, 13, mod)
        for h in range(13):
            check((rs[h+1] - rs[h]) % B**(h+1) == (-2*B**h) % B**(h+1),
                  f'sharp leading digit: {B}, {h}')
        for m in range(1, 13):
            fixed = stable_radix_residue(B, m)
            check(fixed == rs[m] % B**m, f'lift: {B}, {m}')
            check(pow(a, fixed, B**m) == fixed, f'fixed point: {B}, {m}')
            check(first_permanent_height(a, B, m) == m,
                  f'exact height: {B}, {m}')
            if m >= 2:
                check((rs[m] // B) % B == B-2, f'penultimate digit: {B}, {m}')
                check(rs[m] % B**2 == (B*B - B - 1) % B**2,
                      f'two-digit residue: {B}, {m}')
    counts['sharp_radix_congruences_and_digit_lifting'] = checks - before

    before = checks
    for B in (4, 6, 8):
        for m in range(1, 4):
            modulus = B**m
            target = stable_radix_residue(B, m)
            fixed_points = []
            for start in range(modulus):
                x = start
                if pow(B-1, start, modulus) == start:
                    fixed_points.append(start)
                for _ in range(m+1):
                    x = pow(B-1, x, modulus)
                check(x == target, f'all starts converge: {B}, {m}, {start}')
            check(fixed_points == [target], f'unique fixed point: {B}, {m}')
    counts['exhaustive_small_fixed_point_dynamics'] = checks - before

    before = checks
    for a in range(3, 100, 2):
        for radix in range(2, 51):
            try:
                lines = local_lines(a, radix)
            except ValueError:
                continue
            max_h = 8
            precision = max((alpha+max_h*beta+power-1)//power + 2
                            for alpha, beta, power in lines.values())
            modulus = 2*radix**precision
            rs = residue_towers(a, max_h+1, modulus)
            for h in range(max_h+1):
                difference = (rs[h+1]-rs[h]) % modulus
                for p, (alpha, beta, power) in lines.items():
                    check(valuation(difference, p) == alpha+h*beta,
                          f'general radix local line: {a}, {radix}, {h}, {p}')
                observed = min(valuation(difference, p)//power
                               for p, (_, _, power) in lines.items())
                check(observed == stable_digits_radix(a, radix, h),
                      f'general radix stable count: {a}, {radix}, {h}')
    values = [stable_digits_radix(3, 16, h) for h in range(21)]
    check(values == [(1+2*h)//4 for h in range(21)],
          'nonconstant eventual periodic radix-16 speed')
    counts['general_radix_affine_valuation_checks'] = checks - before

    before = checks
    profiles = []
    for p in primes_below(100000):
        if p % 10 != 9:
            continue
        profile = DecimalProfile.for_base(p)
        if profile.onset > 2:
            row = asdict(profile)
            row.update(eventual_speed=profile.eventual_speed, onset=profile.onset)
            profiles.append(row)
    check(profiles[0]['a'] == 2749, 'least prime counterexample')
    check(len(profiles) == 23, 'prime counterexamples below 100000')
    write_csv('prime_counterexamples_below_100000.csv', profiles)
    p = 2749
    remainders = [(q, p % q) for q in primes_below(isqrt(p)+1)]
    check(all(r != 0 for q, r in remainders), '2749 trial certificate')
    check(is_prime_trial(229), '229 is prime')
    check(pow(2, 2748, 2749) == 1, 'Pocklington Fermat condition')
    check(pow(2, 12, 2749) == 1347 and gcd(1346, 2749) == 1,
          'Pocklington gcd condition')
    check(is_prime_trial(16249), '16249 exact primality')
    (DATA/'2749_primality_certificate.json').write_text(json.dumps({
        'number': p, 'method': 'trial division by every prime <= floor(sqrt(n))',
        'sqrt_floor': isqrt(p),
        'divisor_remainder_pairs': remainders,
        'optional_pocklington': {'q': 229, 'base': 2,
            'pow_2_2748_mod_n': 1, 'pow_2_12_mod_n': 1347,
            'gcd_1346_n': 1}}, indent=2)+'\n', encoding='utf-8')
    counts['prime_counterexample_certificates'] = checks - before

    before = checks
    crt_rows = []
    for s in range(2, 13):
        r, mod = prime_delay_progression(s)
        for j in range(20):
            profile = DecimalProfile.for_base(r + j*mod)
            check((profile.s, profile.t, profile.e, profile.onset) ==
                  (s, 1, s+1, s+1), f'CRT valuations: {s}, {j}')
        # Trial division is practical for the small demonstration primes only.
        candidate = r
        if s <= 6:
            while not is_prime_trial(candidate):
                candidate += mod
        crt_rows.append(dict(s=s, onset=s+1, residue=r, modulus=mod,
                             certified_example_prime=candidate if s<=6 else ''))
    write_csv('arbitrarily_delayed_prime_progressions.csv', crt_rows)
    counts['crt_exact_valuation_checks'] = checks - before

    before = checks
    # Formula-derived integer counts, not claims about a prime density.
    limit, tails = 1_000_000, {k: 0 for k in range(2, 7)}
    for a in range(9, limit, 10):
        onset = DecimalProfile.for_base(a).onset
        for k in tails:
            tails[k] += onset > k
    density_rows = []
    for k, count in tails.items():
        density = delay_tail_density(k)
        density_rows.append(dict(k=k, integer_sample_size=limit//10,
            sample_count_H_greater_k=count,
            exact_density_numerator=density.numerator,
            exact_density_denominator=density.denominator))
    check(delay_tail_density(2).numerator == 4 and
          delay_tail_density(2).denominator == 441, 'density rational')
    write_csv('integer_delay_density_counts.csv', density_rows)
    counts['density_constant_check'] = checks - before

    # Auditable exact decimal traces at sufficient precision.
    traces = []
    for a in (499, 749, 2749, 16249, 781249):
        profile = DecimalProfile.for_base(a)
        precision, height = 100, 9
        modulus = 10**precision
        rs = residue_towers(a, height+1, modulus)
        for h in range(height+1):
            d = (rs[h+1]-rs[h]) % modulus
            traces.append(dict(a=a, h=h, v2_D=valuation(d, 2),
                v5_D=valuation(d, 5), C=profile.stable_digits(h),
                V='' if h == 0 else profile.speed(h),
                T_h_mod_10_16=str(rs[h] % 10**16).zfill(16),
                D_h_mod_10_16=str(d % 10**16).zfill(16)))
    write_csv('decimal_tower_traces.csv', traces)
    return profiles


def diagonal_suite() -> None:
    """All checks inherited from the one-digit-per-height investigation."""
    # Level one: check the independent oracle against actual, manageable integers.
    for a in range(3, 31):
        exacts = [1, a, a**a]
        if a <= 5:
            exacts.append(a ** (a**a))
        for h, exact in enumerate(exacts):
            for modulus in range(1, 101):
                dcheck('oracle_against_exact_integers',
                       oracle(a, h, modulus) == exact % modulus)
    # The capped totient lift is valid for nonunit bases too.
    for modulus in range(2, 60):
        period = phi(modulus)
        for base in range(2, 12):
            for extra in (0, 1, 3):
                E = period + extra
                dcheck('capped_lift_nonunit',
                       pow(base, E, modulus) ==
                       pow(base, (E % period) + period, modulus))

    rows = []
    for B in range(4, 202, 2):
        a = B - 1
        for h in range(0, 11):
            for gap in range(1, 4):
                M = B**(h + 1)
                delta = (oracle(a, h + gap, M) - oracle(a, h, M)) % M
                dcheck('universal_leading_difference', delta == (B - 2) * B**h)
                dcheck('optimized_difference', difference_residue(B, h, gap) == B - 2)
                for q in factor_trial(B):
                    v = predicted_prime_distance(B, h, q)
                    P = q**(v + 1)
                    d = (oracle(a, h + gap, P) - oracle(a, h, P)) % P
                    dcheck('exact_prime_valuations', d != 0 and valuation(d, q) == v)
            for m in range(1, 11):
                dcheck('optimized_tower_against_oracle',
                       tetration_mod(B, h, m) == oracle(a, h, B**m))
        for m in range(1, 11):
            r = stable_radix_residue(B, m)
            dcheck('fixed_point', pow(a, r, B**m) == r)
            for j in (0, 1, 7):
                k = r + j * B**m
                dcheck('fixed_point_representatives', pow(a, k, B**m) == k % B**m)
            dcheck('compatibility',
                   m == 1 or r % B**(m-1) == stable_radix_residue(B, m-1))
            if m >= 2:
                dcheck('second_digit', (oracle(a, m, B*B) // B) == B - 2)
                dcheck('third_conjecture_false',
                       oracle(a, m, B**(m+1)) != stable_radix_residue(B, m+1))
            if B <= 20:
                rows.append({'n': B//2, 'B': B, 'height': m, 'residue': r,
                             'previous_height_mod_B_to_m': oracle(a, m-1, B**m),
                             'new_digit': r // B**(m-1)})
    write_csv('oeis_a324017_values.csv', rows)

    # Unique finite fixed points, exhaustively checking all representatives.
    for B in range(4, 26, 2):
        for m in range(1, 4):
            M = B**m
            solutions = [x for x in range(M) if pow(B-1, x, M) == x]
            dcheck('exhaustive_unique_fixed_points',
                   solutions == [stable_radix_residue(B, m)])
            diagonal_counts['fixed_point_candidates_examined'] = (
                diagonal_counts.get('fixed_point_candidates_examined', 0) + M)

    # Independently known small hyperoperations and capped threshold logic.
    for a in range(3, 10):
        for rank, n, value in [(1,0,1),(1,1,a),(1,2,a*a),(1,3,a**3),
                               (2,0,1),(2,1,a),(2,2,a**a),
                               (3,0,1),(3,1,a),(4,1,a)]:
            for cap in range(1, 301):
                dcheck('capped_hyper_exact',
                       capped_hyper(a, rank, n, cap) == min(value, cap))
    for B in range(4, 22, 2):
        a = B - 1
        for m in range(1, 21):
            for n in range(0, 5):
                dcheck('rank_two', knuth_mod(B, 2, n, m) == oracle(a, n, B**m))
            dcheck('rank_three_at_two', knuth_mod(B, 3, 2, m) == oracle(a, a, B**m))
            # U_3(a,3)=T[U_3(a,2)], and U_3(a,2)=T[a] is far above 20.
            dcheck('rank_three_at_three',
                   knuth_mod(B, 3, 3, m) == stable_radix_residue(B, m))
            dcheck('enormous_rank',
                   knuth_mod(B, 10**100, 2, m) == stable_radix_residue(B, m))
    # Base 2 is excluded from the capped hyperoperation helper.
    try:
        capped_hyper(2, 3, 2, 10)
    except ValueError:
        dcheck('base_two_excluded', True)
    else:
        dcheck('base_two_excluded', False)
    dcheck('base_two_is_flat', all(capped_hyper(3, r, 2, 10**9) >= 27
                                   for r in range(2, 5)))

    # Exact rational-series check of the sign-sensitive local Lambert formula.
    lambert_rows = []
    for B in [4, 6, 8, 10, 12, 14, 18, 20, 30, 42]:
        for q in factor_trial(B):
            for K in [3, 6, 9]:
                r = local_lambert_residue(B, q, K)
                dcheck('local_lambert_series', r == oracle(B-1, K+2, q**K))
                lambert_rows.append({'B': B, 'q': q, 'precision': K, 'residue': r})
    write_csv('local_lambert.csv', lambert_rows)

    witness = {'B': 4, 'n': 2, 'm': 2, 'modulus': 64, 'T_m': 27,
               'T_m_plus_1': 3**27, 'T_m_mod_modulus': 27,
               'T_m_plus_1_mod_modulus': 59,
               'difference': 3**27 - 27,
               'v2_difference': valuation(3**27 - 27, 2),
               'hand_check': '3^8=33, 3^16=1, 3^27=1*33*9*3=59 (mod 64)',
               'statement': 'A324017 comment C3 fails at the smallest allowed pair'}
    (DATA/'oeis_a324017_counterexample.json').write_text(
        json.dumps(witness, indent=2)+'\n', encoding='utf-8')


def main() -> None:
    profiles = decimal_suite()
    decimal_total = sum(counts.values())
    diagonal_suite()
    candidates = diagonal_counts.pop('fixed_point_candidates_examined', 0)
    diagonal_total = sum(diagonal_counts.values())

    report = {'status': 'PASS', 'python_version': platform.python_version(),
        'exact_assertions': checks,
        'note_on_totals': ('The two suites overlap on even radices 4..100 at '
                           'heights 0..10. The subtotals are counts of assertions '
                           'executed, not of distinct mathematical facts, and are '
                           'reported separately for that reason.'),
        'decimal_suite': {'assertions': decimal_total, 'test_groups': counts},
        'diagonal_suite': {'assertions': diagonal_total,
                           'test_groups': diagonal_counts,
                           'fixed_point_candidates_examined': candidates,
                           'parameters': {'even_B_min': 4, 'even_B_max': 200,
                               'height_min': 0, 'height_max': 10,
                               'gaps': [1, 2, 3], 'tower_precision_max': 10,
                               'unique_fixed_points_B_max': 24}},
        'decimal_bases_checked': 2000,
        'prime_counterexamples_below_100000': len(profiles),
        'smallest_prime_counterexample': profiles[0],
        'sample_density_population': 'integers < 1000000 ending in 9',
        'limitations': ['Finite checks are not substitutes for the proofs.',
            'Dirichlet infinitude is a theorem used in the article, not computed.',
            'Novelty and literature completeness are not mechanically certified.',
            'No formal proof assistant verification has been performed.',
            'The two suites overlap; their subtotals must not be added.']}
    (DATA/'verification_report.json').write_text(json.dumps(report, indent=2)+'\n',
                                               encoding='utf-8')
    lines = ["EXACT VERIFICATION: PASS", f"Python {platform.python_version()}",
             f"Assertions passed (merged suite): {checks}", '',
             f"Decimal suite subtotal: {decimal_total}"]
    lines += [f'  {name}: {count}' for name, count in counts.items()]
    lines += ['', f"Diagonal suite subtotal: {diagonal_total}"]
    lines += [f'  {name}: {count}' for name, count in diagonal_counts.items()]
    lines += ['', f'Fixed-point residue classes examined (not assertions): {candidates}',
              'The two suites overlap on even radices 4..100 at heights 0..10;',
              'their subtotals are assertions executed, not distinct facts.',
              '', 'Least prime counterexample: 2749',
              'Prime counterexamples below 100000: 23',
              'Smallest A324017 C3 counterexample: 3^^2=27, 3^^3=59 mod 64',
              'All reported primality certificates are deterministic.',
              'All arithmetic tests use integers; no floating point.',
              'See article for proofs and precise limitations.']
    output = '\n'.join(lines) + '\n'
    (ROOT/'verification.txt').write_text(output, encoding='utf-8')
    print(output)


if __name__ == '__main__':
    main()
