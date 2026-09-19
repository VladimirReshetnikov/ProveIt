"""Run exact checks, generate CSV/JSON data, and print a reproducibility report.

Usage: python code/verify.py
No dependencies beyond Python 3.10+ standard library. Finite checks complement,
but do not replace, the article's proofs. No test constructs a high power tower.
"""
from __future__ import annotations
import csv
import json
import platform
from dataclasses import asdict
from pathlib import Path
from math import gcd, isqrt
from tetration import (DecimalProfile, valuation, residue_towers,
    tower_mod_25_euler, primes_below, is_prime_trial, prime_delay_progression,
    delay_tail_density, stable_radix_residue, local_lines,
    stable_digits_radix, first_permanent_height)

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'data'
DATA.mkdir(exist_ok=True)
checks = 0
counts: dict[str, int] = {}


def check(condition: bool, message: str) -> None:
    global checks
    checks += 1
    if not condition:
        raise AssertionError(message)


def write_csv(name: str, rows: list[dict]) -> None:
    if not rows:
        raise ValueError('refusing to write empty CSV')
    with (DATA/name).open('w', newline='', encoding='utf-8') as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def main() -> None:
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
    counts['direct_towers_and_guard'] = checks - before

    before = checks
    oeis = []
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
            if B <= 20 and m <= 8:
                oeis.append(dict(n=B//2, B=B, height=m, residue=fixed))
    write_csv('oeis_a324017_values.csv', oeis)
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

    report = {'status': 'PASS', 'python_version': platform.python_version(),
        'exact_assertions': checks, 'test_groups': counts,
        'decimal_bases_checked': 2000,
        'prime_counterexamples_below_100000': len(profiles),
        'smallest_prime_counterexample': profiles[0],
        'sample_density_population': 'integers < 1000000 ending in 9',
        'limitations': ['Finite checks are not substitutes for the proofs.',
            'Dirichlet infinitude is a theorem used in the article, not computed.',
            'Novelty and literature completeness are not mechanically certified.',
            'No formal proof assistant verification has been performed.']}
    (DATA/'verification_report.json').write_text(json.dumps(report, indent=2)+'\n',
                                               encoding='utf-8')
    lines = ["EXACT VERIFICATION: PASS", f"Python {platform.python_version()}",
             f"Assertions passed: {checks}", '']
    lines += [f'{name}: {count}' for name, count in counts.items()]
    lines += ['', 'Least prime counterexample: 2749',
              'Prime counterexamples below 100000: 23',
              'All reported primality certificates are deterministic.',
              'All arithmetic tests use integers; no floating point.',
              'See article for proofs and precise limitations.']
    output = '\n'.join(lines) + '\n'
    (ROOT/'verification.txt').write_text(output, encoding='utf-8')
    print(output)


if __name__ == '__main__':
    main()
