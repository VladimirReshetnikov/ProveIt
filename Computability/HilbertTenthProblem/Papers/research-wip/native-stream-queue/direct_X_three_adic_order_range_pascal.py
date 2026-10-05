#!/usr/bin/env python3
"""Original finite modular certificates; no scientific predecessor is loaded."""
from hashlib import sha256
from math import gcd, isqrt, lcm, prod
from pathlib import Path
import json

HERE = Path(__file__)
BASE = Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
SOURCES = [
    ('direct_X_varying_three_adic_offset_bound_pascal.md', '926f648494c4bac101901f4dd1552402f94a44c39efb80ee4df3c30466254394', None),
    ('direct_X_canonical_three_adic_family_pascal.md', 'c18f09aa7fd0b4eb89bbdbbca2a5b5ad3aed3f5d559e6afb02034cb9bb62f7cc', None),
    ('complete75_half_binomial_compiler.md', '68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117', (1, 70)),
    ('direct_X_authentic_outer_root.md', '35d5d5080a615583779f31b1985768045455ab6cbbfc394dac4b93cc2713a617', (1, 49)),
]

def ensure(value, why):
    if not value:
        raise RuntimeError(why)

def digest(raw):
    return sha256(raw).hexdigest()

def main():
    dependency_pins = []
    for name, pin, interval in SOURCES:
        path = BASE / name
        raw = path.read_bytes()
        ensure(digest(raw) == pin, 'dependency: ' + name)
        lines = raw.splitlines(keepends=True)
        a, b = interval or (1, len(lines))
        dependency_pins.append({
            'path': str(path), 'sha256': pin, 'bytes': len(raw),
            'read_lines': [a, b], 'span_sha256': digest(b''.join(lines[a-1:b])),
        })
    declarations = [
        {'modulus': 33554431, 'two_exponent': 25, 'three_order': 450,
         'order_factorization': {2: 1, 3: 2, 5: 2},
         'expected_proper_residues': {2: 14069411, 3: 6967995, 5: 5738380}},
        {'modulus': 269089806001, 'two_exponent': 125, 'three_order': 44848301000,
         'order_factorization': {2: 3, 5: 3, 41: 1, 107: 1, 10223: 1},
         'expected_proper_residues': {2: 269089806000, 5: 164136984823,
                                     41: 47900848917, 107: 38645547593,
                                     10223: 207448671296}},
    ]
    all_factors = sorted(set().union(*(set(c['order_factorization']) for c in declarations)))
    primality_records = []
    for p in all_factors:
        tests = [[n, p % n] for n in range(2, isqrt(p) + 1)]
        ensure(p >= 2 and all(r != 0 for _, r in tests), 'prime factor trial division')
        primality_records.append({'prime': p, 'square_root_floor': isqrt(p), 'complete_trial_remainders': tests})
    certificates = []
    for declaration in declarations:
        modulus = declaration['modulus']
        h = declaration['two_exponent']
        order = declaration['three_order']
        factorization = declaration['order_factorization']
        ensure(prod(p**a for p, a in factorization.items()) == order, 'complete factorization')
        ensure(gcd(3, modulus) == 1, 'unit')
        r2, r3 = pow(2, h, modulus), pow(3, order, modulus)
        ensure(r2 == r3 == 1, 'modular identity')
        proper_tests = []
        for prime, expected in declaration['expected_proper_residues'].items():
            ensure(order % prime == 0, 'prime divisor of order')
            residue = pow(3, order // prime, modulus)
            ensure(residue == expected and residue != 1, 'proper-divisor test')
            proper_tests.append({'prime': prime, 'exponent': order // prime, 'residue': residue})
        ensure(set(factorization) == set(declaration['expected_proper_residues']), 'complete proper-divisor coverage')
        certificates.append({
            'modulus': modulus, 'two_exponent': h, 'two_power_residue': r2,
            'three_order': order, 'order_power_residue': r3,
            'order_factorization': factorization, 'proper_divisor_tests': proper_tests,
            'modulus_primality_required': False,
        })
    combined = lcm(*(c['three_order'] for c in certificates))
    ensure(combined == 403634709000, 'combined order divisor')
    ensure(2**11 < 3**7, 'exponent comparison')
    dmax = (11*combined - 11) // 28
    ensure(dmax == 158570778535, 'exact d threshold')
    d16, d17 = 5**16, 5**17
    ensure(11*450 >= 11+28*25, 'd25 exclusion')
    ensure(d16 <= dmax < d17, 'covered power-of-five range')
    margin = 11*combined - 11 - 28*d16
    ensure(margin == 167520861489, 'strict endpoint margin')
    ensure(2*combined < 3*d17, 'partial-test limitation')
    note = HERE.with_suffix('.md')
    result = {
        'status': 'PASS: two exact order certificates and finite range proof controls',
        'author_note': {'path': str(note), 'sha256': digest(note.read_bytes())},
        'helper_sha256': digest(HERE.read_bytes()), 'dependencies': dependency_pins,
        'certificates': certificates, 'order_prime_certificates': primality_records,
        'range': {'combined_order_divisor': combined, 'criterion': '11*O >= 11+28*d',
                  'maximum_d_for_combined_criterion': dmax,
                  'authentic_powers_of_five_excluded': [2, 16],
                  'd16': d16, 'endpoint_margin': margin},
        'retained_partial_boundary': {'d': d17, 'k': combined,
                                     'twice_k': 2*combined, 'three_d': 3*d17,
                                     'full_repunit_asserted': False,
                                     'any_index_or_source_zero_asserted': False},
        'counts': {'moduli': 2, 'order_primes': len(all_factors),
                   'proper_divisor_tests': sum(len(c['proper_divisor_tests']) for c in certificates)},
        'scope': {'all_powers_of_five_excluded': False,
                  'scientific_code_is_new_before_freeze': True,
                  'predecessor_or_frozen_code_executed_or_imported': False,
                  'saved_source_arrays_evaluated_or_propagated': False,
                  'large_endpoint_radix_q_R_X_Y_or_native_tuple_materialized': False},
    }
    print(json.dumps(result, sort_keys=True, indent=2))

if __name__ == '__main__':
    main()
