#!/usr/bin/env python3
"""Fresh arithmetic checks of a symbolic actual-compiler outer-family proof.

Synthetic scalar cases below are NOT compiler instances. No predecessor
program/source DAG is executed, imported, reconstructed, or evaluated.
"""
import argparse
import hashlib
import json
from pathlib import Path

WIP = Path('Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
OLD = Path('Computability/HilbertTenthProblem/Papers/1980')
PINS = [
    (WIP / 'complete83_shared_projection_scout.json', 'dd9e105d295bf2fb3e3b0246234bb68cb78487ee919405bc052f2b67a9def34c', 'unchanged source identity'),
    (WIP / 'complete83_shared_projection_math.md', '1a9923b7202bef2e5a640b3b27c942423b9d9829d9fc6e7f4b55fa5c4d91053c', 'outer identities and uniform Pell completion'),
    (WIP / 'complete83_even_radix_boundary.md', 'eba3e2944154dd7ff28e5b20d5e32e8ee6a0138b515c8e5f3846979dadaaa8dc', 'even-radix four-term criterion and parametric completion'),
    (WIP / 'complete75_half_binomial_compiler.md', '68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117', 'Sections 1 and 4: actual fixed ports and coefficient bound'),
    (OLD / 'FIXED_RAW_UNIVERSAL_76_PROOF.md', '75a13b5fd0c44c3ec91366306fb5876a3ea2f867e464b84cebd46ca08d060f87', 'Section 1: powers of five, high monomial, L bound'),
    (OLD / 'FIXED_RAW_UNIVERSAL_78_PROOF.md', 'b28ddb9aec5225cda7dabc85fb952daf49de4041cf35910f62dabf3893749d39', 'Section 2: literal M0,Hfield,T1,T2 geometry'),
    (WIP / 'complete75_positive_transport_projection_obstruction.md', '6fed5e50d1f07039b0243c40ae712dc4e618b821d308327d36d05803d8a94ee8', 'Sections 1-4, context only: changed source and negative F mechanism'),
    (WIP / 'complete84_odd_prime_compiler_transfer.md', 'd308f5e2649ee31814f6c93060f4dd06a36df14f4f15749e984c8dd1880a88a2', 'Sections 1-3, context only: separate coefficient recipe not included'),
]


def require(value, message):
    if not value:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def valuation(number, prime):
    require(number != 0, 'zero valuation input')
    out = 0
    while number % prime == 0:
        number //= prime
        out += 1
    return out


def least_positive_crt_four(residue, modulus):
    # modulus is an odd power of five. Exhaust only the four lifts.
    for j in range(4):
        z = residue + j * modulus
        if z % 4 == 1:
            require(1 <= z <= 4 * modulus, 'CRT representative range')
            return z
    raise ValueError('CRT failed')


def outer_case(d, b, n, coefficient, mask):
    require(n % 4 == 1 and d % 5 == 0, 'synthetic parameter domain')
    B = 1 << d
    D = d * n
    Q = 1 << D
    native_field_mask = 4
    shifted_field_mask = native_field_mask + B - 1
    repunit = (Q - 1) // (B - 1)
    shape = 'minus' if coefficient % 5 == 3 else 'plus'
    if shape == 'plus':
        q = Q * (Q + 1) // 2
        J = repunit * (Q // 2 + 1)
        T = n * (D - 1)
        factors = [Q + 1, Q - 1, Q // 2 + 1]
        small_periods = [2 * D, D, 2 * (D - 1)]
    else:
        q = Q * (2 * Q - 1)
        J = repunit * (2 * Q + 1)
        T = n * (D + 1)
        factors = [2 * Q - 1, Q - 1, 2 * Q + 1]
        small_periods = [D + 1, D, 2 * (D + 1)]
    require(q == (B - 1) * J + 1, 'repunit failure')
    require(q % 2 == 0 and q & (q - 1), 'radix not even non-dyadic')
    a0 = q * q * (q * q - 1) + (mask + q * shifted_field_mask) * J
    g0 = (1 + q * coefficient) * (q * q - 1)
    if shape == 'plus':
        require(g0 % 5 != 0, 'plus coefficient nonunit')
        modulus = d
        residue = ((a0 - b) * pow(g0, -1, modulus)) % modulus
    else:
        require(valuation(J, 5) == valuation(q * q - 1, 5) == valuation(g0, 5) == 1,
                'minus exact valuation failed')
        require(a0 % 5 == b % 5 == 0, 'minus target not divisible by five')
        modulus = d // 5
        residue = (((a0 - b) // 5) * pow(g0 // 5, -1, modulus)) % modulus
    z = least_positive_crt_four(residue, modulus)
    R = a0 - g0 * z
    require(R % (2 * d) == b % (2 * d), 'index congruence')
    require(R % 4 == 3 and z % 4 == 1, 'index parity')
    x = n + (((R - b) // (2 * d) - n) % T)
    u = 2 * d * x + b
    F = coefficient * z
    alpha = q - (coefficient + 2) * z - 2 * d * x
    require(alpha > q // 4, 'strict slack failed')
    require(n <= x < n + T and x <= n * (D + 2), 'input range')
    require(0 < u < 2 * q < R and 3 * q + 1 < R and R + 2 < q ** 4,
            'completion size range')
    period = 2 * d * T
    require((R - u) % period == 0, 'exponent period')
    for factor, subperiod in zip(factors, small_periods):
        require(pow(2, subperiod, factor) == 1 and period % subperiod == 0,
                'odd-factor period')
    modulus_x = q * (q - 1)
    require((pow(2, R, modulus_x) - pow(2, u, modulus_x)) % modulus_x == 0,
            'strong X divisibility')
    require(q - F - z - alpha - 2 * d * x == z, 'raw C definition')
    # This checks the residue sufficient for a positive integer quotient,
    # not the astronomically large quotient itself.
    require((coefficient * z - F) % (q - 1) == 0, 'transport residue')
    return {'synthetic_only': True, 'd': d, 'b': b, 'n': n,
            'K': str(coefficient), 'MC': mask, 'native_MF': native_field_mask,
            'shape': shape, 'z': z, 'x': x, 'u': u,
            'q_bits': q.bit_length(), 'R_bits': R.bit_length(),
            'alpha_bits': alpha.bit_length(), 'v2_q': valuation(q, 2),
            'outer_signature_sha256': digest(json.dumps([str(v) for v in [q, J, z, F, alpha, R, u]],
                                                       separators=(',', ':')).encode()),
            'cubed_binomial_scale_checked': False}


def finite_evidence():
    size_cases = 0
    for d in range(25, 1001):
        # Integer fourth powers eliminate all fractional exponent rounding.
        require((64 * d) ** 4 < (1 << (3 * d)), 'fixed K margin')
        require(24 * d * d < (1 << (2 * d)), 'input margin')
        size_cases += 1
    layout_cases = 0
    for tiles in range(1, 30):
        for extra in range(1, 20):
            M = 3 * tiles + extra
            H = 51 * M + 3 * tiles + 1
            minimum_bound = 213 * M + 4 * tiles + 4
            require(minimum_bound > 4 * H, 'layout quarter bound')
            layout_cases += 1
    cases = []
    for d, n in [(25, 1), (25, 5), (25, 9), (125, 1)]:
        B = 1 << d
        coefficients = [1, 2, 3, 4, 8, 13, B + 1, B + 7,
                        B * (1 << (d // 5)) + 1, B * (1 << (d // 5)) + 2]
        for coefficient in coefficients:
            for mask in [2, 6, 10]:
                cases.append(outer_case(d, 5, n, coefficient, mask))
    return {'size_inequality_integer_cases': size_cases, 'layout_inequality_cases': layout_cases,
            'synthetic_outer_cases': len(cases), 'cases': cases,
            'warning': 'No scalar case is asserted to be a compiled universal program; scale is not tested.'}


def build(root, companions):
    pins = []
    for relative, expected, scope in PINS:
        path = root / relative
        if not path.exists():
            path = companions / relative.name
        data = path.read_bytes()
        require(digest(data) == expected, f'pin mismatch: {relative}')
        pins.append({'logical_path': str(relative), 'sha256': expected,
                     'bytes': len(data), 'read_scope': scope})
    return {'schema': 'complete83_nondyadic_outer_family_v1',
            'source_sha256': digest(Path(__file__).read_bytes()),
            'proof_sha256': digest((companions / 'complete83_nondyadic_outer_family.md').read_bytes()),
            'dependencies': pins, 'finite_evidence': finite_evidence(),
            'scope': {'compiler_recipe': 'original powers-of-five modified75, exact fixed ports',
                      'predecessor_execution': False, 'source_dag_evaluation': False,
                      'complete_positive_zero_claim': False, 'rejected_input_claim': False,
                      'fixed_prescribed_input_claim': False,
                      'remaining_condition': 'C0+C1*X+C2*X^2+C3*X^3=0 mod 2*q^3'}}


def unique_pairs(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'duplicate JSON key')
        result[key] = value
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--companion-dir', type=Path, default=Path('/tmp'))
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument('--output', type=Path)
    modes.add_argument('--expect', type=Path)
    args = parser.parse_args()
    receipt = build(args.root, args.companion_dir)
    if args.output:
        with args.output.open('x') as stream:
            stream.write(json.dumps(receipt, sort_keys=True, indent=2) + '\n')
    else:
        old = json.loads(args.expect.read_text(), object_pairs_hook=unique_pairs)
        require(json.dumps(old, sort_keys=True) == json.dumps(receipt, sort_keys=True), 'receipt mismatch')
    print('PASS: exact outer family; cubed-binomial completion remains unproved')


if __name__ == '__main__':
    main()
