"""Fresh scalar checks only; never reads or evaluates an SLP source array."""
import argparse
import hashlib
import json
from math import comb
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def valuation(n, p):
    require(n > 0, 'valuation needs a positive integer')
    answer = 0
    while n % p == 0:
        n //= p
        answer += 1
    return answer


def evidence():
    parity_count = 0
    congruence_count = 0
    for parameter in range(2, 18):
        previous, current = 0, 1
        discriminant = parameter * parameter - 1
        for index in range(66):
            if index == 0:
                coefficient = previous
            else:
                coefficient = current
                previous, current = current, 2 * parameter * current - previous
            require(coefficient % 2 == index % 2, 'Pell coefficient parity')
            parity_count += 1
            residue = index if index % 2 else parameter * index
            require((coefficient - residue) % discriminant == 0, 'input index residue')
            congruence_count += 1

    outer_count = 0
    for radix in (32, 64, 128):
        for repunit in range(1, 25):
            scale = (radix - 1) * repunit + 1
            # Only these parities are used, not an assertion of valid compiler masks.
            mask_c = 2
            mask_f_source = radix + 3
            for field in range(1, 5):
                for marker in range(1, 5):
                    complement = scale - field
                    packed_index = (scale * complement - marker) * (scale * scale - 1)
                    packed_index += (mask_c + scale * mask_f_source) * repunit
                    if scale % 2:
                        require(packed_index % 2 == 0, 'odd scale forces even index')
                    else:
                        require(repunit % 2 == 1, 'even scale forces odd repunit')
                        require(packed_index % 2 == marker % 2, 'even scale index parity')
                    outer_count += 1

    scale = 54
    index = 1223
    half_index = (index - 1) // 2
    modulus = 32 * 3**12
    # Accumulate the upper half from its central coefficient outwards.
    # Reducing the numerator modulo twice the desired modulus permits exact halving.
    numerator_modulus = 2 * modulus
    base_residue = pow(2, index, numerator_modulus)
    coefficient = comb(2 * half_index, half_index)
    power_residue = 1
    numerator_residue = 0
    for offset in range(half_index + 1):
        numerator_residue = (numerator_residue + coefficient * power_residue) % numerator_modulus
        if offset < half_index:
            numerator = coefficient * (half_index - offset)
            denominator = half_index + offset + 1
            require(numerator % denominator == 0, 'exact adjacent binomial coefficient')
            coefficient = numerator // denominator
            power_residue = power_residue * base_residue % numerator_modulus
    require(numerator_residue % 2 == 0, 'even half-binomial numerator')
    y_residue = numerator_residue // 2
    require(y_residue % 3**12 == 452709, 'independent 3-adic residue')
    require(y_residue % 32 == 16, 'exact 2-adic residue')
    require(y_residue % scale**3 == 0, 'even nondyadic cubic scale')
    require(pow(2, index, scale) == 14, 'missing X divisibility')
    central_v2 = valuation(comb(2 * half_index, half_index), 2)
    require(central_v2 == half_index.bit_count() == 5, 'central-binomial valuation')
    require(index.bit_count() == 6, 'index population')
    require(index - 1 > central_v2 - 1, 'noncentral terms have higher valuation')
    require(3 * scale + 1 <= index < scale**4, 'weak inherited kernel range')
    require(index < (2 * scale - 1) * (scale**2 - 1), 'outside actual outer lower range')
    return {
        'scope': 'Fresh handwritten scalar identities and one kernel example; no source-array evaluation or full compiler zero.',
        'pell_parity_checks': parity_count,
        'input_residue_checks': congruence_count,
        'outer_parity_checks': outer_count,
        'kernel': {
            'q': scale, 'R': index, 'r': half_index,
            'modulus': modulus, 'Y_mod_modulus': y_residue,
            'Y_mod_3_power_12': y_residue % 3**12,
            'Y_mod_32': y_residue % 32,
            'v2_Y': 4, 'v3_Y': 9,
            'Y_mod_q_cubed': y_residue % scale**3,
            'X_mod_q': pow(2, index, scale),
            'q_even': True, 'q_dyadic': False,
            'valid_actual_compiler_zero': False,
            'actual_outer_lower_bound_fails': True,
            'minimal_B_32_repunit_congruence_fails': (scale - 1) % 31 != 0,
        },
        'helper_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }


parser = argparse.ArgumentParser()
parser.add_argument('--output', type=Path)
parser.add_argument('--expect', type=Path)
args = parser.parse_args()
result = evidence()
if args.expect is not None:
    expected = json.loads(args.expect.read_text())
    require(json.dumps(result, sort_keys=True) == json.dumps(expected, sort_keys=True), 'receipt mismatch')
if args.output is not None:
    require(not args.output.exists(), 'refuse to replace an existing receipt')
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
print(json.dumps(result, sort_keys=True))
