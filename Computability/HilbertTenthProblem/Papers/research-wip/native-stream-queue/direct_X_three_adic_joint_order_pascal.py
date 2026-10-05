#!/usr/bin/env python3
"""Fresh scalar order certificates and byte/span bindings; no source arrays."""
import argparse
import hashlib
import json
import math
from pathlib import Path

ROOT = Path('/home/codex/.codex/worktrees/2a71/Proofs')
BASE = ROOT / 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue'
STEM = Path('/tmp/direct_X_three_adic_joint_order_pascal')
MODULUS = 42535295865117307932921825928971026431
ORDER = 2576525686996852656333000
FACTORS = [(2, 3), (3, 2), (5, 3), (41, 2), (107, 1), (10223, 1), (184711, 1), (842887, 1)]
RESIDUES = {
    2: 30956704208697257411056507980356130152,
    3: 15658468161339686373973998107111488354,
    5: 10664710849360348179995350704375424989,
    41: 8264232980333680078538289627652816672,
    107: 10006089262660319110576718966247817960,
    10223: 21042106684190814350812957586723129037,
    184711: 16393777223232271084185805725897864898,
    842887: 5542338464860825349674650997828247544,
}
DEPENDENCIES = [
    ('direct_X_three_adic_order_range_pascal.md', 'd57209396a8baffd74782c6c8380f41be5bbcbbd360438b3819182f01a37a948', None),
    ('direct_X_varying_three_adic_offset_bound_pascal.md', '926f648494c4bac101901f4dd1552402f94a44c39efb80ee4df3c30466254394', None),
    ('direct_X_fixed_offset_repunit_divisor_root.md', '8e54b2963256a1a239e91a495f22c6c43c26d439c287f724b0e2679f96827717', None),
    ('direct_X_authentic_outer_root.md', '35d5d5080a615583779f31b1985768045455ab6cbbfc394dac4b93cc2713a617', None),
]

def require(condition, message):
    if not condition:
        raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def modular_power(base, exponent, modulus):
    result = 1
    residue = base % modulus
    while exponent:
        if exponent & 1:
            result = (result * residue) % modulus
        residue = (residue * residue) % modulus
        exponent //= 2
    return result

def authenticate(path, expected=None, spans=None):
    data = path.read_bytes()
    digest = sha(data)
    if expected is not None:
        require(digest == expected, 'dependency changed: ' + str(path))
    lines = data.splitlines(keepends=True)
    ranges = spans or [(1, len(lines))]
    return {
        'path': str(path), 'bytes': len(data), 'sha256': digest,
        'read_spans': [
            {'first': lo, 'last': hi, 'sha256': sha(b''.join(lines[lo-1:hi]))}
            for lo, hi in ranges
        ],
    }

def collect():
    require(MODULUS == (1 << 125) - 1, 'Mersenne modulus')
    require(math.prod(p ** a for p, a in FACTORS) == ORDER, 'order factorization')
    primes = []
    tests = []
    for p, exponent in FACTORS:
        bound = math.isqrt(p)
        divisors = [n for n in range(2, bound + 1) if p % n == 0]
        require(not divisors, 'nonprime order factor')
        primes.append({'prime': p, 'exponent': exponent, 'trial_last': bound, 'proper_divisors': divisors})
        power = modular_power(3, ORDER // p, MODULUS)
        require(power == pow(3, ORDER // p, MODULUS), 'independent power agreement')
        require(power == RESIDUES[p] and power != 1, 'proper order residue')
        tests.append({'prime': p, 'exponent': ORDER // p, 'residue': power})
    base2 = modular_power(2, 125, MODULUS)
    identity = modular_power(3, ORDER, MODULUS)
    require(base2 == 1 and identity == 1, 'order certificate identities')
    require(identity == pow(3, ORDER, MODULUS), 'full power agreement')
    threshold = (11 * ORDER - 11) // 28
    require(threshold == 1012206519891620686416535, 'threshold')
    d34, d35 = 5 ** 34, 5 ** 35
    require(11 * ORDER >= 11 + 28 * d34, 'covered endpoint')
    require(11 * ORDER < 11 + 28 * d35, 'next endpoint outside certificate')
    require(2 * ORDER < 3 * d35, 'next endpoint passes partial exponential bound')
    require(ORDER % 403634709000 == 0, 'extends old joint order')
    return {
        'schema': 'fresh-scalar-order-and-proof-bindings-v1',
        'author': authenticate(STEM.with_suffix('.md')),
        'helper': {'path': str(Path(__file__)), 'sha256': sha(Path(__file__).read_bytes())},
        'dependencies': [authenticate(BASE / name, expected, spans) for name, expected, spans in DEPENDENCIES],
        'certificate': {
            'modulus': MODULUS, 'modulus_definition': '2^125-1',
            'base2_residue': base2, 'order': ORDER, 'order_residue': identity,
            'prime_factor_tests': primes, 'proper_order_tests': tests,
            'modulus_primality_assumed': False,
        },
        'range': {
            'd_threshold': threshold, 'covered_n': [2, 34],
            'n2_basis': 'inherited full proof, d25 order450',
            'd34': d34, 'endpoint_margin': 11*ORDER-11-28*d34,
            'd35': d35, 'next_margin': 11*ORDER-11-28*d35,
            'partial_test_counterexample': {'d': d35, 'k': ORDER, 'two_k': 2*ORDER, 'three_d': 3*d35},
        },
        'proof_only': ['Jacobi parity k even, e odd, c odd', 'transfer of exact order to every d divisible by125'],
        'scope': {
            'new_scalar_code_only': True, 'saved_helper_executed_or_imported': False,
            'source_array_evaluation': False, 'compiler_fixture_constructed': False,
            'all_n_exclusion_claimed': False, 'repository_or_git_mutation': False,
            'exclusion_family': 'q=2^d*3^k, R=2*3^e-3 with repunit, J|R and authentic numerical window',
        },
    }

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    result = collect()
    Path(args.output).write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print('PASS: one exact full-modulus order certificate; eight proper tests; n<=34; n35 boundary')
