import argparse
import hashlib
import json
from math import comb, gcd
from pathlib import Path


PINS = {
    'gamma83_quartic_complement.md': '135edefc6b53e0d55350f74a7fe1186eda3c59046f0098128bbef4796fcd6d9c',
    'gamma83_composite_complement_certificate.md': '70d5311c481545f0dc1655dff54040b7badc3802a6e621d284c39c5751a8c255',
    'gamma83_native_next.md': '6cf4719fab43ad8873e372a5be0108192cc0a90cadccd84fe58d1e7a76cdaf74',
    'complete83_gamma_small_prime_digit_rules.md': 'b7248efe5f292bd5dcbf093ccd9f664d663b2eb23c022974b1a9f64b537a4f8e',
    'gamma_parity_padding_scout.md': '0def681763b4039a7074bd13f33def941c2b215db8f90b4194400e84ffc4080c',
    'complete83_gamma_native_finite_prime_avoidance.md': '93aa3b61dcd03f7ce65acca9619f90c29710235ec2438cb4dd14000d8bdb8a96',
    'complete83_independent_gamma_scout.json': 'ed570bc9e96d59e88ec6b6c1302ac177eb6704cfcd85fe39a3346798e89f5e20',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def base_seven(n):
    out = []
    while n:
        out.append(n % 7)
        n //= 7
    return out or [0]


def evidence(root):
    dependencies = []
    for name, expected in PINS.items():
        raw = (root / name).read_bytes()
        actual = hashlib.sha256(raw).hexdigest()
        require(actual == expected, 'dependency ' + name)
        dependencies.append({'name': name, 'sha256': actual, 'bytes': len(raw)})
    units = [f for f in range(30) if gcd(f, 30) == 1]
    require(units == [1, 7, 11, 13, 17, 19, 23, 29], 'exponents')
    tests31 = {str(e): pow(22, e, 31) for e in [30, 15, 10, 6]}
    require(tests31 == {'30': 1, '15': 30, '10': 5, '6': 8}, 'order31')
    ternary = []
    for p in [1, 2]:
        if (p+1)*(p*p+1) % 3 == 0:
            require(p == 2, 'quartic divisor forces p=-1')
            for f in [1, 3, 5]:
                require(pow(p, f, 3) == 2, 'odd power contradicts H/3=1')
                ternary.append({'p_mod3': p, 'P_mod3': 1, 'f_mod6': f, 'complement_power_mod3': 2})
    root_sets = {0: [6], 1: [], 2: [2], 3: [], 4: [3], 5: [], 6: [4, 5]}
    table = []
    cases = 0
    for k in range(7):
        roots = [p for p in range(7) if p * (k * p - k + 1) % 7 == 6]
        require(roots == root_sets[k], 'root table')
        for f in units:
            actual = [p for p in range(7) if pow(p * (k * p - k + 1) % 7, f, 7) == 6]
            require(actual == roots, 'exponent permutation')
            cases += 7
        table.append({'k_mod7': k, 'discriminant_mod7': (k*k-6*k+1) % 7, 'p_roots': roots})
    carry_table = []
    for f in [1, 5]:
        rows = []
        for p in [1, 2, 4, 5, 6]:
            u = p * (10*p-9) % 7
            require(u != 0, 'prime-unit residues')
            C = (3 * pow(u, f, 7) - 4) * pow(2, -1, 7) % 7
            rows.append({'p_mod7': p, 'u_mod7': u, 'C_mod7': C})
        require(sorted({r['C_mod7'] for r in rows}) == ([1, 2, 3] if f == 1 else [3, 4, 6]), 'carry-unit table')
        carry_table.append({'f_mod6': f, 'rows': rows})
    digit_counts = [0] * 7
    for r in range(2048):
        digits = base_seven(r)
        central = comb(2*r, r) % 7
        if any(d >= 4 for d in digits):
            require(central == 0, 'carry zero')
        else:
            wanted = (-1)**sum(d in [2, 3] for d in digits) * 2**digits.count(1) % 7
            require(central == wanted and central != 0, 'Lucas unit')
        digit_counts[central] += 1
    native_formula_checks = []
    for R in range(15, 1000, 60):
        r = (R-1)//2
        C = comb(2*r, r) % 7
        x = pow(2, R, 7)
        tail = sum(comb(2*r, r+j) * pow(x, j, 7) for j in range(r+1)) % 7
        H = (2*(x+1)*tail+3) % 7
        require(x == 1 and H == (4+2*C) % 7, 'native formula')
        native_formula_checks.append({'R': R, 'C_mod7': C, 'H_mod7': H})
    return {
        'status': 'PASS',
        'scope': 'Fresh finite-field and exact binomial formula evidence only. No compiler history, native Pell tuple, source array or predecessor program executed.',
        'helper_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'dependencies': dependencies,
        'order31_tests': tests31,
        'ternary_quartic_obstruction': ternary,
        'exponent_classes': units,
        'general_k_table': table,
        'general_k_exponent_cases': cases,
        'k10_central_unit_table': carry_table,
        'central_binomial_digit_checks': 2048,
        'central_binomial_residue_counts': digit_counts,
        'native_formula_only_checks': native_formula_checks,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', required=True, type=Path)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument('--output', type=Path)
    modes.add_argument('--expect', type=Path)
    args = parser.parse_args()
    value = evidence(args.root)
    encoded = json.dumps(value, sort_keys=True, indent=2) + '\n'
    if args.output:
        with args.output.open('x') as handle:
            handle.write(encoded)
    else:
        require(args.expect.read_text() == encoded, 'exact receipt mismatch')
    print(json.dumps({'status': 'PASS', 'general_k_exponent_cases': value['general_k_exponent_cases'], 'digit_checks': value['central_binomial_digit_checks'], 'formula_cases': len(value['native_formula_only_checks'])}, sort_keys=True))
