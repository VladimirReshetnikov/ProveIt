#!/usr/bin/env python3
"""Independent modular replay of the actual fixed T4/Jones instance.

Usage after integration:
  python3 code/verify_fixed_instance.py --package-root . \
      --generated nine --output verification/nine_fixed_instance.json

The package root supplies code/fixed_coefficients.py, coefficients/t4_windows.json,
base/normalized_quartic32.json and base/index_bound_s.json. The generated
directory supplies this task's constants and literal binary DAG files.
No giant fixed integer is materialized. No solvability assertion is tested.
"""
from __future__ import annotations

import argparse
from hashlib import sha256
import importlib.util
from itertools import combinations_with_replacement
import json
from math import factorial, isqrt
from pathlib import Path
from random import Random

import nine_compressor as nc


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def record_polynomial(records):
    out = {}
    for r in records:
        key = tuple(r['powers'])
        require(key not in out, 'Duplicate sparse monomial')
        if r['coefficient']:
            out[key] = r['coefficient']
    return out


def evaluate(poly, values, modulus):
    total = 0
    for exponents, coefficient in poly.items():
        term = coefficient % modulus
        for v, k in zip(values, exponents):
            term = term*pow(v, k, modulus) % modulus
        total = (total+term) % modulus
    return total


def load_module(path):
    spec = importlib.util.spec_from_file_location('fixed_t4_module', path)
    require(spec is not None and spec.loader is not None, 'Cannot load coefficient module')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def geometric(base, count, modulus):
    """Recursive power/sum identity, independent of the binary-DAG emitter."""
    if count == 0:
        return 1 % modulus, 0
    if count == 1:
        return base % modulus, 1 % modulus
    p, s = geometric(base, count//2, modulus)
    p2, s2 = p*p % modulus, s*(1+p) % modulus
    if count % 2:
        return p2*base % modulus, (s2+p2) % modulus
    return p2, s2


def coding_exponents(nu):
    """Literal finite alpha sum, enumerated by multisets instead of recursion.

    Returns (alpha, L-expo(alpha)). Different alpha have different exponents
    because all digits are in [0,4] in base five.
    """
    dimension, L = nu+1, 5**(nu+1)
    powers = [5**j for j in range(dimension)]
    for degree in range(5):
        for indices in combinations_with_replacement(range(dimension), degree):
            alpha = [0]*dimension
            pos = 0
            for j in indices:
                alpha[j] += 1
                pos += powers[j]
            yield tuple(alpha), L-pos


def direct_digit_value(B, z, coeffs, all_exponents, modulus):
    total = 0
    for alpha, exponent in all_exponents:
        total = (total+(z+coeffs.get(alpha, 0))*pow(B, exponent, modulus)) % modulus
    return total


def fast_digit_value(B, z, coeffs, nu, modulus):
    top, L = 5**nu, 5**(nu+1)
    terms = [pow(B, top, modulus)]
    terms += [pow(B, top-5**j, modulus) for j in range(nu+1)]
    h = [1, 0, 0, 0, 0]
    for term in terms:
        for degree in range(1, 5):
            h[degree] = (h[degree]+term*h[degree-1]) % modulus
    baseline = pow(B, top, modulus)*h[4] % modulus
    correction = sum(coefficient*pow(B, L-nc.expo(alpha), modulus)
                     for alpha, coefficient in coeffs.items()) % modulus
    return (z*baseline+correction) % modulus


def direct_blocks(nu, coeffs, z, y, unknowns, all_exponents, modulus):
    """Closed formulas, with direct 66,045-term digit sum and log-time lambda."""
    p = modulus
    epsilon, g0, h0, s0, w0, phi, i0, j0, n = unknowns
    g, h, s, w, i, j = g0+1, h0+1, s0+1, w0+1, i0+1, j0+1
    b = (y+1+epsilon) % p
    B = pow(b, 5, p)
    L = 5**(nu+1)
    q = pow(B, L, p)
    ell = sum(pow(B, 5**r, p) for r in range(1, nu+1)) % p
    lam = geometric(B, 4*L, p)[1]
    e = direct_digit_value(B, z, coeffs, all_exponents, p)
    N = pow(q, 16, p)
    Gcap = 32*b*pow(B, 5**nu, p) % p
    theta = B-2*z
    R = ((g+e*q**3+ell*q**5+
          (2*(e-z*lam)*(1+B+g)**4+lam*B+lam*B*q**4)*q**7)*(N*N-N)
         +(q**3-b*ell+ell+theta*lam*q**3+(B-2)*q**8)*(N*N-1)) % p
    U, Y = N*N*w % p, N*N*s % p
    M = R*Y % p
    PP = 2*M*M*U % p
    K = (R+1+h*(PP-1)) % p
    A = M*(U+1) % p
    B1, W1 = (2*R+1) % p, b*w % p
    C = (B1+W1+phi) % p
    J = (4*A-5) % p
    Q = (3*W1*C-2*(W1*W1-1)) % p
    D = ((A*A-1)*C*C+1) % p
    E = i*J*D*C*C % p
    F = ((A*A-1)*E*E+1) % p
    G1 = (A+F*(C*D+1-A)) % p
    H = (B1+j*C) % p
    I = ((G1*G1-1)*H*H+1) % p
    a0, a1 = ((PP*PP-1)*K*K+1) % p, D*F*I % p
    divisor = (J*F)**2 % p
    dividend = (Q*F+J*(H-C))**2 % p
    margin = (K*K*Gcap-4*(C-K*Y)**2*Gcap-8*g*K*K) % p
    return {'b': b, 'B': B, 'q': q, 'ell': ell, 'lambda': lam, 'e': e,
            'N': N, 'Gcap': Gcap, 'R': R, 'U': U, 'Y': Y, 'M': M,
            'P': PP, 'K': K, 'A': A, 'Wsmall': W1, 'C': C, 'J': J,
            'Q': Q, 'D': D, 'E': E, 'F': F, 'Gp': G1, 'H': H,
            'I': I, 'a0': a0, 'a1': a1, 'divisor': divisor,
            'dividend': dividend, 'margin': margin}


def direct_finalizer(blocks, n, modulus, weights):
    t = blocks
    p = modulus
    if weights == 'literal':
        V0, V1 = (t['a0']**2+2) % p, (t['a1']**2+2) % p
    else:
        V0 = (t['P']**2+t['K']**2+2) % p
        V1 = ((t['A']**2+t['C']**2+1)*(t['A']**2+t['E']**2+1)*
              (t['Gp']**2+t['H']**2+1)+1) % p
    W = t['divisor']*(2*t['margin']-1) % p
    T = (t['divisor']*n+t['dividend']-W*(t['dividend']+V0*V1)) % p
    out = ((T*T-W*W*(t['a0']+V0*V0*t['a1']))**2-
           4*W**4*V0*V0*t['a0']*t['a1']) % p
    return out, {'V0': V0, 'V1': V1, 'W': W, 'T': T, 'output': out}


def verify_base(package, generated):
    constants = json.loads((generated/'constants.json').read_text())
    source = json.loads((package/'base/normalized_quartic32.json').read_text())
    require(source['coefficient_ring_order'] == constants['fixed_port_order'], 'Port orders differ')
    require(source['coding_nu'] == constants['nu'] == 32, 'Wrong dimension')
    require(source['coding_L'] == constants['L'] == 5**33, 'Wrong fixed exponent')
    parent = package/'base/quartic32.upstream.json'
    require(sha256(parent.read_bytes()).hexdigest() == constants['parent_sha256'], 'Parent source hash differs')
    ours = {tuple(c['alpha']): record_polynomial(c['coefficient_polynomial_in_fixed_ports'])
            for c in constants['coefficient_records']}
    theirs = {}
    for c in source['coefficients']:
        alpha = (0,)+tuple(c['witness_powers'])
        multiplier = factorial(4-sum(alpha))
        for a in alpha:
            multiplier *= factorial(a)
        require(multiplier == c['factorial_multiplier'], 'Root factorial multiplier differs')
        require(c['position'] == nc.expo(alpha), 'Root base-five position differs')
        theirs[alpha] = {a: multiplier*v for a, v in record_polynomial(c['coefficient']).items()}
    require(ours == theirs, 'Independent weighted coefficient polynomials differ')
    sb = json.loads((package/'base/index_bound_s.json').read_text())
    ours_b = json.loads((generated/'index_bound_s.json').read_text())
    require(sb['fixed_port_order'] == constants['fixed_port_order'], 'Index bound port order differs')
    require(record_polynomial(sb['s_terms']) == record_polynomial(ours_b['terms']), 'Index bound polynomials differ')
    require([record_polynomial(x) for x in sb['rho_terms']] ==
            [record_polynomial(x) for x in ours_b['rho']], 'Individual residual majorants differ')
    return constants, ours, record_polynomial(sb['s_terms'])


def run(package, generated, output):
    constants, coefficient_polynomials, s_poly = verify_base(package, generated)
    fixed_path = package/'code/fixed_coefficients.py'
    fixed = load_module(fixed_path)
    windows_path = package/'coefficients/t4_windows.json'
    windows = json.loads(windows_path.read_text())
    require(len(windows) == 37075, 'Incorrect T4 window count')
    names = {tuple(c['alpha']): c['name'] for c in constants['coefficient_records']}
    bodies = {weights: json.loads((generated/f'nine_{weights}_dag.json').read_text())
              for weights in ['majorant', 'literal']}
    all_exponents = list(coding_exponents(32))
    require(len(all_exponents) == 66045, 'Incorrect finite digit sum size')
    rng = Random(21520261022)
    tuples = [[0]*9, [1]*9, list(range(9)), [rng.randrange(10) for _ in range(9)]]
    records = []
    compared_nodes = 0
    for prime in [101, 1009, 1000003]:
        require(prime % 2 and all(prime % j for j in range(2, isqrt(prime)+1)), 'Test modulus is not an odd prime')
        ports_p = fixed.t4_ports(prime, windows)
        ports_exponent = fixed.t4_ports(prime-1, windows)
        # Independently transcribed finite sums also support the fast T4 evaluation.
        require(ports_p == fixed.direct_t4_ports(prime, windows), 'Fast/direct T4 coefficient mismatch modulo p')
        require(ports_exponent == fixed.direct_t4_ports(prime-1, windows), 'Fast/direct T4 coefficient mismatch modulo p-1')
        order = constants['fixed_port_order']
        s_residue = evaluate(s_poly, [ports_exponent[x] for x in order], prime-1)
        z = pow(2, s_residue, prime)
        coefficients = {alpha: evaluate(poly, [ports_p[x] for x in order], prime)
                        for alpha, poly in coefficient_polynomials.items()}
        y = direct_digit_value(2*z % prime, z, coefficients, all_exponents, prime)
        require(y == fast_digit_value(2*z % prime, z, coefficients, 32, prime),
                'Direct/complete-homogeneous index y differs')
        fixed_leaves = {'z_index': z, 'y_index': y}
        fixed_leaves.update({names[a]: v for a, v in coefficients.items()})
        sample_records = []
        for sample in tuples:
            blocks = direct_blocks(32, coefficients, z, y, sample, all_exponents, prime)
            require(blocks['e'] == fast_digit_value(blocks['B'], z, coefficients, 32, prime),
                    'Direct/complete-homogeneous variable digit polynomial differs')
            outputs = {}
            for weights, body in bodies.items():
                got, named = nc.evaluate_dag(body, fixed_leaves, dict(zip(body['variables'], sample)), prime)
                want, final = direct_finalizer(blocks, sample[8], prime, weights)
                require(got == want, f'Actual-instance output mismatch p={prime}, weights={weights}')
                for name, value in {**blocks, **final}.items():
                    require(named[name] == value, f'Actual-instance named node mismatch: {name}')
                    compared_nodes += 1
                outputs[weights] = got
            sample_records.append({'unknowns': sample, 'output_residues': outputs})
        records.append({'prime': prime, 'fixed_ports_mod_prime': ports_p,
                        'fixed_ports_mod_prime_minus_one': ports_exponent,
                        's_mod_prime_minus_one': s_residue, 'z_mod_prime': z,
                        'y_mod_prime': y, 'samples': sample_records})
    input_paths = [package/'base/normalized_quartic32.json', package/'base/index_bound_s.json',
                   package/'base/quartic32.upstream.json', windows_path, fixed_path,
                   generated/'constants.json', generated/'index_bound_s.json',
                   generated/'nine_majorant_dag.json', generated/'nine_literal_dag.json']
    receipt = {'status': 'pass', 'scope': 'Actual fixed T4 coefficient instance; independently matching base coefficients/index bound; exact modular comparisons of DAGs and direct closed formulas. No consistency or solvability conclusion is inferred from residues.',
               'base_agreement': {'witness_coefficient_records': len(coefficient_polynomials),
                                  'index_bound_terms': len(s_poly), 'rho_records': 23,
                                  'coding_sum_cardinality': len(all_exponents)},
               'fixed_coefficient_fast_direct_checks': 6,
               'dag_direct_output_comparisons': len(records)*len(tuples)*len(bodies),
               'named_node_comparisons': compared_nodes,
               'fingerprints': records,
               'inputs': [{'name': ('generated/'+str(p.relative_to(generated))) if p.is_relative_to(generated)
                                   else ('package/'+str(p.relative_to(package))),
                           'sha256': sha256(p.read_bytes()).hexdigest()} for p in input_paths]}
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(receipt, indent=2)+'\n')
    return receipt


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--package-root', type=Path, required=True)
    ap.add_argument('--generated', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    receipt = run(args.package_root.resolve(), args.generated.resolve(), args.output.resolve())
    print(json.dumps({k: v for k, v in receipt.items() if k not in ['fingerprints', 'inputs']}, indent=2))
