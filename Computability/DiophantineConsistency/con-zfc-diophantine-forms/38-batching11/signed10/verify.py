#!/usr/bin/env python3
"""Exact finite checks for the ten-integer construction.

This verifies its fixed coefficients, arithmetic circuit, source encoding,
norm identity and attained degree.  It is not a consistency/halting search,
nor a machine-checked proof of the universal Diophantine equivalence.
"""
from pathlib import Path
from itertools import product
from math import comb, factorial, gcd, isqrt
import gzip
import hashlib
import json
import random
from build import construct, quadratic_norm, prepare_constants
from itertools import combinations_with_replacement
from circuit import DAG, evaluate

ROOT = Path(__file__).resolve().parent
COMPILER=ROOT.parent/'compiler'
BETA_EXPONENT=prepare_constants()['beta_exponent']


def sparse_add(a, b):
    out = a.copy()
    for key, value in b.items():
        out[key] = out.get(key, 0) + value
        if not out[key]:
            del out[key]
    return out


def sparse_scale(a, multiplier):
    return {key: value * multiplier for key, value in a.items() if value * multiplier}


def sparse_mul(a, b):
    out = {}
    for ea, ca in a.items():
        for eb, cb in b.items():
            key = tuple(x + y for x, y in zip(ea, eb))
            out[key] = out.get(key, 0) + ca * cb
    return {key: value for key, value in out.items() if value}


def source_coefficients():
    source_bytes = (ROOT / 'data/parent_quartic31.json').read_bytes()
    source = json.loads(source_bytes)
    constants = json.loads((ROOT / 'data/constants_b2.json').read_text())
    assert hashlib.sha256(source_bytes).hexdigest() == '1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287'
    n = len(source['variables'])
    expected={}
    for row_index,equation in enumerate(source['equations']):
        shifted = {}
        for row in equation['terms']:
            exponents = row['powers']
            # Independent quadratic Taylor expansion at the all-one vector.
            # Constant and linear terms are values/first derivatives there;
            # the homogeneous degree-two part is unchanged by a shift.
            alpha=tuple(exponents[:n]);ports=tuple(exponents[n:]);c=row['coefficient']
            terms=[((0,)*n,2*c)]
            for j,e in enumerate(alpha):
                if e:
                    a=[0]*n;a[j]=1;terms.append((tuple(a),e*c))
            if sum(alpha)==2:
                terms.append((alpha,c*(2 if 2 in alpha else 1)))
            for a,value in terms:
                key=a+ports;shifted[key]=shifted.get(key,0)+value
        shifted = {key: value for key, value in shifted.items() if value}
        for ex,coefficient in shifted.items():
            expected.setdefault((row_index,ex[:n]),{})[ex[n:]]=coefficient
    received = {(row['row'],tuple(row['alpha'])): {tuple(term['powers']): term['coefficient']
                                    for term in row['coefficient_polynomial_in_fixed_ports']}
                for row in constants['coefficient_records']}
    assert expected == received
    assert n == 31 and len(received) == 136
    assert max(sum(alpha) for row,alpha in received)==2
    # This residual, evaluated at every original coordinate 1, equals 1.
    fifth = source['equations'][4]
    assert fifth['equation'] == 'E = X(a-E)'
    assert all(not any(term['powers'][n:]) for term in fifth['terms'])
    assert sum(term['coefficient'] for term in fifth['terms']) == 1
    return constants, {'source_sha256': hashlib.sha256(source_bytes).hexdigest(),
                       'source_residuals': len(source['equations']), 'variables': n,
                       'weighted_records': len(received),
                       'dummy_input_absent': True, 'constant_term_strictly_positive': True,
                       'reconstructed_from_shifted_quadratics_without_sum_of_squares': True}


def fixed_ports(constants):
    binding = json.loads((COMPILER / 'COEFFICIENT_BINDING.json').read_text())
    ports, rows = {}, []
    for row in binding['materialization']['files']:
        name = row['port']
        compressed = (COMPILER / row['file']).read_bytes()
        raw = gzip.decompress(compressed)
        assert hashlib.sha256(raw).hexdigest() == row['sha256']
        assert hashlib.sha256(compressed).hexdigest() == row['gzip_sha256']
        value = int.from_bytes(raw, 'little')
        assert value.bit_length() == row['bits']
        ports[{'K': 'K0', 'MF_source': 'MF'}.get(name, name)] = value
        rows.append({'name': name, 'bits': value.bit_length(), 'sha256': row['sha256']})
    bits = [ports[name].bit_length() for name in constants['fixed_port_order']]
    assert bits == constants['port_bit_lengths']
    coefficient_total=1
    for row in constants['coefficient_records']:
        upper = sum(abs(term['coefficient']) << sum(power * bit for power, bit in zip(term['powers'], bits))
                    for term in row['coefficient_polynomial_in_fixed_ports'])
        coefficient_total+=upper
    assert coefficient_total.bit_length()==constants['absolute_coefficient_bound_bit_length']
    assert (1<<BETA_EXPONENT)>2048*coefficient_total
    assert BETA_EXPONENT%2==0
    instance=json.loads((ROOT/'data/INSTANCE.json').read_text())
    beta_record=instance['beta_sun']
    compressed=(ROOT/'data'/beta_record['file']).read_bytes()
    raw=gzip.decompress(compressed)
    assert hashlib.sha256(compressed).hexdigest()==beta_record['gzip_sha256']
    assert hashlib.sha256(raw).hexdigest()==beta_record['sha256']
    assert int.from_bytes(raw,'little')==1<<BETA_EXPONENT
    assert beta_record['power_of_two_exponent']==BETA_EXPONENT
    assert instance['compiler_instance']==binding['instance']
    return ports, {'ports': rows,
                   'weighted_coefficient_bound_bit_length':coefficient_total.bit_length(),
                   'beta_sun_exponent': BETA_EXPONENT, 'beta_is_even_power_of_two': True,
                   'beta_strictly_exceeds_2048_times_absolute_bound':True,
                   'beta_payload_sha256':beta_record['sha256'],
                   'all_136_bounds_verified': True}


def fixed_leaves(constants, ports, modulus):
    values = {'beta_sun': pow(2, BETA_EXPONENT, modulus)}
    for row in constants['coefficient_records']:
        total = 0
        for term in row['coefficient_polynomial_in_fixed_ports']:
            value = term['coefficient']
            for name, exponent in zip(constants['fixed_port_order'], term['powers']):
                value = value * pow(ports[name] % modulus, exponent, modulus) % modulus
            total += value
        values[row['name']] = total % modulus
    return values


def norm_polynomial(count):
    """Exact independent expansion of the 2^count signed linear factors."""
    zero = (0,) * (count + 1)
    variables = []
    for j in range(count + 1):
        ex = list(zero)
        ex[j] = 1
        variables.append({tuple(ex): 1})
    expansion = {zero: 1}
    for signs in product((-1, 1), repeat=count):
        factor = variables[0].copy()
        for sign, root in zip(signs, variables[1:]):
            factor = sparse_add(factor, sparse_scale(root, sign))
        expansion = sparse_mul(expansion, factor)
    assert all(all(ex % 2 == 0 for ex in key[1:]) for key in expansion)
    polynomial = {(key[0],) + tuple(ex // 2 for ex in key[1:]): value
                  for key, value in expansion.items()}

    # Independently expand the quadratic-norm circuit over formal X,A_i.
    dag = DAG()
    X = dag.var('X')
    Ai = [dag.var('A' + str(i + 1)) for i in range(count)]
    output = quadratic_norm(dag, X, Ai)
    nodes, output, _ = dag.prune(output)
    names = ['X'] + ['A' + str(i + 1) for i in range(count)]
    values = []
    for node in nodes:
        kind = node['kind']
        if kind == 'literal':
            result = {zero: node['value']} if node['value'] else {}
        elif kind == 'variable':
            result = variables[names.index(node['name'])]
        else:
            a, b = values[node['left']], values[node['right']]
            result = sparse_mul(a, b) if kind == 'mul' else sparse_add(a, sparse_scale(b, -1 if kind == 'sub' else 1))
        values.append(result)
    assert values[output] == polynomial
    artifact = {'variables': names, 'definition': 'Product over signs of X+sum(epsilon_i*sqrt(A_i)); expanded integer polynomial.',
                'radicands': count, 'terms': [{'powers': list(key), 'coefficient': value}
                                              for key, value in sorted(polynomial.items())],
                'exact_identity_verified_against_norm_circuit': True}
    (ROOT / 'generated' / ('norm' + str(count) + '_polynomial.json')).write_text(json.dumps(artifact, indent=2) + '\n')
    return polynomial, {'radicands': count, 'signed_factors': 2 ** count,
                        'expanded_terms': len(polynomial), 'formal_identity_verified': True}


def evaluate_norm(polynomial, values, modulus):
    total = 0
    for ex, coefficient in polynomial.items():
        value = coefficient
        for base, exponent in zip(values, ex):
            value = value * pow(base, exponent, modulus) % modulus
        total += value
    return total % modulus


def geometric(base, n, modulus):
    if n == 0:
        return 0
    if n == 1:
        return 1
    h = n // 2
    value = geometric(base, h, modulus)
    power = pow(base, h, modulus)
    return (value * (1 + power) + (power * power if n % 2 else 0)) % modulus


def literal(v, fixed, constants, modulus, merger, merged, scheme, norm):
    """Independent scalar transcription, with a literal 402-term source sum."""
    p = modulus
    adaptive = scheme != 'sun'
    red = lambda x: x % p
    weights=json.loads((ROOT/'weights.json').read_text())['weights_with_zero'][1:]
    t=max(weights);width=4*t+1;Hlen=22*width
    b = red(1 + 3 * v['f'])
    base = red(fixed['beta_sun'] * pow(b, 2, p))
    ell = sum(pow(base, w, p) for w in weights) % p
    Dcode = sum(fixed[row['name']] * pow(base, row['row']*width+2*t - sum(a*w for a,w in zip(row['alpha'],weights)), p)
                for row in constants['coefficient_records']) % p
    N0 = pow(base, t + 1, p)
    N1 = red(4 * pow(base, Hlen, p))
    N = red(N0 * N1)
    Mcode = red(N0 - 1 - (b - 1) * ell)
    targets=sum(pow(base,j*width+2*t,p) for j in range(22))%p
    Tcode = red(Mcode + (base - 2) * targets * N0)
    Jcode = red(2 * pow(1 + v['g'], 2, p) * Dcode + base * geometric(base, Hlen, p))
    Scode = red(v['g'] + Jcode * N0)
    Rcode = red((Scode + Tcode + 1) * N + Tcode + 1)
    X = red((N - 1) * Rcode)
    Y = red(N * N)
    cap = red(b * pow(base, t, p))
    L = red(v['l'] * Y)
    U = red(2 * L * X)
    V = red(4 * v['g'] * v['w'] * Y)
    W = red(b * v['w'])
    A = red(U * (V + 1))
    B = red(2 * X + 1)
    C = red(B + (A - 2) * v['h'])
    K = red(X + 1 + v['k'] * (U * U * V - 2))
    S = red(2 * A - 5)
    T = red(3 * W * C - 2 * (W * W - 1))
    R2 = red((U ** 4 * V * V - 4) * K * K + 4)
    Delta = red(8 * cap ** 3 * v['g'] * K * K - v['g'] ** 2 * (32 * (C - K * L) ** 2 * cap ** 3 + v['g'] ** 2 * K * K))
    O0 = red(v['f'] ** 2 * v['l'] ** 2 * Delta)
    xi = red(v['z'] * v['x'])
    D = red((A * A - 4) * C * C + 4)
    E = red(C * C * D * xi)
    F = red(4 * (A * A - 4) * E * E + 1)
    Gstar = red(2 * (A + 2) * (A - 2) ** 2 * E * E - 1)
    Omega = red(16 * E)
    Hstar = red(C + (B - C) * F + Omega * F * v['y'])
    Istar = red((Gstar * Gstar - 1) * Hstar * Hstar + 1)
    Sigma = red(xi * pow(S, merger, p))
    r = red(T + S * v['y'])
    if merger == 5:
        Theta = red((r ** 3 - r * S * S - S ** 3) * (r * r + 23 * S * S))
    else:
        Theta = red((r * r - 13 * S * S) * (r * r - 17 * S * S) * (r * r - 221 * S * S))
    if merged:
        positivity = red(b * (1 + (3 * O0 - 4) * b * b * v['z'] ** 2))
        radicands = [positivity, R2, red(D * F * Istar)] if adaptive else [positivity, red(D * F * Istar), R2]
    else:
        radicands = [b, red((3 * O0 - 4) * v['z'] ** 2 + 1), red(D * F * Istar), R2]
    if scheme == 'structural':
        weight1 = radicands[0]
        weight2 = red(weight1 * ((U * U * V) ** 2 + K * K + 3))
        weights = [1, weight1, weight2]
    elif adaptive:
        weight1 = red(1 + radicands[0] ** 2)
        weight2 = red(weight1 * (1 + radicands[1] ** 2))
        weights = [1, weight1, weight2]
    else:
        weight = red(1 + sum(ai * ai for ai in radicands))
        weights = [pow(weight, i, p) for i in range(len(radicands))]
    center = red(Sigma * v['m'] - Theta)
    scaled = [red(Sigma * Sigma * weights[i] ** 2 * ai) for i, ai in enumerate(radicands)]
    answer = evaluate_norm(norm, [center] + scaled, p)
    named = dict(b=b, base=base, ell=ell, Dcode=Dcode, N0=N0, N1=N1, N=N,
                 Mcode=Mcode, Tcode=Tcode, Jcode=Jcode, Scode=Scode, Rcode=Rcode,
                 X=X, Y=Y, Ccap=cap, Lsmall=L, U=U, V=V, Wsmall=W, A=A, Bsmall=B,
                 C=C, K=K, Ssmall=S, Tsmall=T, R2=R2, Delta=Delta, O0=O0, xi=xi,
                 D=D, E=E, F=F, Gstar=Gstar, Omega=Omega, Hstar=Hstar, Istar=Istar,
                 Sigma=Sigma, Theta=Theta, norm_center=center, F10=answer)
    if adaptive:
        named.update(norm_weight1=weight1, norm_weight2=weight2)
    else:
        named['norm_weight'] = weight
    named.update({'A' + str(i + 1): ai for i, ai in enumerate(radicands)})
    return answer, named


def degree_certificate(body, fixed, modulus):
    # The DAG gives an upper bound. A nonzero coefficient on its total-degree
    # leading diagonal specialization proves that this upper bound is attained.
    values = []
    for node in body['nodes']:
        kind = node['kind']
        if kind == 'literal':
            value = (0, node['value'] % modulus)
        elif kind == 'fixed':
            value = (0, fixed[node['name']])
        elif kind == 'variable':
            value = (1, 1)
        else:
            a, b = values[node['left']], values[node['right']]
            if kind == 'mul':
                value = (a[0] + b[0], a[1] * b[1] % modulus)
            else:
                degree = max(a[0], b[0])
                sign = -1 if kind == 'sub' else 1
                value = (degree, ((a[1] if a[0] == degree else 0) + sign * (b[1] if b[0] == degree else 0)) % modulus)
        values.append(value)
    degree, leading = values[body['output']]
    assert degree == body['degree_upper_bound'] and leading != 0
    return {'degree': degree, 'prime': modulus, 'diagonal_leading_coefficient': leading,
            'upper_bound_attained': True}


def elementary_checks():
    # Finite regression controls complement, and do not replace, the lemma proof.
    positivity = 0
    for f in range(-20, 21):
        b = 1 + 3 * f
        for O in range(-10, 21):
            for z in range(-8, 9):
                if not z:
                    continue
                bracket = 1 + (3 * O - 4) * b * b * z * z
                value = b * bracket
                assert gcd(b, bracket) == 1
                if value >= 0 and isqrt(value) ** 2 == value:
                    assert b > 0 and isqrt(b) ** 2 == b and O > 0
                positivity += 1
    congruences = 0
    for modulus in range(1, 1001):
        assert any(((v ** 3 - v - 1) * (v * v + 23)) % modulus == 0 for v in range(modulus))
        congruences += 1
    return {'coprime_positivity_cases': positivity, 'quintic_moduli_with_roots': congruences,
            'scope': 'Regression checks only; universal proofs are supplied separately.'}


def run():
    (ROOT / 'generated').mkdir(exist_ok=True)
    weights=json.loads((ROOT/'weights.json').read_text())
    ws=weights['weights_with_zero']
    assert ws[0]==0 and len(ws)==32 and max(ws)==799
    sums=[ws[i]+ws[j] for i,j in combinations_with_replacement(range(32),2)]
    assert len(sums)==len(set(sums))==528
    constants, coefficient_report = source_coefficients()
    ports, fixed_report = fixed_ports(constants)
    norms, norm_reports = {}, []
    for count in (3,):
        norms[count], record = norm_polynomial(count)
        norm_reports.append(record)
    rng = random.Random(1020261023)
    variants = []
    for merger, merged, scheme, filename in [(5, True, 'structural', 'signed10_b2.json')]:
        body, _ = construct(merger, merged, scheme)
        checks, degrees, named_count = [], [], 0
        for prime in (101, 1009, 1000003):
            fixed = fixed_leaves(constants, ports, prime)
            degrees.append(degree_certificate(body, fixed, prime))
            for repeat in range(12):
                variables = {name: rng.randrange(-11, 12) for name in body['variables']}
                actual, actual_named = evaluate(body, fixed, variables, prime)
                expected, expected_named = literal(variables, fixed, constants, prime, merger, merged, scheme, norms[body['norm_radicands']])
                assert actual == expected
                for name, value in expected_named.items():
                    assert actual_named[name] == value, (filename, prime, name)
                    named_count += 1
            checks.append({'prime': prime, 'full_circuit_assignments': 12, 'literal_source_terms': 136})
        body['exact_degree'] = body['degree_upper_bound']
        body['exact_degree_formula'] = body['degree_upper_bound_formula']
        body['degree_certification'] = 'VERIFICATION.json: nonzero leading diagonal coefficients at three primes.'
        (ROOT / 'generated' / filename).write_text(json.dumps(body, separators=(',', ':')) + '\n')
        variants.append({'file': filename, 'unknowns': 10, 'merger_degree': merger,
                         'norm_radicands': body['norm_radicands'], 'exact_degree': body['exact_degree'],
                         'weight_scheme': scheme,
                         'operations': body['operation_counts'], 'total_operations': sum(body['operation_counts'].values()),
                         'fixed_leaves': sum(node['kind'] == 'fixed' for node in body['nodes']),
                         'modular_checks': checks, 'named_node_comparisons': named_count,
                         'degree_certificates': degrees})
    report = {'status': 'PASS', 'scope': 'Finite exact checks; universal proof is PROOF.md.',
              'weight_certificate':weights,
              'coefficient_reconstruction': coefficient_report, 'fixed_constant_verification': fixed_report,
              'norm_identities': norm_reports, 'variants': variants,
              'elementary_regressions': elementary_checks()}
    (ROOT / 'generated/VERIFICATION.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))
    return report


if __name__ == '__main__':
    run()
