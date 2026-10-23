#!/usr/bin/env python3
"""Independent finite audit of the primary signed10 packet.

This file imports neither builder, verifier, nor shared circuit code.  It reads
the delivered JSON, reconstructs the source coefficients, and evaluates a
separate literal transcription.  Its checks supplement the mathematical proof;
they are not an end-to-end formal proof or a search for a Diophantine solution.
"""
from collections import Counter, defaultdict
from itertools import product
from math import comb, factorial, gcd, isqrt
from pathlib import Path
import gzip
import hashlib
import json
import random

HERE = Path(__file__).resolve().parent
SOURCE_SHA256 = '1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287'
NAMES = ['f', 'g', 'h', 'k', 'l', 'w', 'x', 'y', 'z', 'm']
NU, DELTA, BETA_EXPONENT = 31, 4, 4269882


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def read(name):
    return json.loads((HERE / name).read_text())


def padd(a, b, sign=1):
    result = dict(a)
    for exponent, coefficient in b.items():
        result[exponent] = result.get(exponent, 0) + sign * coefficient
    return {key: value for key, value in result.items() if value}


def pmul(a, b):
    result = defaultdict(int)
    for ea, ca in a.items():
        for eb, cb in b.items():
            result[tuple(x + y for x, y in zip(ea, eb))] += ca * cb
    return {key: value for key, value in result.items() if value}


def reconstruct_source():
    raw = (HERE / 'data/parent_quartic31.json').read_bytes()
    need(digest(raw) == SOURCE_SHA256, 'Pinned parent source bytes differ')
    source, constants = json.loads(raw), read('data/constants.json')
    need(source['constants'] == ['beta', 'K0', 'MC', 'MF'], 'Wrong port order')
    need(len(source['variables']) == NU and len(source['equations']) == 22,
         'Wrong parent dimensions')
    whole = {}
    for equation in source['equations']:
        shifted = defaultdict(int)
        for term in equation['terms']:
            exponents, coefficient = term['powers'], term['coefficient']
            support = [j for j in range(NU) if exponents[j]]
            for chosen in product(*(range(exponents[j] + 1) for j in support)):
                powers = [0] * NU + exponents[NU:]
                factor = coefficient
                for j, k in zip(support, chosen):
                    powers[j] = k
                    factor *= comb(exponents[j], k)
                shifted[tuple(powers)] += factor
        whole = padd(whole, pmul(shifted, shifted))
    weighted = defaultdict(dict)
    for exponents, coefficient in whole.items():
        alpha = (0,) + exponents[:NU]
        multiplier = factorial(DELTA - sum(alpha))
        for exponent in alpha:
            multiplier *= factorial(exponent)
        weighted[alpha][exponents[NU:]] = coefficient * multiplier
    records = constants['coefficient_records']
    received = {
        tuple(row['alpha']): {
            tuple(term['powers']): term['coefficient']
            for term in row['coefficient_polynomial_in_fixed_ports']}
        for row in records}
    need(dict(weighted) == received and len(records) == 402,
         'Weighted coefficient recipes do not match shifted quartic')
    need(max(sum(e[:NU]) for e in whole) == DELTA, 'Wrong source degree')
    for row in records:
        need(row['alpha'][0] == 0, 'Dummy source input occurs')
        need(row['expo'] == sum(e * 5 ** j for j, e in enumerate(row['alpha'])),
             'Incorrect reversed-base coefficient position')
        need(row['expo'] <= 4 * 5 ** NU < 5 ** (NU + 1), 'Negative coding exponent')
    fifth = source['equations'][4]
    need(fifth['equation'] == 'E = X(a-E)', 'Unexpected constant-term witness')
    need(all(not any(t['powers'][NU:]) for t in fifth['terms']),
         'Constant-term witness depends on a fixed port')
    need(sum(t['coefficient'] for t in fifth['terms']) == 1,
         'Source normalization does not certify positive constant term')
    need(constants['parent_sha256'] == SOURCE_SHA256 and constants['nu'] == NU,
         'Coefficient metadata mismatch')
    return constants, {
        'parent_sha256': SOURCE_SHA256,
        'quadratic_residuals': 22, 'source_variables': NU,
        'source_degree': DELTA, 'symbolic_terms': len(whole),
        'weighted_coefficient_records': len(records),
        'all_base_positions_checked': True,
        'dummy_input_absent': True, 'positive_constant_term': True}


def authenticate_constants(constants):
    master = json.loads((HERE.parent / 'coefficients/COEFFICIENT_BINDING.json').read_text())
    need(master['instance'] == 'wang943-mixed-121x8801', 'Wrong active tuple')
    local = read('data/coefficients_binding.json')
    need(local['variant'] == master['instance'], 'Local tuple differs from active tuple')
    local_files = {row['name']: row for row in local['files']}
    port_values, checks = {}, []
    mapping = {'beta': 'beta', 'K': 'K0', 'MC': 'MC', 'MF_source': 'MF'}
    for row in master['files']:
        name = row['port']
        packed = (HERE / 'data' / (name + '.bin.gz')).read_bytes()
        raw = gzip.decompress(packed)
        meta = local_files[name]
        need(digest(raw) == row['sha256'] == meta['sha256'], 'Fixed port hash mismatch')
        need(digest(packed) == row['gzip_sha256'] == meta['gzip_sha256'],
             'Compressed port hash mismatch')
        value = int.from_bytes(raw, 'little')
        need(value.bit_length() == row['bit_length'] == meta['bit_length'],
             'Fixed port bit length mismatch')
        port_values[mapping[name]] = value
        checks.append({'port': name, 'bits': value.bit_length(), 'sha256': digest(raw)})
    instance = read('data/INSTANCE.json')
    need(instance['parent_sha256'] == SOURCE_SHA256, 'Instance parent mismatch')
    meta = instance['beta_sun']
    packed = (HERE / 'data' / meta['file']).read_bytes()
    raw = gzip.decompress(packed)
    need(digest(packed) == meta['gzip_sha256'] and digest(raw) == meta['sha256'],
         'Source radix hash mismatch')
    need(int.from_bytes(raw, 'little') == 1 << BETA_EXPONENT,
         'Source radix is not the specified even power of two')
    bits = [port_values[name].bit_length() for name in constants['fixed_port_order']]
    bound = read('data/index_bound.json')
    need(bits == bound['port_bit_lengths'], 'Coefficient bound uses wrong ports')
    exponent = 4269855
    need(bound['index_exponent'] == exponent, 'Wrong coefficient bound')
    for row in constants['coefficient_records']:
        upper = 0
        for term in row['coefficient_polynomial_in_fixed_ports']:
            upper += abs(term['coefficient']) << sum(e * bit for e, bit in zip(term['powers'], bits))
        need(upper + 1 < 1 << exponent, 'Coefficient exceeds source bound')
    sun_multiplier = 2 * factorial(DELTA) * (NU + 2) ** DELTA
    need(sun_multiplier == 56924208 < 1 << 27, 'Wrong Sun coefficient multiplier')
    need(BETA_EXPONENT == exponent + 27 and BETA_EXPONENT % 2 == 0,
         'Radix fails Sun normalization')
    return port_values, {
        'active_instance': master['instance'], 'ports': checks,
        'weighted_coefficient_exponent_bound': exponent,
        'radix_exponent': BETA_EXPONENT,
        'radix_sha256': digest(raw), 'source_multiplier': sun_multiplier,
        'all_coefficient_bounds_checked': True}


def fixed_modulo(constants, ports, modulus):
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


def expand_norm_independently(packet):
    # Expand all eight signed linear factors in X and three formal roots.
    unit = (0, 0, 0, 0)
    variables = []
    for j in range(4):
        ex = list(unit)
        ex[j] = 1
        variables.append({tuple(ex): 1})
    expanded = {unit: 1}
    for signs in product((-1, 1), repeat=3):
        factor = variables[0]
        for root, sign in zip(variables[1:], signs):
            factor = padd(factor, root, sign)
        expanded = pmul(expanded, factor)
    need(all(all(e % 2 == 0 for e in ex[1:]) for ex in expanded),
         'Radicals survived symmetric product')
    norm = {(ex[0],) + tuple(e // 2 for e in ex[1:]): c for ex, c in expanded.items()}

    # Independently evaluate only the delivered graph above its four norm ports.
    names = packet['named_nodes']
    boundary = {names[name]: variables[j] for j, name in enumerate(
        ['norm_center', 'scaled_A1', 'scaled_A2', 'scaled_A3'])}
    memo = dict(boundary)
    def visit(index):
        if index not in memo:
            node = packet['nodes'][index]
            kind = node['kind']
            if kind == 'literal':
                memo[index] = {unit: node['value']} if node['value'] else {}
            else:
                need(kind in ('add', 'sub', 'mul'), 'Norm escapes its four inputs')
                left, right = visit(node['left']), visit(node['right'])
                memo[index] = pmul(left, right) if kind == 'mul' else padd(left, right, -1 if kind == 'sub' else 1)
        return memo[index]
    need(visit(packet['output']) == norm, 'Delivered norm is not the eight-factor product')
    need(len(norm) == 35, 'Unexpected norm expansion')
    return norm, {'signed_factors': 8, 'integer_polynomial_terms': len(norm),
                  'exact_formal_identity_verified': True}


def geometric_sum(base, length, modulus):
    # Binary composition of affine maps, independently of the builder recursion.
    accumulated_power, accumulated_sum = 1, 0
    block_power, block_sum = base % modulus, 1
    while length:
        if length & 1:
            accumulated_sum = (accumulated_sum + accumulated_power * block_sum) % modulus
            accumulated_power = accumulated_power * block_power % modulus
        block_sum = block_sum * (1 + block_power) % modulus
        block_power = block_power * block_power % modulus
        length >>= 1
    return accumulated_sum


def literal_formula(v, fixed, records, modulus, norm):
    """Literal Sun source formulas and the three local replacements."""
    q = lambda x: x % modulus
    power = lambda x, e: pow(x, e, modulus)
    n = {}
    def put(name, value):
        n[name] = value % modulus
        return n[name]
    t, lc = 5 ** NU, 5 ** (NU + 1)
    b = put('b', 1 + 3 * v['f'])
    base = put('base', fixed['beta_sun'] * power(b, 4))
    put('qcode', power(base, lc))
    top = put('top', power(base, t))
    ell = put('ell', sum(power(base, 5 ** j) for j in range(1, NU + 1)))
    code = put('Dcode', sum(fixed[row['name']] * power(base, lc - row['expo']) for row in records))
    n0 = put('N0', power(base, t + 1))
    n1 = put('N1', 4 * power(base, 9 * t + 1))
    nn = put('N', n0 * n1)
    mask = put('Mcode', n0 - 1 - (b - 1) * ell)
    tc = put('Tcode', mask + (base - 2) * power(base, lc) * n0)
    jc = put('Jcode', 2 * power(1 + v['g'], 4) * code + base * geometric_sum(base, 9 * t + 1, modulus))
    sc = put('Scode', v['g'] + jc * n0)
    rc = put('Rcode', (sc + tc + 1) * nn + tc + 1)
    xx = put('X', (nn - 1) * rc)
    yy = put('Y', nn * nn)
    cap = put('Ccap', b * top)
    ll = put('Lsmall', v['l'] * yy)
    uu = put('U', 2 * ll * xx)
    vv = put('V', 4 * v['g'] * v['w'] * yy)
    ww = put('Wsmall', b * v['w'])
    aa = put('A', uu * (vv + 1))
    bb = put('Bsmall', 2 * xx + 1)
    cc = put('C', bb + (aa - 2) * v['h'])
    pn = put('Pn', uu * uu * vv)
    kk = put('K', xx + 1 + v['k'] * (pn - 2))
    ss = put('Ssmall', 2 * aa - 5)
    tt = put('Tsmall', 3 * ww * cc - 2 * (ww * ww - 1))
    r1 = put('R2', (pn * pn - 4) * kk * kk + 4)
    dd = put('Delta', 8 * cap ** 3 * v['g'] * kk * kk - v['g'] ** 2 * (32 * (cc - kk * ll) ** 2 * cap ** 3 + v['g'] ** 2 * kk * kk))
    oo = put('O0', v['f'] ** 2 * v['l'] ** 2 * dd)
    xi = put('xi', v['z'] * v['x'])
    ds = put('D', (aa * aa - 4) * cc * cc + 4)
    es = put('E', cc * cc * ds * xi)
    fs = put('F', 4 * (aa * aa - 4) * es * es + 1)
    gs = put('Gstar', 2 * (aa + 2) * (aa - 2) ** 2 * es * es - 1)
    omega = put('Omega', 16 * es)
    hs = put('Hstar', cc + (bb - cc) * fs + omega * fs * v['y'])
    ii = put('Istar', (gs * gs - 1) * hs * hs + 1)
    sigma = put('Sigma', xi * power(ss, 5))
    rr = put('merger_argument', tt + ss * v['y'])
    theta = put('Theta', (rr ** 3 - rr * ss ** 2 - ss ** 3) * (rr ** 2 + 23 * ss ** 2))
    bracket = put('positivity_bracket', 1 + (3 * oo - 4) * b ** 2 * v['z'] ** 2)
    r0 = put('A1', b * bracket)
    put('A2', r1)
    r2 = put('A3', ds * fs * ii)
    w1 = put('norm_weight1', r0)
    w2 = put('norm_weight2', r0 * (pn * pn + kk * kk + 3))
    center = put('norm_center', sigma * v['m'] - theta)
    scaled = [put('scaled_A' + str(j + 1), sigma ** 2 * weight ** 2 * radicand)
              for j, (weight, radicand) in enumerate(zip([1, w1, w2], [r0, r1, r2]))]
    out = 0
    for ex, coefficient in norm.items():
        value = coefficient
        for base_value, exponent in zip([center] + scaled, ex):
            value = value * power(base_value, exponent) % modulus
        out += value
    put('F10', out)
    return n


def audit_graph(packet, fixed, variables, modulus):
    values, leading = [], []
    for index, node in enumerate(packet['nodes']):
        kind = node['kind']
        if kind == 'variable':
            value, top = variables[node['name']], (1, 1)
        elif kind in ('literal', 'fixed'):
            value = node['value'] if kind == 'literal' else fixed[node['name']]
            top = (0, value % modulus)
        else:
            need(kind in ('add', 'sub', 'mul'), 'Non-polynomial graph operation')
            i, j = node['left'], node['right']
            need(0 <= i < index and 0 <= j < index, 'Graph is not topologically ordered')
            a, b = values[i], values[j]
            da, ca = leading[i]
            db, cb = leading[j]
            if kind == 'mul':
                value, top = a * b, (da + db, ca * cb % modulus)
            else:
                sign = -1 if kind == 'sub' else 1
                degree = max(da, db)
                value = a + sign * b
                top = (degree, ((ca if da == degree else 0) + sign * (cb if db == degree else 0)) % modulus)
        values.append(value % modulus)
        leading.append(top)
    named = {name: values[index] for name, index in packet['named_nodes'].items()}
    return named, leading[packet['output']]


def local_regressions():
    # Exercise the structural domain restriction O=f^2*l^2*Delta, including f=0.
    cases, square_cases = 0, 0
    for f, l, delta, z in product(range(-8, 9), range(-3, 4), range(-6, 7), range(-4, 5)):
        if z == 0:
            continue
        b, oo = 1 + 3 * f, f * f * l * l * delta
        bracket = 1 + (3 * oo - 4) * b * b * z * z
        r0 = b * bracket
        need(abs(r0) > 1 and gcd(b, bracket) == 1, 'Structural nonvanishing regression')
        if r0 >= 0 and isqrt(r0) ** 2 == r0:
            need(b > 0 and isqrt(b) ** 2 == b and oo > 0, 'Positivity merger regression')
            square_cases += 1
        cases += 1
    bound_cases = 0
    for pn, kk in product(range(-50, 51), repeat=2):
        r1 = (pn * pn - 4) * kk * kk + 4
        need(abs(r1) <= (pn * pn + kk * kk + 2) ** 2, 'Root magnitude bound regression')
        bound_cases += 1
    roots = []
    for modulus in [2 ** k for k in range(1, 12)] + [23 ** k for k in range(1, 4)] + [3, 5, 7, 11, 13, 17, 19, 31, 37, 41, 101, 1009]:
        root = next((a for a in range(modulus) if (a ** 3 - a - 1) * (a * a + 23) % modulus == 0), None)
        need(root is not None, 'Quintic prime-power root regression')
        roots.append({'modulus': modulus, 'root': root})
    return {'structural_positivity_cases': cases, 'square_cases': square_cases,
            'root_bound_cases': bound_cases, 'quintic_roots': roots,
            'scope': 'Finite regression examples; universal arguments are in INDEPENDENT_AUDIT.md.'}


def main():
    constants, source_report = reconstruct_source()
    ports, constant_report = authenticate_constants(constants)
    packed = (HERE / 'generated/signed10.json').read_bytes()
    packet = json.loads(packed)
    need(packet['variables'] == NAMES, 'Wrong ten unknowns')
    need(packet['weight_scheme'] == 'structural' and packet['merger_degree'] == 5
         and packet['norm_radicands'] == 3 and packet['merged_positivity'], 'Wrong primary variant')
    seen, todo = set(), [packet['output']]
    while todo:
        index = todo.pop()
        if index in seen:
            continue
        seen.add(index)
        node = packet['nodes'][index]
        if node['kind'] in ('add', 'sub', 'mul'):
            todo.extend((node['left'], node['right']))
    need(len(seen) == len(packet['nodes']), 'Dead graph nodes counted as operations')
    kinds = Counter(node['kind'] for node in packet['nodes'])
    counts = {kind: kinds[kind] for kind in ('add', 'sub', 'mul')}
    need(counts == packet['operation_counts'] and sum(counts.values()) == 1442,
         'Primary operation count mismatch')
    need([node['name'] for node in packet['nodes'] if node['kind'] == 'variable'] == NAMES,
         'Hidden or repeated variable leaf')
    norm, norm_report = expand_norm_independently(packet)
    rng = random.Random(202610231023)
    cases = [dict.fromkeys(NAMES, value) for value in (0, 1, -1)]
    for name in NAMES:
        case = dict.fromkeys(NAMES, 2)
        case[name] = 0
        cases.append(case)
    cases += [dict(zip(NAMES, [rng.randrange(-17, 18) for _ in NAMES])) for _ in range(12)]
    cases += [dict(zip(NAMES, [0, -3, 2, -7, 1, 4, -2, 9, 3, -5])),
              dict(zip(NAMES, [-2, 5, -7, 3, -1, 2, 4, -5, -6, 1]))]
    modular, certificates, comparisons = [], [], 0
    for prime in (1009, 1000003, 1000033):
        fixed = fixed_modulo(constants, ports, prime)
        for v in cases:
            actual, top = audit_graph(packet, fixed, v, prime)
            expected = literal_formula(v, fixed, constants['coefficient_records'], prime, norm)
            need(actual == expected, 'Literal formula mismatch at modulus ' + str(prime))
            comparisons += len(expected)
            if v['x'] == 0 or v['z'] == 0:
                need(actual['Sigma'] == 0 and actual['F10'] == pow(actual['Theta'], 8, prime),
                     'Zero-witness specialization mismatch')
            if v['f'] == 0:
                need(actual['O0'] == 0 and actual['A1'] == (1 - 4 * v['z'] ** 2) % prime,
                     'f=0 structural guard mismatch')
        degree = 126496 * 5 ** 31 + 27064
        need(top[0] == degree == packet['degree_upper_bound'] == packet['exact_degree']
             and top[1] != 0, 'Degree upper bound not attained')
        certificates.append({'prime': prime, 'degree': top[0], 'diagonal_leading_coefficient': top[1]})
        modular.append({'prime': prime, 'assignments': len(cases), 'all_named_nodes_compared': len(actual)})
    report = {
        'status': 'PASS', 'auditor_imports_builder_or_verifier': False,
        'scope': 'Finite exact arithmetic checks and an independent mathematical review; not a formal proof of the entire compiler.',
        'primary_circuit_sha256': digest(packed), 'source': source_report,
        'fixed_constants': constant_report, 'norm_identity': norm_report,
        'unknowns': NAMES, 'live_nodes': len(seen), 'operation_counts': counts,
        'total_operations': sum(counts.values()), 'modular_cases': modular,
        'named_node_comparisons': comparisons, 'degree_certificates': certificates,
        'local_regressions': local_regressions(),
        'source_review': ['https://arxiv.org/html/1704.03504v7#S3',
                          'https://arxiv.org/html/2609.01594v2#S3',
                          'https://arxiv.org/html/2609.01594v2#S4',
                          'https://arxiv.org/html/2609.01594v2#S6',
                          'https://arxiv.org/html/2609.01594v2#S7']}
    (HERE / 'INDEPENDENT_AUDIT.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({key: report[key] for key in ('status', 'total_operations', 'named_node_comparisons', 'degree_certificates')}, indent=2))


if __name__ == '__main__':
    main()
