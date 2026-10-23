#!/usr/bin/env python3
"""Independent arithmetic and source checks for the sixteen-integer equation.

These finite checks validate definitions and exact algebra. The accompanying
paper, rather than a finite test of Diophantine solutions, proves the theorem.
"""
from collections import defaultdict
from itertools import combinations_with_replacement, product
from pathlib import Path
import gzip
import hashlib
import json
import math
import random

ROOT = Path(__file__).resolve().parents[1]


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def evaluate_dag(body, inputs, fixed, modulus):
    values = []
    for k, n in enumerate(body['nodes']):
        kind = n['kind']
        if kind == 'literal':
            value = n['value']
        elif kind == 'variable':
            value = inputs[n['name']]
        elif kind == 'fixed':
            value = fixed[n['name']]
        else:
            need(0 <= n['left'] < k and 0 <= n['right'] < k, 'Non-topological DAG')
            a, b = values[n['left']], values[n['right']]
            if kind == 'add':
                value = a+b
            elif kind == 'sub':
                value = a-b
            elif kind == 'mul':
                value = a*b
            else:
                raise RuntimeError('Bad node kind')
        values.append(value % modulus)
    return values[body['output']], {k: values[i] for k, i in body['named_nodes'].items()}


def verify_sources():
    data = json.loads((ROOT/'SOURCE_MANIFEST.json').read_text())
    for row in data['files']:
        blob = (ROOT/row['path']).read_bytes()
        need(hashlib.sha256(blob).hexdigest() == row['sha256'], 'Source hash mismatch: '+row['path'])
        need(hashlib.sha1(b'blob '+str(len(blob)).encode()+b'\0'+blob).hexdigest() == row['git_blob_sha1'],
             'Git blob mismatch: '+row['path'])
    return len(data['files'])


def native_ports():
    binding = json.loads((ROOT/'upstream/compiler/binding.json').read_text())
    result = {}
    for record in binding['files']:
        path = ROOT/'upstream/compiler'/(record['name']+'.bin.gz')
        need(hashlib.sha256(path.read_bytes()).hexdigest() == record['gzip_sha256'], 'Gzip hash mismatch')
        raw = gzip.decompress(path.read_bytes())
        need(hashlib.sha256(raw).hexdigest() == record['sha256'], 'Coefficient byte mismatch')
        number = int.from_bytes(raw, 'little')
        need(number.bit_length() == record['bit_length'], 'Coefficient bit length mismatch')
        result[record['name']] = number
    need(result['beta']+1 == 1 << 9765625, 'Incorrect native radix')
    B = result['beta']+1
    MC, MF = result['MC'], result['MF_source']-result['beta']
    need(0 < MC < B-1 and 0 < MF < B-1, 'Incorrect masks')
    need(MC % 4 == 2 and MF % 8 == 4, 'Incorrect low mask bits')
    need(MC.bit_count()+MF.bit_count() == 9765625, 'Unbalanced populations')
    return [result[k] for k in ('beta', 'K', 'MC', 'MF_source')]


def coefficient_audit(constants, ports):
    """Expand the shifted literal quadratic system, independent of its builder."""
    parent = json.loads((ROOT/'quartic31/polynomials.json').read_text())
    nu = len(parent['variables'])
    total = defaultdict(int)
    zero_values = []
    for eq in parent['equations']:
        shifted = defaultdict(int)
        for term in eq['terms']:
            ex = term['powers']
            active = [i for i in range(nu) if ex[i]]
            for choices in product(*(range(ex[i]+1) for i in active)):
                new = list(ex)
                coef = term['coefficient']
                for i, j in zip(active, choices):
                    coef *= math.comb(ex[i], j)
                    new[i] = j
                shifted[tuple(new)] += coef
        shifted = {e: c for e, c in shifted.items() if c}
        zero_values.append({e[nu:]: c for e, c in shifted.items() if not any(e[:nu])})
        for e, c in shifted.items():
            for f, d in shifted.items():
                total[tuple(a+b for a, b in zip(e, f))] += c*d
    total = {e: c for e, c in total.items() if c}
    need(zero_values[4] == {(0, 0, 0, 0): -1}, 'Quartic normalization failed')
    grouped = defaultdict(dict)
    for e, c in total.items():
        alpha = (0,)+e[:nu]
        factor = math.factorial(4-sum(alpha))*math.prod(math.factorial(j) for j in alpha)
        grouped[alpha][e[nu:]] = c*factor
    records = {tuple(r['alpha']): {tuple(t['powers']): t['coefficient']
                                  for t in r['coefficient_polynomial_in_fixed_ports']}
               for r in constants['coefficient_records']}
    need(dict(grouped) == records, 'Weighted quartic coefficients differ')
    exponent = constants['index_exponent']
    bits = [v.bit_length() for v in ports]
    max_bound = 0
    for recipe in records.values():
        bound = sum(abs(c) << sum(x*b for x, b in zip(ex, bits)) for ex, c in recipe.items())
        need(bound+1 < 1 << exponent, 'Index bound insufficient')
        max_bound = max(max_bound, (bound+1).bit_length())
    need(max_bound == exponent == 45933757, 'Index certificate is not the fixed selected one')
    return dict(shifted_terms=len(total), weighted_records=len(records), index_exponent=exponent,
                quartic_variables=nu, normalization_residual=5)


def direct_digit_value(x, z, records, nu, modulus):
    """Literal bounded sum: no Horner or homogeneous recurrence is used."""
    L = 5**(nu+1)
    places = [5**j for j in range(nu+1)]+[0]
    baseline = sum(pow(x, L-sum(places[j] for j in group), modulus)
                   for group in combinations_with_replacement(range(nu+2), 4)) % modulus
    correction = sum(c*pow(x, L-sum(j*5**k for k, j in enumerate(alpha)), modulus)
                     for alpha, c in records.items()) % modulus
    return (z*baseline+correction) % modulus


def fixed_leaves(constants, ports, prime):
    vals = [v % prime for v in ports]
    records = {}
    fixed = {}
    for rec in constants['coefficient_records']:
        value = sum(t['coefficient']*math.prod(pow(v, e, prime) for v, e in zip(vals, t['powers']))
                    for t in rec['coefficient_polynomial_in_fixed_ports']) % prime
        records[tuple(rec['alpha'])] = value
        fixed[rec['name']] = value
    z = pow(2, constants['index_exponent'], prime)
    fixed['z_index'] = z
    fixed['y_index'] = direct_digit_value(2*z % prime, z, records, constants['nu'], prime)
    return fixed, records


def finalizer_direct(base, v, p):
    stack = 1
    discs = [3*v['epsilon']+2, 3*v['g']-1, 3*v['s']-1, 3*v['w']-1,
             3*v['phi']+2, 3*base['margin']-1]
    for k, disc in enumerate(discs, 1):
        stack = stack*(1+4*disc*stack*stack*v['z'+str(k)]**2) % p
    D = base['J']*base['F'] % p
    T0 = (base['Q']*base['F']+base['J']*(base['H']-base['C'])) % p
    Z = v['i']*math.prod(v['z'+str(k)] for k in range(1, 7)) % p
    S = Z*pow(D, 5, p) % p
    r = (T0+D*v['residue']) % p
    T = ((r**3-D*D*r-D**3)*(r*r+23*D*D)) % p
    w1 = stack+1
    w2 = w1*(base['P']**2+base['K']**2+2) % p
    X = (S*v['normroot']-T) % p
    A0, A1, A2 = S*S*stack % p, S*S*w1*w1*base['a0'] % p, S*S*w2*w2*base['a1'] % p
    V = (X*X+A2-A0-A1) % p
    W = (V*V+4*X*X*A2-4*A0*A1) % p
    return (W*W-16*V*V*X*X*A2) % p


def jones_direct(v, fixed, records, prime):
    """Displayed formulas over F_p, including a literal bounded digit sum.

    The geometric sum here uses a field division with a separate B=1 case;
    the delivered polynomial circuit contains no divisions.
    """
    p = prime
    L = 5**32
    z = fixed['z_index']
    eps, g, h, s, w, phi, ii, jj = [v[k] % p for k in ('epsilon', 'g', 'h', 's', 'w', 'phi', 'i', 'j')]
    b = (fixed['y_index']+1+eps) % p
    B = pow(b, 5, p)
    q = pow(B, L, p)
    ell = sum(pow(B, 5**j, p) for j in range(1, 32)) % p
    lam = (4*L) % p if B == 1 else ((pow(B, 4*L, p)-1)*pow(B-1, -1, p)) % p
    e = direct_digit_value(B, z, records, 31, p)
    N = pow(q, 16, p)
    Gcap = 32*b*pow(B, 5**31, p) % p
    left = (g+e*q**3+ell*q**5+(2*(e-z*lam)*(1+B+g)**4+lam*B+lam*B*q**4)*q**7) % p
    right = (q**3-b*ell+ell+(B-2*z)*lam*q**3+(B-2)*q**8) % p
    R = (left*(N*N-N)+right*(N*N-1)) % p
    U, Y = N*N*w % p, N*N*s % p
    M = R*Y % p
    P = 2*M*M*U % p
    K = (R+1+h*(P-1)) % p
    A = M*(U+1) % p
    B1, W1 = (2*R+1) % p, b*w % p
    C = (B1+W1+phi) % p
    J = (4*A-5) % p
    Q = (3*W1*C-2*(W1*W1-1)) % p
    D = ((A*A-1)*C*C+1) % p
    E = ii*J*D*C*C % p
    F = ((A*A-1)*E*E+1) % p
    G1 = (A+F*(C*D+1-A)) % p
    H = (B1+jj*C) % p
    I = ((G1*G1-1)*H*H+1) % p
    a0, a1 = ((P*P-1)*K*K+1) % p, D*F*I % p
    margin = (K*K*Gcap-4*(C-K*Y)**2*Gcap-8*g*K*K) % p
    result = dict(locals())
    result['lambda'] = lam
    return result


def norm_identity():
    """Exact sparse-polynomial equality with the eight conjugate factors."""
    def add(a, b):
        out = defaultdict(int, a)
        for e, c in b.items():
            out[e] += c
        return {e: c for e, c in out.items() if c}
    def mul(a, b):
        out = defaultdict(int)
        for e, c in a.items():
            for f, d in b.items():
                out[tuple(x+y for x, y in zip(e, f))] += c*d
        return {e: c for e, c in out.items() if c}
    def scale(a, c):
        return {e: d*c for e, d in a.items() if d*c}
    one = {(0, 0, 0, 0): 1}
    x, r, s, t = [{tuple(int(j == k) for j in range(4)): 1} for k in range(4)]
    prod = one
    for e, f, g in product((-1, 1), repeat=3):
        prod = mul(prod, add(add(add(x, scale(r, -e)), scale(s, -f)), scale(t, -g)))
    x2, a0, a1, a2 = [mul(v, v) for v in (x, r, s, t)]
    v = add(add(add(x2, a2), scale(a0, -1)), scale(a1, -1))
    v2 = mul(v, v)
    w = add(add(v2, scale(mul(x2, a2), 4)), scale(mul(a0, a1), -4))
    expanded = add(mul(w, w), scale(mul(mul(v2, x2), a2), -16))
    need(expanded == prod, 'Norm identity failure')
    return len(prod)


def pell_residue_examples():
    """Construct positive Pell coordinates with prescribed prior residues.

    Work with exact units in Z[sqrt(a^2-1)], including negative starts.
    """
    examples = []
    for a in range(2, 7):
        d = a*a-1
        def mul(u, v):
            return u[0]*v[0]+d*u[1]*v[1], u[0]*v[1]+u[1]*v[0]
        for modulus in range(2, 18):
            current = (1, 0)
            order = 0
            while True:
                order += 1
                current = mul(current, (a, 1))
                current = (current[0] % modulus, current[1] % modulus)
                if current == (1 % modulus, 0):
                    break
                need(order <= modulus**2, 'Finite unit cycle did not close')
            step = (1, 0)
            for _ in range(order):
                step = mul(step, (a, 1))
            initial = (a, -1)
            moved = initial
            while moved[1] <= 10:
                moved = mul(moved, step)
            need(moved[0]**2-d*moved[1]**2 == 1, 'Pell norm changed')
            need((moved[0]-initial[0]) % modulus == (moved[1]-initial[1]) % modulus == 0,
                 'Pell residues changed')
            examples.append((a, modulus, order))
    return len(examples)


def main():
    sources = verify_sources()
    ports = native_ports()
    constants = json.loads((ROOT/'data/coefficients31.json').read_text())
    coeff = coefficient_audit(constants, ports)
    new = json.loads((ROOT/'data/signed16.json').read_text())
    rng = random.Random(1601023102026)
    compared, digit_checks, fingerprints = 0, 0, []
    for prime in (101, 1009, 65537):
        fixed, records = fixed_leaves(constants, ports, prime)
        fingerprints.append(dict(prime=prime, ports=[x % prime for x in ports],
                                 z=fixed['z_index'], y=fixed['y_index']))
        for trial in range(8):
            variables = {k: rng.randrange(-30, 31) for k in new['variables']}
            baseline = jones_direct(variables, fixed, records, prime)
            result, named = evaluate_dag(new, variables, fixed, prime)
            for name in ('b', 'B', 'q', 'ell', 'lambda', 'e', 'N', 'Gcap', 'R', 'U', 'Y', 'M',
                         'P', 'K', 'A', 'C', 'J', 'Q', 'D', 'E', 'F', 'H', 'I', 'a0', 'a1', 'margin'):
                need(named[name] == baseline[name], 'Jones prefix mismatch at '+name)
                compared += 1
            need(result == finalizer_direct(baseline, variables, prime), 'Independent finalizer mismatch')
            digit_checks += 1
    need(len(new['variables']) == len(set(new['variables'])) == 16, 'Wrong input count')
    operations = sum(n['kind'] in ('add', 'sub', 'mul') for n in new['nodes'])
    need(operations == sum(new['operation_counts'].values()), 'Unexpected operation count')
    norm_terms = norm_identity()
    pell_tests = pell_residue_examples()
    for C in range(-10003, 10004, 4):
        need(C % 4 == 1 and (C+1)**2 > abs(C), 'Parity weight inequality failed')
    for n in range(1, 601):
        need(any((t**3-t-1)*(t*t+23) % n == 0 for t in range(n)), 'Intersective diagnostic failed')
    receipt = dict(status='PASS', scope='Definition checks and exact algebra; no kernel proof or consistency decision.',
                   authenticated_source_files=sources, coefficient_audit=coeff, source_prefix_comparisons=compared,
                   actual_instance_finalizer_comparisons=24, literal_digit_sum_comparisons=digit_checks,
                   norm_identity='Exact equality of sparse polynomials in four independent indeterminates',
                   expanded_norm_terms=norm_terms, pell_residue_examples=pell_tests,
                   parity_weight_examples=5002, intersective_moduli=600,
                   variables=16, live_operations=operations, fixed_fingerprints=fingerprints)
    (ROOT/'verification/signed16_independent.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
