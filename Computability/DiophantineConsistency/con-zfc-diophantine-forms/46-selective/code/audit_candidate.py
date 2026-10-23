#!/usr/bin/env python3
"""Independent exact audit of the sparse quadratic source and its F10 DAG.

Does not import the builder, search, or upstream executable programs.
"""
import collections
import copy
import gzip
import itertools
import json
import math
from pathlib import Path
import random
import sys

HERE = Path(__file__).resolve().parent
ROOT = Path(sys.argv[1]) if len(sys.argv) > 1 else HERE.parent
PARENT = ROOT / 'upstream/parent_sparse.json'


def need(condition, message):
    if not condition:
        raise ValueError(message)


def read(name):
    return json.loads((ROOT / name).read_text())


def coefficient(term, data):
    if isinstance(term['leaf'], int):
        return {(0,) * 4: term['sign'] * term['leaf']}
    return {tuple(t['powers']): term['sign'] * t['coefficient']
            for t in data['recipes'][term['leaf']]}


def exact_source(layout, data, parent):
    w = layout['weights']; t = max(w); targets = layout['targets']
    permutation = layout['row_permutation']; n = 31
    need(w[0] == 0 and min(w[1:]) > 0 and len(set(w)) == 32, 'weights are not distinct/positive')
    need(len(targets) == 22 and sorted(targets) == targets and len(set(targets)) == 22,
         'targets are not strictly increasing')
    need(sorted(permutation) == list(range(22)), 'row permutation is invalid')
    all_pairs = collections.defaultdict(list)
    for i in range(32):
        for j in range(i, 32):
            alpha = [0] * n
            if i: alpha[i - 1] += 1
            if j: alpha[j - 1] += 1
            all_pairs[w[i] + w[j]].append((tuple(alpha), 1 if i == j else 2, (i, j)))
    kernel = {}
    marked = set()
    for target, row_index in zip(targets, permutation):
        for term in data['rows'][row_index]:
            alpha = tuple(term['alpha'])
            padded = (0,) * (2 - sum(alpha)) + tuple(i + 1 for i, a in enumerate(alpha) for _ in range(a))
            marked.add(padded)
            e = sum(a * b for a, b in zip(alpha, w[1:]))
            need(len(all_pairs[e]) == 1 and all_pairs[e][0][2] == padded, 'active pair collision')
            exponent = target - e
            need(exponent >= 0, 'negative kernel exponent')
            need(exponent not in kernel, 'two kernel terms overlap')
            kernel[exponent] = coefficient(term, data)
    need(max(kernel) == targets[-1] and kernel[max(kernel)] == {(0,) * 4: 2}, 'wrong top coefficient')
    extracted_terms = 0
    for target, row_index in zip(targets, permutation):
        actual = collections.defaultdict(int)
        for exponent, coeffs in kernel.items():
            for alpha, factor, pair in all_pairs.get(target - exponent, []):
                for ports, scalar in coeffs.items():
                    actual[alpha + ports] += factor * scalar
        actual = {mon: co for mon, co in actual.items() if co}
        original = data['row_order_one_based'][row_index]
        sign = -1 if original in data['negated_original_rows'] else 1
        expected = collections.defaultdict(int)
        for term in parent['equations'][original - 1]['terms']:
            expected[tuple(term['powers'])] += 2 * sign * term['coefficient']
        expected = {mon: co for mon, co in expected.items() if co}
        need(actual == expected, f'extraction mismatch at original parent row {original}')
        extracted_terms += len(actual)
    forbidden_checks = 0
    for i, (target, row_index) in enumerate(zip(targets, permutation)):
        for term in data['rows'][row_index]:
            exponent = target - sum(a * b for a, b in zip(term['alpha'], w[1:]))
            for j, other in enumerate(targets):
                if i != j:
                    forbidden_checks += 1
                    need(other - exponent not in all_pairs, 'cross-target contribution')
    return {'protected_pairs': len(marked), 'all_pairs': 528,
            'distinct_all_pair_sums': len(all_pairs), 'kernel_terms': len(kernel),
            'symbolic_target_identities': 22, 'extracted_symbolic_terms': extracted_terms,
            'cross_target_support_checks': forbidden_checks,
            'minimum_kernel_exponent': min(kernel), 'maximum_kernel_exponent': max(kernel)}, kernel


def ports_and_bound(parent):
    ports = {name: int.from_bytes(gzip.decompress((ROOT / 'coefficients/payloads' / (fn + '.bin.gz')).read_bytes()), 'little')
             for name, fn in zip(['beta', 'K0', 'MC', 'MF'], ['beta', 'K', 'MC', 'MF_source'])}
    maxnorm = 0; maxdegree = 0
    for row in parent['equations']:
        grouped = collections.defaultdict(lambda: collections.defaultdict(int))
        for term in row['terms']:
            grouped[tuple(term['powers'][:31])][tuple(term['powers'][31:])] += term['coefficient']
        for coefficient in grouped.values():
            maxnorm = max(maxnorm, sum(abs(c) for c in coefficient.values()))
            maxdegree = max(maxdegree, max(map(sum, coefficient)))
    need(maxnorm <= 8 and maxdegree <= 2, 'ordinary coefficient bound fails')
    H = 8 * (1 + sum(ports.values())) ** 2
    beta = 1 << 2140030
    need(beta > 4 * 33 ** 2 * H, 'source-base inequality fails')
    need(beta > 36 * H + 2, 'broad-g word-shift bound fails')
    need(all(v > 0 and v < 1 << 1070004 for v in ports.values()), 'port bound fails')
    return ports, {'coefficient_maximum_l1': maxnorm, 'maximum_port_degree': maxdegree,
                   'H_bit_length': H.bit_length(), 'required_bound_bit_length': (4 * 33 ** 2 * H).bit_length(),
                   'source_exponent': 2140030, 'shifted_word_broad_bound': '36 H b^2 <= B-2 for b>=4',
                   'port_bit_lengths': {name: v.bit_length() for name, v in ports.items()}}


def evaluate_dag(body, assignment, fixed, prime):
    values = []; degrees = []; leads = []
    for index, node in enumerate(body['nodes']):
        kind = node['kind']
        if kind == 'variable': value, degree, lead = assignment[node['name']], 1, 1
        elif kind == 'fixed': value, degree, lead = fixed[node['name']], 0, fixed[node['name']]
        elif kind == 'literal': value, degree, lead = node['value'], 0, node['value']
        else:
            a, b = node['left'], node['right']
            need(0 <= a < index and 0 <= b < index, 'non-topological DAG edge')
            if kind == 'mul':
                value = values[a] * values[b]; degree = degrees[a] + degrees[b]; lead = leads[a] * leads[b]
            else:
                need(kind in ('add', 'sub'), 'illegal circuit operation')
                sign = 1 if kind == 'add' else -1
                value = values[a] + sign * values[b]
                degree = max(degrees[a], degrees[b])
                lead = (leads[a] if degrees[a] == degree else 0) + sign * (leads[b] if degrees[b] == degree else 0)
        values.append(value % prime); degrees.append(degree); leads.append(lead % prime)
    return {name: values[i] for name, i in body['named_nodes'].items()}, degrees, leads


def direct_source(layout, kernel, assignment, ports, prime):
    f, g = assignment['f'], assignment['g']
    w = layout['weights']; t = max(w); targets = layout['targets']; span = targets[-1] + 2 * t
    mod = lambda x: x % prime
    b = mod(1 + 3 * f); B = mod(pow(2, 2140030, prime) * b * b)
    top = pow(B, t, prime)
    ell = sum(pow(B, a, prime) for a in w[1:]) % prime
    D = 0
    for exponent, poly in kernel.items():
        c = 0
        for powers, scalar in poly.items():
            term = scalar
            for name, degree in zip(['beta', 'K0', 'MC', 'MF'], powers):
                term *= pow(ports[name], degree, prime)
            c += term
        D += c * pow(B, exponent, prime)
    D %= prime
    N0 = pow(B, t + 1, prime); N1 = mod(4 * pow(B, span + 1, prime)); N = mod(N0 * N1)
    targets_sum = sum(pow(B, a, prime) for a in targets) % prime
    target = mod((B - 2) * targets_sum)
    mask = mod(N0 - 1 - (b - 1) * ell)
    T = mod(mask + target * N0)
    J = mod(2 * (1 + ell + g) ** 2 * D + sum(pow(B, i + 1, prime) for i in range(span + 1)))
    S = mod(g + J * N0); R = mod((S + T + 1) * N + T + 1)
    X = mod((N - 1) * R); Y = mod(N * N); cap = mod(b * top)
    return dict(b=b, base=B, top=top, ell=ell, Dcode=D, N0=N0, N1=N1, N=N,
                targetsum=targets_sum, target=target, mask=mask, Tcode=T,
                Jcode=J, Scode=S, Rcode=R, X=X, Y=Y, Ccap=cap)


def direct_finalizer(v, s, prime):
    # Literal equations in inherited report40, independently transcribed.
    m = lambda x: x % prime
    b, X, Y, cap = [s[n] for n in ['b', 'X', 'Y', 'Ccap']]
    f, g, h, k, l, w, x, y, z, last = [v[n] for n in ['f', 'g', 'h', 'k', 'l', 'w', 'x', 'y', 'z', 'm']]
    L=m(l*Y);U=m(2*L*X);V=m(4*g*w*Y);W=m(b*w)
    A=m(U*(V+1));B1=m(2*X+1);C=m(B1+(A-2)*h);P=m(U*U*V);K=m(X+1+k*(P-2))
    S=m(2*A-5);T=m(3*W*C-2*(W*W-1));R2=m((P*P-4)*K*K+4)
    delta=m(8*cap**3*g*K*K-g*g*(32*(C-K*L)**2*cap**3+g*g*K*K))
    O=m(f*f*l*l*delta);xi=m(z*x);D=m((A*A-4)*C*C+4);E=m(C*C*D*xi)
    F=m(4*(A*A-4)*E*E+1);G=m(2*(A+2)*(A-2)**2*E*E-1);omega=m(16*E)
    H=m(C+(B1-C)*F+omega*F*y);I=m((G*G-1)*H*H+1);sigma=m(xi*S**5)
    r=m(T+S*y);theta=m((r**3-r*S*S-S**3)*(r*r+23*S*S))
    r0=m(b*(1+(3*O-4)*b*b*z*z));r1=R2;r2=m(D*F*I)
    weight1=r0;weight2=m(weight1*(P*P+K*K+3));center=m(sigma*last-theta)
    a0=m(sigma*sigma*r0);a1=m(sigma*sigma*weight1**2*r1);a2=m(sigma*sigma*weight2**2*r2)
    vn=m(center*center+a2-a0-a1);wn=m(vn*vn+4*center*center*a2-4*a0*a1)
    result=m(wn*wn-16*vn*vn*center*center*a2)
    return dict(Lsmall=L,U=U,V=V,Wsmall=W,A=A,Bsmall=B1,C=C,Pn=P,K=K,
                Ssmall=S,Tsmall=T,R2=R2,Delta=delta,O=O,xi=xi,D=D,E=E,F=F,
                Gstar=G,Omega=omega,Hstar=H,Istar=I,Sigma=sigma,merger_argument=r,
                Theta=theta,r0=r0,r1=r1,r2=r2,weight1=weight1,weight2=weight2,
                center=center,a0=a0,a1=a1,a2=a2,Vnorm=vn,Wnorm=wn,F10=result)


def exact_norm_identity():
    zero = (0, 0, 0, 0)
    def add(a, b, scale=1):
        out = dict(a)
        for e, c in b.items(): out[e] = out.get(e, 0) + scale * c
        return {e: c for e, c in out.items() if c}
    def mul(a, b):
        out = collections.defaultdict(int)
        for e, c in a.items():
            for f, d in b.items():
                out[tuple(x + y for x, y in zip(e, f))] += c * d
        return {e: c for e, c in out.items() if c}
    def scale(a, n): return {e: c * n for e, c in a.items() if c * n}
    variables = [{tuple(int(i == j) for i in range(4)): 1} for j in range(4)]
    Z, u, v, w = variables
    Z2, u2, v2, w2 = [mul(p, p) for p in variables]
    V = add(add(add(Z2, w2), u2, -1), v2, -1)
    V2 = mul(V, V)
    W = add(add(V2, scale(mul(Z2, w2), 4)), scale(mul(u2, v2), 4), -1)
    F = add(mul(W, W), scale(mul(mul(V2, Z2), w2), 16), -1)
    product = {zero: 1}
    for signs in itertools.product((-1, 1), repeat=3):
        linear = Z
        for sign, p in zip(signs, (u, v, w)): linear = add(linear, p, sign)
        product = mul(product, linear)
    need(F == product, 'final eight-factor norm identity failed')
    return {'status': 'PASS', 'variables': ['Z', 'u', 'v', 'w'],
            'identity': 'F(Z,u^2,v^2,w^2) = product_(e0,e1,e2 in {-1,1}) (Z+e0*u+e1*v+e2*w)',
            'expanded_terms': len(F), 'degree': max(map(sum, F))}


def main():
    layout = read('data/layout.json'); data = read('data/raw_recipes.json'); body = read('data/polynomial.json')
    parent = json.loads(PARENT.read_text())
    source, kernel = exact_source(layout, data, parent)
    ports, bounds = ports_and_bound(parent)
    controls = []
    for field, index, deltas in [('weights', 2, [1, -1, 2, -2]), ('targets', 1, [1, -1, 2, -2])]:
        rejected = False
        for delta in deltas:
            bad = copy.deepcopy(layout); bad[field][index] += delta
            try: exact_source(bad, data, parent)
            except ValueError as error:
                controls.append({'field': field, 'index': index, 'delta': delta, 'rejected_for': str(error)})
                rejected = True;break
        need(rejected, 'deliberate perturbation was not rejected')
    prime = 1000000007
    fixed = {'beta_source': pow(2, 2140030, prime)}
    for name, terms in data['recipes'].items():
        fixed[name] = sum(term['coefficient'] * math.prod(pow(ports[p], e, prime)
                         for p, e in zip(data['ports'], term['powers'])) for term in terms) % prime
    rng = random.Random(231024)
    checked = 0
    for trial in range(12):
        assignment = {name: rng.randrange(-1000, 1001) for name in body['variables']}
        actual, degrees, leads = evaluate_dag(body, assignment, fixed, prime)
        expected = direct_source(layout, kernel, assignment, ports, prime)
        expected.update(direct_finalizer(assignment, expected, prime))
        for name, value in expected.items():
            need(actual[name] == value, f'literal formula disagrees at {name}, sample {trial}')
            checked += 1
    out = body['output']
    need(leads[out] != 0, 'degree upper-bound coefficient vanished')
    need(degrees[out] == 35876184, 'unexpected final exact degree')
    counts = collections.Counter(node['kind'] for node in body['nodes'] if node['kind'] in ('add', 'sub', 'mul'))
    need(sum(counts.values()) == 640, 'unexpected operation count')
    used = set(); stack = [out]
    while stack:
        i = stack.pop()
        if i in used: continue
        used.add(i);node = body['nodes'][i]
        if 'left' in node: stack.extend([node['left'], node['right']])
    need(len(used) == len(body['nodes']), 'dead DAG nodes are counted')
    source_degrees = {n: degrees[body['named_nodes'][n]] for n in ['X', 'Y', 'Ccap']}
    need(source_degrees == {'X': 34050, 'Y': 22700, 'Ccap': 351}, 'source degree mismatch')
    norm = exact_norm_identity()
    receipt = {'status': 'PASS', 'source_exact_symbolic_audit': source, 'coefficient_bounds': bounds,
               'exact_final_norm_identity': norm,
               'negative_controls': controls, 'literal_formula_controls': {'samples': 12, 'named_values_checked': checked, 'prime': prime},
               'exact_degree_certificate': {'degree': degrees[out], 'diagonal_leading_coefficient_mod_prime': leads[out], 'prime': prime,
                                            'source_degrees': source_degrees, 'method': 'coefficient at propagated upper bound after all variables equal T; nonzero modulo prime'},
               'operations': dict(counts), 'total_operations': sum(counts.values()),
               'scope': 'Exact finite algebra/data certificates and deterministic diagnostic circuit tests, not an unbounded parent-compiler proof.'}
    (ROOT / 'certificates/candidate_independent_audit.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
