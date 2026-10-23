#!/usr/bin/env python3
"""Ten-integer Con(ZFC) equation with Bose-Chowla quartic coding.

Source: package31 build_signed10.py, pinned in SOURCE_PINS.json.
The source-code block is replaced by the proved B4 adapter; bridge and
finalizer formulas retain their original attribution.

The primary circuit merges two square conditions and uses the degree-five
intersective polynomial (v^3-v-1)(v^2+23).  A four-square degree-six variant
reproduces Sun 2026 (7.3).
All powers are fixed positive integer powers, expanded into binary gates.
The output is a division-free integer polynomial, with ten variable leaves.
"""
from pathlib import Path
from functools import lru_cache
import json
from circuit import DAG, canonical_keys
from b4_code import coding_blocks_b4

ROOT = Path(__file__).resolve().parent
VARIABLES = ['f', 'g', 'h', 'k', 'l', 'w', 'x', 'y', 'z', 'm']
BETA_EXPONENT = 4269882


def geometric_pair(d, base, n):
    """Return (base^n, sum(base^i, 0<=i<n)) without division."""
    assert n >= 0
    if n == 0:
        return d.const(1), d.const(0)
    if n == 1:
        return base, d.const(1)
    power, total = geometric_pair(d, base, n // 2)
    power2 = d.times(power, power)
    total2 = d.times(total, d.plus(d.const(1), power))
    if n % 2:
        return d.times(power2, base), d.plus(total2, power2)
    return power2, total2


def quadratic_norm(d, X, radicands):
    """Product over all signs of X + sum(sign_i sqrt(radicand_i)).

    Operate in a free rank-2^k algebra with formal r_i^2=radicand_i.
    At each step write an element A+r_i B and replace it by A^2-a_i B^2.
    Exactly k steps leave a scalar. No radicals occur in the emitted circuit.
    """
    count = len(radicands)
    if count == 3:
        # Collected form of the three quadratic norms (35 expanded terms).
        # The verifier proves this identity against all eight signed factors.
        a0, a1, a2 = radicands
        x2 = d.times(X, X)
        v = d.minus(d.minus(d.plus(x2, a2), a0), a1)
        v2 = d.times(v, v)
        four_xa = d.times(d.const(4), x2, a2)
        w = d.minus(d.plus(v2, four_xa), d.times(d.const(4), a0, a1))
        return d.minus(d.times(w, w), d.times(d.const(4), v2, four_xa))
    def ring_square(a):
        result = {}
        items = sorted(a.items())
        for ii, (mask, value) in enumerate(items):
            for jj in range(ii, len(items)):
                mask2, value2 = items[jj]
                term = d.times(value, value2)
                overlap = mask & mask2
                for k in range(count):
                    if overlap & (1 << k):
                        term = d.times(term, radicands[k])
                if ii != jj:
                    term = d.times(d.const(2), term)
                key = mask ^ mask2
                result[key] = d.plus(result.get(key, d.const(0)), term)
        return result

    element = {0: X, **{1 << i: d.const(1) for i in range(count)}}
    for i, radicand in enumerate(radicands):
        bit = 1 << i
        a = {mask: value for mask, value in element.items() if not mask & bit}
        b = {mask ^ bit: value for mask, value in element.items() if mask & bit}
        aa, bb = ring_square(a), ring_square(b)
        element = {}
        for mask in sorted(aa.keys() | bb.keys()):
            value = d.minus(aa.get(mask, d.const(0)),
                            d.times(radicand, bb.get(mask, d.const(0))))
            if d.known.get(value) != 0:
                element[mask] = value
    assert set(element) == {0}
    return element[0]


def construct(merger_degree=5, merged_positivity=True, weight_scheme='structural'):
    assert merger_degree in (5, 6)
    assert weight_scheme in ('structural', 'universal', 'sun')
    adaptive_weights = weight_scheme != 'sun'
    assert not adaptive_weights or merged_positivity
    constants = json.loads((ROOT / 'data/constants.json').read_text())
    nu = constants['nu']
    assert nu == 31
    code = json.loads((ROOT / 'bose_chowla32.json').read_text())
    t = code['max_weight']
    Lcode = 4*t
    keys, aliases = canonical_keys(constants)
    d = DAG()
    A, M, S, P, c = d.plus, d.times, d.minus, d.power, d.const
    v = {name: d.var(name) for name in VARIABLES}

    # Sun 2021, proof of Theorem 3.1, specialized to a=0,p=2,delta=4.
    b = d.save('b', A(c(1), M(c(3), v['f'])))
    base = d.save('base', M(d.fixed('beta_sun'), P(b, 4)))
    qcode, ell, Dcode, top = coding_blocks_b4(d, base, code['weights'][1:], keys)
    for name, value in [('qcode', qcode), ('ell', ell), ('Dcode', Dcode), ('top', top)]:
        d.save(name, value)
    N0 = d.save('N0', M(top, base))
    N1 = d.save('N1', M(c(4), P(top, 8), base))
    N = d.save('N', M(N0, N1))
    mask = d.save('Mcode', S(S(N0, c(1)), M(S(b, c(1)), ell)))
    Tcode = d.save('Tcode', A(mask, M(S(base, c(2)), qcode, N0)))
    _, geosum = geometric_pair(d, base, 8 * t + 1)
    Jcode = d.save('Jcode', A(M(c(2), P(A(c(1), v['g']), 4), Dcode), M(base, geosum)))
    Scode = d.save('Scode', A(v['g'], M(Jcode, N0)))
    Rcode = d.save('Rcode', A(M(A(Scode, Tcode, c(1)), N), Tcode, c(1)))
    X = d.save('X', M(S(N, c(1)), Rcode))
    Y = d.save('Y', P(N, 2))
    cap = d.save('Ccap', M(b, top))

    # Sun 2026, (6.1)--(6.7).
    L = d.save('Lsmall', M(v['l'], Y))
    U = d.save('U', M(c(2), L, X))
    V = d.save('V', M(c(4), v['g'], v['w'], Y))
    W = d.save('Wsmall', M(b, v['w']))
    AA = d.save('A', M(U, A(V, c(1))))
    BB = d.save('Bsmall', A(M(c(2), X), c(1)))
    C = d.save('C', A(BB, M(S(AA, c(2)), v['h'])))
    Pn = d.save('Pn', M(P(U, 2), V))
    K = d.save('K', A(X, c(1), M(v['k'], S(Pn, c(2)))))
    SS = d.save('Ssmall', S(M(c(2), AA), c(5)))
    TT = d.save('Tsmall', S(M(c(3), W, C), M(c(2), S(P(W, 2), c(1)))))
    R2 = d.save('R2', A(M(S(P(Pn, 2), c(4)), P(K, 2)), c(4)))
    cap3 = P(cap, 3)
    Delta = d.save('Delta', S(M(c(8), cap3, v['g'], P(K, 2)),
                            M(P(v['g'], 2), A(M(c(32), P(S(C, M(K, L)), 2), cap3),
                                               M(P(v['g'], 2), P(K, 2))))))
    O0 = d.save('O0', M(P(v['f'], 2), P(v['l'], 2), Delta))

    # Sun 2026, (3.1)--(3.7) and (7.1).
    xi = d.save('xi', M(v['z'], v['x']))
    D = d.save('D', A(M(S(P(AA, 2), c(4)), P(C, 2)), c(4)))
    E = d.save('E', M(P(C, 2), D, xi))
    F = d.save('F', A(M(c(4), S(P(AA, 2), c(4)), P(E, 2)), c(1)))
    Gstar = d.save('Gstar', S(M(c(2), A(AA, c(2)), P(S(AA, c(2)), 2), P(E, 2)), c(1)))
    Omega = d.save('Omega', M(c(16), E))
    Hstar = d.save('Hstar', A(C, M(S(BB, C), F), M(Omega, F, v['y'])))
    Istar = d.save('Istar', A(M(S(P(Gstar, 2), c(1)), P(Hstar, 2)), c(1)))

    Sigma = d.save('Sigma', M(xi, P(SS, merger_degree)))
    r = d.save('merger_argument', A(TT, M(SS, v['y'])))
    SS2 = P(SS, 2)
    if merger_degree == 5:
        Theta = M(S(S(P(r, 3), M(r, SS2)), M(SS2, SS)), A(P(r, 2), M(c(23), SS2)))
    else:
        Theta = M(*(S(P(r, 2), M(c(gamma), SS2)) for gamma in (13, 17, 221)))
    d.save('Theta', Theta)

    # H_k of Sun 2021 (5.4), represented as exact quadratic norms.
    positivity_discriminant = S(M(c(3), O0), c(4))
    if merged_positivity:
        bracket = d.save('positivity_bracket', A(c(1), M(positivity_discriminant, P(b, 2), P(v['z'], 2))))
        radicands = [M(b, bracket), R2, M(D, F, Istar)] if adaptive_weights else [M(b, bracket), M(D, F, Istar), R2]
    else:
        radicands = [b, A(M(positivity_discriminant, P(v['z'], 2)), c(1)), M(D, F, Istar), R2]
    for j, value in enumerate(radicands, 1):
        d.save('A' + str(j), value)
    if weight_scheme == 'structural':
        weight1 = d.save('norm_weight1', radicands[0])
        weight2 = d.save('norm_weight2', M(weight1, A(P(Pn, 2), P(K, 2), c(3))))
        weights = [c(1), weight1, weight2]
    elif adaptive_weights:
        weight1 = d.save('norm_weight1', A(c(1), P(radicands[0], 2)))
        weight2 = d.save('norm_weight2', M(weight1, A(c(1), P(radicands[1], 2))))
        weights = [c(1), weight1, weight2]
    else:
        weight = d.save('norm_weight', A(c(1), *(P(value, 2) for value in radicands)))
        weights = [P(weight, j) for j in range(len(radicands))]
    center = d.save('norm_center', S(M(Sigma, v['m']), Theta))
    Sigma2 = P(Sigma, 2)
    scaled = [d.save('scaled_A' + str(j + 1), M(Sigma2, P(weights[j], 2), value))
              for j, value in enumerate(radicands)]
    out = d.save('F10', quadratic_norm(d, center, scaled))
    nodes, output, names = d.prune(out)
    variables = [n['name'] for n in nodes if n['kind'] == 'variable']
    assert variables == VARIABLES and len(variables) == 10
    degree = []
    for node in nodes:
        if node['kind'] == 'variable':
            degree.append(1)
        elif node['kind'] in ('fixed', 'literal'):
            degree.append(0)
        else:
            a, bdeg = degree[node['left']], degree[node['right']]
            degree.append(a + bdeg if node['kind'] == 'mul' else max(a, bdeg))
    body = {
        'schema': 'proveit-b4-signed10-v1', 'domain': 'unrestricted integers',
        'variables': variables, 'nu': nu, 't': t, 'Lcode': Lcode,
        'merger_degree': merger_degree, 'norm_radicands': len(radicands),
        'merged_positivity': merged_positivity, 'adaptive_weights': adaptive_weights,
        'weight_scheme': weight_scheme,
        'nodes': nodes, 'output': output,
        'named_nodes': names,
        'operation_counts': {kind: sum(n['kind'] == kind for n in nodes) for kind in ['add', 'sub', 'mul']},
        'degree_upper_bound': degree[output],
        'degree_upper_bound_formula': 'Exact integer upper bound in degree_upper_bound; B4 max weight T=942302',
        'coding': 'Bose-Chowla 32-element B4 code, zero element reserved for homogenization; 31 polynomial witnesses',
        'named_degree_upper_bounds': {name: degree[i] for name, i in names.items()},
        'fixed_binding': 'data/INSTANCE.json', 'proof': 'PROOF.md',
        'counting': 'Each binary +,-,* is one operation; constant leaves and reuse free; all fixed powers expanded.',
        'attribution': 'B4 source adapter in PROOF.md; adapted from package31 at 22e75dd6b87b1b199bb08c778d7cf075ae5aae08. Sun 2021 Theorem 3.1 and (5.4); Sun 2026 (6.1)--(7.3); local coprime positivity merge and quintic merger when selected.',
    }
    return body, aliases


def main():
    out = ROOT / 'generated'
    out.mkdir(exist_ok=True)
    for merger, merged, scheme, filename in [(5, True, 'structural', 'b4_signed10.json'),
                                             (5, True, 'universal', 'b4_signed10_universal_weights.json'),
                                             (5, True, 'sun', 'b4_signed10_h3quintic.json'),
                                             (5, False, 'sun', 'b4_signed10_h4quintic.json'),
                                             (6, False, 'sun', 'b4_signed10_sun6.json')]:
        body, aliases = construct(merger, merged, scheme)
        (out / filename).write_text(json.dumps(body, separators=(',', ':')) + '\n')
        print(json.dumps({'file': filename, 'variables': len(body['variables']),
                          'degree_upper_bound': body['degree_upper_bound'],
                          'operations': body['operation_counts'],
                          'total_operations': sum(body['operation_counts'].values()),
                          'fixed_leaves': sum(n['kind'] == 'fixed' for n in body['nodes'])}))
    (out / 'coefficient_aliases.json').write_text(json.dumps(aliases, indent=2) + '\n')


if __name__ == '__main__':
    main()

