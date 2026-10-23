#!/usr/bin/env python3
"""Build an explicit ten-integer consistency polynomial using B_4 positions.

Source: ProveIt package 31, pinned in upstream/SOURCE31_MANIFEST.json.
The new part is coefficient coding on a Bose--Chowla set.  The downstream
Sun bridge and the structural quintic finalizer are unchanged formulas.
Only standard Python is required.  Fixed powers become binary multiplications.
"""
from pathlib import Path
from functools import lru_cache
import json
import sys

ROOT = Path(__file__).resolve().parents[1]
UPSTREAM = ROOT / 'upstream/source31/signed10'
sys.path.insert(0, str(UPSTREAM))
from circuit import DAG, canonical_keys
from build_signed10 import quadratic_norm, geometric_pair, BETA_EXPONENT, VARIABLES
from shared_powers import power_map


def coding_blocks(d, base, weights, keys):
    """D(B)=sum c_alpha B^(4W-alpha.w), by a homogeneous Horner scheme."""
    A, M, P, c = d.plus, d.times, d.power, d.const
    W = weights[-1]
    powers = power_map(d, base, weights)
    top = powers[W]
    complements = [top] + [powers[W - w] for w in weights[1:]]
    terms = []
    for alpha, name in keys:
        assert alpha[0] == 0
        exponents = (4 - sum(alpha),) + tuple(alpha[1:])
        coefficient = c(name) if isinstance(name, int) else d.fixed(name)
        terms.append((exponents, coefficient))

    @lru_cache(None)
    def horner(ts):
        if not ts:
            return c(0)
        counts = [sum(ex[j] > 0 for ex, co in ts) for j in range(len(complements))]
        if not max(counts):
            return A(*(co for ex, co in ts))
        j = max(range(len(complements)),
                key=lambda j: (counts[j], sum(ex[j] for ex, co in ts), j))
        yes, no = [], []
        for ex, co in ts:
            if ex[j]:
                ex = list(ex)
                ex[j] -= 1
                yes.append((tuple(ex), co))
            else:
                no.append((ex, co))
        return A(horner(tuple(no)), M(complements[j], horner(tuple(yes))))

    Dcode = horner(tuple(terms))
    ell = A(*(powers[w] for w in weights[1:]))
    return P(top, 4), ell, Dcode, top


def construct(literal_sun=False):
    constants = json.loads((UPSTREAM / 'data/constants.json').read_text())
    certificate = json.loads((ROOT / 'data/weights_certificate.json').read_text())
    weights, Wmax = certificate['weights'], certificate['maximum']
    assert len(weights) == 32 and constants['nu'] == 31
    keys, aliases = canonical_keys(constants)
    d = DAG()
    A, M, S, P, c = d.plus, d.times, d.minus, d.power, d.const
    v = {name: d.var(name) for name in VARIABLES}

    # New B_4 source code: reversal target 4W, padding through 8W.
    b = d.save('b', A(c(1), M(c(3), v['f'])))
    base = d.save('base', M(d.fixed('beta_sun'), P(b, 4)))
    qcode, ell, Dcode, top = coding_blocks(d, base, weights, keys)
    for name, value in [('qcode', qcode), ('ell', ell), ('Dcode', Dcode), ('top', top)]:
        d.save(name, value)
    N0 = d.save('N0', M(top, base))
    N1 = d.save('N1', M(c(4), P(top, 8), base))
    N = d.save('N', M(N0, N1))
    mask = d.save('Mcode', S(S(N0, c(1)), M(S(b, c(1)), ell)))
    Tcode = d.save('Tcode', A(mask, M(S(base, c(2)), qcode, N0)))
    _, geosum = geometric_pair(d, base, 8 * Wmax + 1)
    Jcode = d.save('Jcode', A(M(c(2), P(A(c(1), v['g']), 4), Dcode), M(base, geosum)))
    Scode = d.save('Scode', A(v['g'], M(Jcode, N0)))
    Rcode = d.save('Rcode', A(M(A(Scode, Tcode, c(1)), N), Tcode, c(1)))
    X = d.save('X', M(S(N, c(1)), Rcode))
    Y = d.save('Y', P(N, 2))
    cap = d.save('Ccap', M(b, top))

    # Sun's binomial/Lucas bridge (upstream formulas, unchanged).
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
    xi = d.save('xi', M(v['z'], v['x']))
    D = d.save('D', A(M(S(P(AA, 2), c(4)), P(C, 2)), c(4)))
    E = d.save('E', M(P(C, 2), D, xi))
    F = d.save('F', A(M(c(4), S(P(AA, 2), c(4)), P(E, 2)), c(1)))
    Gstar = d.save('Gstar', S(M(c(2), A(AA, c(2)), P(S(AA, c(2)), 2), P(E, 2)), c(1)))
    Omega = d.save('Omega', M(c(16), E))
    Hstar = d.save('Hstar', A(C, M(S(BB, C), F), M(Omega, F, v['y'])))
    Istar = d.save('Istar', A(M(S(P(Gstar, 2), c(1)), P(Hstar, 2)), c(1)))

    merger_degree = 6 if literal_sun else 5
    Sigma = d.save('Sigma', M(xi, P(SS, merger_degree)))
    r = d.save('merger_argument', A(TT, M(SS, v['y'])))
    SS2 = P(SS, 2)
    if literal_sun:
        Theta = M(*(S(P(r, 2), M(c(gamma), SS2)) for gamma in (13, 17, 221)))
        radicands = [b, A(M(S(M(c(3), O0), c(4)), P(v['z'], 2)), c(1)),
                     M(D, F, Istar), R2]
        weight = d.save('norm_weight', A(c(1), *(P(value, 2) for value in radicands)))
        norm_weights = [P(weight, j) for j in range(4)]
    else:
        Theta = M(S(S(P(r, 3), M(r, SS2)), M(SS2, SS)), A(P(r, 2), M(c(23), SS2)))
        bracket = d.save('positivity_bracket', A(c(1), M(S(M(c(3), O0), c(4)), P(b, 2), P(v['z'], 2))))
        radicands = [M(b, bracket), R2, M(D, F, Istar)]
        weight1 = d.save('norm_weight1', radicands[0])
        weight2 = d.save('norm_weight2', M(weight1, A(P(Pn, 2), P(K, 2), c(3))))
        norm_weights = [c(1), weight1, weight2]
    d.save('Theta', Theta)
    for j, value in enumerate(radicands, 1):
        d.save('A' + str(j), value)
    center = d.save('norm_center', S(M(Sigma, v['m']), Theta))
    Sigma2 = P(Sigma, 2)
    scaled = [d.save('scaled_A' + str(j + 1), M(Sigma2, P(norm_weights[j], 2), value))
              for j, value in enumerate(radicands)]
    out = d.save('F10', quadratic_norm(d, center, scaled))
    nodes, output, names = d.prune(out)
    variables = [n['name'] for n in nodes if n['kind'] == 'variable']
    assert variables == VARIABLES
    degree = []
    for node in nodes:
        if node['kind'] == 'variable':
            degree.append(1)
        elif node['kind'] in ('fixed', 'literal'):
            degree.append(0)
        else:
            aa, bb = degree[node['left']], degree[node['right']]
            degree.append(aa + bb if node['kind'] == 'mul' else max(aa, bb))
    return {
        'schema': 'proveit-bose-chowla10-v1', 'domain': 'unrestricted integers',
        'variables': variables, 'source_variables': 31, 'source_degree': 4,
        'weights': weights, 'W': Wmax, 'reversal_target': 4 * Wmax,
        'convolution_top': 8 * Wmax, 'literal_sun_finalizer': literal_sun,
        'nodes': nodes, 'output': output, 'named_nodes': names,
        'operation_counts': {k: sum(n['kind'] == k for n in nodes) for k in ('add', 'sub', 'mul')},
        'degree_upper_bound': degree[output],
        'named_degree_upper_bounds': {name: degree[i] for name, i in names.items()},
        'fixed_binding': '../data/INSTANCE.json',
        'attribution': 'Bose--Chowla weights; Sun 2021/2026; ProveIt package31 parent and finalizer.',
        'counting': 'Binary additions/subtractions/multiplications count; constant leaves and reuse free.',
    }, aliases


def main():
    out = ROOT / 'generated'
    out.mkdir(exist_ok=True)
    summaries = []
    for literal_sun, filename in [(False, 'equation10.json'), (True, 'equation10_sun_finalizer.json')]:
        body, aliases = construct(literal_sun)
        (out / filename).write_text(json.dumps(body, separators=(',', ':')) + '\n')
        summary = {'file': filename, 'unknowns': len(body['variables']), 'W': body['W'],
                   'degree_upper_bound': body['degree_upper_bound'],
                   'operations': sum(body['operation_counts'].values()),
                   'operation_counts': body['operation_counts'],
                   'fixed_leaves': sum(n['kind'] == 'fixed' for n in body['nodes'])}
        summaries.append(summary)
        print(json.dumps(summary))
    (out / 'coefficient_aliases.json').write_text(json.dumps(aliases, indent=2) + '\n')
    (out / 'metrics.json').write_text(json.dumps(summaries, indent=2) + '\n')


if __name__ == '__main__':
    main()
