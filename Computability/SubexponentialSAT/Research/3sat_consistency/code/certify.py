#!/usr/bin/env python3
"""Replay the finite time/space certificate using exact integer arithmetic.

No optimizer, third-party module, network access, or upstream source is used.
The analytic contraction identities and fast matrix algorithms are imported
mathematical dependencies, not claims verified by this finite checker.
"""
from fractions import Fraction as F
from itertools import combinations, permutations
from math import isqrt
from pathlib import Path
import argparse
import json

ROOT = Path(__file__).resolve().parents[1]
TRIPLES = sorted(set(permutations((1400007, 1400007, 0))) |
                 set(permutations((1400000, 1175014, 750000))))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def plan_data(r, blocks):
    require(len(blocks) == 3 and all(blocks), "three nonempty blocks required")
    require(sorted(sum(blocks, [])) == list(range(r)), "invalid ordered partition")
    operations = []
    stored = []
    universe = set(range(r))

    def visit(block):
        if len(block) > 1:
            midpoint = len(block) // 2
            left, right = block[:midpoint], block[midpoint:]
            visit(left)
            visit(right)
            operations.append((left, right, sorted(universe - set(block))))
        stored.append(frozenset(block))

    for block in blocks:
        visit(block)
    operations.append(blocks)
    edges = list(combinations(range(r), 2))
    rows = []
    for parts in operations:
        label = {v: k for k, part in enumerate(parts) for v in part}
        for triple in TRIPLES:
            coeff = dict(zip(((0, 1), (0, 2), (1, 2)), triple))
            rows.append(tuple(0 if label[x] == label[y] else
                              coeff[tuple(sorted((label[x], label[y])))]
                              for x, y in edges))
    boundaries = sorted(set(tuple(int((x in block) != (y in block))
                                  for x, y in edges) for block in stored))
    require(len(operations) == r - 2, "operation count")
    return rows, boundaries, operations


def atan_bounds(inverse, terms=45):
    x = F(1, inverse)
    value = sum(((-1) ** j * x ** (2*j+1) / (2*j+1)
                 for j in range(terms)), F(0))
    adjacent = value + (-1) ** terms * x ** (2*terms+1) / (2*terms+1)
    return min(value, adjacent), max(value, adjacent)


def pi_ln_bounds():
    a, b = atan_bounds(5)
    c, d = atan_bounds(239)
    pi = (16*a - 4*d, 16*b - 4*c)
    terms = 50
    lnlo = 2*sum((F(1, 3) ** (2*j+1) / (2*j+1)
                  for j in range(terms)), F(0))
    remainder = 2*F(1, 3)**(2*terms+1) / ((2*terms+1)*F(8, 9))
    return pi, (lnlo, lnlo+remainder)


def sqrt_bounds(x, digits=28):
    unit = 10 ** digits
    low = isqrt(x.numerator * unit * unit // x.denominator)
    require(F(low*low, unit*unit) <= x < F((low+1)**2, unit*unit),
            "square-root interval failure")
    return F(low, unit), F(low+1, unit)


def coefficient_interval(radicals):
    pi, ln = pi_ln_bounds()
    roots = [sqrt_bounds(x) for x in radicals]
    return (pi[0]/ln[1]*sum(x[0] for x in roots),
            pi[1]/ln[0]*sum(x[1] for x in roots))


def short_interval(interval, digits=16):
    unit = 10**digits
    a, b = interval
    lo = (a.numerator*unit)//a.denominator
    hi = -((-b.numerator*unit)//b.denominator)
    return [str(F(lo, unit)), str(F(hi, unit))]


def check_schedule(beta2):
    eta0, eta1, eta2 = F(301, 20000), F(119, 10000), F(1549, 324000)
    ratio = F(4, 9)
    require(eta0 + eta1 + eta2/(1-ratio) == F(8, 225), "total taper")
    require(10**1000 < 2**3322 and 13**1000 < 2**3701 and 7**100 < 2**281,
            "exact logarithm upper bound")
    gaps = [1-F(9, 10)-2*eta0*F(3322, 1000),
            1-F(9, 10)-(eta0+eta1)*F(3701, 1000),
            1-F(9, 10)-F(8, 225)*F(281, 100)]
    require(gaps == [F(39, 5000000), F(5161, 20000000), F(1, 11250)],
            "packing margins")
    require(min(gaps) > 0 and F(8, 225)*(1+2*F(3701, 1000)) < 1,
            "strict packing gates")
    require(ratio > F(1, 3), "positive taper growth in provisional depth")
    require(F(3, 4) > F(632, 1225), "tail entry branch dominates aggregation")
    C0 = coefficient_interval([2*beta2/eta0])
    C1 = coefficient_interval([F(7200, 301), F(50304, 20111)])
    Cinf = coefficient_interval([F(7200, 301), F(19200, 20111), F(77760, 261781)])
    CS = tuple(F(20, 21)*x for x in C0)
    child_space = [coefficient_interval([2*F(1572, 4225)/(25*eta1)]),
                   coefficient_interval([2*F(632, 1225)*F(4, 4225)/eta2])]
    require(C0[0] > max(C1[1], Cinf[1]), "root time must dominate")
    require(CS[0] > max(x[1] for x in child_space), "root storage must dominate")
    require(C0[1] < F(29747, 1000) and CS[1] < F(28330, 1000),
            "safe eventual coefficient")
    old = coefficient_interval([2*F(15952347164548384057, 49000000000000000000)/eta0])
    require(C0[1] < old[0], "strict old/new comparison")
    return {"root_time": short_interval(C0), "depth_one_time": short_interval(C1),
            "infinite_tail_time": short_interval(Cinf), "space": short_interval(CS),
            "old_time": short_interval(old),
            "child_space": [short_interval(x) for x in child_space],
            "packing_gaps": list(map(str, gaps)),
            "display_only": {"time": float(C0[0]), "space": float(CS[0]),
                             "old_time": float(old[0]),
                             "time_coefficient_reduction_percent": float(100*(1-C0[0]/old[0])),
                             "space_coefficient_reduction_percent": float(100*(1-CS[0]/old[0]))}}


def verify(certificate, expected_receipts=None):
    c = certificate
    r, q, scale, W = c['r'], c['q'], c['support_scale'], c['mixing_denominator']
    require((r, q, scale, W) == (10, 9, 1400000, 100000), "unexpected fixed model")
    weights = c['mixing_weights']
    require(weights == [12527,11761,13353,11841,10132,12324,11088,10184,6790],
            "unexpected fixed mixture")
    require(sum(weights) == W and len(c['plans']) == q, "mixture normalization")
    pair_order = list(combinations(range(q), 2))
    require(c['pairs'] == [list(p) for p in pair_order], "pair ordering")
    denominator = (q-1)*W*W*scale*scale
    P = c['potential_denominator']
    require(P == 10**12 and denominator % P == 0, "potential denominator")
    phi = c['potentials']
    require(set(phi) == {f'{e},{i}' for e,p in enumerate(pair_order) for i in p},
            "potential incidence keys")
    menus, augmented, maps = [], [], []
    for i, plan in enumerate(c['plans']):
        rows, boundaries, _ = plan_data(r, plan)
        require(len(rows) == 72 and len(boundaries) == 17, "support count")
        lookup = {tuple(v): k for k, v in reversed(list(enumerate(rows)))}
        boundary_maps = [lookup[tuple(1400007*x for x in b)] for b in boundaries]
        all_rows = rows + [tuple(1470000*x for x in b) for b in boundaries]
        menus.append(rows)
        augmented.append(all_rows)
        maps.append(list(range(72)) + boundary_maps)
        incident = [e for e, pair in enumerate(pair_order) if i in pair]
        for e in incident:
            require(len(phi[f'{e},{i}']) == 72 and
                    all(type(x) is int for x in phi[f'{e},{i}']), "potential entries")
        for h in maps[-1]:
            require(sum(phi[f'{e},{i}'][h] for e in incident) == 0,
                    "potential conservation")
    norms = [[dot(v, v) for v in menu] for menu in augmented]
    time_sum = 0
    receipts = []
    mixed_margin = None
    for e, (i, j) in enumerate(pair_order):
        wi, wj = weights[i], weights[j]
        pi, pj = phi[f'{e},{i}'], phi[f'{e},{j}']

        def numerator(h, k):
            return (wi*wi*norms[i][h] + wj*wj*norms[j][k]
                    + 2*(q-1)*wi*wj*dot(augmented[i][h], augmented[j][k])
                    + (pi[maps[i][h]] + pj[maps[j][k]])*(denominator//P))

        value, h, k = max((numerator(a, b), a, b)
                          for a in range(72) for b in range(72))
        mixed = max(numerator(a, b) for a in range(89) for b in range(89)
                    if a >= 72 or b >= 72)
        require(mixed <= value, "joint storage support increases time certificate")
        mixed_margin = value-mixed if mixed_margin is None else min(mixed_margin, value-mixed)
        if expected_receipts is not None:
            old = expected_receipts['pair_receipts'][e]
            require(old['pair'] == [i, j] and old['maximum'] == value,
                    "frozen pair receipt differs")
        time_sum += value
        receipts.append({'pair': [i, j], 'maximum': value, 'witness': [h, k],
                         'mixed_maximum': mixed})
    U = F(time_sum, denominator)
    beta2 = 2*U/(r*r)
    require(beta2 == F(c['beta_squared']), "claimed beta squared")
    require(beta2 == F(283611964650596186827, 875000000000000000000),
            "published beta squared")
    return {'status': 'PASS', 'normalization_denominator': denominator,
            'U': str(U), 'beta_squared': str(beta2), 'rho': '21/20',
            'original_conservation_checks': q*72,
            'augmented_conservation_checks': q*89,
            'original_pair_checks': len(pair_order)*72**2,
            'additional_mixed_pair_checks': len(pair_order)*(89**2-72**2),
            'minimum_mixed_numerator_margin': mixed_margin,
            'pair_receipts': receipts, 'schedule': check_schedule(beta2)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path,
                        default=ROOT/'data/support_consistency_certificate.json')
    parser.add_argument('--output', type=Path, default=ROOT/'results/certificate.json')
    args = parser.parse_args()
    c = json.loads(args.certificate.read_text())
    expected = json.loads((ROOT/'data/support_consistency_receipts.json').read_text())
    result = verify(c, expected)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: result[k] for k in ['status', 'beta_squared', 'rho',
                     'original_pair_checks', 'additional_mixed_pair_checks']} |
                     {'schedule': result['schedule']}, indent=2))


if __name__ == '__main__':
    main()
