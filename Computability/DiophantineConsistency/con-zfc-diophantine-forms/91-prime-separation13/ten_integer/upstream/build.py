#!/usr/bin/env python3
"""Construct three fixed ten-integer equations by triangular polynomial shears.

Python standard library only. The pinned predecessor is inert JSON data;
no predecessor program is executed. No consistency search is performed.
"""
from pathlib import Path
import json
from circuit import Circuit

ROOT = Path(__file__).resolve().parent


def construct(variant):
    old = json.loads((ROOT / 'upstream/integer10.json').read_text())
    d = Circuit()
    ids = []
    for n in old['nodes']:
        kind = n['kind']
        if kind == 'literal':
            v = d.c(n['value'])
        elif kind in ('variable', 'fixed'):
            v = d.leaf(kind, name=n['name'])
        else:
            v = d.op(kind, ids[n['left']], ids[n['right']])
        ids.append(v)
    reg = {name: ids[i] for name, i in old['named_nodes'].items()}
    for name, node in reg.items():
        d.save(name, node)
    v = {n['name']: ids[i] for i, n in enumerate(old['nodes'])
         if n['kind'] == 'variable'}
    add, mul, sub, power, c = d.add, d.mul, d.sub, d.pow, d.c
    h, A, C, xi, G, H = [reg[n] for n in ('halfA', 'A', 'C', 'xi', 'G', 'H')]
    C2 = power(C, 2)
    if variant == 'linear':
        # R = 2 A E G H.
        R = mul(mul(c(2), A), reg['E'], G, H)
        exact_degree = 1179788
    elif variant == 'cubic':
        # The cubic polynomial part of sqrt(D F), multiplied by G H.
        J = sub(reg['D'], mul(c(2), C2))
        P = mul(mul(c(2), A), reg['E0'], J)
        R = mul(P, G, H)
        d.save('root_core', P)
        exact_degree = 1114252
    elif variant == 'sixterm':
        # Six highest h-coefficients of the formal square root of D F I.
        h2 = power(h, 2)
        u = C2
        a = add(mul(u, sub(mul(c(2), h2), c(11))), c(6))
        b = add(sub(mul(c(8), power(h2, 2)), mul(c(52), h2)), c(143))
        b = add(mul(power(u, 2), b), mul(u, sub(mul(c(32), h2), c(176))), c(48))
        J = sub(reg['B1'], C)
        T = add(mul(xi, J, a), mul(c(16), u, power(xi, 2), v['y'], b), mul(c(3), v['y']))
        R = mul(c(32768), power(u, 7), power(xi, 4), power(h, 9),
                sub(mul(sub(h, c(1)), T), mul(c(2), v['y'])))
        exact_degree = 1081125
    else:
        raise ValueError(variant)
    d.save('shear', R)
    shifted_m = d.save('shifted_m', add(v['m'], R))
    center = d.save('shifted_center', sub(mul(reg['Sigma'], shifted_m), reg['Theta']))
    sigma2 = power(reg['Sigma'], 2)
    inner = sub(power(center, 2), mul(sigma2, add(reg['guard'], reg['lucas'])))
    output = sub(power(inner, 2), mul(c(4), power(sigma2, 2), reg['guard'], reg['lucas']))
    body = d.finish(output)
    body.update(
        schema='con-zfc-polynomial-shear-v1', variant=variant, domain='Z',
        variables=old['variables'], exact_degree=exact_degree,
        fixed_recipes=old['fixed_recipes'],
        fixed_coefficients='FIXED_COEFFICIENTS.json',
        predecessor='upstream/integer10.json',
        polynomial_identity='P_new(v,m) = P_old(v,m+R(v))',
        inverse_map='m_new = m_old - R(v)',
        degree_note='degree_upper_bound is the unreduced DAG bound; exact_degree uses the supplied cancellation identities',
        operation_count_convention='Every live binary +,-,* costs one; integer leaves and reuse cost zero',
        proof_boundary='Exact integer-zero-set bijection to the pinned predecessor; its native/compiler/calculus calibration is inherited')
    return body


def main():
    metrics = {}
    for variant in ('linear', 'cubic', 'sixterm'):
        body = construct(variant)
        path = ROOT / ('integer10_' + variant + '.json')
        path.write_text(json.dumps(body, separators=(',', ':')) + '\n')
        metrics[variant] = {k: body[k] for k in ('exact_degree', 'total_operations', 'degree_upper_bound', 'operation_counts')}
    (ROOT / 'METRICS.json').write_text(json.dumps(metrics, indent=2) + '\n')
    print(json.dumps(metrics, indent=2))


if __name__ == '__main__':
    main()
