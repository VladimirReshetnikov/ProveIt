#!/usr/bin/env python3
"""Independent signed-quotient checker; never imports the generator.

Checks source privacy and natural restoration, then applies an independently
defined polynomial section to every source residual.  Exact full expansion
and degree/height/liveness checks follow.  Explicit failures remain active -O.
"""
from collections import defaultdict
from hashlib import sha256
import argparse
from copy import deepcopy
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent


def need(condition, message):
    if not condition:
        raise ValueError(message)


def polynomial(terms):
    result = defaultdict(int)
    for coefficient, monomial in terms:
        need(type(coefficient) is int and coefficient and monomial == sorted(monomial),
             'noncanonical coefficient/monomial')
        result[tuple(monomial)] += coefficient
    need(len(result) == len(terms) and all(result.values()), 'duplicate monomial')
    return dict(result)


def add(a, b):
    out = defaultdict(int, a)
    for m, c in b.items():
        out[m] += c
    return {m: c for m, c in out.items() if c}


def scale(p, c):
    return {m: c*v for m, v in p.items() if c*v}


def multiply(a, b):
    out = defaultdict(int)
    for ma, ca in a.items():
        for mb, cb in b.items():
            out[tuple(sorted(ma+mb))] += ca*cb
    return {m: c for m, c in out.items() if c}


def substitute(p, environment):
    result = {}
    for m, c in p.items():
        term = {(): c}
        for i in m:
            term = multiply(term, environment[i])
        result = add(result, term)
    return result


def audit(parent, equation, expanded, certificate):
    pv, pr = parent['variables'], parent['residuals']
    ev, er = equation['variables'], equation['residuals']
    source_rows = [polynomial(row['terms']) for row in pr]
    use = defaultdict(set)
    for j, row in enumerate(source_rows):
        for i in {i for m in row for i in m}:
            need(0 <= i < len(pv), 'source variable index')
            use[i].add(j)
    retained = certificate['retained_old_variables']
    row_ids = certificate['retained_old_rows']
    nc, nr = certificate['core_variable_count'], certificate['core_row_count']
    need(retained == sorted(set(retained)) and row_ids == sorted(set(row_ids)), 'ordered injective maps')
    need(len(retained) == nc and len(row_ids) == nr, 'certificate dimensions')
    new_index = {old: new for new, old in enumerate(retained)}
    section = {old: {(new,): 1} for old, new in new_index.items()}
    deleted_variables, deleted_rows, quotient_seeds = set(), set(), set()
    pair_data = certificate['signed_quotient_eliminations']
    bridges = certificate['affine_wire_eliminations']
    bridge_outputs = {b['variable'] for b in bridges}
    need(len(pair_data) == 221 and len(bridges) in (2, 442), 'expected private patterns')

    for item in pair_data:
        p, q = item['plus'], item['minus']
        u, v = item['products']
        ru, rv = item['definition_rows']
        final = item['use_row']
        factor = polynomial(item['factor'])
        need(item['orientation'] in (-1, 1), 'unit congruence orientation')
        need(p in new_index and q not in new_index and u not in new_index and v not in new_index,
             'private variable deletion map')
        need(pv[p]['name'].replace('.qp.', '.qm.') == pv[q]['name'], 'quotient metadata pair')
        need(ev[new_index[p]] == {'name': pv[p]['name'].replace('.qp.', '.signed.'),
                                 'kind': 'signed_quotient'}, 'signed coordinate metadata')
        need(use[p] == {ru} and use[q] == {rv}, 'quotient is not private')
        need(all(c > 0 and len(m) <= 1 for m, c in factor.items()), 'modulus is not natural affine')
        need(source_rows[ru] == add({(u,): 1}, scale(multiply(factor, {(p,): 1}), -1)),
             'plus product identity')
        need(source_rows[rv] == add({(v,): 1}, scale(multiply(factor, {(q,): 1}), -1)),
             'minus product identity')
        need(len(use[u]-{ru}) == len(use[v]-{rv}) == 1, 'product privacy')
        for output, defining in ((u, ru), (v, rv)):
            actual_use = next(iter(use[output]-{defining}))
            need(actual_use == final or any(b['definition_row'] == actual_use and b['use_row'] == final
                                           for b in bridges), 'product path to final residual')
        # The free signed section q=0,p=z is enough for the exact polynomial
        # comparison below; order-preserving lifting uses positive/negative parts.
        section[q] = {}
        need(all(i in section for m in factor for i in m), 'modulus contains a deleted coordinate')
        section[u] = multiply(substitute(factor, section), section[p])
        section[v] = {}
        deleted_variables.update((q, u, v)); deleted_rows.update((ru, rv)); quotient_seeds.add(p)

    for item in bridges:
        g, dr, ur = item['variable'], item['definition_row'], item['use_row']
        rhs = polynomial(item['rhs'])
        need(pv[g]['kind'] == 'gate' and pr[dr]['label'] == 'addition', 'affine gate metadata')
        need(use[g] == {dr, ur} and all(c > 0 and len(m) <= 1 for m, c in rhs.items()),
             'private nonnegative affine bridge')
        need(source_rows[dr] == add({(g,): 1}, scale(rhs, -1)), 'affine definition identity')
        need(all(i in section for m in rhs for i in m), 'affine bridge dependency')
        section[g] = substitute(rhs, section)
        deleted_variables.add(g); deleted_rows.add(dr)

    need(set(retained) | deleted_variables == set(range(len(pv)))
         and not (set(retained) & deleted_variables), 'complete variable partition')
    need(set(row_ids) | deleted_rows == set(range(len(pr)))
         and not (set(row_ids) & deleted_rows), 'complete residual partition')

    # Check both coefficients of each quotient product after expanding its
    # private affine bridge, so the section cannot hide an asymmetric pair.
    bridge_environment = {i: {(i,): 1} for i in range(len(pv))}
    for b in bridges:
        bridge_environment[b['variable']] = polynomial(b['rhs'])
    for item in pair_data:
        r = substitute(source_rows[item['use_row']], bridge_environment)
        u, v = item['products']; epsilon = item['orientation']
        need(r.get((u,)) == epsilon and r.get((v,)) == -epsilon, 'opposite quotient coefficients')
        need(all((u not in m or m == (u,)) and (v not in m or m == (v,)) for m in r),
             'linear quotient-product use')

    expected_core = [(pr[j]['label'], substitute(source_rows[j], section)) for j in row_ids]
    actual_core = [(row['label'], polynomial(row['terms'])) for row in er[:nr]]
    need(actual_core == expected_core, 'entire transformed core polynomial identity')
    need(all(not substitute(source_rows[j], section) for j in deleted_rows),
         'deleted defining residual not identically zero under section')

    signed = {i for i, meta in enumerate(ev[:nc]) if meta['kind'] == 'signed_quotient'}
    need(signed == {new_index[i] for i in quotient_seeds}, 'complete signed coordinate set')
    for old, new in new_index.items():
        if old not in quotient_seeds:
            need(ev[new] == pv[old], 'retained metadata altered')
    gate_set = {i for i, meta in enumerate(ev[:nc]) if meta['kind'] == 'gate'}
    gate_seen = set()
    for row in er[:nr]:
        if row['label'] not in ('addition', 'multiplication'):
            continue
        p = polynomial(row['terms'])
        positive = [(m, c) for m, c in p.items() if c > 0]
        need(len(positive) == 1 and positive[0][1] == 1 and len(positive[0][0]) == 1,
             'unique monic gate')
        out = positive[0][0][0]
        need(out in gate_set and out not in gate_seen, 'unique gate output')
        need(all(m == (out,) or c < 0 and all(i < out and i not in signed for i in m)
                 for m, c in p.items()), 'natural topological gate restoration')
        gate_seen.add(out)
    need(gate_seen == gate_set, 'complete gate restoration')

    semantics = {i for i, meta in enumerate(ev[:nc]) if meta['kind'] in ('outer', 'witness')}
    guards = equation['natural_input_guards']
    need({g['input'] for g in guards} == semantics and len(guards) == len(semantics),
         'complete natural guard coverage')
    need(len(er) == nr+len(guards), 'extra or missing guards')
    auxiliary = set()
    for g, row in zip(guards, er[nr:]):
        i = g['input']; a, b, c = g['auxiliaries']
        need(len({a,b,c}) == 3 and min(a,b,c) >= nc and not (auxiliary & {a,b,c}), 'fresh guard inputs')
        auxiliary.update((a,b,c))
        need(polynomial(row['terms']) == {(i,): 1, (a,a): -1, (b,b): -1, (c,c): -1, (c,): -1},
             'three-square guard identity')
    need(auxiliary == set(range(nc, len(ev))), 'complete auxiliary coordinate set')
    out = {}
    for row in er:
        p = polynomial(row['terms'])
        need(all(len(m) <= 2 and all(0 <= i < len(ev) for i in m) for m in p),
             'literal quadratic residual schema')
        out = add(out, multiply(p,p))
    need(out == polynomial(expanded['terms']), 'complete expanded polynomial identity')
    need({i for m in out for i in m} == set(range(len(ev))), 'all coordinates live')
    result = {'variables': len(ev), 'rows': len(er), 'expanded_terms': len(out),
              'degree': max(map(len,out)), 'height': max(map(abs,out.values())),
              'signed_quotient_pairs': len(pair_data), 'affine_bridges': len(bridges),
              'natural_inputs_guarded': len(semantics), 'natural_gates_restored': len(gate_set),
              'all_source_rows_checked': len(pr)}
    need(result['degree'] == 4 and out[(len(ev)-1,)*4] == 1, 'degree-four witness')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--retained', action='store_true')
    args = parser.parse_args()
    directory = HERE/('retained_candidate' if args.retained else 'candidate')
    parent_path = HERE/('source/retained/equation.json' if args.retained else 'source/natural_equation.json')
    raw = parent_path.read_bytes()
    expected = ('39b3e264c05180c5d1f9028c48c4a28544d5c7641ce7d6d38fae430414ecf710' if args.retained else
                'e851ff1d420a39be069e63f6f117557356c38e6d8272a481258fe38cb38dc6ea')
    need(sha256(raw).hexdigest() == expected, 'source pin')
    parent = json.loads(raw)
    equation = json.loads((directory/'equation.json').read_text())
    expanded = json.loads((directory/'expanded_polynomial.json').read_text())
    certificate = json.loads((directory/'transformation_certificate.json').read_text())
    need(equation['parent_natural_sha256'] == certificate['parent_natural_sha256'] == expected,
         'certificate parent pin')
    metrics = audit(parent,equation,expanded,certificate)
    # Operation/size-preserving corruption: reverse the sign of one quotient
    # monomial in the transformed core while leaving all metadata untouched.
    bad = deepcopy(equation)
    q = next(i for i,v in enumerate(bad['variables']) if v['kind'] == 'signed_quotient')
    changed = False
    for row in bad['residuals']:
        for term in row['terms']:
            if q in term[1]:
                term[0] *= -1; changed = True; break
        if changed: break
    need(changed, 'mutation target')
    rejected = False
    try:
        audit(parent,bad,expanded,certificate)
    except ValueError:
        rejected = True
    need(rejected, 'sign corruption escaped independent check')
    receipt = {'status':'PASS', 'python_optimization':sys.flags.optimize,
               'metrics':metrics, 'entire_source_substitution_verified': True,
               'same_size_signed_quotient_corruption_rejected': True,
               'sha256':{name:sha256((directory/name).read_bytes()).hexdigest()
                         for name in ('equation.json','expanded_polynomial.json','transformation_certificate.json')},
               'scope':'Exact full source transformation, natural restoration, guard coverage, and quartic coefficients; no consistency decision.'}
    output = directory/('CHECK_OPTIMIZED.json' if sys.flags.optimize else 'CHECK.json')
    output.write_text(json.dumps(receipt, indent=2, sort_keys=True)+'\n')
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
