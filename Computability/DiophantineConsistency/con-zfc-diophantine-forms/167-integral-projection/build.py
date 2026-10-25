#!/usr/bin/env python3
"""Rebuild the explicit quartic from the exact pooled225 input and certificate.

Python standard library only. This program replays finite integer-polynomial
identities; it does not search for a zero or enumerate a consistency proof.
"""
from collections import defaultdict
from pathlib import Path
import copy
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def canonical(obj):
    return (json.dumps(obj, sort_keys=True, separators=(',', ':')) + '\n').encode()


def digest(obj):
    return hashlib.sha256(canonical(obj)).hexdigest()


def mathematical_digest(eq):
    return digest({'variables': len(eq['variables']),
                   'residuals': [terms(poly(r['terms'])) for r in eq['residuals']]})


def poly(terms):
    out = defaultdict(int)
    for c, m in terms:
        out[tuple(sorted(m))] += c
    return {m: c for m, c in out.items() if c}


def terms(p):
    return [[c, list(m)] for m, c in sorted(p.items()) if c]


def add(p, q, a=1):
    out = dict(p)
    for m, c in q.items():
        out[m] = out.get(m, 0) + a*c
        if not out[m]:
            del out[m]
    return out


def mul(p, q):
    out = defaultdict(int)
    for m, c in p.items():
        for n, d in q.items():
            out[tuple(sorted(m+n))] += c*d
    return {m: c for m, c in out.items() if c}


def substitute(p, mapping):
    out = {}
    for m, c in p.items():
        term = {(): c}
        for i in m:
            term = mul(term, mapping.get(i, {(i,): 1}))
        out = add(out, term)
    return out


def delete_coordinate(p, coordinate):
    if any(coordinate in m for m in p):
        raise ValueError('Deleted coordinate still occurs')
    return {tuple(i-(i > coordinate) for i in m): c for m, c in p.items()}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def replay(equation, certificate, *, check_hashes=True, stage_callback=None):
    eq = copy.deepcopy(equation)
    for number, step in enumerate(certificate['steps']):
        before_hash, before_math = digest(eq), mathematical_digest(eq)
        if check_hashes:
            require(before_hash == step['input_sha256'], 'Canonical input hash mismatch')
            require(before_math == step['input_mathematical_sha256'], 'Mathematical input hash mismatch')
        kind = step['kind']
        if kind == 'radical':
            n = len(eq['variables'])
            p, rid = step['pivot'], step['deleted_row']
            d = dict(step['direction'])
            require(d.get(p) == 1, 'Nonunit radical pivot')
            shear = {i: {(i,): 1, (p,): a} for i, a in d.items() if i != p}
            rows = [substitute(poly(r['terms']), shear) for r in eq['residuals']]
            require(all(not (len(m)>1 and p in m) for r in rows for m in r), 'Direction not in common radical')
            a = rows[rid].get((p,), 0)
            require(abs(a) == 1, 'Nonunit radical slope')
            solved = {m: -a*c for m, c in rows[rid].items() if m != (p,)}
            require(terms(solved) == step['sheared_pivot_solution'], 'Wrong radical restoration')
            keep = [i for i in range(n) if i != p]
            variables = [copy.deepcopy(eq['variables'][i]) for i in keep]
            for j, i in enumerate(keep):
                if d.get(i):
                    variables[j]['name'] = f'radical{n}.{i}'
            residuals = []
            for j, row in enumerate(rows):
                if j != rid:
                    newrow = delete_coordinate(substitute(row, {p: solved}), p)
                    require(all(len(m)<=2 for m in newrow), 'Degree increase')
                    residuals.append(dict(eq['residuals'][j], terms=terms(newrow)))
            eq['variables'], eq['residuals'] = variables, residuals
            eq.pop('metrics', None)
            eq['variant'] = eq.get('variant', '') + ':radical_projection'
        elif kind == 'affine':
            p, rid = step['eliminated_coordinate'], step['omitted_residual']
            rel = step['affine_consequence']
            relation = {}
            for c, i in rel['row_combination']:
                relation = add(relation, poly(eq['residuals'][i]['terms']), c)
            require(terms(relation) == rel['affine_terms'], 'Incorrect affine consequence')
            content = rel['whole_content']
            require(content > 0 and all(c % content == 0 for c in relation.values()), 'Bad content')
            relation = {m: c//content for m, c in relation.items()}
            a = relation.pop((p,), 0)
            require(abs(a) == 1, 'Nonunit affine coefficient')
            solved = {m: -a*c for m, c in relation.items()}
            require(terms(solved) == step['restoration_terms_original_indices'], 'Wrong affine restoration')
            require(any(c and i==rid for c, i in rel['row_combination']), 'Invalid omitted row')
            eq['variables'] = [v for i, v in enumerate(eq['variables']) if i != p]
            eq['residuals'] = [dict(r, terms=terms(delete_coordinate(substitute(poly(r['terms']), {p: solved}), p))) for i, r in enumerate(eq['residuals']) if i != rid]
            eq['variant'] = eq.get('variant', '') + '; exact affine projection'
        elif kind == 'shear':
            p = step['variable']
            replacement = poly(step['replacement'])
            require(replacement.get((p,))==1 and all(m==(p,) or p not in m for m in replacement), 'Not a triangular unit shear')
            eq['residuals'] = [dict(r, terms=terms(substitute(poly(r['terms']), {p: replacement}))) for r in eq['residuals']]
            eq['variant'] = eq.get('variant', '') + step['variant_suffix']
        elif kind == 'row_operations':
            rows = [poly(r['terms']) for r in eq['residuals']]
            for i, j, k in step['operations']:
                require(i != j, 'Noninvertible row update')
                rows[i] = add(rows[i], rows[j], k)
            eq['residuals'] = [dict(r, terms=terms(p)) for r, p in zip(eq['residuals'], rows)]
            eq['variant'] = eq.get('variant', '') + ':integer_row_reduction'
        else:
            raise ValueError('Unknown certificate step')
        after_hash, after_math = digest(eq), mathematical_digest(eq)
        if check_hashes:
            require(after_hash == step['output_sha256'], 'Canonical output hash mismatch')
            require(after_math == step['output_mathematical_sha256'], 'Mathematical output hash mismatch')
        if stage_callback is not None:
            stage_callback(number, before_hash, after_hash, before_math, after_math)
    return eq


def expand(eq):
    out = {}
    for r in eq['residuals']:
        p = poly(r['terms'])
        out = add(out, mul(p, p))
    return out


def metrics(eq, polynomial):
    rows = [poly(r['terms']) for r in eq['residuals']]
    return {'variables': len(eq['variables']), 'rows': len(rows),
            'residual_terms': sum(map(len, rows)),
            'row_height': max(abs(c) for r in rows for c in r.values()),
            'degree': max(map(len, polynomial)), 'monomials': len(polynomial),
            'height': max(map(abs, polynomial.values()))}


def main():
    certificate = json.loads((ROOT/'certificate.json').read_text())
    raw = (ROOT/'inputs/pooled225.json').read_bytes()
    require(hashlib.sha256(raw).hexdigest()==certificate['source']['sha256'], 'Source SHA256 mismatch')
    eq = replay(json.loads(raw), certificate)
    polynomial = expand(eq)
    met = metrics(eq, polynomial)
    require(met == certificate['expected_metrics'], 'Unexpected final metrics')
    output = ROOT/'equation'
    output.mkdir(exist_ok=True)
    for name, obj in [('equation.json', eq), ('metrics.json', met), ('expanded_polynomial.json', {'schema':'sparse_integer_polynomial_v1','variables':len(eq['variables']),'terms':terms(polynomial)})]:
        (output/name).write_bytes(canonical(obj))
    print(json.dumps(met, sort_keys=True))


if __name__ == '__main__':
    main()
