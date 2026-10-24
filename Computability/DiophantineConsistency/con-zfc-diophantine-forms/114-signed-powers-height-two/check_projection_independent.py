#!/usr/bin/env python3
"""Independent exact integral projection and full coefficient verification.

No producer, optimizer, or inherited algebra module is imported.  This checker
proves the finite polynomial identities used by the supplied elimination
certificate; it does not replace the unbounded arithmetic source proof.
"""
import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path


def need(ok, message):
    if not ok:
        raise ValueError(message)


def poly(terms):
    result = {}
    for coefficient, monomial in terms:
        need(type(coefficient) is int, 'integer coefficient')
        need(all(type(i) is int and i >= 0 for i in monomial), 'variable indices')
        key = tuple(sorted(monomial))
        result[key] = result.get(key, 0) + coefficient
    return {m: c for m, c in result.items() if c}


def add(a, b, factor=1):
    out = dict(a)
    for m, c in b.items():
        out[m] = out.get(m, 0) + factor*c
        if not out[m]:
            del out[m]
    return out


def mul(a, b):
    out = {}
    for u, c in a.items():
        for v, d in b.items():
            m = tuple(sorted(u + v))
            out[m] = out.get(m, 0) + c*d
    return {m: c for m, c in out.items() if c}


def replace(a, variable, value):
    if all(variable not in m for m in a):
        return a
    out = {}
    for m, c in a.items():
        n = m.count(variable)
        term = {tuple(i for i in m if i != variable): c}
        for _ in range(n):
            term = mul(term, value)
        out = add(out, term)
    return out


def read(path):
    return json.loads(path.read_bytes())


def check(parent, child, certificate, expanded):
    original_n = len(parent['variables'])
    rows = {i: poly(r['terms']) for i, r in enumerate(parent['residuals'])}
    need(certificate['unconstrained_removed'] == [], 'no unconstrained deletions')
    deleted = set()
    for index, step in enumerate(certificate['steps']):
        v, row_id = step['variable'], step['row_id']
        need(v not in deleted and 0 <= v < original_n, 'fresh pivot variable')
        need(row_id in rows, 'pivot row exists')
        restoration = poly(step['restoration'])
        used = {j for m in restoration for j in m}
        need(v not in used and not used.intersection(deleted), 'acyclic restoration')
        need(all(j < original_n for j in used), 'restoration variable range')
        defining = add({(v,): 1}, restoration, -1)
        actual = rows.pop(row_id)
        need(actual == defining or actual == {m: -c for m, c in defining.items()},
             f'exact integral monic definition at step {index}')
        for row in list(rows):
            rows[row] = replace(rows[row], v, restoration)
            need(max(map(len, rows[row]), default=0) <= 2, 'quadratic residual preserved')
        deleted.add(v)
    retained = certificate['retained_original_variables']
    retained_rows = certificate['retained_original_rows']
    need(len(set(retained)) == len(retained), 'distinct retained variables')
    need(set(retained) == set(range(original_n)) - deleted, 'complete variable partition')
    need(set(retained_rows) == set(rows), 'complete row partition')
    need(child['variables'] == [parent['variables'][i] for i in retained], 'variable metadata')
    mapping = {old: new for new, old in enumerate(retained)}
    need(len(retained_rows) == len(child['residuals']), 'residual count')
    for old_id, new_row in zip(retained_rows, child['residuals']):
        translated = poly([[c, [mapping[i] for i in m]] for m, c in rows[old_id].items()])
        need(translated == poly(new_row['terms']), 'whole projected row')
        need(new_row['label'] == parent['residuals'][old_id]['label'], 'row label binding')
    result = {}
    for row in child['residuals']:
        value = poly(row['terms'])
        result = add(result, mul(value, value))
    need(result == poly(expanded['terms']), 'every expanded coefficient')
    live = {v for m in result for v in m}
    need(live == set(range(len(retained))), 'all final variables live')
    metrics = {
        'variables': len(retained),
        'quadratic_rows': len(retained_rows),
        'expanded_monomials': len(result),
        'exact_degree': max(map(len, result), default=0),
        'max_abs_expanded_coefficient': max(map(abs, result.values()), default=0),
        'integer_restorations': len(deleted),
    }
    for key in metrics.keys() - {'integer_restorations'}:
        need(child['metrics'][key] == metrics[key], 'literal metric '+key)
    return metrics


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('packet', type=Path)
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    directory = args.packet.resolve()
    parent = read(directory/'parent.json')
    census = read(directory/'CENSUS.json')
    results = {}
    hashes = {}
    for name in census:
        child = read(directory/name/'equation.json')
        cert = read(directory/name/'projection.json')
        expanded = read(directory/name/'polynomial.json')
        results[name] = check(parent, child, cert, expanded)
        for file in ['equation.json', 'projection.json', 'polynomial.json']:
            path = directory/name/file
            hashes[str(path.relative_to(directory))] = sha256(path.read_bytes()).hexdigest()
    # These controls actually exercise the checker, not the stored metric fields.
    first = next(iter(census))
    p = directory/first
    child, cert, expanded = (read(p/f) for f in ['equation.json','projection.json','polynomial.json'])
    cert['steps'][0]['restoration'][0][0] += 1
    try:
        check(parent, child, cert, expanded)
    except ValueError:
        inverse_rejected = True
    else:
        raise ValueError('altered inverse accepted')
    cert = read(p/'projection.json')
    expanded['terms'][0][0] += 1
    try:
        check(parent, child, cert, expanded)
    except ValueError:
        coefficient_rejected = True
    else:
        raise ValueError('altered coefficient accepted')
    report = {
        'status': 'PASS', 'profiles': results,
        'mutations_rejected': {'restoration': inverse_rejected, 'coefficient': coefficient_rejected},
        'sha256': hashes,
        'scope': 'Exact integer polynomial transformations and complete coefficient comparison; unbounded arithmetic proof remains in report.',
    }
    if args.output:
        args.output.write_text(json.dumps(report, indent=2, sort_keys=True)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k != 'sha256'}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
