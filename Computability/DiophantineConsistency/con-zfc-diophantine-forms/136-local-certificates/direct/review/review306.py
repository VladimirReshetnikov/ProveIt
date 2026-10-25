#!/usr/bin/env python3
"""Independent exact review of the 306-variable Pell orientation transformation.

This checker imports no code from the constructor. It checks literal finite
algebra only; REVIEW306.md contains the independent unbounded argument review.
"""
from collections import defaultdict
from hashlib import sha256
from itertools import combinations_with_replacement
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]


def load(p):
    return json.loads((ROOT / p).read_text())


def canonical(x):
    return (json.dumps(x, sort_keys=True, separators=(',', ':')) + '\n').encode()


def normal(terms):
    p = defaultdict(int)
    for c, m in terms:
        p[tuple(sorted(m))] += c
    return {m: c for m, c in p.items() if c}


def require(b, message):
    if not b:
        raise ValueError(message)


def main():
    old = load('parent/integer324-equation.json')
    new = load('integer306/equation.json')
    cert = load('integer306/transformation_certificate.json')
    expanded = load('integer306/expanded_polynomial.json')
    metrics = load('integer306/METRICS.json')
    trans = load('parent/integer324-translation-certificate.json')
    raw = load('parent/cap-source.json')
    sem = load('parent/cap-transform-certificate.json')
    proj = load('parent/cap-projection-certificate.json')
    require(len(old['variables']) == 324 and len(old['residuals']) == 208,
            'Incorrect parent dimensions')
    require(len(new['variables']) == 306 and len(new['residuals']) == 206,
            'Incorrect successor dimensions')
    require(cert['parent_canonical_sha256'] == sha256(canonical(old)).hexdigest(),
            'Incorrect parent binding')
    require(cert['output_canonical_sha256'] == sha256(canonical(new)).hexdigest(),
            'Incorrect output binding')
    deleted = set(range(252, 279))
    removed_rows = set(range(184, 193))
    require(cert['removed_parent_variables'] == sorted(deleted), 'Wrong deleted coordinates')
    require(cert['removed_parent_rows'] == sorted(removed_rows), 'Wrong deleted rows')
    for g in range(3, 12):
        ri = 181 + g
        require(old['residuals'][ri]['label'] == 'domain_guard.' + str(g), 'Guard label')
        triple = set(range(243+3*g, 246+3*g))
        require(triple <= deleted, 'Incorrect guard triple')
        for v in triple:
            occurrences = [i for i, r in enumerate(old['residuals'])
                           if any(v in m for _, m in r['terms'])]
            require(occurrences == [ri], 'Deleted witness is not private')
    q_occurrences = [i for i, r in enumerate(old['residuals'])
                     if any(242 in m for _, m in r['terms'])]
    require(q_occurrences == [180], 'Pool quotient is not private')
    require(old['variables'][242]['name'] == 'cap.pooled_quotient', 'Pool quotient name')
    keep = [i for i in range(324) if i not in deleted]
    ren = {v: i for i, v in enumerate(keep)}
    xs = [174, 180, 184, 188, 192, 200, 204, 212, 216]
    sh = dict(trans['shifts'])
    require(all(sh.get(i, 0) == 0 for i in xs), 'Abscissa chart shift')
    require(sh.get(151, 0) == 1, 'Main center A is not z151+1')
    require(sh.get(10, 0) == -2, 'First encoded chart shift')
    require(all(sh.get(i, 0) == -1 for i in range(11, 19)), 'Other encoded chart shifts')
    count = 0
    for i, r in enumerate(old['residuals']):
        if i in removed_rows:
            continue
        expected = normal(r['terms'])
        if i == 180:
            expected[()] = expected.get((), 0) + 9
            for x in xs:
                expected[(x,)] = expected.get((x,), 0) - 1
        mapped = {tuple(ren[j] for j in m): c for m, c in expected.items() if c}
        nr = new['residuals'][count]
        require(nr['label'] == r['label'], 'Retained row label')
        require(normal(nr['terms']) == mapped, 'Unexpected changed retained row')
        count += 1
    require(count == 199, 'Retained row count')
    for i in range(297):
        require(new['variables'][i] == old['variables'][keep[i]], 'Retained variable metadata')
    # Restore the raw power-port chart independently from the two parent certificates.
    old_to_parent = {v: i for i, v in enumerate(proj['retained_original_variables'])}
    calls = [5, 7, 8, 9, 10, 12, 13, 15, 16]
    port_records = []
    for position, call in enumerate(calls):
        seed = next(s for s in sem['seed_data'] if call in s['calls'])
        raw_x, raw_y = seed['pair']
        parent_x = old_to_parent[raw_x]
        require(parent_x == xs[position], 'Wrong selected abscissa port')
        exp = normal(seed['exponent'])
        require(exp == {(): 1, (16+position,): 1}, 'Wrong encoded requested index')
        output = normal(sem['square_budget']['power_calls'][call]['output'])
        require(len(output) == 1 and next(iter(output.values())) == 1, 'Unexpected output chart')
        raw_m = next(iter(output))[0]
        parent_m = old_to_parent[raw_m]
        require(sh.get(parent_m, 0) == 0, 'Unexpected output translation')
        port_records.append({'call': call, 'raw_pair': [raw_x, raw_y],
                             'parent_abscissa': parent_x, 'parent_output': parent_m})
    # No discarded witness or changed quotient is used in a body restoration.
    forbidden = {v for g in sem['guards'][3:12] for v in g['auxiliary']}
    forbidden.add(sem['pooled_quotient'])
    for step in proj['steps']:
        require(not any(forbidden.intersection(m) for _, m in step['restoration']),
                'A body restoration depends on a changed private witness')
    for g in sem['guards'][3:12]:
        require(g['row'] in proj['retained_original_rows'], 'Deleted guard used for projection')
    # Six ordinary products and the fused eighth factor, with all signs preserved.
    expected_products = [
        {(297,): 1, (10, 11): -1, (11,): 1},
        {(298,): 1, (297, 12): -1},
        {(299,): 1, (298, 13): -1},
        {(300,): 1, (299, 14): -1},
        {(301,): 1, (300, 15): -1},
        {(302,): 1, (301, 16): -1},
    ]
    for row, e in zip(new['residuals'][199:205], expected_products):
        e = {tuple(sorted(m)): c for m, c in e.items()}
        require(normal(row['terms']) == e, 'Incorrect product chain')
    fused = {(17, 302): 1, (): -1, (303, 303): -1, (304, 304): -1,
             (305, 305): -1, (305,): -1}
    require(normal(new['residuals'][205]['terms']) == fused, 'Incorrect fused strict guard')
    # Re-expand by unordered pairs. The producer uses all ordered pairs.
    total = defaultdict(int)
    for r in new['residuals']:
        p = sorted(normal(r['terms']).items())
        require(all(len(m) <= 2 for m, _ in p), 'Residual degree exceeds two')
        for i, j in combinations_with_replacement(range(len(p)), 2):
            m, a = p[i]
            n, b = p[j]
            total[tuple(sorted(m+n))] += a*b*(1 if i == j else 2)
    total = {m: c for m, c in total.items() if c}
    require(total == normal(expanded['terms']), 'Complete expansion differs')
    measured = {'variables': 306, 'residuals': 206, 'degree': max(map(len, total)),
                'monomials': len(total), 'coefficient_height': max(map(abs, total.values())),
                'residual_height': max(abs(c) for r in new['residuals'] for c, _ in r['terms'])}
    require(measured == metrics, 'Metrics differ')
    degree_witness = next([c, list(m)] for m, c in sorted(total.items()) if len(m) == 4)
    result = {'reviewer': 'independently written checker, no constructor import',
              'status': 'passed', 'finite_scope': 'literal interfaces and full coefficient identity',
              'unbounded_review': 'REVIEW306.md', 'metrics': measured,
              'parent_sha256': sha256(canonical(old)).hexdigest(),
              'successor_sha256': sha256(canonical(new)).hexdigest(),
              'quartic_coefficient_witness': degree_witness,
              'power_port_bindings': port_records,
              'changed_private_quotient_occurrences': q_occurrences,
              'body_restoration_dependence_on_changed_private_witnesses': 0,
              'retained_rows_compared': count, 'new_product_rows_compared': 7,
              'deleted_private_guard_coordinates_checked': 27}
    print(json.dumps(result, sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
