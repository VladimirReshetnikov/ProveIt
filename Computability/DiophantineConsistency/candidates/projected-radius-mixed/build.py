#!/usr/bin/env python3
"""A new mixed-domain parent; preserves every frozen natural/integer parent."""
import argparse
from collections import Counter
from copy import deepcopy
from functools import lru_cache
from hashlib import sha256
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent


def need(ok, message):
    if not ok:
        raise ValueError(message)


def encoded(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n').encode()


def add_term(p, m, c):
    if c:
        p[m] = p.get(m, 0) + c
        if not p[m]:
            del p[m]


def mul(a, b):
    result = {}
    for m, c in a.items():
        for n, d in b.items():
            add_term(result, tuple(sorted(m + n)), c * d)
    return result


def decode(terms):
    return {tuple(m): c for c, m in terms}


def terms(p):
    return [[c, list(m)] for m, c in sorted(p.items())]


def load(name):
    return json.loads((HERE / name).read_text())


def generate():
    pins = load('SOURCE_PINS.json')
    for name, pin in pins['sources'].items():
        need(sha256((HERE / 'source' / name).read_bytes()).hexdigest() == pin['sha256'],
             'immutable source copy ' + name)
    parent = load('source/natural667.json')
    raw = load('source/raw_builder.json')
    conversion = load('source/full_domain_conversion.json')['positivity']
    variables = parent['variables']
    guards = set(conversion['guard_indices'])
    removed = {i for i in guards if re.fullmatch(
        r'pow\d+\.quotient|index\d+\.(S|R)quotient|shared_index\.Bquotient',
        variables[i]['name'])}
    need(len(removed) == 52, 'exact52 old seed omissions')
    known = guards - removed
    steps = []
    blocked = []
    for step in conversion['proof_steps']:
        if set(step['dependencies']) <= known:
            known.add(step['variable'])
            steps.append(step)
        else:
            blocked.append(step)
    unknown = set(range(len(variables))) - known
    sr = {i for i in unknown if re.fullmatch(r'index\d+\.(S|R)', variables[i]['name'])}
    products = unknown - removed - sr
    need((len(known), len(sr), len(products)) == (533, 30, 52), 'complete mixed closure')
    late = {i for i in removed if re.fullmatch(
        r'pow\d+\.quotient|shared_index\.Bquotient', variables[i]['name'])}
    late_known = known | late
    late_steps = []
    for step in blocked:
        if set(step['dependencies']) <= late_known:
            late_known.add(step['variable'])
            late_steps.append(step)
    need(len(late) == len(late_steps) == 22 and len(late_known) == 577,
         'late oriented quotient boundary')
    sign = dict(schema='mixed667_actual_sign_certificate_v1',
        parent_sha256=sha256(encoded(parent)).hexdigest(),
        guards=sorted(guards - removed), removed_guards=sorted(removed),
        proof_steps=steps, known_after_ordinary_steps=sorted(known),
        unresolved={'quotients': sorted(removed), 'comparison_coordinates': sorted(sr),
                    'private_products': sorted(products)},
        late_semantic_quotients=sorted(late), late_proof_steps=late_steps,
        known_after_late_quotients=sorted(late_known))

    identities = {encoded(v): i for i, v in enumerate(raw['variables'])}
    retained = [identities[encoded(v)] for v in variables]
    rename = {v: i for i, v in enumerate(retained)}
    definitions = {}
    for row in raw['rows']:
        if row.get('gate') is not None:
            v = row['gate']
            definitions[v] = {tuple(m): -c for c, m in row['terms'] if m != [v]}

    @lru_cache(None)
    def restore(v):
        if v in rename:
            return {(rename[v],): 1}
        need(v in definitions, 'all raw omitted inputs defined')
        result = {}
        for m, c in definitions[v].items():
            need(c > 0 and len(m) <= 1, 'omitted gate affine/positive')
            if not m:
                add_term(result, (), c)
            else:
                for n, d in restore(m[0]).items():
                    add_term(result, n, c * d)
        return result

    restoration = dict(schema='raw667_integer_restoration_v1', retained_raw_indices=retained,
        omitted=[{'raw_variable': v, 'terms': terms(restore(v))}
                 for v in range(len(raw['variables'])) if v not in rename])
    natural_raw = {v for v in range(len(raw['variables']))
                   if all(c > 0 and all(j in known for j in m)
                          for m, c in restore(v).items())}
    start = raw['scale'][0][1]
    need(set(range(start)) <= natural_raw, 'whole semantic prefix is nonnegative')
    rows_by_label = {r['label']: i for i, r in enumerate(raw['rows']) if r.get('gate') is None}
    names = {v['name']: i for i, v in enumerate(raw['variables'])}
    seed_records = []
    for seed in raw['seeds']:
        X, Y = seed['pair']
        prefix = raw['variables'][X[1]]['name'].removesuffix('.X')
        seed_records.append(dict(exponent=seed['exponent'], X=X, Y=Y,
            **{s: ['v', names[prefix + '.' + s]] for s in
               ['S', 'R', 'YminusK', 'Squotient', 'Rquotient']},
            rows={s: rows_by_label[prefix + '.' + s] for s in
                  ['index_at_most_Y', 'norm1', 'norm3', 'S_mod_U', 'R_mod_4Y']}))
    power_records = []
    for j, power in enumerate(raw['powers']):
        power_records.append(dict(power, quotient=['v', names['pow' + str(j) + '.quotient']],
                                  row=rows_by_label['pow' + str(j) + '.power_congruence']))
    semantic_rows = []
    private_rows = []
    for i, row in enumerate(raw['rows']):
        if row.get('gate') is None:
            target = private_rows if any(v >= start for c, m in row['terms'] for v in m) else semantic_rows
            target.append(i)
    interface = dict(schema='mixed667_complete_arithmetic_interfaces_v1',
        private_start=start, semantic_prefix_raw_variables=list(range(start)),
        raw_nonnegative_from_initial_sign_steps=sorted(natural_raw),
        frame=raw['scale'], auxiliary=raw['auxiliary'], discriminant=raw['discriminant'],
        seeds=seed_records, all_indices=raw['indices'], derivations=raw['derivations'],
        powers=power_records,
        semantic_non_gate_rows=semantic_rows, private_non_gate_rows=private_rows,
        all_gate_rows=[i for i, r in enumerate(raw['rows']) if r.get('gate') is not None],
        private_free_variables=[i for i, v in enumerate(raw['variables'])
                                if i >= start and v['kind'] != 'gate'])

    equation = deepcopy(parent)
    equation['domain'] = 'unrestricted integers'
    equation['variant'] = 'projected667_with109guards_signed_private_pell_comparisons'
    equation['schema'] = 'mixed_pell_quartic_v1'
    equation['variables'] = deepcopy(variables)
    equation['residuals'] = deepcopy(parent['residuals'])
    for v in sign['guards']:
        a, b, c = range(len(equation['variables']), len(equation['variables']) + 3)
        for i, label in zip((a, b, c), ('a', 'b', 'c')):
            equation['variables'].append({'kind': 'nonnegative_guard', 'name': 'guard.' + str(v) + '.' + label})
        equation['residuals'].append({'label': 'mixed_nonnegative.' + str(v),
            'terms': [[1, [v]], [-1, [a, a]], [-1, [b, b]], [-1, [c]], [-1, [c, c]]]})
    polynomial = {}
    for row in equation['residuals']:
        for m, c in mul(decode(row['terms']), decode(row['terms'])).items():
            add_term(polynomial, m, c)
    equation['metrics'] = dict(variables=len(equation['variables']), quadratic_rows=len(equation['residuals']),
        exact_degree=max(map(len, polynomial)), expanded_monomials=len(polynomial),
        max_abs_expanded_coefficient=max(map(abs, polynomial.values())),
        original_coordinates=667, nonnegative_guards=109, guard_auxiliaries=327,
        omitted_seed_guards=52, initially_proved_nonnegative_original_coordinates=533,
        late_proved_nonnegative_original_coordinates=577)
    expansion = dict(schema='collected_integer_polynomial_v1', variables=len(equation['variables']),
                     terms=terms(polynomial))
    files = {'mixed_sign_certificate.json': encoded(sign), 'raw_restoration.json': encoded(restoration),
             'arithmetic_interfaces.json': encoded(interface), 'equation.json': encoded(equation),
             'expanded_polynomial.json': encoded(expansion)}
    files['BUILD.json'] = encoded(dict(status='PASS', generator_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        sha256={name: sha256(data).hexdigest() for name, data in files.items()},
        metrics=equation['metrics'], scope='Literal complete994-integer quartic. Ordinary mixed-domain proof and independent certificate checker are separate.'))
    return files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    files = generate()
    for name, raw in files.items():
        path = HERE / name
        if args.check:
            need(path.read_bytes() == raw, 'deterministic output ' + name)
        else:
            path.write_bytes(raw)
    print(json.dumps({'status': 'PASS', 'check': args.check,
                      'metrics': json.loads(files['BUILD.json'])['metrics']}, indent=2))


if __name__ == '__main__':
    main()
