#!/usr/bin/env python3
"""Replace exact exponential growth by a standalone divisibility-forced Pell block.

This is a semantic source change. Its soundness/completeness is proved in the
accompanying article; coefficient replay does not substitute for that proof.
"""
from pathlib import Path
import argparse, copy, hashlib, json, sys

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / 'inherited/anchor'
sys.path.insert(0, str(SOURCE / 'code'))
from polynomial import add, scale, sub, mul, const, var, terms, poly, degree, canonical, compact, expand

ELL = 1 << 20
MULTIPLIER = 1 << 19


def build(input_path, output_dir):
    raw = input_path.read_bytes()
    old = json.loads(raw)
    if len(old['variables']) != 219 or len(old['residuals']) != 158:
        raise ValueError('Expected frozen anchor219 source')
    expected = {0: 't0', 2: 'growth.F', 144: 'base0.T', 145: 'pow0.quotient',
                186: 'growth.index_pair.X_minus_AY', 187: 'growth.index_pair.Y',
                188: 'growth.index_pair.AY', 190: 'cofinal.horizon_root'}
    for index, name in expected.items():
        if old['variables'][index]['name'] != name:
            raise ValueError(('coordinate binding', index, name))
    rows = [poly(r['terms']) for r in old['residuals']]
    t, F = var(0), var(2)
    K = scale(ELL, t)
    Dg, Yg, Zg = var(186), var(187), var(188)
    edits = {}
    # The old exponent was a frame atom and a member of the orientation pool.
    edits[134] = add(rows[134], mul(K, K))
    old_orientation = add(const(2), mul(Zg, Zg), scale(-2, Dg),
                          scale(-2, Zg), mul(K, K), scale(-2, mul(K, Yg)))
    edits[147] = sub(rows[147], old_orientation)
    edits[150] = add(rows[150], mul(Yg, Yg))
    deleted = {102, 103, 132, 133}
    variables = copy.deepcopy(old['variables'])
    X, Z, u = [var(len(variables) + i) for i in range(3)]
    for name in ['growth_pell.X', 'growth_pell.tF', 'growth_pell.odd_half']:
        variables.append({'name': name, 'kind': 'signed_growth_witness'})
    new_rows = [
        {'label': 'growth_pell.product', 'terms': terms(sub(Z, mul(t, F)))},
        {'label': 'growth_pell.norm', 'terms': terms(add(mul(X, X), scale(-16, mul(Z, Z)), scale(-8, mul(Z, F)), const(-1)))},
        {'label': 'growth_pell.divisibility', 'terms': terms(sub(F, scale(MULTIPLIER, mul(t, add(scale(2, u), const(1))))))},
    ]
    residuals = []
    for i, row in enumerate(old['residuals']):
        if i not in deleted:
            residuals.append(dict(row, terms=terms(edits.get(i, rows[i]))))
    residuals += new_rows
    eq = copy.deepcopy(old)
    eq.update(schema='conzfc-divisibility-growth-v1', variables=variables,
              residuals=residuals, variant='standalone_pell_growth',
              source_equation_sha256=hashlib.sha256(raw).hexdigest(),
              growth_multiplier=MULTIPLIER,
              growth_label_degree=MULTIPLIER,
              growth_pell_center='4*t+1')
    if any(degree(poly(r['terms'])) > 2 for r in residuals):
        raise ValueError('Residual degree exceeded two')
    final, ren = compact(eq)
    removed = sorted(set(range(len(variables))) - set(ren))
    if removed != [144, 145, 186, 187, 188]:
        raise ValueError(('unexpected liveness', removed))
    expansion = expand(final)
    metrics = {'variables': len(final['variables']), 'rows': len(final['residuals']),
               'degree': degree(expansion), 'monomials': len(expansion),
               'height': max(map(abs, expansion.values())),
               'row_height': max(abs(c) for r in final['residuals'] for c, _ in r['terms'])}
    cert = {'schema': 'standalone-pell-growth-graft-v1',
            'input_sha256': hashlib.sha256(raw).hexdigest(),
            'removed_label_exponent': ELL, 'label_degree': MULTIPLIER,
            'label_bound': '8^(2^19-1)*t^(2^19)', 'ordinate_multiplier': MULTIPLIER,
            'pell_center': '4*t+1',
            'horizon_minimum': 16, 'horizon_square_coefficient': 4,
            'deleted_rows': sorted(deleted), 'removed_coordinates': removed,
            'edits': [{'row': i, 'before': terms(rows[i]), 'after': terms(p)} for i, p in sorted(edits.items())],
            'new_rows': new_rows,
            'removed_orientation_contribution': terms(old_orientation),
            'old_to_new': [[i, j] for i, j in ren.items()],
            'output_sha256': hashlib.sha256(canonical(final)).hexdigest()}
    output_dir.mkdir(parents=True, exist_ok=True)
    for name, obj in [('equation.json', final), ('uncontracted.json', eq),
                      ('growth_certificate.json', cert), ('metrics.json', metrics),
                      ('expanded_polynomial.json', {'schema': 'sparse-polynomial-v1',
                       'variables': len(final['variables']), 'terms': terms(expansion)})]:
        (output_dir / name).write_bytes(canonical(obj))
    print(json.dumps(metrics))
    return final


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--input', type=Path, default=SOURCE / 'source/anchor219/equation.json')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    build(args.input, args.output)
