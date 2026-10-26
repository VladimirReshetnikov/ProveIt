#!/usr/bin/env python3
"""Compose the independent affine-radix semantic change and exact projections."""
from pathlib import Path
import argparse, copy, hashlib, json, sys
HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / 'inherited/anchor'
sys.path.insert(0, str(SOURCE / 'code'))
from polynomial import add, scale, const, var, terms, poly, degree, canonical, compact, expand, subst
import reduce_radical, affine_search, affine_project


def save(out, eq, certificate=None):
    out.mkdir(parents=True, exist_ok=True)
    p = expand(eq)
    met = {'variables': len(eq['variables']), 'rows': len(eq['residuals']),
           'degree': degree(p), 'monomials': len(p), 'height': max(map(abs, p.values())),
           'row_height': max(abs(c) for r in eq['residuals'] for c, _ in r['terms'])}
    (out / 'equation.json').write_bytes(canonical(eq))
    (out / 'expanded_polynomial.json').write_bytes(canonical({'schema': 'sparse-polynomial-v1',
        'variables': len(eq['variables']), 'terms': terms(p)}))
    (out / 'metrics.json').write_bytes(canonical(met))
    if certificate is not None:
        (out / 'certificate.json').write_bytes(canonical(certificate))
    print(out, met, flush=True)
    return met


def build(inp, out):
    raw = inp.read_bytes()
    old = json.loads(raw)
    names = {v['name']: i for i, v in enumerate(old['variables'])}
    base = names['self_radix.BH']
    F = var(names['growth.F'])
    C_half = var(names['crt.even_index_half'])
    D = add(const(2), scale(2, F), scale(4, C_half))
    deleted = [i for i, r in enumerate(old['residuals']) if r['label'] == 'self_radix.base_definition']
    if len(deleted) != 1:
        raise ValueError('Ambiguous base equation')
    eq = copy.deepcopy(old)
    eq['residuals'] = []
    changed = []
    for i, row in enumerate(old['residuals']):
        if i in deleted:
            continue
        before = poly(row['terms'])
        after = subst(before, base, D)
        if degree(after) > 2:
            raise ValueError('Degree increase')
        eq['residuals'].append(dict(row, terms=terms(after)))
        if before != after:
            changed.append({'row': i, 'label': row['label'], 'before': terms(before), 'after': terms(after)})
    eq['variant'] += ':affine_radix'
    eq['radix_base'] = '2*(C+F+1)'
    eq, ren = compact(eq)
    cert = {'schema': 'affine-radix-composition-v1', 'input_sha256': hashlib.sha256(raw).hexdigest(),
            'deleted_rows': deleted, 'base_coordinate': base, 'replacement': terms(D),
            'changed_rows': changed, 'old_to_new': [[i, j] for i, j in ren.items()],
            'output_sha256': hashlib.sha256(canonical(eq)).hexdigest()}
    save(out / 'source216', eq, cert)
    projected, pc = reduce_radical.reduce(eq)
    save(out / 'projection211', projected, pc)
    search = affine_search.run(out / 'projection211/equation.json')
    (out / 'affine_search.json').write_bytes(canonical(search))
    for j, rel in enumerate(search['certified_relations']):
        for v in rel['unit_variables_after_content_normalization']:
            final, ac = affine_project.project(projected, rel, v)
            ac.update(input_sha256=hashlib.sha256(canonical(projected)).hexdigest(),
                      output_sha256=hashlib.sha256(canonical(final)).hexdigest())
            save(out / f'projection210_r{j}_v{v}', final, ac)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--input', type=Path, default=HERE.parent / 'stages/growth217/equation.json')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    build(args.input, args.output)
