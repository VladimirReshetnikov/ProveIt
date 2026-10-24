# Validation uses explicit exceptions, including under python -O.
"""Independent replay of substitution identities, degrees and positive-projection structure."""
import json, hashlib, sympy as s
from pathlib import Path
R = Path(__file__).resolve().parent
p = json.loads((R / 'parent_source.json').read_text())
names = p['sparse_term_coordinate_order']
symbols = s.symbols(' '.join(names))
ds = dict(zip(names, symbols))
original = [s.Poly.from_dict({tuple(t['powers']): t['coefficient'] for t in e['terms']}, symbols).as_expr() for e in p['equations']]
for tag in ('24', '21', '26'):
    data = json.loads((R / f'source{tag}.json').read_text())
    if not data['source_sha256'] == hashlib.sha256((R / 'parent_source.json').read_bytes()).hexdigest():
        raise RuntimeError("Validation failed: data['source_sha256'] == hashlib.sha256((R / 'parent_source.json').read_bytes()).hexdigest()")
    defs = {ds[k]: s.sympify(v, locals=ds) for k, v in data['definitions'].items()}
    ret = [ds[k] for k in data['variables']]
    if not set(ret).isdisjoint(defs):
        raise RuntimeError('Validation failed: set(ret).isdisjoint(defs)')
    if not set(ret) | set(defs) == set(symbols[:31]):
        raise RuntimeError('Validation failed: set(ret) | set(defs) == set(symbols[:31])')
    if not all((not v.free_symbols & set(defs) for v in defs.values())):
        raise RuntimeError('Validation failed: all((not v.free_symbols & set(defs) for v in defs.values()))')
    reduced = {e['old_row']: s.sympify(e['residual'], locals=ds) for e in data['equations']}
    for j, r in enumerate(original, 1):
        if not s.expand(r.subs(defs, simultaneous=True) - reduced.get(j, 0)) == 0:
            raise RuntimeError('Validation failed: s.expand(r.subs(defs, simultaneous=True) - reduced.get(j, 0)) == 0')
    for e in data['equations']:
        r = reduced[e['old_row']]
        t = sum((s.sympify(t['coefficient'], locals=ds) * s.prod((v ** a for v, a in zip(ret, t['powers']))) for t in e['terms']))
        if not s.expand(t - r) == 0:
            raise RuntimeError('Validation failed: s.expand(t - r) == 0')
        if not s.Poly(r, *ret).total_degree() == e['degree']:
            raise RuntimeError("Validation failed: s.Poly(r, *ret).total_degree() == e['degree']")
    if not max((e['degree'] for e in data['equations'])) == data['metrics']['degree']:
        raise RuntimeError("Validation failed: max((e['degree'] for e in data['equations'])) == data['metrics']['degree']")
    j = next(iter(reduced))
    if not s.expand(original[j - 1].subs(defs, simultaneous=True) - (reduced[j] + 1)) != 0:
        raise RuntimeError('Validation failed: s.expand(original[j - 1].subs(defs, simultaneous=True) - (reduced[j] + 1)) != 0')
    print(tag, 'PASS; reconstruction identities, sparse records, degree metadata, corruption control')
