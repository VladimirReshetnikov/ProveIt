# Validation uses explicit exceptions, including under python -O.
import json, hashlib, sympy as s, sys
from pathlib import Path
R = Path(__file__).resolve().parent
src = R / 'parent_source.json'
p = json.loads(src.read_text())
vs = s.symbols(' '.join(p['sparse_term_coordinate_order']))
D = dict(zip(p['sparse_term_coordinate_order'], vs))
rs = [s.expand(sum((t['coefficient'] * s.prod((v ** k for v, k in zip(vs, t['powers']))) for t in e['terms']))) for e in p['equations']]
seq = [('C2', 10), ('F2', 15), ('Delta', 9), ('L', 0), ('X', 2), ('N', 1), ('D', 8)]
variant = sys.argv[1] if len(sys.argv) > 1 else '24'
if variant == '21':
    seq += [('Baux', 19), ('P', 6), ('V', 12)]
if variant == '26':
    seq = [('C2', 10), ('F2', 15), ('L', 0), ('X', 2), ('Baux', 19)]
rem = list(vs[:31])
rr = rs[:]
defs = {}
for name, idx in seq:
    v = D[name]
    sol = s.solve(rr[idx], v)[0]
    if not s.expand(rr[idx] - (v - sol)) == 0:
        raise RuntimeError('Validation failed: s.expand(rr[idx] - (v - sol)) == 0')
    defs[name] = sol
    rr = [s.expand(r.subs(v, sol)) for r in rr]
    rem.remove(v)
    for k in defs:
        defs[k] = s.expand(defs[k].subs(v, sol))
if not not any((expr.free_symbols & {D[k] for k in defs} for expr in defs.values())):
    raise RuntimeError('Validation failed: not any((expr.free_symbols & {D[k] for k in defs} for expr in defs.values()))')
for k, r in enumerate(rs):
    if not s.expand(r.subs({D[v]: expr for v, expr in defs.items()}, simultaneous=True) - rr[k]) == 0:
        raise RuntimeError('Validation failed: s.expand(r.subs({D[v]: expr for v, expr in defs.items()}, simultaneous=True) - rr[k]) == 0')
out = {'source_sha256': hashlib.sha256(src.read_bytes()).hexdigest(), 'domain': 'strictly positive integers', 'constants': p['constants'], 'variables': list(map(str, rem)), 'definitions': {k: str(v) for k, v in defs.items()}, 'equations': [{'old_row': i + 1, 'residual': str(r), 'degree': s.Poly(r, *rem).total_degree(), 'terms': [{'powers': list(mon), 'coefficient': str(c)} for mon, c in s.Poly(r, *rem).terms()]} for i, r in enumerate(rr) if r != 0]}
out['metrics'] = {'variables': len(rem), 'equations': len(out['equations']), 'degree': max((e['degree'] for e in out['equations'])), 'support_terms': sum((len(e['terms']) for e in out['equations']))}
(R / f'source{variant}.json').write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps(out['metrics']))
