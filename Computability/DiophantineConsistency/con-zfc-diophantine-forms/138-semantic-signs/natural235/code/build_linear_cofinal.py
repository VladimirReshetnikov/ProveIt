#!/usr/bin/env python3
from pathlib import Path
import argparse
import build_single_row as a
s = a.s

def transform(staged=False):
    raw, rec = s.transform(True) if staged else a.transform(True)
    ns = {v['name']: i for i, v in enumerate(raw['variables'])}
    r0, y, V = [ns[n] for n in ['endpoint.r0', 'y', 'pow0.output']]
    for r in raw['residuals']:
        r['terms'] = s.psd.dump(s.psd.subst(s.psd.loadpoly(r['terms']), V, {(): 1, (V,): 1}))
    raw['variables'][V]['name'] = 'pow0.output_minus_one'
    replacement = []
    for i, r in enumerate(raw['residuals']):
        if r['label'] == 'endpoint.first_remainder':
            r['label'] = 'endpoint.cofinal_linear_modulus'
            r['terms'] = s.psd.dump({(y,): 1, (V,): -1})
            replacement.append(i)
    if len(replacement) != 1:
        raise ValueError('Expected one endpoint row')
    kept = [i for i in range(len(raw['variables'])) if i != r0]
    ren = {v: i for i, v in enumerate(kept)}
    raw['variables'] = [raw['variables'][i] for i in kept]
    for r in raw['residuals']:
        r['terms'] = [[c, [ren[v] for v in m]] for c, m in r['terms']]
    raw['variant'] += '__cofinal_linear_modulus'
    raw['metrics'] = s.psd.metrics_and_polynomial(raw)[0]
    rec.update({'cofinal_modulus': {'y_variable_before': y, 'V_variable_before': V, 'formula': 'y=V0-1', 'shift': 'V0=v+1'}, 'semantic_deleted_variables': [r0], 'replaced_row': replacement[0]})
    return (raw, rec)
if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--staged', action='store_true')
    a0 = p.parse_args()
    raw, rec = transform(a0.staged)
    s.write(a0.output / 'raw/equation.json', raw)
    s.write(a0.output / 'raw/transformation.json', rec)
    results = {}
    for cap in [20] if a0.staged else [20, 40]:
        t, c, pol = s.psd.contract(raw, support_cap=cap)
        v, ind = s.check.verify(raw, t, c)
        if ind != pol['terms']:
            raise ValueError('Independent polynomial mismatch')
        for fn, o in [('equation.json', t), ('elimination_certificate.json', c), ('expanded_polynomial.json', pol), ('VERIFICATION.json', v)]:
            s.write(a0.output / str(cap) / fn, o)
        results[cap] = t['metrics']
        print(cap, t['metrics'], flush=True)
    s.write(a0.output / 'RESULTS.json', results)
