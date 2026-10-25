#!/usr/bin/env python3
from pathlib import Path
import copy, json, argparse
import build_staged_rows as s

def transform(shift=True):
    raw, rec = s.transform(shift)
    ns = {v['name']: i for i, v in enumerate(raw['variables'])}
    rows = raw['residuals']
    i0 = next((i for i, r in enumerate(rows) if r['label'] == 'index_cap.staged_one_row_cap.0'))
    i1 = next((i for i, r in enumerate(rows) if r['label'] == 'index_cap.staged_one_row_cap.1'))
    W, Y, L, slack, Q0, Q1 = [ns[n] for n in ['shared.W', 'index_cap.Y', 'shared.lower_A', 'shared.A_slack', 'index_cap.error_square_quotient', 'index_cap.range_error_quotient']]
    late = {(): 16, (17,): 5, (29,): 2, (155,): 1}
    for k in [16, 18, 19, 20, 21, 22, 23, 24]:
        late[k,] = 1
    yp = [ns['index' + str(j) + '.Y'] for j in range(5, 15)]
    p1 = s.psd.loadpoly(rows[i1]['terms'])
    actual = {}
    for y in yp:
        for m, c in p1.items():
            if y in m and m != (y, y):
                if not c % 2 == 0:
                    raise ValueError('Generator invariant failed')
                mm = list(m)
                mm.remove(y)
                mm = tuple(mm)
                actual[mm] = actual.get(mm, 0) - c // 2
    if not actual == late:
        raise ValueError((actual, late))
    p0 = s.psd.loadpoly(rows[i0]['terms'])
    for m, c in p1.items():
        if Q1 not in m and m not in [(W,), (Y,)]:
            p0[m] = p0.get(m, 0) + c
    rows[i0] = {'label': 'index_cap.one_row_all_indices', 'terms': s.psd.dump(p0)}
    rows.pop(i1)
    for r in rows:
        if r['label'] == 'shared.frame_definition':
            p = s.psd.loadpoly(r['terms'])
            for m, c in late.items():
                p[m] = p.get(m, 0) - 2 * c
            r['terms'] = s.psd.dump(p)
    kept = [i for i in range(len(raw['variables'])) if i != Q1]
    ren = {v: i for i, v in enumerate(kept)}
    raw['variables'] = [raw['variables'][i] for i in kept]
    for r in rows:
        r['terms'] = [[c, [ren[v] for v in m]] for c, m in r['terms']]
    raw['variant'] = 'all_indices_one_row_cap_dominant_modulus'
    raw['metrics'] = s.psd.metrics_and_polynomial(raw)[0]
    rec.update({'additional_frame': s.psd.dump(late), 'second_quotient_deleted': Q1, 'index_batches': 1})
    return (raw, rec)
if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--no-shift', action='store_true')
    a = p.parse_args()
    raw, rec = transform(not a.no_shift)
    s.write(a.output / 'raw/equation.json', raw)
    s.write(a.output / 'raw/transformation.json', rec)
    results = {}
    for name, prot in [('minimum', []), ('protected_frame', [169]), ('protected_frame_wire', [169, 94])]:
        t, c, poly = s.psd.contract(raw, support_cap=20, protected_variables=prot)
        v, ind = s.check.verify(raw, t, c)
        if not ind == poly['terms']:
            raise ValueError('Generator invariant failed')
        for fn, o in [('equation.json', t), ('elimination_certificate.json', c), ('expanded_polynomial.json', poly), ('VERIFICATION.json', v)]:
            s.write(a.output / name / fn, o)
        results[name] = t['metrics']
        print(name, t['metrics'], flush=True)
    s.write(a.output / 'RESULTS.json', results)
