#!/usr/bin/env python3
from pathlib import Path
import argparse, copy, hashlib, importlib.util, json
BASE = Path(__file__).resolve().parent.parent / 'inherited'
RAW = BASE / 'source_equation.json'

def load(name, path):
    s = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(s)
    s.loader.exec_module(m)
    return m
psd = load('stage_contract', BASE / 'contract.py')
check = load('stage_check', BASE / 'check.py')

def write(p, x):
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(x, sort_keys=True, separators=(',', ':')) + '\n')

def transform(shift=True):
    raw = json.loads(RAW.read_text())
    source = copy.deepcopy(raw)
    names = {v['name']: i for i, v in enumerate(raw['variables'])}
    W, Y, L, sigma = [names[n] for n in ['shared.W', 'index_cap.Y', 'shared.lower_A', 'shared.A_slack']]
    if not (W, Y, L, sigma) == (169, 180, 170, 171):
        raise ValueError('Generator invariant failed')
    if shift:
        for r in raw['residuals']:
            r['terms'] = psd.dump(psd.subst(psd.loadpoly(r['terms']), sigma, {(): 1, (sigma,): 1}))
    for r in raw['residuals']:
        if r['label'] == 'shared.frame_definition':
            p = psd.loadpoly(r['terms'])
            p = {m: c if m == (W,) else 2 * c for m, c in p.items()}
            r['terms'] = psd.dump(p)
        if r['label'].startswith('index_cap.squared_index_errors.'):
            qi = names['index_cap.error_square_quotient' if r['label'].endswith('.0') else 'index_cap.range_error_quotient']
            p = psd.loadpoly(r['terms'])
            p = {m: -c if qi in m else c for m, c in p.items()}
            p[W,] = p.get((W,), 0) + 1
            p[Y,] = p.get((Y,), 0) - 1
            r['terms'] = psd.dump(p)
            r['label'] = r['label'].replace('squared_index_errors', 'staged_one_row_cap')
    gone = {333, 334, 335, 336, 337}
    remove = []
    for i, r in enumerate(raw['residuals']):
        if any((v in gone for c, m in r['terms'] for v in m)):
            remove.append(i)
    if not len(remove) == 5:
        raise ValueError('Generator invariant failed')
    raw['residuals'] = [r for i, r in enumerate(raw['residuals']) if i not in remove]
    kept = [i for i in range(len(raw['variables'])) if i not in gone]
    ren = {v: i for i, v in enumerate(kept)}
    raw['variables'] = [raw['variables'][i] for i in kept]
    for r in raw['residuals']:
        r['terms'] = [[c, [ren[v] for v in m]] for c, m in r['terms']]
    raw['variant'] = 'staged_one_row_pell_caps_shifted' if shift else 'staged_one_row_pell_caps'
    met, pol = psd.metrics_and_polynomial(raw)
    raw['metrics'] = met
    receipt = {'source_sha256': hashlib.sha256(RAW.read_bytes()).hexdigest(), 'deleted_variables': sorted(gone), 'deleted_source_rows': remove, 'frame_multiplier': 2, 'base_slack_shift': int(shift), 'cap_rows': 2, 'original_to_new': ren}
    return (raw, receipt)
if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--no-shift', action='store_true')
    a = p.parse_args()
    raw, receipt = transform(not a.no_shift)
    write(a.output / 'raw/equation.json', raw)
    write(a.output / 'raw/transformation.json', receipt)
    results = {}
    for name, protected in [('minimum', []), ('protected_frame', [169]), ('protected_frame_wire', [169, 94])]:
        target, cert, poly = psd.contract(raw, support_cap=20, protected_variables=protected)
        checked, independent = check.verify(raw, target, cert)
        if not independent == poly['terms']:
            raise ValueError('Generator invariant failed')
        for fn, obj in [('equation.json', target), ('elimination_certificate.json', cert), ('expanded_polynomial.json', poly), ('VERIFICATION.json', checked)]:
            write(a.output / name / fn, obj)
        results[name] = target['metrics']
        print(name, target['metrics'], flush=True)
    write(a.output / 'RESULTS.json', results)
