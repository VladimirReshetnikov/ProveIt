#!/usr/bin/env python3
"""Binding checker for the Nine121 Lean modules of the 105/456 nine-positive endpoint.

Checks (exact integer polynomial arithmetic, standard library only):
  1. Nine121/N105Layout.lean is byte-identical to a fresh run of generate_n105_layout.py, which
     re-derives every gapN86 row from the package-31 parent (through package 101's generator:
     affine map and row operations), checks that 105's H1868 tables are 101's translated tables
     shifted back (weights +1, targets +2, kernel positions +2/+1/+0, identical coefficients), and
     re-derives the 22 extraction identities directly for 105's own weights, targets and kernels;
  2. Source31Rows.rows parses to the 22 equations of the package-31 parent (SHA-256 pinned in the
     101 generator), as in the 101 record;
  3. the four ports of 105's fixed/h1868/BINDING.json have the SHA-256 of package 55's
     wang943-mixed-121x8801 payloads (the tuple of Mixed121Ports.ports);
  4. the prefix constants of N105Prefix (B = 2^2134939 b^2, N0 = B^117, L = 2 b B^1986,
     N = 2^16012032 B^1055, t = b B^116, H = 1868) are those of h1868.json's source_parameters
     and BINDING.json;
  5. rejected mutations: a changed kernel coefficient, weight, target, parent-row coefficient and
     port hash are each detected.
Writes CHECK.json next to the record README.
"""
from pathlib import Path
import copy, hashlib, importlib.util, json, re

HERE = Path(__file__).resolve()
REC = HERE.parents[1]
DC = HERE.parents[3]
LEAN = DC / 'Lean/DiophantineConsistency'
FORMS = DC / 'con-zfc-diophantine-forms'
P105 = FORMS / '105-bootstrap-certificates/nine'


def need(ok, msg):
    if not ok:
        raise SystemExit('FAIL: ' + msg)


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


gen = load_module('gen105', HERE.parent / 'generate_n105_layout.py')
bind101 = load_module('bind101', DC / 'research/nine-positive-p101-420-endpoint/tools/check_binding.py')


def main():
    report = {}
    g101 = gen.gen101()
    # 1. generated file and the layout analysis
    d = gen.analyse()
    text = gen.render(d)
    need((LEAN / 'Nine121/N105Layout.lean').read_text(encoding='utf-8') == text, 'stale N105Layout.lean')
    report['generated_files'] = ['N105Layout.lean']
    report['kernel_records'] = list(d['counts'])
    d101 = g101.analyse()
    rows = d101['rows']
    need(gen.extraction_holds(g101, d['w'], d['E'], d['pos'], d['coef'], rows), 'unmutated extraction')
    report['extraction_identities'] = 22
    # 2. parent rows
    ours = bind101.lean_rows(LEAN / 'Nine121/Source31Rows.lean', 'rows')
    docs, _ = g101.load()
    parent = docs['parent']
    names = parent['variables'] + parent['constants']
    porder = parent['sparse_term_coordinate_order']
    pj = [g101.poly_of(eq, porder, names) for eq in parent['equations']]
    for k, row in enumerate(ours):
        need(bind101.parse_row(row) == pj[k], f'parent row {k}')
    report['parent_rows'] = 22
    # 3. ports
    p55 = json.loads((FORMS / '55-congruence-norms/fourteen/coefficients/ports.json').read_text())
    need(p55['instance'] == 'wang943-mixed-121x8801', '55 instance')
    binding = json.loads((P105 / 'fixed/h1868/BINDING.json').read_text())
    need([p['name'] for p in binding['ports']] == ['beta', 'K0', 'MC', 'MF'], 'port order')
    h55 = [p['sha256'] for p in p55['ports']]
    h105 = [p['raw_sha256'] for p in binding['ports']]
    need(h55 == h105, 'port payload hashes')
    report['ports_sha256'] = dict(zip(['beta', 'K', 'MC', 'MF'], h55))
    # 4. prefix constants
    eq = json.loads((P105 / 'equations/h1868.json').read_text())
    sp = eq['source_parameters']
    need(sp == binding['source_parameters'], 'source parameters agree')
    need((sp['base_exp'], sp['threshold_exp'], sp['L_power'], sp['L_scalar'], sp['N_power'], sp['W'], sp['H'])
         == (2134939, 16012032, 1986, 2, 1055, 116, 1868), 'prefix constants')
    pre = (LEAN / 'Nine121/N105Prefix.lean').read_text(encoding='utf-8')
    for pat in [r'def N0 \(b : A\) : A := Bq b \^ 117', r'def Lq \(b : A\) : A := 2 \* b \* Bq b \^ 1986',
                r'def Nq \(b : A\) : A := \(thresholdScale : A\) \* Bq b \^ 1055',
                r'def tq \(b : A\) : A := b \* Bq b \^ 116']:
        need(re.search(pat, pre) is not None, 'N105Prefix constant ' + pat)
    p101 = (LEAN / 'Nine121/N101Prefix.lean').read_text(encoding='utf-8')
    need('def baseScale : ℤ := 2 ^ 2134939' in p101 and 'def thresholdScale : ℤ := 2 ^ 16012032' in p101,
         'scales')
    report['prefix'] = {'kappa': 2134939, 'theta': 16012032, 'N0': 'B^117', 'L': '2 b B^1986',
                        'N': '2^theta B^1055', 't': 'b B^116', 'H': 1868}
    # 5. mutations
    rejected = {}
    m1 = copy.deepcopy(d); m1['coef'][2][5] = g101.add(m1['coef'][2][5], {(0, 0, 0, 0): 1})
    rejected['kernel_coefficient'] = not gen.extraction_holds(g101, m1['w'], m1['E'], m1['pos'], m1['coef'], rows)
    m2 = copy.deepcopy(d); m2['w'][7] += 1
    rejected['weight'] = not gen.extraction_holds(g101, m2['w'], m2['E'], m2['pos'], m2['coef'], rows)
    m3 = copy.deepcopy(d); m3['E'][4] += 1
    rejected['target'] = not gen.extraction_holds(g101, m3['w'], m3['E'], m3['pos'], m3['coef'], rows)
    m4 = list(ours); m4[9] = m4[9].replace('(-3)', '(-4)', 1)
    rejected['parent_row'] = bind101.parse_row(m4[9]) != pj[9]
    m5 = list(h105); m5[1] = m5[1][:-1] + ('0' if m5[1][-1] != '0' else '1')
    rejected['port_hash'] = m5 != h55
    need(all(rejected.values()), 'a mutation was accepted')
    report['rejected_mutations'] = rejected
    report['pins'] = d['pins']
    report['h1868_json_sha256'] = hashlib.sha256((P105 / 'equations/h1868.json').read_bytes()).hexdigest()
    report['status'] = 'PASS'
    (REC / 'CHECK.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n', encoding='utf-8')
    print(json.dumps(report, sort_keys=True))


if __name__ == '__main__':
    main()
