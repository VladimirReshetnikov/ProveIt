#!/usr/bin/env python3
"""Binding checker for the Nine121 Lean modules of the 82/726 nine-positive endpoint.

Checks (exact integer polynomial arithmetic, standard library only):
  1. Nine121/N82Layout.lean is byte-identical to a fresh run of generate_n82_layout.py, which checks
     that package 65's shared-tap kernels belong to the package-31 parent (source SHA-256 1c336ba0...),
     takes the rows as the parent rows after the recorded row operations (no coordinate map), and
     re-derives all 22 extraction identities [T^{q_k}](K2 U^2 + K1 U + K0) = 2 rho_k coefficient by
     coefficient; Nine121/N82Majorant.lean is byte-identical to generate_n82_majorant.py;
  2. Source31Rows.rows parses to the 22 equations of the package-31 parent (as in the 101 record);
  3. the four raw coefficient SHA-256 values of package 82's COEFFICIENT_RECONSTRUCTION.json
     (instance wang943-mixed-121x8801) equal package 55's wang943-mixed-121x8801 payload hashes (the
     tuple of Mixed121Ports.ports);
  4. the source parameters of laurent9_positive.json (base and threshold exponents, B-power of N,
     height, W, layout and source hashes) are those of N82Prefix / N82Layout, and the prefix
     definitions of N82Prefix have the PROOF.md exponents (N0 = B^117, L = b B^1991,
     N = 2^17079501 b B^1057, t = b B^116);
  5. rejected mutations: a changed kernel coefficient, weight, target, parent-row coefficient and port
     hash are each detected.
Writes CHECK.json next to the record README.
"""
from pathlib import Path
import copy, hashlib, importlib.util, json, re

HERE = Path(__file__).resolve()
REC = HERE.parents[1]
DC = HERE.parents[3]
LEAN = DC / 'Lean/DiophantineConsistency'
FORMS = DC / 'con-zfc-diophantine-forms'
P82 = FORMS / '82-pell-congruences/nine_full_radical'


def need(ok, msg):
    if not ok:
        raise SystemExit('FAIL: ' + msg)


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


gen = load_module('gen82', HERE.parent / 'generate_n82_layout.py')
mgen = load_module('mgen82', HERE.parent / 'generate_n82_majorant.py')
bind101 = load_module('bind101', DC / 'research/nine-positive-p101-420-endpoint/tools/check_binding.py')


def main():
    report = {}
    # 1. generated files
    d = gen.analyse()
    g = d['g']
    need((LEAN / 'Nine121/N82Layout.lean').read_text(encoding='utf-8') == gen.render(d), 'stale N82Layout.lean')
    md = mgen.analyse()
    need((LEAN / 'Nine121/N82Majorant.lean').read_text(encoding='utf-8') == mgen.render(md), 'stale N82Majorant.lean')
    report['generated_files'] = ['N82Layout.lean', 'N82Majorant.lean']
    report['kernel_records'] = list(d['counts'])
    report['interactions'] = [sum(map(len, d[s])) for s in ('S2', 'S1', 'S0')]
    rows = d['rows']
    need(gen.extraction_holds(g, d['w'], d['E'], d['pos'], d['coef'], rows), 'unmutated extraction')
    report['extraction_identities'] = 22
    # 2. parent rows
    ours = bind101.lean_rows(LEAN / 'Nine121/Source31Rows.lean', 'rows')
    for k, row in enumerate(ours):
        need(bind101.parse_row(row) == d['prows'][k], f'parent row {k}')
    report['parent_rows'] = 22
    # 3. ports
    p55 = json.loads((FORMS / '55-congruence-norms/fourteen/coefficients/ports.json').read_text())
    need(p55['instance'] == 'wang943-mixed-121x8801', '55 instance')
    rec = json.loads((P82 / 'COEFFICIENT_RECONSTRUCTION.json').read_text())
    need(rec['instance'] == 'wang943-mixed-121x8801' and rec['status'] == 'PASS', '82 reconstruction instance')
    need([e['port'] for e in rec['entries']] == ['beta', 'K', 'MC', 'MF_source'], 'port order (MF already shifted)')
    need(all(e['raw_byte_identical'] for e in rec['entries']), 'raw reconstruction')
    h55 = [p['sha256'] for p in p55['ports']]
    h82 = [e['raw_sha256'] for e in rec['entries']]
    need(h55 == h82, 'port payload hashes')
    report['ports_sha256'] = dict(zip(['beta', 'K', 'MC', 'MF'], h55))
    # 4. source parameters and prefix constants
    eq = json.loads((P82 / 'laurent9_positive.json').read_text())
    need((eq['base_scale_exponent'], eq['threshold_scale_exponent'], eq['threshold_B_power'], eq['Kcode'], eq['W'])
         == (2134939, 17079501, 1057, 1873, 116), 'JSON source parameters')
    need(eq['layout_sha256'] == gen.PINS['layout'][1] and eq['source_sha256'] == gen.PARENT_SHA, 'layout/source hashes')
    need(eq['port_bit_lengths'] == [1064921, 1070004, 1064921, 1064922] and eq['coherent_tuple'] == 'old31',
         'port bit lengths')
    pre = (LEAN / 'Nine121/N82Prefix.lean').read_text(encoding='utf-8')
    for pat in [r'def thresholdScale82 : ℤ := 2 \^ 17079501', r'def N0 \(b : A\) : A := Bq b \^ 117',
                r'def Lq \(b : A\) : A := b \* Bq b \^ 1991',
                r'def Nq \(b : A\) : A := \(thresholdScale82 : A\) \* b \* Bq b \^ 1057',
                r'def tq \(b : A\) : A := b \* Bq b \^ 116']:
        need(re.search(pat, pre) is not None, 'N82Prefix constant ' + pat)
    p101 = (LEAN / 'Nine121/N101Prefix.lean').read_text(encoding='utf-8')
    need('def baseScale : ℤ := 2 ^ 2134939' in p101, 'base scale')
    report['prefix'] = {'kappa': 2134939, 'theta': 17079501, 'N0': 'B^117', 'L': 'b B^1991',
                        'N': '2^theta b B^1057', 't': 'b B^116', 'H': 1873,
                        'layout_sha256': eq['layout_sha256'], 'source_sha256': eq['source_sha256']}
    # 5. mutations
    rejected = {}
    m1 = copy.deepcopy(d['coef']); m1[2][5] = g.add(m1[2][5], {(0, 0, 0, 0): 1})
    rejected['kernel_coefficient'] = not gen.extraction_holds(g, d['w'], d['E'], d['pos'], m1, rows)
    m2 = list(d['w']); m2[7] += 1
    rejected['weight'] = not gen.extraction_holds(g, m2, d['E'], d['pos'], d['coef'], rows)
    m3 = list(d['E']); m3[4] += 1
    rejected['target'] = not gen.extraction_holds(g, d['w'], m3, d['pos'], d['coef'], rows)
    m4 = list(ours); m4[9] = m4[9].replace('(-3)', '(-4)', 1)
    rejected['parent_row'] = bind101.parse_row(m4[9]) != d['prows'][9]
    m5 = list(h82); m5[1] = m5[1][:-1] + ('0' if m5[1][-1] != '0' else '1')
    rejected['port_hash'] = m5 != h55
    need(all(rejected.values()), 'a mutation was accepted')
    report['rejected_mutations'] = rejected
    report['pins'] = d['pins']
    report['laurent9_positive_sha256'] = hashlib.sha256((P82 / 'laurent9_positive.json').read_bytes()).hexdigest()
    report['status'] = 'PASS'
    (REC / 'CHECK.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n', encoding='utf-8')
    print(json.dumps(report, sort_keys=True))


if __name__ == '__main__':
    main()
