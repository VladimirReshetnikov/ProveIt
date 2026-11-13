#!/usr/bin/env python3
"""Binding checker for the Nine121 Lean modules of the 101/1,057 nine-positive endpoint.

The 1,057 form reuses the whole 101/420 prefix and contract. Checks (standard library only):
  1. the 101/420 bindings, re-run from ../../nine-positive-p101-420-endpoint/tools/check_binding.py
     (generated N101Source/N101Layout byte-identical, Source31Rows = the 22 parent equations,
     101's original31 port SHA-256 = package 55's wang943-mixed-121x8801 payloads);
  2. boundary_complete.json (SHA-256 pinned) has exactly the nodes 0..434 of boundary_simple.json
     (SHA-256 pinned): the prefix, the kernels, the ten coefficient leaves, the scales and the
     saturated registers through DFI; and the same W, height, scale exponents, B-threshold and
     coefficient recipes, so N101Prefix/N101Contract are the prefix of both equations;
  3. Nine121/N1057Majorant.lean is byte-identical to a fresh run of generate_n1057_majorant.py,
     whose model checks Pi = data/saturated_corrected_P.json, Pi^2 - sigma^2 DFI = the 2,599-term
     defect whose translate by A=x+3, C=y+1, i=u+1, Z=v+1 equals the package's 36,309-term positive
     certificate, both domination checks, and the Kronecker bounds and the equality pos = neg at
     the Kronecker point (exactly, about 5.09 Mbit);
  4. rejected mutations: a changed majorant coefficient breaks Pi = saturated_corrected_P.json and
     the Kronecker equality; a changed defect coefficient breaks the Kronecker equality; a node of
     the shared prefix changed in boundary_complete is detected; a changed port hash is detected.
Writes CHECK.json next to the record README.
"""
from pathlib import Path
import copy, hashlib, importlib.util, json

HERE = Path(__file__).resolve()
REC = HERE.parents[1]
DC = HERE.parents[3]
LEAN = DC / 'Lean/DiophantineConsistency/Nine121'
FORMS = DC / 'con-zfc-diophantine-forms'
NINE = FORMS / '101-constructive-reductions/nine'
SIMPLE_PIN = 'ea0804c38989d9c5bedeca04a9dced04d4daeb1b3cc79176e3f0580b76f83528'


def need(ok, msg):
    if not ok:
        raise SystemExit('FAIL: ' + msg)


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


B420 = load_module('b420', HERE.parents[1].parent / 'nine-positive-p101-420-endpoint/tools/check_binding.py')
MAJ = load_module('maj', HERE.parent / 'generate_n1057_majorant.py')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    report = {}
    # 1. the 101/420 bindings
    gen = B420.gen
    d = gen.analyse()
    out = gen.render(d)
    for name, text in out.items():
        need((LEAN / name).read_text(encoding='utf-8') == text, 'stale generated ' + name)
    ours = B420.lean_rows(LEAN / 'Source31Rows.lean', 'rows')
    docs, _ = gen.load()
    parent = docs['parent']
    names = parent['variables'] + parent['constants']
    porder = parent['sparse_term_coordinate_order']
    pj = [gen.poly_of(eq, porder, names) for eq in parent['equations']]
    need(all(B420.parse_row(t) == pj[k] for k, t in enumerate(ours)), 'parent rows')
    need(B420.extraction_ok(d), 'extraction identities')
    p55 = json.loads((FORMS / '55-congruence-norms/fourteen/coefficients/ports.json').read_text())
    need(p55['instance'] == 'wang943-mixed-121x8801', '55 instance')
    rec = json.loads((NINE / 'COEFFICIENT_RECONSTRUCTION.json').read_text())
    h55 = [p['sha256'] for p in p55['ports']]
    h101 = [p['sha256'] for p in rec['original31']]
    need(h55 == h101 and all(p['equal'] for p in rec['original31']), 'port payload hashes')
    report['shared_101_420_bindings'] = dict(generated_files=sorted(out), parent_rows=len(ours),
                                             pins=d['pins'])
    report['ports_sha256'] = dict(zip(['beta', 'K', 'MC', 'MF'], h55))
    # 2. the shared prefix
    simple_p = NINE / 'equations/boundary_simple.json'
    complete_p = NINE / 'equations/boundary_complete.json'
    need(sha(simple_p) == SIMPLE_PIN, 'boundary_simple.json pin')
    need(sha(complete_p) == MAJ.PIN, 'boundary_complete.json pin')
    ds = json.loads(simple_p.read_bytes())
    dc = json.loads(complete_p.read_bytes())

    def shared(a, b):
        keys = ('W', 'height', 'base_scale_exponent', 'threshold_scale_exponent', 'threshold_B_power',
                'threshold_b_power', 'Ecode', 'coefficient_recipes', 'variables', 'prefix_mode')
        return a['nodes'][:435] == b['nodes'][:435] and all(a[k] == b[k] for k in keys)
    need(shared(ds, dc), 'shared prefix nodes 0..434 and parameters')
    report['shared_prefix'] = 'boundary_complete nodes 0..434 = boundary_simple nodes 0..434'
    # 3. the majorant module
    mj = MAJ.load(MAJ.SRC, MAJ.PIN)
    defect, stats = MAJ.model_checks(mj)
    need((LEAN / 'N1057Majorant.lean').read_text(encoding='utf-8') == MAJ.render(mj, MAJ.PIN, defect,
                                                                                  stats['kron_bits']),
         'stale N1057Majorant.lean')
    report['majorant'] = stats
    report['package_data_sha256'] = {
        'saturated_corrected_P.json': sha(NINE / 'data/saturated_corrected_P.json'),
        'saturated_corrected_certificate.json': sha(NINE / 'data/saturated_corrected_certificate.json'),
    }
    # 4. mutations
    rej = {}
    m1 = copy.deepcopy(mj)
    m1['nodes'][437]['value'] += 1
    Pi1 = MAJ.block(m1, MAJ.p_add, MAJ.p_mul, MAJ.p_lit, *MAJ.X)
    rej['majorant_coefficient_vs_package_P'] = dict(Pi1) != MAJ.terms_of(NINE / 'data/saturated_corrected_P.json')
    X0 = 1 << stats['kron_bits']
    box = MAJ.BOX
    pt = (X0, X0 ** box[0], X0 ** (box[0] * box[1]), X0 ** (box[0] * box[1] * box[2]))
    w1 = MAJ.id_value(m1, defect, pt)
    rej['majorant_coefficient_vs_kronecker'] = w1[0] != w1[1]
    bad = [(m, c + (1 if k == 100 else 0)) for k, (m, c) in enumerate(defect)]
    w2 = MAJ.id_value(mj, bad, pt)
    rej['defect_coefficient_vs_kronecker'] = w2[0] != w2[1]
    dc2 = copy.deepcopy(dc)
    dc2['nodes'][100] = dict(dc2['nodes'][100]); dc2['nodes'][100]['left'] = dc2['nodes'][100].get('left', 0) + 1
    rej['shared_prefix_node'] = not shared(ds, dc2)
    m5 = list(h101); m5[2] = m5[2][:-1] + ('0' if m5[2][-1] != '0' else '1')
    rej['port_hash'] = m5 != h55
    need(all(rej.values()), 'a mutation was accepted')
    report['rejected_mutations'] = rej
    report['status'] = 'PASS'
    (REC / 'CHECK.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n', encoding='utf-8')
    print(json.dumps(report, sort_keys=True))


if __name__ == '__main__':
    main()
