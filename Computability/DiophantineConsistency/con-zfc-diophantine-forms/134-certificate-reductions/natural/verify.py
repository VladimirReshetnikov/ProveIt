#!/usr/bin/env python3
"""Independent finite checks and optional reconstruction of the natural quartic.

These checks do not decide solvability and are not a proof of Con(ZFC).
"""
from pathlib import Path
from copy import deepcopy
from hashlib import sha256
from fractions import Fraction
from math import comb, factorial, gcd
import argparse
import json
import subprocess
import sys
import tempfile

import check_contraction as cc
import check_affine_export as ae

ROOT = Path(__file__).resolve().parent

def need(test, message):
    if not test:
        raise ValueError(message)

def load(path):
    return json.loads(path.read_text())

def pell(a, n):
    x, y = 1, 0
    for _ in range(n):
        x, y = a*x+(a*a-1)*y, x+a*y
    return x, y

def arithmetic_controls():
    fixed = 0
    for t in range(3, 9):
        f0 = factorial(t)
        for f in sorted(set(range(2, 100)) | {f0-1, f0, f0+1}):
            n = f*f-1
            b = comb(n, t) if n >= t else 0
            if b:
                need((n**t//b == f) == (f == f0), 'floor fixed-point control')
                fixed += 1
        ds = [f0*f0//i-1 for i in range(1,t+1)]
        product = 1
        for i, d in enumerate(ds):
            need(d > 1 and (d+1) % f0 == 0, 'descending CRT modulus')
            for e in ds[:i]:
                need(gcd(d,e) == 1, 'CRT coprimality')
            product *= d
        need(product == comb(f0*f0-1,t), 'descending binomial product')
    cap = 0
    for a in (19, 29, 43):
        for ks in ((1,2), (2,2,3), (1,3,4)):
            h = 2*max(ks)+1
            ys = [pell(a,k)[1] for k in ks]
            yh = pell(a,h)[1]
            num = yh-h-sum((y-k)**2 for y,k in zip(ys,ks))
            need(num >= 0 and num % (a-1) == 0, 'one-row canonical completion')
            cap += 1
    t = 12
    f = factorial(t)
    ell, degree_bound = 2**22, 2**23
    a = f.bit_length()-1
    need(a*degree_bound < 2**a and 2*degree_bound <= 2**a, 'local majorant start')
    need(3*ell*(t+1) <= 2*f, 'label majorant start')
    return {'floor_examples':fixed, 'cap_examples':cap,
            'horizon_floor':t, 'factorial_floor':f, 'binary_floor_exponent':a,
            'local_majorant':degree_bound, 'label_majorant':ell}

def verify(rebuild=False):
    eq = load(ROOT/'equation.json')
    src = load(ROOT/'source/equation.json')
    meta = load(ROOT/'source/semantic.json')
    cert = load(ROOT/'elimination_certificate.json')
    poly = load(ROOT/'expanded_polynomial.json')
    receipt, terms = cc.verify(src, eq, cert)
    need(terms == poly['terms'], 'expanded polynomial differs')
    need((receipt['variables'],receipt['rows'],receipt['exact_degree'],
          receipt['expanded_monomials'],receipt['coefficient_height']) ==
         (233,182,4,7313,86543666), 'wrong measured endpoint')
    affine, affine_cert = ae.verify(meta, src)
    affine.update(ae.check_expansion(src,load(ROOT/'source/expanded_polynomial.json')))
    labels = [r['label'] for r in meta['rows']]
    need(labels.count('fact0.floor') == 1 and 'fact0.ceiling' not in labels,
         'incorrect factorial interface')
    need(labels.count('index_cap.one_row_bound_and_errors') == 1,
         'missing one-row certificate')
    need('index_cap.all_indices_bound' not in labels and
         'index_cap.squared_index_errors' not in labels, 'old cap retained')
    need(meta['amplification']['horizon_minimum'] == 12, 'wrong horizon')
    need(meta['semantic_anchor'] and meta['dominant_modulus'], 'missing architecture')
    need(len(meta['powers']) == 6 and len(meta['modular_requests']) == 11 and
         len(meta['seed_certificates']) == 14, 'wrong arithmetic ports')
    mutated = deepcopy(eq)
    mutated['residuals'][0]['terms'][0][0] += 1
    badcert = deepcopy(cert)
    badcert['target_equation_sha256'] = sha256(cc.canonical(mutated)).hexdigest()
    rejected = False
    try:
        cc.verify(src, mutated, badcert)
    except (ValueError, KeyError, IndexError):
        rejected = True
    need(rejected, 'corrupted coefficient accepted after rehashing')
    checked = 0
    for row in load(ROOT/'ENGINE_MAP.json'):
        need(sha256((ROOT/row['path']).read_bytes()).hexdigest() == row['sha256'],
             'engine hash: '+row['path'])
        checked += 1
    rebuild_files = 0
    if rebuild:
        with tempfile.TemporaryDirectory(prefix='conzfc-natural-') as td:
            cmd = [sys.executable]+(['-O'] if sys.flags.optimize else [])+[
                '-B',str(ROOT/'build.py'),'--output',td,'--support-cap','64',
                '--dominant','--semantic-anchor','--coordinates','consecutive']
            subprocess.run(cmd,check=True,stdout=subprocess.DEVNULL)
            td = Path(td)
            for name in ('equation.json','expanded_polynomial.json',
                         'elimination_certificate.json','VERIFICATION.json'):
                need((td/'natural'/name).read_bytes() == (ROOT/name).read_bytes(),
                     'target reconstruction: '+name)
                rebuild_files += 1
            for name in ('equation.json','expanded_polynomial.json','METRICS.json',
                         'semantic.json','local_majorant.json'):
                need((td/'raw'/name).read_bytes() == (ROOT/'source'/name).read_bytes(),
                     'source reconstruction: '+name)
                rebuild_files += 1
    return {'status':'PASS','scope':'finite exact identities, coefficients, reconstruction, and bounded controls; not a solvability test',
            'projection':receipt,'affine_export':affine,
            'arithmetic_controls':arithmetic_controls(),
            'corruption_rejected_after_rehash':rejected,
            'engine_files_checked':checked,'reconstructed_files':rebuild_files,
            'optimized_python':bool(sys.flags.optimize)}

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--rebuild',action='store_true')
    p.add_argument('--receipt',type=Path)
    a = p.parse_args()
    data = json.dumps(verify(a.rebuild),indent=2,sort_keys=True)+'\n'
    if a.receipt:
        a.receipt.write_text(data)
    print(data,end='')
