#!/usr/bin/env python3
"""Construct three literal P66 descendants; no source coefficient is changed."""
import copy
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def build(mode):
    p = json.loads((ROOT / 'inherited/P66.json').read_text())
    rows = []
    for row in p['source']:
        name, op, a, b = row
        if name == 'q3' and mode != 'E':
            rows.append(['q4', '*', 'q2', 'q2'])
        if name == 'hE':
            rows.append(['carrier_product', '*', 'n', 'E' if mode == 'E' else 'q4'])
        elif name == 'index_partial':
            rows.append(['carrier_partial', '-', 'k', 'carrier_product'])
        elif name == 'Nk':
            rows.append(['carrier', '-', 'carrier_partial', 'R'])
        elif name == 'normalized_S':
            if mode == 'q_direct':
                rows.extend([
                    ['ordinate0', '*', 'i', 'c2'],
                    ['ordinate', '*', 'q2', 'ordinate0'],
                    ['normalized_S', '*', 'Delta', 'ordinate'],
                ])
            else:
                rows.extend([
                    ['normalized_S0', '*', 'i', 'Dc2'],
                    ['normalized_S', '*', 'E' if mode == 'E' else 'q2', 'normalized_S0'],
                ])
        elif name == 'y2':
            rows.append(['y2', '*', 'carrier', 'carrier'])
        elif name == 'scaled_f2' and mode == 'q_direct':
            rows.append(['strong_product', '*', 'normalized_S', 'ordinate'])
        elif name == 'scaled_Ns' and mode == 'q_direct':
            rows.append(['strong_norm', '-', 'f2', 'strong_product'])
        elif name == 'product2':
            continue
        elif name == 'product3':
            rows.append(['product3', '*', 'product1', 'Nt'])
        elif name == 'product4' and mode == 'q_direct':
            rows.append(['product4', '*', 'product3', 'strong_norm'])
        elif name == 'polynomial' and mode == 'q_direct':
            rows.append(['polynomial', '-', 'product4', 1])
        else:
            rows.append(row)
    p['name'] = {'E':'positive14_ops66_degree174', 'q':'positive14_ops67_degree158', 'q_direct':'positive14_ops68_degree146'}[mode]
    p['source'] = rows
    p['witnesses'] = ['n' if x == 'h' else x for x in p['witnesses'] if x != 'y']
    p['operations'] = len(rows)
    p['operation_counts'] = {op:sum(row[1] == op for row in rows) for op in ('*','+','-')}
    p['exact_degree'] = {'E':174,'q':158,'q_direct':146}[mode]
    p['carrier_modulus'] = 'E' if mode == 'E' else 'q4'
    p['strong_ordinate_multiplier'] = 'E' if mode == 'E' else 'q2'
    p['proof'] = '../PROOF.md'
    p['coefficient_binding']['path'] = '../coefficients/'
    p['coefficient_binding']['certificate'] = '../inherited/start_only_certificate.json'
    p['coefficient_binding']['ordinary_proof'] = '../inherited/START_ONLY_PROOF.md'
    p['coefficient_binding']['recipe'] = '../coefficients.tex'
    p['coefficient_binding']['builder'] = '../rebuild_coefficients.py'
    p['coefficient_binding']['recipe_origin'] = '174-start-marker-compositions/compact66/preferred4127'
    p['coefficient_binding']['recipe_commit'] = '02a78a08603cbae248c19c23a75907c6c6bd6443'
    p['proof_boundary'] = 'New residue-ordinate elimination, ordinary proof at the retained P66 and whole Start-only4127 native/refutation calibration. No new proof-assistant object.'
    p['parent'] = {'path':'../inherited/P66.json','sha256':hashlib.sha256((ROOT/'inherited/P66.json').read_bytes()).hexdigest()}
    return p


if __name__ == '__main__':
    for mode in ('E','q','q_direct'):
        p = build(mode)
        target=ROOT/'equations'/f"{p['name']}.json"
        target.write_text(json.dumps(p,indent=2)+'\n')
        print(p['name'],p['operations'],p['operation_counts'])
