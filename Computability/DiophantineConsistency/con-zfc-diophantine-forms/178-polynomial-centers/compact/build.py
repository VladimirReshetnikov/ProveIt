#!/usr/bin/env python3
"""Construct five trace/inverse-Lucas circuits from a pinned literal parent.

This script reads the parent graph as data and executes no inherited code.
All coordinates are strictly positive integers. See PROOF.md for the
unbounded mathematical argument; this producer proves no such argument.
"""
from collections import Counter
from pathlib import Path
import argparse
import copy
import hashlib
import json

ROOT = Path(__file__).resolve().parent
VARIANTS = [('trace_inverse85', 'bV', None, 232),
            ('square_transport85', 'b2', None, 232),
            ('lower_center87', 'bV', 'Am1', 228),
            ('centered_transport88', 'bV', 'A', 224),
            ('quotient_center96', 'bV', 'quotient', 220)]


def construct(name, weight, centered, degree):
    parent_file = ROOT / 'parents/inverse85.json'
    parent = json.loads(parent_file.read_text())
    graph = copy.deepcopy(parent)
    rows = []
    for name0, op, x, y in parent['source']:
        if name0 == 'Fsqr':
            rows.append(['trace_f', '+', 'DpI2', 'Df'])
            continue
        if name0 == 'L' and centered:
            if centered in ('A','quotient'): rows.append(['A', '+', 'Am1', 1])
            if centered=='quotient':
                rows.extend([
                    ['Yp1','+','Y',1],
                    ['quotient_product','*','kY','Yp1'],
                    ['quotient_difference','-','V0kk','quotient_product'],
                    ['quotient_E','*','kY','quotient_difference'],
                    ['upper_root','*','A','UE'],
                    ['twice_upper','*',2,'upper_root'],
                    ['U_quotient','*','U','quotient_E'],
                    ['center_root','-','twice_upper','U_quotient']])
            else:
                rows.append(['center_root', '*', centered, 'UE'])
            rows.extend([
                ['center_bB', '*', 'cTR', 'Bt'],
                ['center_inner', '+', 'center_bB', 'center_root'],
                ['center_product', '*', 'V', 'center_inner'],
                ['center', '-', 'n', 'center_product']])
            continue
        if name0 in ('LBt','center') and centered:
            continue
        if name0 == 'L' and weight == 'b2':
            rows.append(['L', '*', 'cTR', 'cTR'])
            continue
        x = 'trace_f' if x == 'Fsqr' else x
        y = 'trace_f' if y == 'Fsqr' else y
        if name0=='RG' and centered=='quotient':y='scaledG'
        rows.append([name0, op, x, y])
        if name0=='Dg' and centered=='quotient':rows.append(['scaledG','*',4,'Dg'])
    graph.update(name=name, source=rows, operations=len(rows),
                 operation_breakdown=dict(Counter(r[1] for r in rows)),
                 exact_degree=degree, transport_weight=weight,
                 polynomial_center=bool(centered), center_parameter=centered,
                 root_scale=2 if centered=='quotient' else 1,
                 parent={'path': 'parents/inverse85.json',
                         'sha256': hashlib.sha256(parent_file.read_bytes()).hexdigest()},
                 generation='Trace-linear V, inverse-Lucas correction, optional b^2 transport and AUEV center.',
                 proof='PROOF.md')
    graph['coefficient_binding']['path'] = 'coefficients/'
    return graph


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--check', action='store_true')
    args = ap.parse_args()
    output = []
    for spec in VARIANTS:
        g = construct(*spec)
        path = ROOT / 'equations' / (spec[0] + '.json')
        text = json.dumps(g, indent=2) + '\n'
        if args.check:
            if path.read_text() != text:
                raise ValueError('reconstruction mismatch: ' + spec[0])
        else:
            path.write_text(text)
        output.append({k: g[k] for k in ('name', 'operations', 'exact_degree',
                                        'transport_weight', 'polynomial_center')})
    print(json.dumps(output, indent=2))


if __name__ == '__main__':
    main()
