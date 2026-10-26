#!/usr/bin/env python3
"""Rebuild the free-chart degree-190 polynomial from the pinned parent."""
import argparse
import collections
import copy
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def construct(parent):
    graph = copy.deepcopy(parent)
    center = [
        ['wc_A', '+', 'Am1', 1],
        ['wc_kqY', '*', 'k', 'qY'],
        ['wc_e2', '*', 'wc_kqY', 'wc_kqY'],
        ['wc_qYp1', '+', 'qY', 1],
        ['wc_kYYp1', '*', 'wc_kqY', 'wc_qYp1'],
        ['wc_sinner', '-', 'V0kk', 'wc_kYYp1'],
        ['wc_S', '*', 'wc_kqY', 'wc_sinner'],
        ['wc_U2', '*', 'U', 'U'],
        ['wc_theta', '*', 'wc_U2', 'cTR'],
        ['wc_threeE', '*', 3, 'Dtau'],
        ['wc_Zc', '+', 'wc_threeE', 'wc_e2'],
        ['wc_thetaZc', '*', 'wc_theta', 'wc_Zc'],
        ['wc_bmc', '-', 'cTR', 'c'],
        ['wc_Rc', '-', 'wc_thetaZc', 'wc_bmc'],
        ['wc_E2', '*', 'Dtau', 'Dtau'],
        ['wc_fourE2', '*', 4, 'wc_E2'],
        ['wc_S2', '*', 'wc_S', 'wc_S'],
        ['wc_threeS2', '*', 3, 'wc_S2'],
        ['wc_e22', '*', 'wc_e2', 'wc_e2'],
        ['wc_sum1', '+', 'wc_fourE2', 'wc_threeS2'],
        ['wc_Sc', '+', 'wc_sum1', 'wc_e22'],
        ['wc_EV', '*', 'Dtau', 'V'],
        ['wc_fourEV', '*', 4, 'wc_EV'],
        ['wc_thetaSc', '*', 'wc_theta', 'wc_Sc'],
        ['wc_Vdiff', '-', 'wc_fourEV', 'wc_thetaSc'],
        ['wc_Apart', '*', 'wc_A', 'wc_Vdiff'],
        ['wc_SRc', '*', 'wc_S', 'wc_Rc'],
        ['wc_twoSRc', '*', 2, 'wc_SRc'],
        ['wc_inner', '+', 'wc_Apart', 'wc_twoSRc'],
        ['wc_Omega', '*', 'U', 'wc_inner'],
    ]
    rows = []
    for name, op, x, y in parent['source']:
        if name == 'L':
            rows.extend(center)
            rows.append(['wc_b2', '*', 'cTR', 'cTR'])
            rows.append(['L', '*', 'wc_b2', 'UE'])
        elif name == 'center':
            rows.append(['wc_raw_center', op, x, y])
            rows.append(['center', '-', 'wc_raw_center', 'wc_Omega'])
        elif name == 'RG':
            rows.append([name, op, x, 'wc_G16'])
        else:
            rows.append([name, op, x, y])
        if name == 'Dg':
            rows.append(['wc_G16', '*', 16, 'Dg'])
    graph.update(
        name='positive10_degree190_ops120',
        source=rows,
        operations=len(rows),
        operation_breakdown=dict(sorted(collections.Counter(r[1] for r in rows).items())),
        exact_degree=190,
        transport_weight='b^2 U E',
        root_scale=4,
        proof='PROOF.md',
        parent={
            'path':'inherited/parent87.json',
            'sha256':hashlib.sha256((ROOT/'inherited/parent87.json').read_bytes()).hexdigest(),
        },
        generation='Whole-product polynomial centering in the free Y=s chart, with weighted square transport b^2 U E.',
        normalization='lambda=q; Y=s; no auxiliary positive shift',
    )
    graph['coefficient_binding']['path']='coefficients'
    graph['coefficient_binding']['endianness']='little'
    return graph


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    parent=json.loads((ROOT/'inherited/parent87.json').read_text())
    graph=construct(parent)
    target=ROOT/'equation.json'
    data=json.dumps(graph,indent=2)+'\n'
    if args.check:
        if target.read_text()!=data:
            raise ValueError('Equation differs from reconstruction')
    else:
        target.write_text(data)
    print(json.dumps({k:graph[k] for k in ['name','operations','operation_breakdown','exact_degree']}))


if __name__=='__main__':
    main()
