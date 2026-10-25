#!/usr/bin/env python3
"""Produce the five trace-linear compact polynomials from frozen data.

This producer reads its inherited graphs as JSON. It executes no inherited
program. All independent variables remain strictly positive integers.
"""
from pathlib import Path
from collections import Counter
import copy, hashlib, json, argparse

ROOT = Path(__file__).resolve().parent
VARIANTS = [
    ('trace75_degree402', 'inherited/lucas/parent/equation_XY_V2.json', 'q3', 402),
    ('trace76_degree352', 'inherited/lucas/parent/equation_XY_bV.json', 'q3', 352),
    ('trace79_degree290', 'inherited/cofinal/q2_bv.json', 'q2', 290),
    ('trace80_degree258', 'inherited/cofinal/q1_bv.json', 'q1', 258),
    ('trace87_degree232', 'inherited/lucas/equation_bV.json', 'lucas', 232),
]

def construct(name, relative, chart, degree):
    parent = ROOT / relative
    graph = json.loads(parent.read_text())
    rows = []
    for register, op, left, right in graph['source']:
        if register == 'Fsqr':
            rows.append(['trace_f', '+', 'DpI2', 'Df'])
            continue
        if left == 'Fsqr': left = 'trace_f'
        if right == 'Fsqr': right = 'trace_f'
        rows.append([register, op, left, right])
    graph.update(name=name, source=rows, operations=len(rows),
        operation_breakdown=dict(Counter(row[1] for row in rows)),
        exact_degree=degree, chart=chart, proof='PROOF.md',
        parent={'path':relative, 'sha256':hashlib.sha256(parent.read_bytes()).hexdigest()},
        generation='The explicit doubled strong trace f=1+2a replaces f^2 in V=f(cT-R)-c. All other polynomial definitions are retained.',
        status='Ordinary proof composed with the named inherited native/refutation calibration; finite artifact checks do not replace the unbounded proof.')
    graph['coefficient_binding']['path'] = 'coefficients/'
    return graph

def main():
    parser=argparse.ArgumentParser(); parser.add_argument('--check',action='store_true')
    args=parser.parse_args(); results=[]
    for name,relative,chart,degree in VARIANTS:
        graph=construct(name,relative,chart,degree)
        target=ROOT/'equations'/(name+'.json')
        rendered=json.dumps(graph,indent=2)+'\n'
        if args.check:
            if target.read_text()!=rendered: raise ValueError('reconstruction mismatch: '+name)
        else:
            target.parent.mkdir(exist_ok=True); target.write_text(rendered)
        results.append({'equation':str(target.relative_to(ROOT)), 'domain':graph['domain'],
            'variables':len(graph['witnesses']),'operations':len(graph['source']),
            'degree':degree,'parent_operations':len(graph['source']),
            'parent_degree':json.loads((ROOT/relative).read_text())['exact_degree']})
    if not args.check: (ROOT/'RESULTS.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results,indent=2))

if __name__=='__main__': main()
