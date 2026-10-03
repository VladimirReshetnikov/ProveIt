#!/usr/bin/env python3
"""Independent checker for exported polynomial/power-atom certificates."""
import json
import sys
from pathlib import Path


def evaluate(terms, values):
    total=0
    for coefficient,monomial in terms:
        term=coefficient
        for variable in monomial:
            term*=values[variable]
        total+=term
    return total


def check(path):
    data=json.loads(Path(path).read_text())
    values=data['sample_assignment']
    assert all(type(v) is int and v>=0 for v in values)
    assert len(values)==len(data['variables'])
    assert all(len(m)<=2 for terms in data['quadratic_residuals'] for _,m in terms)
    residual_values=[evaluate(p,values) for p in data['quadratic_residuals']]
    assert all(x==0 for x in residual_values), 'Arithmetic residual failed'
    for a in data['power_atoms']:
        assert values[a['result']]==pow(a['base'],values[a['exponent']]), 'Power atom failed'
    if 'expanded_quartic' in data:
        assert all(len(m)<=4 for _,m in data['expanded_quartic'])
        assert evaluate(data['expanded_quartic'],values)==0
        # Check the expanded SOS identity off the zero set on a deterministic test vector.
        v=[(i*7+3)%11 for i in range(len(values))]
        assert evaluate(data['expanded_quartic'],v)==sum(evaluate(p,v)**2 for p in data['quadratic_residuals'])
    print(f'PASS {Path(path).name}: {len(values)} natural coordinates, '
          f'{len(residual_values)} quadratic residuals, {len(data["power_atoms"])} power atoms')


if __name__=='__main__':
    if len(sys.argv)<2:
        raise SystemExit('Usage: python check_export.py FILE.json [FILE.json ...]')
    for name in sys.argv[1:]: check(name)
