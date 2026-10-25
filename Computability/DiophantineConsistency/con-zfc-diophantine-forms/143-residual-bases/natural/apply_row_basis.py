#!/usr/bin/env python3
"""Replay the explicit reversible row shears and materialize the final SOS."""
from pathlib import Path
import argparse,copy,json
from collections import defaultdict

def emit(source,operations):
    rows=[{tuple(m):c for c,m in r['terms']} for r in source['residuals']]
    for i,j,k in operations:
        if type(k) is not int or i==j or not k:raise ValueError('invalid elementary shear')
        for m,c in rows[j].items():
            rows[i][m]=rows[i].get(m,0)+k*c
            if not rows[i][m]:del rows[i][m]
    total=defaultdict(int)
    for r in rows:
        for m,c in r.items():
            for n,d in r.items():total[tuple(sorted(m+n))]+=c*d
    total={m:c for m,c in total.items() if c}
    target=copy.deepcopy(source)
    target['variant']+='.unimodular_row_basis42'
    target['residuals']=[{'label':'basis.R'+str(i).zfill(3),'terms':[[c,list(m)] for m,c in sorted(r.items())]} for i,r in enumerate(rows)]
    target['metrics'].update(variables=len(target['variables']),quadratic_rows=len(rows),exact_degree=max(map(len,total)),expanded_monomials=len(total),max_abs_expanded_coefficient=max(map(abs,total.values())),max_abs_row_coefficient=max(abs(c) for r in rows for c in r.values()),elementary_unimodular_row_shears=len(operations))
    return target,dict(schema='sparse_integer_polynomial_v1',domain=source['domain'],variables=len(source['variables']),terms=[[c,list(m)] for m,c in sorted(total.items())])

def main():
    p=argparse.ArgumentParser();p.add_argument('source',type=Path);p.add_argument('operations',type=Path);p.add_argument('output',type=Path);a=p.parse_args()
    eq,poly=emit(json.loads(a.source.read_text()),json.loads(a.operations.read_text()))
    a.output.mkdir(parents=True,exist_ok=True)
    for name,obj in [('equation.json',eq),('expanded_polynomial.json',poly)]:
        (a.output/name).write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')
    print(json.dumps(eq['metrics'],indent=2))
if __name__=='__main__':main()
