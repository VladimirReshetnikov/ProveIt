#!/usr/bin/env python3
"""Evaluate a literal sum of squared residuals at a supplied integer tuple."""
import json,sys
from pathlib import Path
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
if len(sys.argv)!=3:raise SystemExit('Usage: python3 evaluate.py equation.json tuple.json')
eq=json.loads(Path(sys.argv[1]).read_text());x=json.loads(Path(sys.argv[2]).read_text())
if len(x)!=len(eq['variables']) or any(type(a)is not int for a in x):raise ValueError('Wrong dimension or noninteger coordinate')
res=[]
for row in eq['residuals']:
    total=0
    for c,mon in row['terms']:
        for i in mon:c*=x[i]
        total+=c
    res.append(total)
print(json.dumps({'polynomial_value':sum(a*a for a in res),'zero':all(a==0 for a in res),'nonzero_residual_count':sum(a!=0 for a in res)}))
