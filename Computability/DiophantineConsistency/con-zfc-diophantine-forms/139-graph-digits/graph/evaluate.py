#!/usr/bin/env python3
"""Evaluate a released graph polynomial at one explicit integer tuple."""
import argparse,json
from pathlib import Path

pa=argparse.ArgumentParser(description=__doc__);pa.add_argument('polynomial',type=Path);pa.add_argument('point',type=Path)
a=pa.parse_args();p=json.loads(a.polynomial.read_text());x=json.loads(a.point.read_text())
if not isinstance(x,list) or len(x)!=len(p['variables']) or any(type(v) is not int for v in x):raise ValueError('Wrong integer tuple')
value=0
for c,m in p['terms']:
    for i in m:c*=x[i]
    value+=c
print(value)
