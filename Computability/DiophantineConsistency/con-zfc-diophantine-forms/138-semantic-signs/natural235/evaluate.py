#!/usr/bin/env python3
from pathlib import Path
import argparse,json
p=argparse.ArgumentParser();p.add_argument('equation',type=Path);p.add_argument('point',type=Path);a=p.parse_args()
e=json.loads(a.equation.read_text());v=json.loads(a.point.read_text())
if not isinstance(v,list) or len(v)!=len(e['variables']) or not all(type(x)is int and x>=0 for x in v):raise ValueError('Expected one nonnegative integer per coordinate')
res=[]
for row in e['residuals']:
 z=0
 for c,m in row['terms']:
  q=c
  for i in m:q*=v[i]
  z+=q
 res.append(z)
print(json.dumps({'value':sum(x*x for x in res),'zero':not any(res),'nonzero_residuals':sum(x!=0 for x in res)}))
