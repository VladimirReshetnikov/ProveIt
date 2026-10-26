#!/usr/bin/env python3
import argparse,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
def evaluate(eq,x):
 if type(x)is not list or len(x)!=len(eq['variables'])or any(type(a)is not int for a in x):raise ValueError('exact integer tuple required')
 rs=[]
 for r in eq['residuals']:
  s=0
  for c,m in r['terms']:
   for i in m:c*=x[i]
   s+=c
  rs.append(s)
 p=sum(a*a for a in rs);return{'polynomial_value':p,'is_zero':p==0,'residual_values':rs}
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('endpoint');ap.add_argument('point',type=Path);a=ap.parse_args();choices=json.loads((ROOT/'ENDPOINTS.json').read_text())
 if a.endpoint not in choices:raise ValueError('unknown endpoint')
 print(json.dumps(evaluate(json.loads((ROOT/a.endpoint/'equation.json').read_text()),json.loads(a.point.read_text()))))
