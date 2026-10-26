#!/usr/bin/env python3
"""Evaluate one supplied tuple; not a root search or consistency decision."""
import argparse,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def evaluate(e,x):
 if type(x)is not list or len(x)!=len(e['variables'])or any(type(v)is not int for v in x):raise ValueError('exact integer tuple of declared length required')
 residuals=[]
 for row in e['residuals']:
  out=0
  for c,m in row['terms']:
   for i in m:c*=x[i]
   out+=c
  residuals.append(out)
 value=sum(v*v for v in residuals);return {'polynomial_value':value,'is_zero':value==0,'residuals':residuals}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('endpoint');ap.add_argument('point',type=Path);args=ap.parse_args();known=json.loads((ROOT/'ENDPOINTS.json').read_text())
 if args.endpoint not in known:raise ValueError('unknown endpoint')
 result=evaluate(json.loads((ROOT/args.endpoint/'equation.json').read_text()),json.loads(args.point.read_text()));print(json.dumps(result))
if __name__=='__main__':main()
