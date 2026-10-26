#!/usr/bin/env python3
"""Evaluate the supplied literal decic at one 212-integer tuple."""
import argparse,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def evaluate(e,x):
 if type(x)is not list or len(x)!=len(e['variables'])or any(type(v)is not int for v in x):raise ValueError('exact integer tuple required')
 residuals=[]
 for r in e['residuals']:
  total=0
  for c,m in r['terms']:
   for i in m:c*=x[i]
   total+=c
  residuals.append(total)
 v=sum(y*y for y in residuals);return{'polynomial_value':v,'is_zero':v==0,'residuals':residuals}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('point',type=Path);args=ap.parse_args();print(json.dumps(evaluate(json.loads((ROOT/'equations/equation.json').read_text()),json.loads(args.point.read_text()))))
if __name__=='__main__':main()
