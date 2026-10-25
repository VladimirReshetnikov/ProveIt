#!/usr/bin/env python3
"""Evaluate one delivered polynomial at a supplied integer tuple."""
import argparse,json,sys
from pathlib import Path
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('equation',type=Path);p.add_argument('point',type=Path);a=p.parse_args()
 e=json.loads(a.equation.read_text());x=json.loads(a.point.read_text())
 if not isinstance(x,list) or len(x)!=len(e['variables']) or any(type(z) is not int for z in x):raise ValueError('Expected one integer for each variable')
 residuals=[]
 for r in e['residuals']:
  total=0
  for c,m in r['terms']:
   for i in m:c*=x[i]
   total+=c
  residuals.append(total)
 value=sum(t*t for t in residuals)
 print(json.dumps({'value':value,'is_zero':value==0,'nonzero_residuals':sum(t!=0 for t in residuals)}))
if __name__=='__main__':main()
