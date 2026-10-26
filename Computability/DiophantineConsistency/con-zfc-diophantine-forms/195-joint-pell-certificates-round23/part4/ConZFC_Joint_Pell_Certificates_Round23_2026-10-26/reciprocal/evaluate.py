#!/usr/bin/env python3
"""Evaluate a supplied tuple; never searches for a zero or decides consistency."""
import argparse,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
NAMES=['integer138_degree8','integer114_degree16','integer113_degree16','control114_degree16']
def polynomial(terms,point,modulus=None):
 total=0
 for coefficient,monomial in terms:
  value=coefficient
  for i in monomial:value*=point[i]
  total+=value
  if modulus is not None:total%=modulus
 return total
def residuals(equation,point,modulus=None):
 if len(point)!=len(equation['variables'])or any(type(v)is not int for v in point):raise ValueError('Supply exactly the listed number of integer coordinates')
 return [polynomial(row['terms'],point,modulus)for row in equation['residuals']]
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('equation',choices=NAMES);ap.add_argument('tuple',type=Path,nargs='?');ap.add_argument('--variables',action='store_true');ap.add_argument('--modulus',type=int);args=ap.parse_args();eq=json.loads((ROOT/'equations'/args.equation/'equation.json').read_text())
 if args.variables:print(json.dumps(eq['variables'],indent=2))
 else:
  if args.tuple is None:raise ValueError('Provide a tuple JSON file or --variables')
  if args.modulus is not None and args.modulus<2:raise ValueError('Modulus must be at least2')
  point=json.loads(args.tuple.read_text());rr=residuals(eq,point,args.modulus);value=sum(r*r for r in rr)
  if args.modulus is not None:value%=args.modulus
  print(json.dumps({'value':value,'modulus':args.modulus,'residuals':rr,'scope':'A modular zero is not an integer zero; no zero search is performed.'}))
