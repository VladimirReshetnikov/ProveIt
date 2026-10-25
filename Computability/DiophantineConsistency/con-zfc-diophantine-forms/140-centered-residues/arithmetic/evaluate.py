#!/usr/bin/env python3
"""Exactly evaluate one supplied equation at a supplied integer tuple."""
import argparse,json
from pathlib import Path
HERE=Path(__file__).resolve().parent
def main():
 p=argparse.ArgumentParser();p.add_argument('point',type=Path);p.add_argument('--equation',choices=['signed258','signed259','natural222','natural221_high','natural223_sparse','audit261'],default='signed258');a=p.parse_args()
 e=json.loads((HERE/a.equation/'equation.json').read_text());xs=json.loads(a.point.read_text())
 if len(xs)!=len(e['variables'])or any(type(x)is not int for x in xs):raise ValueError('wrong integer coordinate list')
 if e['domain']=='nonnegative integers'and any(x<0 for x in xs):raise ValueError('natural equation requires nonnegative coordinates')
 total=0
 for row in e['residuals']:
  r=0
  for c,m in row['terms']:
   v=c
   for i in m:v*=xs[i]
   r+=v
  total+=r*r
 print(total)
if __name__=='__main__':main()
