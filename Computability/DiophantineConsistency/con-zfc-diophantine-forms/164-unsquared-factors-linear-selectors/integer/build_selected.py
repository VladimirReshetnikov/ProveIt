#!/usr/bin/env python3
"""Replay frozen elementary row certificates; no optimization or network."""
import argparse,copy,hashlib,json
from pathlib import Path
from build import ROOT,data,write,normalized,terms,measure

def construct(cert):
 src=ROOT/cert['source']/'equation.json'
 if hashlib.sha256(src.read_bytes()).hexdigest()!=cert['source_sha256']:raise ValueError('row source hash')
 old=data(src);eq=copy.deepcopy(old);rows=[normalized(r['terms'])for r in old['residuals']]
 for i,j,k in cert['operations']:
  if i==j or type(k)is not int or not k:raise ValueError('elementary row operation')
  for m,c in rows[j].items():rows[i][m]=rows[i].get(m,0)+k*c
  rows[i]={m:c for m,c in rows[i].items()if c}
 eq['residuals']=[dict(r,terms=terms(p))for r,p in zip(old['residuals'],rows)];eq['variant']=cert['endpoint']
 return eq,measure(eq),data(ROOT/cert['source']/'RESTORATION.json')
def main():
 p=argparse.ArgumentParser();p.add_argument('--out',type=Path,default=ROOT);a=p.parse_args()
 for c in sorted((ROOT/'certificates').glob('*.json')):
  cert=data(c);eq,(pol,met),rest=construct(cert);out=a.out/cert['endpoint']
  for fn,o in [('equation.json',eq),('expanded_polynomial.json',pol),('METRICS.json',met),('RESTORATION.json',rest),('row_certificate.json',cert)]:write(out/fn,o)
  print(cert['endpoint'],json.dumps(met,sort_keys=True))
if __name__=='__main__':main()
