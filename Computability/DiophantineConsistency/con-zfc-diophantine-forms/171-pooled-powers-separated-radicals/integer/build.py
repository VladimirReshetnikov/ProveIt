#!/usr/bin/env python3
"""Replay frozen transformations into a separate output; never run optimizers."""
from pathlib import Path
import argparse,copy,json,sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'code'))
import build_pools,shear_pell,linear_beta,reduce_radical as R

def emit(out,eq,cert,certname):
 out.mkdir(parents=True,exist_ok=True);pol=R.add(*(R.mul(R.norm(r['terms']),R.norm(r['terms']))for r in eq['residuals']))
 for fn,obj in [('equation.json',eq),(certname,cert),('metrics.json',R.metric(eq,True)),('expanded_polynomial.json',{'schema':'sparse_integer_polynomial_v1','variables':len(eq['variables']),'terms':R.terms(pol)})]:(out/fn).write_bytes(R.canonical(obj))

def main(dest):
 for source_n in [235,236]:
  pn=source_n-11;rn=pn-6;bn=rn-1
  build_pools.main(ROOT/'sources'/f'strict{source_n}.json',dest/f'pooled{pn}')
  shear_pell.main(dest/f'pooled{pn}'/'equation.json',dest/f'differences{pn}')
  eq=json.loads((dest/f'differences{pn}'/'equation.json').read_text());cert=json.loads((ROOT/f'radical{rn}'/'projection_certificate.json').read_text())
  for step in cert['steps']:
   d=[0]*len(eq['variables'])
   for i,c in step['direction']:d[i]=c
   eq,actual=R.project(eq,d,step['pivot'],step['deleted_row'])
   if actual!=step:raise ValueError('frozen radical replay')
  emit(dest/f'radical{rn}',eq,cert,'projection_certificate.json')
  linear_beta.main(dest/f'radical{rn}'/'equation.json',dest/f'beta{bn}')
  for tag in [f'integer{bn}',f'integer{bn}_sparse']:
   eq=json.loads((dest/f'beta{bn}'/'equation.json').read_text());cert=json.loads((ROOT/tag/'row_certificate.json').read_text());rows=[R.norm(r['terms'])for r in eq['residuals']]
   for i,j,k in cert['operations']:
    if i==j or type(k)is not int or not k:raise ValueError('invalid row operation')
    rows[i]=R.add(rows[i],R.scale(rows[j],k))
   eq['residuals']=[dict(r,terms=R.terms(p))for r,p in zip(eq['residuals'],rows)];eq['variant']+=':integer_row_reduction'
   if R.digest(eq)!=cert['output_sha256']:raise ValueError('frozen row replay')
   emit(dest/tag,eq,cert,'row_certificate.json')
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--out',required=True,type=Path);a=p.parse_args();main(a.out)
