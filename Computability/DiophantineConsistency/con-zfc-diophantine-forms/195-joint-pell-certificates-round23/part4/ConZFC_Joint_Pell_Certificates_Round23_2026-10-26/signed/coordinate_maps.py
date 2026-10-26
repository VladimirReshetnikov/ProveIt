#!/usr/bin/env python3
"""Explicit integral maps. No root search and no positivity assumption."""
import argparse,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
def read(p):return json.loads((ROOT/p).read_text())
def need(x,s):
 if not x:raise ValueError(s)
def valid(x,n):need(type(x)is list and len(x)==n and all(type(a)is int for a in x),'integer tuple of exact dimension required')
def value(ts,x):
 answer=0
 for c,mon in ts:
  for i in mon:c*=x[i]
  answer+=c
 return answer
def lift(x,name):
 c=read(f'{name}/certificate.json')['projection'];keep=c['retained_indices'];valid(x,len(keep));y=[0]*(len(keep)+1)
 for i,a in zip(keep,x):y[i]=a
 y[c['eliminated_coordinate']]=value(c['replacement'],y);return y
def project(x,name):
 c=read(f'{name}/certificate.json')['projection'];valid(x,len(c['retained_indices'])+1);return[x[i]for i in c['retained_indices']]
def split_extend(x,name):
 valid(x,210);y=x.copy()
 for d in read(f'{name}/certificate.json')['split']['definitions']:need(d['coordinate']==len(y),'sequential wire');y.append(d['factor']*y[d['previous']])
 return y
def split_forget(x,name):
 valid(x,len(read(f'{name}/modified_source.json')['variables']));return x[:210]
def controls():
 result={}
 for name in read('ENDPOINTS.json'):
  n=len(read(f'{name}/equation.json')['variables'])
  for seed in range(8):
   x=[(i*(seed+3)+seed)%11-5 for i in range(n)];need(project(lift(x,name),name)==x,'all-point project after lift')
   z=[(i*(seed+2))%9-4 for i in range(210)];need(split_forget(split_extend(z,name),name)==z,'all-point forget after insertion')
  for bad in [None,{},[0]*(n-1),[0]*(n+1),[False]+[0]*(n-1),[0.0]+[0]*(n-1)]:
   try:lift(bad,name)
   except ValueError:pass
   else:raise ValueError('bad map input accepted')
  result[name]={'all_point_inverse_controls':16,'invalid_inputs_rejected':6,'exact_symbolic_identities':'verify.py independently checks every affine substitution and monic pullback; reverse identity on source zeros uses the defining rows'}
 return result
def main():
 ap=argparse.ArgumentParser();ap.add_argument('direction',choices=['lift','project','split_extend','split_forget','check']);ap.add_argument('endpoint',nargs='?');ap.add_argument('point',type=Path,nargs='?');args=ap.parse_args()
 if args.direction=='check':print(json.dumps(controls(),indent=2));return
 need(args.endpoint in read('ENDPOINTS.json')and args.point is not None,'endpoint and point required');print(json.dumps(globals()[args.direction](json.loads(args.point.read_text()),args.endpoint)))
if __name__=='__main__':main()
