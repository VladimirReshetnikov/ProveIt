#!/usr/bin/env python3
"""Evaluate explicit integral maps between a chosen source and a final zero set.

Row basis changes leave points unchanged. The maps begin at the chosen weighted
or quadratic source, not at an old source with a different cofinal horizon.
"""
import argparse,copy,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent;sys.path.insert(0,str(ROOT/'code'))
import operations as O

def read(p):return json.loads((ROOT/p).read_text())
def value(ts,x):
 out=0
 for c,m in ts:
  for i in m:c*=x[i]
  out+=c
 return out

def trace(profile):
 e=read(f'stages/{profile}_source/equation.json');trace=[]
 for ops in read(f'stages/{profile}_transport/operations.json'):
  rows=[O.poly(r['terms'])for r in e['residuals']];n=len(e['variables'])
  for op in ops:
   k=op['kind']
   if k=='row_add':rows[op['i']]=O.add(rows[op['i']],rows[op['j']],op['k'])
   elif k=='shear':rows=[O.subst(p,op['j'],{(op['j'],):1,(op['i'],):op['k']})for p in rows]
   elif k=='project':rows=[O.subst(p,op['variable'],O.poly(op['replacement']))for p in rows]
   else:raise ValueError('unrecognized map operation')
  keep=sorted({i for p in rows for m in p for i in m});trace.append((n,keep,ops));e=O.compact(e,rows)
 return trace

def project(x,endpoint):
 desc=read('ENDPOINTS.json')[endpoint];profile=desc['profile'];source=read(f'stages/{profile}_source/equation.json');O.need(len(x)==len(source['variables']),'source dimension')
 for n,keep,ops in trace(profile):
  for op in ops:
   if op['kind']=='shear':x[op['j']]-=op['k']*x[op['i']]
  x=[x[i]for i in keep]
 for cert in read(f'stages/{profile}_radical/projection_certificate.json')['steps']:
  direction=dict(cert['direction']);a=x[cert['pivot']];x=[x[i]-direction.get(i,0)*a for i in cert['retained_old_indices']]
 return x

def lift(x,endpoint):
 desc=read('ENDPOINTS.json')[endpoint];profile=desc['profile'];target=read(f'{endpoint}/equation.json');O.need(len(x)==len(target['variables']),'target dimension')
 for cert in reversed(read(f'stages/{profile}_radical/projection_certificate.json')['steps']):
  keep=cert['retained_old_indices'];y=[0]*(len(keep)+1)
  for i,v in zip(keep,x):y[i]=v
  a=value(cert['sheared_pivot_solution'],y);direction=dict(cert['direction']);x=[v+direction.get(i,0)*a for i,v in enumerate(y)]
 for n,keep,ops in reversed(trace(profile)):
  y=[0]*n
  for i,v in zip(keep,x):y[i]=v
  for op in reversed(ops):
   if op['kind']=='project':y[op['variable']]=value(op['replacement'],y)
   elif op['kind']=='shear':y[op['j']]+=op['k']*y[op['i']]
  x=y
 return x

def controls():
 receipt={}
 for name in read('ENDPOINTS.json'):
  n=len(read(f'{name}/equation.json')['variables'])
  for seed in range(8):
   x=[((i+1)*(seed+3))%7-3 for i in range(n)];y=lift(x.copy(),name);O.need(project(y.copy(),name)==x,'composed integer maps')
  receipt[name]={'all_point_project_after_lift_controls':8,'source_dimension':len(y),'target_dimension':n}
 return receipt

def main():
 ap=argparse.ArgumentParser();ap.add_argument('direction',choices=['project','lift','check']);ap.add_argument('endpoint',nargs='?');ap.add_argument('point',type=Path,nargs='?');args=ap.parse_args()
 if args.direction=='check':print(json.dumps(controls(),indent=2));return
 O.need(args.endpoint in read('ENDPOINTS.json')and args.point is not None,'endpoint and point required');x=json.loads(args.point.read_text());O.need(type(x)is list and all(type(v)is int for v in x),'integer coordinates required');print(json.dumps((project if args.direction=='project'else lift)(x,args.endpoint)))
if __name__=='__main__':main()
