#!/usr/bin/env python3
"""Explicit projection/lift maps. Quotient restoration is checked only on zeros."""
import argparse,json
from pathlib import Path
from evaluate import polynomial,residuals,NAMES
ROOT=Path(__file__).resolve().parent
SEEDS={'integer138_degree8':None,'integer114_degree16':'plain_22','integer113_degree16':'joint_13_frame','control114_degree16':'plain_13'}
def read(p):return json.loads((ROOT/p).read_text())
def need(b,msg):
 if not b:raise ValueError(msg)
def quotient(a,b):
 need(b!=0,'nonzero denominator required');q,r=divmod(a,b);need(r==0,'integral restoration quotient required');return q
def evalp(p,point):return polynomial(p,point)
def project(name,point):
 source=read('source/pell209_affine.json');need(not any(residuals(source,point)),'Forward pooling map requires a source zero')
 seed=SEEDS[name]
 if seed:
  c=read(f'seeds/{seed}/certificate.json');out=[point[i]for i in c['retained_original_indices']]
  for j,ids in enumerate(c['partition']):
   z=sum(quotient(evalp(c['blocks'][h]['E'],point),evalp(c['blocks'][h]['T'],point))for h in ids)
   if j==c['fused_group']:z+=quotient(evalp(c['Omega'],point),evalp(c['D'],point))
   out.append(z)
 else:out=point
 cert=read(f'equations/{name}/certificate.json');answer=[out[i]for i in cert['retained_original_indices']];need(not any(residuals(read(f'equations/{name}/equation.json'),answer)),'projected residual identity');return answer
def lift(name,point):
 eq=read(f'equations/{name}/equation.json');need(not any(residuals(eq,point)),'Inverse pooling lift requires a selected-equation zero');cert=read(f'equations/{name}/certificate.json');seed=SEEDS[name];parent=read(f'seeds/{seed}/equation.json')if seed else read('source/pell209_affine.json');middle=[0]*len(parent['variables'])
 for i,a in zip(cert['retained_original_indices'],point):middle[i]=a
 for step in reversed(cert['steps']):middle[step['variable']]=evalp(step['definition'],middle)
 need(not any(residuals(parent,middle)),'exact monic inverse')
 if not seed:return middle
 c=read(f'seeds/{seed}/certificate.json');source=read('source/pell209_affine.json');out=[0]*len(source['variables'])
 for i,a in zip(c['retained_original_indices'],middle):out[i]=a
 for block in c['blocks']:
  T=evalp(block['T'],out)
  if 'T_variable'in block:
   out[block['T_variable']]=T;out[block['Q_variable']]=quotient(-evalp(block['delta'],out),T)
  else:
   L=quotient(evalp(block['E'],out),T);out[block['L_variable']]=L;out[block['K_variable']]=2*evalp(block['H'],out)+(2*evalp(c['A'],out)-evalp(block['base'],out))*L
 if c['fused_group'] is not None:out[c['orientation_variable']]=quotient(evalp(c['Omega'],out),evalp(c['D'],out))
 need(not any(residuals(source,out)),'restored every original source row');return out
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('mode',choices=['project','lift']);ap.add_argument('equation',choices=NAMES);ap.add_argument('tuple',type=Path);a=ap.parse_args();point=json.loads(a.tuple.read_text());print(json.dumps(project(a.equation,point)if a.mode=='project'else lift(a.equation,point)))
