#!/usr/bin/env python3
"""Pinned selected graphs, exact witness dependency and partial-zero controls."""
from pathlib import Path
import hashlib,itertools,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
pins=json.loads((HERE/'pins.json').read_text())
for p,h in pins.items():assert hashlib.sha256((ROOT/p).read_bytes()).hexdigest()==h,p
parent=json.loads((ROOT/'research/ordinary13-unit-product80/candidate.json').read_text())
child=json.loads((ROOT/'research/ordinary13-natural-unit-product89/candidate.json').read_text())
assert parent['domain']=='strictly positive integers' and child['domain']=='nonnegative integers'
assert child['witnesses']==['n_'+n for n in parent['witnesses']]
assert child['fixed_numerals']==parent['fixed_numerals']
raw={'f','r','y'}
expected=[[n,'+','n_'+n,1] for n in parent['witnesses'] if n not in raw and n!='zeta']
rename={n:'n_'+n for n in raw}
for n,op,x,y in parent['source']:
 if n=='g52':continue
 if n=='k':expected.extend([['kbase','+','eta','n_zeta'],['k','+','kbase',1]])
 elif n=='r0':expected.append(['r0','-','kbase','R'])
 else:expected.append([n,op,rename.get(x,x),rename.get(y,y)])
assert expected==child['source'] and len(expected)==89 and len(parent['source'])==80
# r has one direct use; the remaining factors cannot transitively depend on it.
rows={n:(op,x,y) for n,op,x,y in parent['source']}
def deps(n):
 if n not in rows:return {n} if isinstance(n,str) else set()
 _,x,y=rows[n]
 return deps(x)|deps(y)
assert [row[0] for row in parent['source'] if 'r' in row[2:]]==['g31']
assert all('r' not in deps(n) for n in ['F1','Fa','Fs'])
assert [row[0] for row in parent['source'] if 'f' in row[2:]]==['f2']
assert [row[0] for row in parent['source'] if 'y' in row[2:]]==['y2']
# Fully evaluate an exact-graph partial assignment: first norm at r=0 holds,
# r=1 breaks it, and the sign-flip r'=2*tau preserves all factors.
e0={n:0 for n in child['witnesses']+child['fixed_numerals']}
e0.update({'n_alpha':1,'n_f':1,'n_s':2,'n_y':1,'beta':1,'K0':-1540})
def evaluate(initial):
 e=dict(initial)
 for name,op,x,y in child['source']:
  a=x if isinstance(x,int) else e[x];b=y if isinstance(y,int) else e[y]
  e[name]={'+':lambda:a+b,'-':lambda:a-b,'*':lambda:a*b}[op]()
 return e
z0=evaluate(e0); assert (z0['q'],z0['X'],z0['Y'],z0['k'],z0['ell'],z0['Bt'],z0['Z'])==(2,2,24,2,2304,1537,-2305)
assert z0['A0']==0 and z0['out']!=0
one=dict(e0,n_r=1);e1=evaluate(one);assert e1['A0']!=0
flip=dict(e0,n_r=4610);ef=evaluate(flip);assert ef['Z']==-z0['Z']
assert all(ef[k]==z0[k] for k in ('F0','F1','Fa','Fs','out'))
# Independent negative-Delta strong/aux-only control: NOT an actual graph zero.
a=-2;D=a*a+4*a+3;c=i=1;f=y=0;z=1;Q=D*(f*f-1)
assert D==-1 and (i*c*c)**2+D==D*f*f and y*y-Q*(y*y-z*z)==1
# Mod-4 exclusions for the first and three remaining factor patterns.
for b,z,x,s,k in itertools.product(range(4),repeat=5):
 q=1+b;Y=q**3*s;ell=x*Y*Y*k
 assert (1+z*z-b*b*(1+ell*(ell+k)))%4!=3
for u,a,c,d in itertools.product(range(4),repeat=4):assert (1+d*d-u*u*(1+(3+4*a+a*a)*c*c))%4!=3
for y,z,a,f in itertools.product(range(4),repeat=4):
 Q=(3+4*a+a*a)*(f*f-1);assert (y*y-Q*(y*y-z*z))%4!=3
for I,a,f in itertools.product(range(4),repeat=3):assert (1+I*I-(3+4*a+a*a)*(f*f-1))%4!=3
print(json.dumps({'source_pins':pins,'parent_rows':80,'natural_rows':89,
 'factor_mod4_cases':1600,'r_zero_partial_graph_control_nonzero_output':z0['out'],
 'partial_control_r_switch':4610,'negative_delta_fact_control':True,
 'lean_executed':False,'scope':'mathematical note and finite controls, not an all-model formal proof'},sort_keys=True,indent=2))
