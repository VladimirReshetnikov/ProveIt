#!/usr/bin/env python3
"""Exact q=4 counterexample to a tempting signed-residual merge."""
import hashlib,json,resource
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(192*1024**2,192*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(10,10));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
root=Path(__file__).resolve().parents[2];here=Path(__file__).resolve().parent
for p,h in json.loads((here/'pins.json').read_text()).items():assert hashlib.sha256((root/p).read_bytes()).hexdigest()==h,p
old=json.loads((root/'research/ordinary10-two-norm-divisible61/candidate.json').read_text())
probe=json.loads((here/'probe.json').read_text())
rows=[]
for row in old['source']:
 if row[0] in ('Bsq','firstsq'):continue
 if row[0]=='sum1':rows.extend([['merge','+','Bres','firstres'],['mergedsq','*','merge','merge']]);continue
 if row[0]=='out':rows.append(['out','+','mergedsq','A1sq']);continue
 rows.append(row)
assert rows==probe['source'] and len(rows)==60 and old['witnesses']==probe['witnesses']
assert old['fixed_numerals']==probe['fixed_numerals']==['beta','K0','MC','MF']
# Exact free-polynomial cancellation of the residual changes in b and tau.
def padd(x,y):
 o=x.copy()
 for k,v in y.items():o[k]=o.get(k,0)+v
 return {k:v for k,v in o.items() if v}
def pmul(x,y):
 o={}
 for a,u in x.items():
  for b,v in y.items():
   k=(a[0]+b[0],a[1]+b[1]);o[k]=o.get(k,0)+u*v
 return {k:v for k,v in o.items() if v}
b0={(1,0):1};t0={(0,1):1};two={(0,0):2}
positive=pmul(b0,padd(pmul(two,t0),b0))
assert padd(pmul(padd(t0,b0),padd(t0,b0)),{k:-v for k,v in pmul(t0,t0).items()})==positive
assert padd(positive,{k:-v for k,v in positive.items()})=={}
# Reconstruct the independently reviewed two-norm zero by binary Pell powers.
def pell(A,n):
 D=A*A-1
 def mul(x,y):return (x[0]*y[0]+D*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
 v=(1,0);b=(A,1)
 while n:
  if n&1:v=mul(v,b)
  b=mul(b,b);n//=2
 return v
q=4;b=3;X=1<<84;Y=64;U=Y*q*q;M=X*Y*Y;a=Y*(X+1);H=4*a+3
u,yf=pell(2*M+1,78);k=2*yf;g,c=pell(a+2,84);R=155
B=2*(X+1)-1;assert B%b==0;h=B//b
p=g-X-a*c;z=k-R-1;assert p%H==0 and z%U==0
gamma=p//H+z//U;eta=c-Y*k;zeta=k-eta-1
assert 0<=eta<k and min(h,gamma,zeta)>=0
vals=[1,0,0,X//q,0,h,u,eta,zeta,gamma];ports=[3,1,1,1]
def ev(graph,vals):
 e=dict(zip(graph['witnesses'],vals));e.update(zip(graph['fixed_numerals'],ports))
 for n,op,a,b in graph['source']:
  a=e[a] if isinstance(a,str) else a;b=e[b] if isinstance(b,str) else b
  e[n]=a+b if op=='+' else a-b if op=='-' else a*b
 return e
orig=ev(old,vals);assert orig['out']==0 and orig['Bres']==orig['firstres']==orig['A1']==0
# tau' = tau+b and h' = h+2*tau+b. Both remain natural.
vals[5]=h+2*u+b;vals[6]=u+b
x=ev(probe,vals);y=ev(old,vals)
assert all(v>=0 for v in vals)
assert x['Bres']==-b*(2*u+b) and x['firstres']==b*(2*u+b)
assert x['A1']==0 and x['merge']==0 and x['out']==0
assert y['out']>0 and y['Bres']!=0 and y['firstres']!=0
assert x['q']==4 and x['C']>0 and x['X']>0 and x['k']>x['q']
# Verify topological liveness of the entire literal probe.
available=set(probe['witnesses']+probe['fixed_numerals']);parents={}
for name,op,a,b in rows:
 assert name not in available and all(not isinstance(z,str) or z in available for z in (a,b))
 available.add(name);parents[name]=(a,b)
stack=['out'];seen=set();used=set()
while stack:
 name=stack.pop()
 if not isinstance(name,str):continue
 if name not in parents:used.add(name);continue
 if name in seen:continue
 seen.add(name);stack.extend(parents[name])
assert len(seen)==60 and set(probe['witnesses'])<=used
print(json.dumps({'probe_operations':60,'probe_live_operations':len(seen),
 'ports':ports,'base_first_main_norms_zero':True,'base_even_main_index':84,
 'generic_residual_changes_polynomial_identity':True,
 'changed_carrier_and_first_residuals_nonzero_opposite':True,
 'changed_main_residual_zero':True,'invalid_probe_output_zero':True,
 'original_output_at_changed_tuple_positive':True,'all_inputs_natural':True,
 'actual_compact_tuple_tested':False,'existential_inequivalence_proved':False,
 'valid_gate_reduction_proved':False,'lean_executed':False},indent=2,sort_keys=True))
