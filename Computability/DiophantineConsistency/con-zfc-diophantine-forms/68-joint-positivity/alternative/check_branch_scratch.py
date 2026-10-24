#!/usr/bin/env python3
"""Independent JSON replay: no builder import; exact integer checks."""
import json, itertools
from pathlib import Path
D=Path(__file__).resolve().parent

def ev(p,e):
 s=0
 for term in p:
  a=term['coefficient']
  for v in term['monomial']:a*=e[v]
  s+=a
 return s

def I(a,b):return 2*(a+b)*(a+b+1)+4*b
def R(a,b):return I(a,b)+1
def A(a,b):return I(a,b)+2
def E(a,b):return I(a,b)+3
def N(a):return I(a,1)
def X(a,b):return N(A(a,N(b)))
def req(b,k,m):return A(b,I(m,N(A(b,I(m,N(R(b,k)))))))
def clos(a,b,k,m):return A(b,I(R(b,k),N(A(a,I(m,N(A(a,I(A(k,I(R(k,a),R(k,b))),req(b,k,m)))))))))
def bundle(a,b,c):return N(I(I(R(a,b),A(c,R(a,b))),A(c,I(clos(a,b,c,c),N(req(b,c,c))))))
def cons(h,t):return 1+(h+t)*(h+t+1)//2+t

def head(name,a,b,c,d):
 if name=='truth':return 0
 if name=='rho1':return X(a,E(a,b))
 if name=='rho2':return I(A(a,I(b,c)),I(A(a,b),A(a,c)))
 if name=='rho3':return I(E(a,b),I(R(c,a),R(c,b)))
 if name=='rho4':return I(A(a,A(b,c)),A(b,A(a,c)))
 if name=='rho5':return I(E(c,a),I(R(c,b),R(a,b)))
 if name=='rho6':return I(X(a,A(a,b)),b)
 if name=='growG':return I(E(c,a),I(E(c,b),A(R(a,b),E(a,b))))
 if name=='rho8':return I(I(I(c,d),a),I(I(a,c),I(b,c)))
 return bundle(a,b,c)

def structural_sos(br):
 from collections import defaultdict
 accum=defaultdict(int)
 for r in br['quadratic_residuals']:
  for x in r:
   for y in r:accum[tuple(sorted(x['monomial']+y['monomial']))]+=x['coefficient']*y['coefficient']
 accum={m:c for m,c in accum.items() if c}
 expected={tuple(x['monomial']):x['coefficient'] for x in br['sum_of_squares']}
 assert accum==expected

cases=0
for filename in ['branch_scratch.json','branch_scratch_split.json','branch_scratch_eliminate0.json','branch_scratch_eliminate1.json','branch_scratch_independent.json','branch_scratch_output_independent.json']:
 obj=json.loads((D/filename).read_text());assert obj['witness_count']==4+max(b['wire_count'] for b in obj['branches'])
 assert obj['degree']==sum(b['degree'] for b in obj['branches'])
 for br in obj['branches']:
  name=br['name'];structural_sos(br)
  inputs=itertools.product(range(2),repeat=4) if not name.startswith('bundle') else [(0,1,2,1),(0,2,1,0)]
  for a,b,c,d in inputs:
   sign=(c-a)*(c-b)
   if name=='bundle_pos' and sign<=0:continue
   if name=='bundle_neg' and sign>=0:continue
   if name=='mp':S=cons(I(a,b),cons(a,c));T=cons(b,c);d=cons(a,c)
   elif name=='gen':S=cons(b,c);T=cons(A(a,b),c)
   else:S=2;T=cons(head(name,a,b,c,d),S)
   env=dict(S=S,T=T,a=a,b=b,c=c,d=d)
   for wire in br['wires']:
    val=ev(wire['value'],env);assert val>=0
    env[wire['name']]=val
   residuals=[ev(p,env) for p in br['quadratic_residuals']]
   assert not any(residuals),(filename,name,a,b,c,d)
   # Exact symbolic SOS expansion was checked above; zero residuals certify zero.
   pass
   env['T']+=1
   assert any(ev(p,env) for p in br['quadratic_residuals'])
   cases+=1
 print(filename, 'PASS',obj['witness_count'],'witnesses',obj['degree'],'degree')
print('exact positive-and-mutated branch replays',cases)

obj=json.loads((D/'horn_output_independent.json').read_text())
horn_cases=0
for br in obj['branches']:
 structural_sos(br);name=br['name']
 inputs=itertools.product(range(2),repeat=4) if name!='bundle' else [(0,1,2,1),(0,2,1,0)]
 for a,b,c,d in inputs:
  if name=='mp':p,q,v=a,I(a,b),b
  elif name=='gen':p,q,v=b,0,A(a,b)
  else:p,q,v=0,0,head(name,a,b,c,d)
  env=dict(p=p,q=q,v=v,a=a,b=b,c=c,d=d)
  for wire in br['wires']:
   value=ev(wire['value'],env);assert value>=0;env[wire['name']]=value
  assert all(ev(r,env)==0 for r in br['quadratic_residuals']),(name,a,b,c,d)
  env['v']+=1
  assert any(ev(r,env) for r in br['quadratic_residuals'])
  horn_cases+=1
print('horn_output_independent.json PASS',obj['witness_count'],'witnesses',obj['degree'],'degree',horn_cases,'replays')
(D/'CHECK_RESULTS.json').write_text(json.dumps({'stack_positive_and_mutated_replays':cases,'horn_positive_and_mutated_replays':horn_cases,'all_branch_SOS_expansions':'exact sparse polynomial equality','status':'PASS','scope':'local certificates only; not final ConZFC equation'},indent=2)+'\n')
