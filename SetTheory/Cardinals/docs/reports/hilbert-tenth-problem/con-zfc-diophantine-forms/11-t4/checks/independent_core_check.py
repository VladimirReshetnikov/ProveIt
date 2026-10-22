"""Independent factored-form versus delivered circuit checks. No solution search."""
import json,random,math,sys
from pathlib import Path
from fractions import Fraction
BASE=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parents[1]/'comparison'
NAMES=['hybrid_system61.json','hybrid_product69.json','hybrid_sos78.json']
packets=[json.loads((BASE/n).read_text()) for n in NAMES]
def direct(v):
 J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma=[v[k] for k in packets[0]['witnesses']]
 m,K,MC,MF=[v[k] for k in ['Bm1','Kconstant','MC','MF']]
 q=m*J+1; C=q-F-alpha; X=w*q; Y=s*q**3; E=X*Y
 k=eta+zeta; c=k*Y+eta; a=E+Y; H=4*a+3; Delta=a*a+H
 D=X+a*c+gamma*H; G=(q-1)*(q-F)+alpha
 R=G*(q*q-1)+(MC+q*MF)*J; L=E*k*Y
 V=c*(T*f-1)-R*f*f; A=Delta*(f*f-1); I=i*c*c
 ns=[tau*tau-L*(L+k),D*D-Delta*c*c,A*(V*V-y*y)+y*y,k-h*E-R,(K+w)*C+q-F-z*(q-1)]
 residual=[n-1 for n in ns]+[I*I-A]
 return residual,math.prod(ns)*(1+I*I-A)-1,sum(t*t for t in residual)
def evaluate(p,v):
 d=dict(v)
 def at(x): return d[x] if isinstance(x,str) else x
 for n,op,x,y in p['source']:
  x,y=at(x),at(y)
  d[n]= x+y if op=='+' else x-y if op=='-' else x*y
 return [at(x)-at(y) for x,y in p['comparisons']] if 'comparisons' in p else at(p['output'])
def run():
 rng=random.Random(20261022); count=0
 for rational in [False,True]:
  for _ in range(128):
   values={k:Fraction(rng.randint(-8,8),rng.randint(1,5)) if rational else rng.randint(-8,8) for k in packets[0]['witnesses']+packets[0]['fixed_numerals']}
   wanted=direct(values)
   for p,expected in zip(packets,wanted):
    if evaluate(p,values)!=expected:raise ValueError('Circuit/factored expression mismatch')
   count+=1
 # A sign fault in the auxiliary coefficient must be detected by this independent form.
 faulty=json.loads(json.dumps(packets[1]))
 for row in faulty['source']:
  if row[0]=='f2_minus_one': row[1]='+';break
 else:
  # Find the subtraction f^2 - 1 by operand semantics rather than a gate name.
  square_names={r[0] for r in faulty['source'] if r[1:] == ['*','f','f']}
  for row in faulty['source']:
   if row[1]=='-' and row[2] in square_names and row[3]==1:row[1]='+';break
  else:raise ValueError('Negative control did not locate target')
 probe={k:3 for k in packets[0]['witnesses']+packets[0]['fixed_numerals']}
 if evaluate(faulty,probe)==direct(probe)[1]:raise ValueError('Negative control not detected')
 return {'exact_integer_and_rational_assignments':count,'circuits_per_assignment':3,'negative_control':'auxiliary f^2-1 changed to f^2+1: detected','scope':'Polynomial identities only; no ZFC refutation, accepting computation, or unbounded equivalence is tested.'}
if __name__=='__main__':print(json.dumps(run(),indent=2))
