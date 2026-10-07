"""Independent exact-rational probes of directed interval primitives and APIs."""
from fractions import Fraction as F
import json
from certified_interval import IV,S,expminus,polynomial,log_rational,binary_product
from saddle_engine import correction

def require(ok,msg):
 if not ok:raise RuntimeError(msg)

def encloses(iv,lo,hi=None):
 if hi is None:hi=lo
 require(F(iv.lo,S)<=lo<=hi<=F(iv.hi,S),'failed exact enclosure')

cases=0
for a in range(-12,13):
 for b in range(1,13):
  x=F(a,13);y=F(b,17);u=IV.of(x);v=IV.of(y)
  for got,want in [(u+v,x+y),(u-v,x-y),(u*v,x*y),(u/v,x/y)]:
   encloses(got,want);cases+=1
# Independent positive Taylor enclosure of exp(x), then reciprocate.
expcases=0
for x in [F(0),F(1,1000),F(1,16),F(1,3),F(1),F(2),F(9,2),F(8)]:
 term=total=F(1)
 for k in range(1,1201):term*=x/k;total+=term
 tail=term*x/F(1201)/(1-x/F(1202))
 e=expminus(x)
 # The two independently certified intervals must intersect.
 lo,hi=1/(total+tail),1/total
 require(max(F(e.lo,S),lo)<=min(F(e.hi,S),hi),'independent exponential disjoint')
 expcases+=1
for coefficients in [[0,1,2,3],[3,0,4],[1]]:
 q=IV.of(F(2,3));got=polynomial(coefficients,q)
 encloses(got,sum(F(a)*F(2,3)**j for j,a in enumerate(coefficients)))
# Exact identities whose common target must be enclosed.
log2=log_rational(F(2));log4=log_rational(F(4))
require(max(log4.lo,2*log2.lo)<=min(log4.hi,2*log2.hi),'log range identity')
# Pure integer jets must stay exact; all unsupported jets are rejected.
P=[2,-1,3,4,5];b=[0,1,7,9,11,13,15]
require(type(correction(2,P,b)) is F,'integer jets lost exactness')
invalid=[float('nan'),float('inf'),float('-inf'),1.0,'1',True,complex(1)]
for x in invalid:
 try:correction(0,[x],[0,1,2])
 except TypeError:pass
 else:raise RuntimeError('unsupported jet accepted')
for order,aa,bb in [(-1,[1],[0,1,2]),(True,[1],[0,1,2]),(1,[1],[0,1,2]),(0,[1],[0,1,0])]:
 try:correction(order,aa,bb)
 except (TypeError,ValueError):pass
 else:raise RuntimeError('invalid saddle API accepted')
print(json.dumps({'status':'PASS','exact_rational_arithmetic_cases':cases,'independent_positive_Taylor_exp_cases':expcases,'Horner_cases':3,'log_range_identity':True,'integer_jets_remain_Fraction':True,'unsupported_jet_rejections':len(invalid),'invalid_saddle_contract_rejections':4,'scope':'Finite rational probes and API checks, not an analytic remainder proof.'},indent=2,sort_keys=True))
