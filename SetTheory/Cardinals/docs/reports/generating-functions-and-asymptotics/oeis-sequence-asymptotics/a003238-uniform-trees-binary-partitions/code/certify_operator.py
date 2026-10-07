"""Directed finite enclosures of the positive cut operator T^r 1, r<=3.
Only integer/rational arithmetic and certified elementary functions are used.
All omitted positive terms receive explicit analytic upper bounds.
"""
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
import json
from certified_interval import IV,S,PREC,ceildiv,expminus,binary_product,log_rational,exp_interval
from operator_constants import get_constants,U0,D,D7,C
P=Path(__file__).resolve().parent;tails,Cb,constant_checks=get_constants()
rho=log_rational(F(3,2))/log_rational(F(2));JJ={1:35,2:20,3:15};stats={'states':0,'pruned':0,'terms':0}
ONE=IV.of(1)
@lru_cache(None)
def BB(t):return binary_product(t)
@lru_cache(None)
def EE(t):return expminus(t)
@lru_cache(None)
def oddrho(n):return exp_interval(log_rational(F(n))*rho)
@lru_cache(None)
def rho_power(t):
 e=t.denominator.bit_length()-1
 if t.denominator!=2**e:raise ValueError('dyadic argument required')
 return oddrho(t.numerator)*IV.of(F(2,3)**e)

def coarse_bound(r,t):
 e=t.denominator.bit_length()-1
 return C[r]*t.numerator**r*F(2,3)**(e*r)

@lru_cache(None)
def Tr(r,t):
 if not 0<t<=U0:raise ValueError('operator argument outside domain')
 if not 1<=r<=3:raise ValueError('unsupported depth')
 stats['states']+=1
 bound=coarse_bound(r,t)
 if bound<F(1,10**12):
  stats['pruned']+=1
  return IV(0,ceildiv(bound.numerator*S,bound.denominator))
 out=IV.of(0)
 for j in range(1,JJ[r]+1):
  u=t/2**j;den=BB(2*u)
  for k in range(3,16):
   v=k*u
   if v>U0:continue
   value=ONE if r==1 else Tr(r-1,v)
   kernel=EE(-(k-2)*u)*BB(v)/den
   out+=kernel*value;stats['terms']+=1
 coeff=C[r]*IV.of(F(2,3)**(r*JJ[r]))+C[r-1]*tails[r-1]
 error=coeff*rho_power(t)**r
 out+=IV(0,error.hi)
 if stats['states']%1000==0:print('states',stats,flush=True)
 return out

rows=[]
for t in [F(9,2**21),F(3,2**19)]:
 vals=[ONE]+[Tr(r,t) for r in [1,2,3]];S3=vals[0]-vals[1]+vals[2]-vals[3]
 if S3.lo<=0:raise RuntimeError('positive S3 not certified')
 z=rho_power(t);err4=14*C[4]*z**4
 eb=Cb*IV.of(t**7)*(1+D7[0]*z+D7[0]*D7[1]*z**2+D7[0]*D7[1]*D7[2]*z**3)
 row={'t':str(t),'Tr':[v.decimal(40) for v in vals],'Tr_integer_bounds':[v.integer_bounds() for v in vals],'S3':S3.decimal(40),'S3_integer_bounds':S3.integer_bounds(),'14T4_upper':err4.decimal(40),'14T4_integer_bounds':err4.integer_bounds(),'epsilon_b':eb.decimal(40),'epsilon_b_integer_bounds':eb.integer_bounds()}
 rows.append(row);print('POINT COMPLETE',row,flush=True)
receipt={'status':'POSITIVE_OPERATOR_ENCLOSED','precision_bits':PREC,'J':JJ,'K':15,'pruning_bound':'[0,Cr t^(r rho)] with numerator-based exact upper estimate','stats':stats,'rows':rows,'no_nonconstancy_claim':True}
(P/'OPERATOR_VALUE_CERTIFICATE.json').write_text(json.dumps(receipt,indent=2)+'\n')
