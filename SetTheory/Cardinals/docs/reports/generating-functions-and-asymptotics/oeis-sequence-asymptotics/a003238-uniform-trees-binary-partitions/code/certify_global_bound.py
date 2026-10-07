from fractions import Fraction as F
from pathlib import Path
import json
from certified_interval import IV,PREC,S,expminus,binary_product,polynomial
from verify_exact import sieve
p=Path(__file__).resolve().parent
a=sieve(10000)

def finite_f(t):return polynomial(a,expminus(t))+IV(0,1)
# For t>=1/16, omitted coefficients have total <33 exp(-325)<2^-319.
# This follows from a_n<=p(n-1)<=exp(3sqrt(n)) and tangent concavity at n=10000.
M0=IV.of(0);u=F(1,16);grids=0
while u<4:
 v=min(4,u*F(65,64))
 bound=finite_f(u)/expminus(u)/binary_product(v)
 M0=IV(max(M0.lo,bound.lo),max(M0.hi,bound.hi));u=v;grids+=1
bound=finite_f(F(4))/expminus(F(4));M0=IV(max(M0.lo,bound.lo),max(M0.hi,bound.hi))
if M0.hi>=4*S:raise RuntimeError(('base bound not proved',M0.decimal()))
M=IV.of(4);rows=[];J=22
for j in range(J):
 tmax=F(1,2**(4+j));tmin=tmax/2;den=binary_product(2*tmax)
 W=sum((expminus(k*tmin)*binary_product(k*tmax)/den for k in range(3,64)),IV.of(0))
 W+=binary_product(64*tmax)/den*expminus(64*tmin)/(1-expminus(tmin))
 candidate=1/den+(expminus(2*tmin)+W)*M
 M=IV(max(M.lo,candidate.lo),max(M.hi,candidate.hi))
 rows.append({'j':j,'W':W.decimal(20),'M':M.decimal(20)})
t=F(1,2**(4+J));x=45*F(2,3)**(4+J)+48*t;Qtail=F(32,3)*t*t
if not x<1:raise RuntimeError('tail exponent too large')
final=(M+Qtail)/(1-x)
if final.hi>=14*S:raise RuntimeError(('global14 bound not proved',final.decimal()))
receipt={'status':'PASS','claim':'0<G(t)=exp(t)F(exp(-t))/B(t)<14 for every real t>0','arithmetic':'directed 256-bit fixed-point integer intervals and rational exponential Taylor bounds','base_grid_count':grids,'base_upper':M0.decimal(),'recurrence_bands':rows,'tail_x':str(x),'final_global_upper':final.decimal(),'final_integer_interval':final.integer_bounds(),'precision_bits':PREC,'no_asserts':True}
(p/'GLOBAL_BOUND_CERTIFICATE.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
