"""Original exact-arithmetic verification of the low-degree cached certificate."""
import math,json
from fractions import Fraction as F
from pathlib import Path
def require(condition,message):
    if not condition:
        raise RuntimeError(message)

P=Path(__file__).resolve().parent
v0=F(239,2000);B=F(63,2000);q=F(7,16);v1=B*(1-q);A=v0+B
require(v1==F(567,32000) and A==F(151,1000), 'check_lowdegree.py: invariant originally at line 7')
require(v0>F(1,12), 'check_lowdegree.py: invariant originally at line 8')
require(12**478<2**1761, 'check_lowdegree.py: invariant originally at line 9')
require(7**302<2**849, 'check_lowdegree.py: invariant originally at line 10')
require(F(2,7)<F(1,3)<q<1, 'check_lowdegree.py: invariant originally at line 11')
# Exact square-root enclosures.
def sb(x,scale=10**12):
 n=math.isqrt(x.numerator*scale*scale//x.denominator);lo=F(n,scale);hi=F(n+1,scale)
 require(lo*lo<=x<hi*hi, 'check_lowdegree.py: invariant originally at line 15')
 return lo,hi
lnlo=2*sum((F(1,(2*j+1)*3**(2*j+1)) for j in range(6)),F(0))
khi=F(22,7)*sb(F(2))[1]/lnlo
require(7**100<2**281, 'check_lowdegree.py: invariant originally at line 19')
tau_hi=F(81,100)
a0=sb(F(22,144));b0=sb((2+tau_hi**2)*F(2,9));j0=F(2,3)
a1=sb(F(12,49));b1=sb(F(30,49));j1=sb(F(24,49))
ghi=F(8,7)/sb(F(7))[0]
K0hi=khi/sb(v0)[0];K1hi=khi/6/sb(v1)[0]
Thi=max(b0[1]*K0hi,a0[1]*K0hi+max(b1[1],a1[1]/(1-ghi))*K1hi)
Shi=max(j0*K0hi,j1[1]*K1hi)
require(Thi<F(143,10) and Shi<F(124,10), 'check_lowdegree.py: invariant originally at line 27')
w=math.log2(7);k=math.pi*math.sqrt(2)/math.log(2)
K0=k/math.sqrt(float(v0));K1=k/6/math.sqrt(float(v1));g=8/(7*math.sqrt(7))
a0f=math.sqrt(22)/12;b0f=math.sqrt(2*(2+(w-2)**2))/3
a1f=math.sqrt(12)/7;b1f=math.sqrt(30)/7
T=max(b0f*K0,a0f*K0+max(b1f,a1f/(1-g))*K1)
S=max(2*K0/3,math.sqrt(24)*K1/7)
result={'status':'PASS','premise':'root degree <= ceil(s^(1/12)); packet degrees may grow','root_taper':str(v0),'tail_initial_taper':str(v1),'tail_ratio':str(q),'total_taper_budget':str(A),'root_capacity':'12^478 < 2^1761','tail_capacity':'7^302 < 2^849','time_formula_decimal':T,'space_formula_decimal':S,'root_matrix_decimal':b0f*K0,'cache_plus_tail_decimal':a0f*K0+max(b1f,a1f/(1-g))*K1,'exact_rational_time_upper':str(Thi),'exact_rational_time_upper_decimal':float(Thi),'exact_rational_space_upper_decimal':float(Shi),'rounded_time':14.3,'rounded_space':12.4,'global_theorem_proven_by_tests':False}
(P/'lowdegree_checks.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
