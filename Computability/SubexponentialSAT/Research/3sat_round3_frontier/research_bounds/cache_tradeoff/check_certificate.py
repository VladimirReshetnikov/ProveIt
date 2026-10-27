"""Original exact-arithmetic checks for the r0=7, rtail=9 cached certificate.
Imported research code is never loaded. All finite checks are proof support only.
"""
import math,json
from fractions import Fraction as F
from pathlib import Path
def require(condition,message):
    if not condition:
        raise RuntimeError(message)

P=Path(__file__).resolve().parent
v0=F(89,5000); B=F(137,10000); q=F(7,25); v1=B*(1-q)
require(v1==F(1233,125000), 'check_certificate.py: invariant originally at line 9')
require(v0+B==F(63,2000), 'check_certificate.py: invariant originally at line 10')
require(7**89<2**250, 'check_certificate.py: invariant originally at line 11')
require(9**63<2**200, 'check_certificate.py: invariant originally at line 12')
# log2(7)<281/100; this simultaneously controls Strassen's omega.
require(7**100<2**281, 'check_certificate.py: invariant originally at line 14')
require(F(9,10)+2*v0*F(250,89)==1 , 'check_certificate.py: invariant originally at line 15')
require(F(9,10)+(v0+B)*F(200,63)==1 , 'check_certificate.py: invariant originally at line 16')
# Exponent of Q_tail^2*C_tail and L_tail Q_tail^2 <= A*(1+2log2 9)<.232.
require((v0+B)*(1+2*F(200,63))<F(232,1000), 'check_certificate.py: invariant originally at line 18')
# Coarse child ratio <=1/4 eventually (2/9<1/4); q>1/4 gives positive taper exponent.
require(F(2,9)<F(1,4)<q<1, 'check_certificate.py: invariant originally at line 20')
# Exact rational sqrt bounds, no floating point used in certificate comparisons.
def sqrt_bounds(x,scale=10**12):
    n=math.isqrt(x.numerator*scale*scale//x.denominator)
    lo=F(n,scale); hi=F(n+1,scale)
    require(lo*lo<=x<hi*hi, 'check_certificate.py: invariant originally at line 25')
    return lo,hi
sqrt2=sqrt_bounds(F(2));sqrt3=sqrt_bounds(F(3));sqrt7=sqrt_bounds(F(7))
ln2_lower=2*sum((F(1,(2*j+1)*3**(2*j+1)) for j in range(6)),F(0))
require(ln2_lower>F(693,1000), 'check_certificate.py: invariant originally at line 29')
base_hi=F(22,7)*sqrt2[1]/ln2_lower
omega_hi=F(281,100);tau_hi=omega_hi-2
alpha0=sqrt_bounds(F(12,49));beta0=sqrt_bounds(F(30,49));j0=sqrt_bounds(F(24,49))
alpha1=F(4,9);beta1=sqrt_bounds((36+18*tau_hi**2)/81);j1=F(2,3)
# beta0 is table-construction dominated, even with omega upper bound.
require((24+8*tau_hi**2)/49<F(30,49), 'check_certificate.py: invariant originally at line 35')
# Tail recurrence max bound: use alpha1/(1-gamma) if larger than beta1.
gamma_hi=F(10,9)/sqrt7[0]
tail_factor_hi=max(beta1[1],alpha1/(1-gamma_hi))
K0_hi=base_hi/sqrt_bounds(v0)[0]
K1_hi=base_hi*F(2,7)/sqrt_bounds(v1)[0]
root_hi=beta0[1]*K0_hi
recursive_hi=alpha0[1]*K0_hi+tail_factor_hi*K1_hi
space_hi=max(j0[1]*K0_hi,j1*K1_hi)
require(root_hi<38, 'check_certificate.py: invariant originally at line 44')
require(recursive_hi<38, 'check_certificate.py: invariant originally at line 45')
require(space_hi<34, 'check_certificate.py: invariant originally at line 46')
# Float only for display of exact formulas.
w=math.log2(7);base=math.pi*math.sqrt(2)/math.log(2)
gamma=10/(9*math.sqrt(7))
beta1f=math.sqrt(36+18*(w-2)**2)/9
f=max(beta1f,(4/9)/(1-gamma))
k0=base/math.sqrt(float(v0));k1=base*(2/7)/math.sqrt(float(v1))
Ctime=max(math.sqrt(30)/7*k0, math.sqrt(12)/7*k0+f*k1)
Cspace=max(math.sqrt(24)/7*k0,(2/3)*k1)
result={'status':'PASS','root_taper':str(v0),'tail_initial_taper':str(v1),'tail_ratio':str(q),'total_budget':str(v0+B),'root_integer_capacity_check':'7^89 < 2^250','tail_integer_capacity_check':'9^63 < 2^200','time_formula_decimal':Ctime,'space_formula_decimal':Cspace,'root_matrix_decimal':math.sqrt(30)/7*k0,'cache_plus_tail_decimal':math.sqrt(12)/7*k0+f*k1,'tail_gamma':gamma,'tail_matrix_factor':beta1f,'tail_cache_limit':(4/9)/(1-gamma),'exact_rational_time_upper':str(max(root_hi,recursive_hi)),'exact_rational_time_upper_decimal':float(max(root_hi,recursive_hi)),'exact_rational_space_upper_decimal':float(space_hi),'rounded_time':38,'rounded_space':34,'global_theorem_proven_by_tests':False}
(P/'certificate_checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
