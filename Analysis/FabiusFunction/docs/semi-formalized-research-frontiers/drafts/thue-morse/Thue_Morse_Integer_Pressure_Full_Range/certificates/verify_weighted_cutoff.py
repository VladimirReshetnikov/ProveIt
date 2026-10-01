"""Exact scalar checks for the new weighted-residual pressure cutoff."""
from fractions import Fraction as F
from pathlib import Path
from math import isqrt
import json
R=F(2,5);w=F(49,100);alpha=F(707,275)
def sqrt_bounds(x,S=10**22):
 k=isqrt(x.numerator*S*S//x.denominator);return F(k,S),F(k+1,S)
lo=hi=F(1);bs=[];S=10**22
for j in range(24):
 bs.append((lo,hi));_,a=sqrt_bounds(1+lo*lo);b,_=sqrt_bounds(1+hi*hi);lo,hi=lo/(1+a),hi/(1+b)
 lo=F((lo.numerator*S)//lo.denominator,S);hi=F(-((-hi.numerator*S)//hi.denominator),S)
tail=F(2)**(1-len(bs));Bup=F(1)
for l,u in bs:Bup*=1+R*u
Bup/=1-R*tail
Lup=F(100,157)*Bup;assert Lup<F(243,200)
atlo=sum((-1)**j*R**(2*j+1)/F(2*j+1)for j in range(20));assert atlo>F(761,2000)
beta=w*F(243,200);rho=R*beta/(2*alpha*F(761,2000)**3);d=224
bound=620020*d**4*rho**d;assert bound<F(1,4)
assert rho*F(d+1,d)**4<1
assert R*F(243,200)<w
assert F(22,7)*F(27,25)<F(17,5)
assert (F(17,5)+1)*610<2700
assert 500+2700+610+7+2000<6000
assert 4*(2+1220+610+2+610)<10000
assert 10000<6000*128
assert beta<F(3,5)
assert F(31,26)*F(6,7)**128<1
out=dict(all_checks_passed=True,cutoff_d=d,cutoff_m=d//2,L_upper=str(Lup),atan_lower=str(atlo),beta=str(beta),rho=str(rho),relative_error_below='1/4',source_norm_constants_checked=True)
Path(__file__).with_name('weighted_cutoff_certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print('Weighted analytic cutoff checks pass: m>=112.')
print('relative bound at d224',float(bound),'rho',float(rho))
