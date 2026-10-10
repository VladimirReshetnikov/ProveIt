"""Exact finite consequences of the written universal Euler contraction proof.

No floating point is used. Finite grids support, but do not replace, the
all-parameter power/chord argument. Gaussian enclosures use its 5/4 budget.
"""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
from math import comb
import json,sys
sys.set_int_max_str_digits(100000)
B=Path(__file__).resolve().parents[1]
def H(n,t):return (1-t)**n/(1+t)
kernel_rows=[];power_count=0;kernel_count=0;equalities=0
for n in [*range(1,17),32,64,128]:
    least=None;witness=None
    for i in range(21):
        r=F(i,20)
        for j in range(1,20):
            v=F(j,20);bound=(1-v)/(1+v)
            gap=bound-(H(n,r*v)-H(n,r))
            assert 0<=H(n,r*v)-H(n,r)<=bound
            assert (gap==0)==(n==1 and r==1)
            kernel_count+=1;equalities+=gap==0
            if gap>0 and (least is None or gap<least):least=gap;witness=(r,v)
    kernel_rows.append(dict(N=n,minimum_strict_slack=str(least),
        witness=dict(r=str(witness[0]),v=str(witness[1]))))
for m in range(2,33):
    for i in range(21):
        r=F(i,20)
        for j in range(1,20):
            v=F(j,20)
            assert (1-r*v)**m-(1-r)**m<=(1-v)/(1+v)
            power_count+=1
for j in range(1,20):
    v=F(j,20);r=1/(1+v)
    assert (1-r*v)**2-(1-r)**2==(1-v)/(1+v)
def toy_euler(n,values):
    return sum((sum((-1)**k*comb(j,k)*values[k] for k in range(j+1))/F(2**(j+1)) for j in range(n)),F(0))
normalizations=0
for i in range(1,9):
    x=F(i,8)
    for j in range(1,8):
        v=F(j,8)
        # Direct imaginary part of x*i^2/((1-x*i)(1-x*v*i)).
        real=1-x*x*v;imag=-(x+x*v)
        g=x*imag/(real*real+imag*imag)
        values=[x**(2*k)*sum(v**ell for ell in range(2*k)) for k in range(32)]
        for n in [*range(1,9),16,32]:
            en=toy_euler(n,values)
            predicted=(H(n,x*x*v*v)-H(n,x*x))/(1-v)
            assert 2**n*(en-g)==predicted
            normalizations+=1
x=v=F(1,2);values=[x**(2*k)*sum(v**ell for ell in range(2*k)) for k in range(3)]
baseline=toy_euler(3,values);values[1]+=1
assert toy_euler(3,values)!=baseline
S=10**100;root_checks=0
@lru_cache(None)
def inverse_power(n,e):
    global root_checks
    p,q=e.numerator,e.denominator
    if p==0:return S,S
    target=S**q;factor=n**p;lo,hi=0,S+1
    while hi-lo>1:
        mid=(lo+hi)//2
        if mid**q*factor<=target:lo=mid
        else:hi=mid
    assert lo**q*factor<=target<(lo+1)**q*factor
    root_checks+=1
    return lo,lo if lo**q*factor==target else lo+1
def coefficients(a,b,last):
    out=[(0,0)];hl=hu=0
    for n in range(1,last+1):
        l,u=inverse_power(n,a);out.append((l*hl,u*hu))
        l,u=inverse_power(n,b);hl+=l;hu+=u
    return out
def linear(coeffs,terms):
    lo=hi=0
    for n,w in terms:
        l,u=coeffs[n]
        if w<0:l,u=u,l
        lo+=w*l;hi+=w*u
    return F(lo,S*S),F(hi,S*S)
def euler(coeffs,n):
    return tuple(x/2**n for x in linear(coeffs,[(2*k+1,(-1)**k*sum(comb(n,j) for j in range(k+1,n+1))) for k in range(n)]))
def gaussian(coeffs,n):
    el,eu=euler(coeffs,n)
    return el-F(5,4)/2**n,eu
pairs=[(F(0),F(3,2)),(F(1,10),F(1,10)),(F(1,10),F(9,10)),
       (F(1,10),F(1)),(F(1,10),F(3,2)),(F(1,20),F(3,2)),
       (F(3,4),F(3,4)),(F(1,2),F(2)),(F(1),F(1,2)),
       (F(3,2),F(1,10)),(F(2),F(3,2))]
n=160;axis={};cases=[];sign_count=0;tail_count=0
for b in sorted({b for a,b in pairs}):
    l,u=gaussian(coefficients(F(0),b,2*n-1),n)
    axis[b]=(-2*u,-2*l)
for a,b in pairs:
    coeffs=coefficients(a,b,2*n-1);gl,gu=gaussian(coeffs,n)
    assert gl<gu<0
    for k in range(1,33):
        dl,du=linear(coeffs,[(2*j+1,(-1)**j*comb(k,j)) for j in range(k+1)])
        assert du<0
        sign_count+=1
    tails=[]
    for k in [1,2,4,8,16,32]:
        el,eu=euler(coeffs,k);lower,upper=2**k*(el-gu),2**k*(eu-gl)
        assert 0<lower<upper
        if a>0 or k>1:assert upper<axis[b][0],(a,b,k)
        else:assert (lower,upper)==axis[b]
        tails.append(dict(N=k,scaled_error_interval=dict(lower=str(lower),upper=str(upper)),
                          upper_below_axis_lower=(upper<axis[b][0])))
        tail_count+=1
    cases.append(dict(a=str(a),b=str(b),Euler_terms=n,
        Gaussian_interval=dict(lower=str(gl),upper=str(gu)),
        axis_constant_interval=dict(lower=str(axis[b][0]),upper=str(axis[b][1])),
        rational_error_constant='5/4',tails=tails,passed=True))
record=dict(status='PASS',arithmetic='Standard-library integers and Fractions',
    kernel_grid_cases=kernel_count,kernel_equality_cases=equalities,
    power_grid_cases=power_count,quadratic_optimum_equalities=19,kernel_rows=kernel_rows,
    exact_tail_normalizations=normalizations,coefficient_corruption_controls=1,
    fractional_grid_digits=100,integer_root_inequalities=root_checks,
    Euler_increment_signs=sign_count,scaled_tail_enclosures=tail_count,Gaussian_cases=cases,
    scope='Exact finite grids, negative Euler signs and analytic Gaussian/tail enclosures. The 5/4 budget follows from the written all-parameter contraction proof. Finite grid checks do not prove the universal inequality; axis-maximum decimals are not certified.')
(B/'verification/universal-Euler-certificates.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in record.items() if k not in ['kernel_rows','Gaussian_cases']},indent=2))
