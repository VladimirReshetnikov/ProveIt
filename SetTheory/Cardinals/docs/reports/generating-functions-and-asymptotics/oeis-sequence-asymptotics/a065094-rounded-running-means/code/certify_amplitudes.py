"""Exact rational certificates; no external code or floating-point arithmetic."""
from fractions import Fraction as F
from math import factorial,isqrt
import json,sys
from pathlib import Path
sys.dont_write_bytecode=True

def check(b,m):
    if not b: raise RuntimeError(m)

def fixed_decimal(x,d,up=False):
    check(type(d) is int and d>=0, "decimal places must be a nonnegative integer")
    x=F(x)
    s=10**d
    v=x.numerator*s//x.denominator
    if up and F(v,s)<x:v+=1
    return ('-' if v<0 else '')+str(abs(v)//s)+'.'+str(abs(v)%s).zfill(d)

def pi_bounds(m=150):
    check(type(m) is int and m>=1, "positive arctangent term count required")
    def atan(k):
        s=sum((F(1,(2*j+1)*k**(2*j+1))*(-1)**j for j in range(m)),F(0))
        nxt=F((-1)**m,(2*m+1)*k**(2*m+1))
        return min(s,s+nxt),max(s,s+nxt)
    l,u=atan(5);v,w=atan(239)
    return 16*l-4*w,16*u-4*v

def exp_half_bounds(m=160):
    check(type(m) is int and m>=1, "positive exponential term count required")
    s=sum((F(1,2**j*factorial(j)) for j in range(m)),F(0))
    # first omitted term times geometric upper bound
    r=F(1,2**m*factorial(m))*F(2*(m+1),2*(m+1)-1)
    return s,s+r

def sqrt_bounds(x,d=150):
    check(x>=0 and type(d) is int and d>=0, "invalid square-root interval input")
    scale=10**d
    z=isqrt(x.numerator*scale*scale//x.denominator)
    return F(z,scale),F(z+1,scale)

def compute(N=10000,digits=70,intervals=None):
    check(type(N) is int and N>=2, 'N must be an integer at least 2')
    check(type(digits) is int and digits>=1, 'digits must be a positive integer')
    a={'floor':1,'ceiling':1};S=a.copy();Pprev=0;P=1;fact=1
    # P denotes (n-1)! L_(n-1)(-1); Pprev=(n-2)! L_(n-2)(-1)
    examples={k:[1] for k in a}
    for n in range(1,N):
        for mode in a:
            inc=(S[mode]+(n-1 if mode=='ceiling' else 0))//n
            a[mode]+=inc;S[mode]+=a[mode]
            if n<50:examples[mode].append(a[mode])
        Pprev,P=P,2*n*P-(n-1)**2*Pprev
        fact*=n
    nextP=2*N*P-(N-1)**2*Pprev
    T=nextP-N*P
    eL,eU=exp_half_bounds();piL,piU=pi_bounds()
    spL,_=sqrt_bounds(4*piL);_,spU=sqrt_bounds(4*piU)
    out={'N':N,'digits':digits,'arithmetic':'integer and Fraction only','sequences':{}}
    for mode in a:
        shifts=(-1,0) if mode=='floor' else (0,1)
        lo=min(F((a[mode]+shifts[0])*fact,P),F((S[mode]+N*shifts[0])*fact,T))
        hi=max(F((a[mode]+shifts[1])*fact,P),F((S[mode]+N*shifts[1])*fact,T))
        simple_lo=F((S[mode]+N*shifts[0])*fact,T)
        simple_hi=F((S[mode]+N*shifts[1])*fact,T)
        check((lo,hi)==(simple_lo,simple_hi),'cone/sum certificate disagreement')
        check(hi-lo==F(N*fact,T),'certificate width mismatch')
        check(0<=lo<hi,'invalid amplitude interval')
        CL,CU=lo/eU,hi/eL
        cL,cU=CL/spU,CU/spL
        if intervals is not None:
            intervals[mode]={"A":(lo,hi),"C_Bessel":(CL,CU),"c_exp":(cL,cU)}
        out['sequences'][mode]={'A': [fixed_decimal(lo,digits),fixed_decimal(hi,digits,True)],'C_Bessel':[fixed_decimal(CL,digits),fixed_decimal(CU,digits,True)],'c_exp':[fixed_decimal(cL,digits),fixed_decimal(cU,digits,True)],'width_A_upper':fixed_decimal(hi-lo,100,True),'prefix':examples[mode], 'a_N':str(a[mode]), 'sum_N':str(S[mode])}
    return out
if __name__=='__main__': print(json.dumps(compute(),indent=2))
