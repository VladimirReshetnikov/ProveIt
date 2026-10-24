#!/usr/bin/env python3
"""Finite, exact regressions for the merged arithmetic lemmas.

These checks do not prove an unbounded theorem or test ZFC consistency.
All assertions remain active under python -O.
"""
from math import comb, factorial, gcd
from pathlib import Path
import argparse, json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def pell(a,n):
    x,y=1,0
    for _ in range(n):
        x,y=a*x+(a*a-1)*y,x+a*y
    return x,y


def root_base(q,modulus,minimum=100):
    c=2*(q+1)
    d=(q+1)**2+1
    g=gcd(c,modulus)
    require(d%g==0,'root congruence incompatible')
    period=modulus//g
    r=(d//g)*pow(c//g,-1,period)%period
    minimum=max(minimum,q+2)
    a=r+max(0,(minimum-r+period-1)//period)*period
    require(a>=2 and (c*a-d)%modulus==0,'wrong root base')
    require(c*a>=d,'root quotient negative')
    return a


def check():
    counts={}
    fcases=0
    for t in range(6,15):
        true=factorial(t)
        candidates=set(range(0,2001)) | {true-2,true-1,true,true+1,true+2,t*t-1,t*t,t*t+1}
        for f in sorted(candidates):
            v=(f*f+1)**t
            b=comb(f*f+t,t)
            fixed=(v+b-1)//b==f
            require(fixed==(f==true),'squared-radius factorial regression')
            if fixed:
                s=b*f-v
                r=b-s-1
                require(r>=0 and s>=0 and v+b==b*f+r+1 and b==r+s+1,
                        'factorial ceiling reconstruction')
            fcases+=1
    counts['factorial_fixed_point_cases']=fcases
    bootstrap=0
    for t in (16,17,20,24,32,40):
        for f in (0,1,2,5,15,16,31,64,256):
            for x,y in ((0,0),(1,0),(0,1),(3,8),(19,27)):
                r=2+t+x+y+f
                require(f*f+t<=r*r+r<=4**r,'independent coefficient base bound')
                n=f*f+t
                require(n**t < 2**(2*r*r) < 2**(4*r*r),'independent radix bootstrap')
                require(all(comb(n,j)<=n**t for j in range(t+1)),
                        'low coefficient bound')
                bootstrap+=1
    counts['radix_bootstrap_cases']=bootstrap
    boundcases=0
    ell=2**22
    for t in range(16,65):
        f=factorial(t)
        require(3*ell*(t+1)<=2*f,'derived range strict radix budget')
        r=2+t+f
        k=2*r
        require(3*ell*(t+1)<k,'derived radix equality lost strictness')
        require(r>=2**44 and 44*(2**23)<2**44 and 2*(2**23)<=2**44,
                'factorial amplification floor')
        boundcases+=1
    counts['factorial_growth_budget_cases']=boundcases
    rcases=0
    for q in range(2,17):
        for degree in range(1,7):
            mod=q**degree
            a=root_base(q,mod)
            for n in range(0,17):
                x,y=pell(a,n)
                residue=x+(q+1-a)*y
                require(residue>0,'Pell residue is not positive')
                require((residue-pow(q+1,n,mod))%mod==0,'common Pell residue identity')
                rcases+=1
    counts['common_root_pell_residue_cases']=rcases
    dcases=0
    for n in range(1,19):
        for k in range(1,min(9,n+3)):
            for modulus in (2,3,5,7):
                coeffs=[comb(n,j) if j<=n else 0 for j in range(k+1)]
                q=modulus*(max(coeffs)//modulus+1)
                d=q**k
                a=root_base(q,q**(k+2))
                x,y=pell(a,n)
                value=x+(q+1-a)*y
                digit=(value//d)%q
                true=comb(n,k) if k<=n else 0
                require(digit==true,'exact modular binomial digit')
                require((value%(modulus*d)<d)==(true%modulus==0),
                        'modular binomial divisibility')
                low=value%d
                high=(value-low-d*true)//(q*d)
                require(high>=0 and value==low+d*true+q*d*high,
                        'nonnegative exact digit quotient')
                dcases+=1
    counts['digit_and_divisibility_cases']=dcases
    # Negative controls demonstrate sensitivity to the critical arithmetic.
    require((pell(2,2)[0]+(4-2)*pell(2,2)[1]-4**2)%9 !=0,
            'bad common root negative control unexpectedly passed')
    for t in (6,7,8,10,12):
        f=factorial(t)-1
        require(((f*f+1)**t+comb(f*f+t,t)-1)//comb(f*f+t,t)!=f,
                'incorrect factorial accepted')
    counts['negative_controls']=6
    return {'status':'PASS','counts':counts,
            'scope':'finite arithmetic regression only; the unbounded proofs are in PROOF.md',
            'optimized_python_safe':True}


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--output',type=Path)
    a=p.parse_args()
    result=check()
    body=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if a.output:
        a.output.write_text(body)
    print(body,end='')
