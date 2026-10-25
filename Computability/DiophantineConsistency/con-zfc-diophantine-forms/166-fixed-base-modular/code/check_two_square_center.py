#!/usr/bin/env python3
"""Finite regressions for TWO_SQUARE_CENTER.md, not an unbounded proof.

No producer, symbolic algebra package, or repository module is imported.
The finite-ring period and quadratic-residue calculations are independent
of any Diophantine source compiler.
"""
import argparse, json
from pathlib import Path

def require(condition, message):
    if not condition:
        raise ValueError(message)

def factor(n):
    result=[];p=2
    while p*p<=n:
        if n%p==0:
            exponent=0
            while n%p==0:n//=p;exponent+=1
            result.append((p,exponent))
        p+=1
    if n>1:result.append((n,1))
    return result

def mul(a,b,d,m):
    return ((a[0]*b[0]+d*a[1]*b[1])%m,
            (a[0]*b[1]+a[1]*b[0])%m)

def power(a,n,d,m):
    result=(1,0)
    while n:
        if n&1:result=mul(result,a,d,m)
        a=mul(a,a,d,m);n//=2
    return result

def order(a,d,m):
    current=(1,0)
    for k in range(1,m*m+1):
        current=mul(current,a,d,m)
        if current==(1,0):return k
    raise ValueError(('unit order exceeded finite ring size',a,d,m))

def two_squares(c,m):
    squares={u*u%m:u for u in range(m)}
    for v in range(m):
        if (c-v*v)%m in squares:return squares[(c-v*v)%m],v
    return None

def run():
    moduli=list(range(3,128,2))+[243,625]
    count=0;local_count=0;max_order=0;nontrivial_k=0;nontrivial_target=0
    for m in moduli:
        fac=factor(m);radical=1
        for p,_ in fac:radical*=p
        for q in [radical,3*radical]:
            target=((q+1)**2+1)*pow(2*(q+1),-1,m)%m
            if target!=1:nontrivial_target+=1
            for w in range(2,19):
                d=w*(w+2);epsilon=(w+1,1)
                seed=power(epsilon,w,d,m)
                o=order(seed,d,m);max_order=max(max_order,o)
                k=o
                while k%2==0:k//=2
                if k!=1:nontrivial_k+=1
                require(k%2==1,'index multiplier not odd')
                g=power(seed,k,d,m)
                remaining=o//k
                require(remaining&(remaining-1)==0,'remaining order not a power of two')
                require(power(g,remaining,d,m)==(1,0),'wrong order projection')
                l=g[0]
                for p,e in fac:
                    pe=p**e
                    if l%p in (1,p-1):require((l*l-1)%pe==0,('trace dichotomy',w,q,m,p,e,k,l))
                    c=(target-l*l)%pe
                    if c:
                        valuation=0
                        while c%p==0:c//=p;valuation+=1
                        require(valuation%2==0,('odd local valuation',w,q,m,p,e,k,l))
                    local_count+=1
                c=(target-l*l)%m
                uv=two_squares(c,m)
                require(uv is not None,('two-square residue missing',w,q,m,k,l,c))
                u,v=uv
                require((l*l+u*u+v*v-target)%m==0,'completion mismatch')
                frame=power(epsilon,w*k,d,2*w)
                require(frame[1]==w,('odd frame quotient',w,k,frame))
                count+=1
    # A valid old frame need not admit the two-square correction. The
    # completeness theorem must choose its odd index multiplier carefully.
    w=4;m=9;q=3;d=w*(w+2)
    minimal_frame=power((w+1,1),w,d,m)
    target=((q+1)**2+1)*pow(2*(q+1),-1,m)%m
    require(minimal_frame[0]==4,'negative control changed')
    require(two_squares((target-minimal_frame[0]**2)%m,m) is None,
            'arbitrary-frame counterexample was not rejected')
    return {'status':'PASS','completion_cases':count,'local_prime_power_cases':local_count,
            'odd_index_multiplier_greater_than_one_cases':nontrivial_k,
            'nontrivial_target_residue_families':nontrivial_target,
            'max_finite_unit_order':max_order,
            'arbitrary_frame_counterexample':{'W':4,'M':9,'q':3,'L':4801,'L_mod_M':4,
                'target_A_mod_M':1,'required_two_square_residue':3,'representable':False},
            'scope':'Finite regressions only; the unbounded proof is TWO_SQUARE_CENTER.md',
            'compiler_imports':False}

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path);args=parser.parse_args()
    result=run();data=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output:args.output.write_text(data)
    print(data,end='')
