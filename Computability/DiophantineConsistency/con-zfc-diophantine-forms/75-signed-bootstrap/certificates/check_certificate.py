"""Authored checks for inert-prime CRT closure. Finite checks are not proof."""
from math import factorial, comb, prod, gcd
import json
from pathlib import Path

def norm_tree(xs):
    if len(xs)==1: return xs[0]
    k=len(xs)//2
    return norm_tree(xs[:k])**2+norm_tree(xs[k:])**2

def prime(n):
    return n>=2 and all(n%d for d in range(2,int(n**.5)+1))

def crt(rs,ms):
    B=prod(ms)
    return sum(r*(B//m)*pow(B//m,-1,m) for r,m in zip(rs,ms))%B

def fall(a,u):
    return prod(a-j for j in range(u+1))

def main():
    checks={}
    count=0
    for H in range(1,8):
      T=factorial(H)
      for n in range(1,H+1):
        ms=[4*T*j-1 for j in range(1,n+1)]
        B=prod(ms); Q=(4*T*n)**n+1; M=4*T*Q+1
        assert all(gcd(a,b)==1 for i,a in enumerate(ms) for b in ms[i+1:])
        assert B<M
        # Avoid astronomical binomial coefficients: exact n-factor product.
        numerator=(4*T)**n*prod(Q+j for j in range(1,n+1))
        assert numerator%M==B
        assert all(m%4==3 for m in ms)
        count+=1
    checks['product_and_coprimality_cases']=count
    count=0
    for p in [3,7,11,19,23,31]:
      for a in range(p):
       for b in range(p):
        assert ((a*a+b*b)%p==0)==(a==b==0)
        count+=1
    checks['anisotropy_pairs']=count
    # Concrete bounded family: for every i<n there is w<=U with w=i.
    n,U,H=3,3,6; T=factorial(H); ms=[4*T*(i+1)-1 for i in range(n)]
    B=prod(ms); c=crt(list(range(n)),ms); a=crt(list(range(n)),ms)
    assert (4*T*(c+1)-1)%B==0
    assert norm_tree([fall(a,U),a-c,4*T*(c+1)-1])%B==0
    checks['crt_complete_fixture']=True
    # Soundness tested over small admissible prime fields.
    count=0
    for p in [7,11,19]:
      U=2
      for i in range(3):
       for a in range(p):
        z=norm_tree([fall(a,U),a-i])%p
        assert (z==0)==(a==i)
        count+=1
    checks['range_and_equation_cases']=count
    # Ordinary sum of >=3 squares is NOT a replacement for nested norms.
    assert (1**2+1**2+1**2)%3==0
    assert norm_tree([1,1,1])%3!=0
    # Dropping the inert-prime condition admits a false pair.
    assert (1**2+2**2)%5==0
    # Dropping the value bound allows nonzero integer residual p.
    assert norm_tree([0,7])%7==0 and 7!=0
    checks['negative_controls']=3
    Path(__file__).with_name('CHECK_RESULTS.json').write_text(json.dumps(checks,indent=2)+'\n')
    print(json.dumps(checks,indent=2))
if __name__=='__main__': main()
